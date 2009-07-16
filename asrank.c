#include <sys/types.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include "asrank.h"

int strict = 0;
int debuglevel = 0;
int progress = 0;
char *desc_fname;
typedef uint32_t asn_t;

typedef struct {
	int as16[65536];
	int *as32[65536];
} asarr;

struct aspath {
	struct aspath *prev;
	asn_t asn;
	uint16_t nnei;
	int pathes:24;
	int leaf:8;
	struct aspath **next;
} rootpath;

struct aspath rootpath;

struct rib_t {
	struct rib_t *next;
#ifdef SAVE_PREFIX
	uint32_t prefix;	/* needed only for debug */
#endif
	u_char preflen;
	u_char npathes;
	struct rib_pathes {
		struct aspath *path;
	} pathes[0];
} *rib_head;

void debug(int level, char *format, ...);

asarr origin, wasas, ndx;
int *tier1, *routes, *proutes, *npath, *tier1_bad, *n24, *npref, *asorder;
char *upstreams;
int *upstreams_arr;
asn_t *asnum;
struct rel_t {
	int nas_rel;
	struct {
		asn_t asn;
		int cnt;
		int val;
	} *as_rel;
} *rel;
struct coneas_t {
	int nas;
	int *asn;
} *coneas;
int nas, ntier1, ntier1_hints, inv_pathes, fullview, nupstreams;
asn_t tier1_arr[2048]; /* array for connections between tier1s should not be too large */

static void usage(void)
{
	printf("Usage: asrank [-s] [-p] [-d level] [-n fname] [-t asn] [file]\n");
	printf("  Options:\n");
	printf("-s          - no euristic, use only strict relations\n");
	printf("-t asn      - hint that asn is tier1\n");
	printf("-d level    - set debug level\n");
	printf("-p          - show progress bar\n");
	printf("-n fname    - get AS names from fname (forman: \"asn: desc\")\n");
	printf("file - input dumb RIB table\n");
}

/* we do not change byte order in ashi and aslo, just change the words order */
static int *as(asarr *arr, asn_t asn)
{
	uint16_t ashi, aslo;

	ashi = *(uint16_t *)&asn;
	aslo = *((uint16_t *)&asn+1);
	if (ashi == 0)
		return &(arr->as16[aslo]);
	if (arr->as32[ashi] == NULL)
		arr->as32[ashi] = calloc(65536, sizeof(arr->as32[0][0]));
	return &(arr->as32[ashi][aslo]);
}

int asndx(asn_t asn)
{
	return *as(&ndx, asn);
}

static void freeas(asarr *arr)
{
	int i;

	for (i=0; i<sizeof(arr->as32)/sizeof(arr->as32[0]); i++)
		if (arr->as32[i]) {
			free(arr->as32[i]);
			arr->as32[i] = NULL;
		}
}

char *printas(asn_t asn)
{
	static char printasbuf[20];

	if (asn < 65536)
		snprintf(printasbuf, sizeof(printasbuf)-1, "%u", asn);
	else
		snprintf(printasbuf, sizeof(printasbuf)-1, "%u.%u", asn>>16, asn % 65536);
	return printasbuf;
}

char *printaspath(asn_t *aspath, int aspathlen)
{
	static char printaspathbuf[4096];
	char *p;
	int i;

	p = printaspathbuf;
	for (i=0; i<aspathlen; i++) {
		if (i) *p++ = ' ';
		strcpy(p, printas(ntohl(aspath[i])));
		p += strlen(p);
	}
	return printaspathbuf;
}

char *printip(uint32_t ip)
{
	struct in_addr in;

	in.s_addr = ip;
	return inet_ntoa(in);
}

void printtree(asn_t *aspath, int pathlen)
{
	debug(8, "%s", printaspath(aspath, pathlen));
}

static void get_npath(asn_t *aspath, int pathlen)
{
	int i;

	for (i=0; i<pathlen; i++)
		npath[asndx(aspath[i])]++;
}

static void fill_asndx(asn_t *aspath, int pathlen)
{
	int i;

	for (i=0; i<pathlen; i++) {
		if (asndx(aspath[i]) == -1) {
			*as(&ndx, aspath[i]) = nas;
			asnum[nas++] = aspath[i];
		}
	}
}

static void addconeas(int as1, asn_t as2)
{
	int left, right, new;

	left = 0; right = coneas[as1].nas-1;
	while (left <= right) {
		new = (left + right) / 2;
		if (coneas[as1].asn[new] > as2)
			right = new-1;
		else if (coneas[as1].asn[new] < as2)
			left = new+1;
		else
			break;
	}
	if (left > right) {
		/* new */
		coneas[as1].nas++;
		coneas[as1].asn = realloc(coneas[as1].asn, coneas[as1].nas * sizeof(coneas[as1].asn[0]));
		new = left;
		bcopy(&(coneas[as1].asn[new]), &(coneas[as1].asn[new+1]), (coneas[as1].nas-new-1)*sizeof(coneas[as1].asn[0]));
		coneas[as1].asn[new] = as2;
	}
}

static int mkrel(asn_t as1, asn_t as2, int val)
{
	int left, right, new;
	struct rel_t *p;

	p = &(rel[asndx(as1)]);
	left = 0; right = p->nas_rel-1;
	while (left <= right) {
		new = (left + right) / 2;
		if (p->as_rel[new].asn > as2)
			right = new-1;
		else if (p->as_rel[new].asn < as2)
			left = new+1;
		else
			break;
	}
	if (left > right) {
		/* new */
		p->nas_rel++;
		p->as_rel = realloc(p->as_rel, p->nas_rel * sizeof(p->as_rel[0]));
		new = left;
		bcopy(&(p->as_rel[new]), &(p->as_rel[new+1]), (p->nas_rel-new-1)*sizeof(p->as_rel[0]));
		p->as_rel[new].asn = as2;
		p->as_rel[new].cnt = abs(val);
		p->as_rel[new].val = val;
	} else {
		p->as_rel[new].cnt += abs(val);
		p->as_rel[new].val += val;
	}
	return p->as_rel[new].val;
}

static void maxroutes(struct aspath *aspath)
{
	int i;

	for (i=0; i<aspath->nnei; i++) {
		if (routes[asndx(aspath->next[i]->asn)] < aspath->next[i]->pathes)
			routes[asndx(aspath->next[i]->asn)] = aspath->next[i]->pathes;
		if (aspath->asn && proutes[asndx(aspath->asn)] < aspath->next[i]->pathes)
			proutes[asndx(aspath->asn)] = aspath->next[i]->pathes;
		if (aspath->asn && aspath->next[i]->pathes > fullview/3) {
			mkrel(aspath->asn, aspath->next[i]->asn, aspath->next[i]->pathes);
			mkrel(aspath->next[i]->asn, aspath->asn, -aspath->next[i]->pathes);
		}
		maxroutes(aspath->next[i]);
	}
}

static void foreach_aspath_rec(struct aspath *aspath, void (*func)(asn_t *aspath, int pathlen), int level)
{
	static asn_t path[MAXPATHLEN];
	int i;

	for (i=0; i<aspath->nnei; i++) {
		path[level] = aspath->next[i]->asn;
		if (aspath->next[i]->leaf)
			func(path, level+1);
		foreach_aspath_rec(aspath->next[i], func, level+1);
	}
}

static void foreach_aspath(void (*func)(asn_t *aspath, int pathlen))
{
	foreach_aspath_rec(&rootpath, func, 0);
}

static void check_valid_path(asn_t *aspath, int pathlen)
{
	int i, seqlen;

	seqlen = 0;
	for (i=0; i<pathlen; i++) {
		if (tier1[asndx(aspath[i])])
			seqlen++;
		else {
			if (seqlen > 2) {
				tier1_bad[asndx(aspath[i-1])]++;
				tier1_bad[asndx(aspath[i-seqlen])]++;
				inv_pathes++;
				if (debuglevel >= 4) {
					char *p = strdup(printaspath(aspath+i-seqlen, seqlen));
					debug(4, "Invalid path: %s (tier1 part: %s)", printaspath(aspath, pathlen), p);
					free(p);
				}
			}
			seqlen = 0;
		}
	}
	if (seqlen > 2) {
		tier1_bad[asndx(aspath[i-1])]++;
		tier1_bad[asndx(aspath[i-seqlen])]++;
		inv_pathes++;
		if (debuglevel >= 4) {
			char *p = strdup(printaspath(aspath+i-seqlen, seqlen));
			debug(4, "Invalid path: %s (tier1 part: %s)", printaspath(aspath, pathlen), p);
			free(p);
		}

	}
}

static void make_rel1(asn_t *aspath, int pathlen)
{
	int i, first, last;

	first = last = 0;
	for (i=0; i<pathlen; i++) {
		if (tier1[asndx(aspath[i])]) {
			if (!first)
				first = i+1;
			else
				last = i+1;
		}
	}
	if (!first) return;
	if (!last) last = first;
	for (i=1; i<pathlen; i++) {
		if (i+1<first || (i+1==first && last==first+1)) {
			mkrel(aspath[i-1], aspath[i], 1);
			mkrel(aspath[i], aspath[i-1], -1);
		}
		if (i>last || (i == last && last == first+1)) {
			mkrel(aspath[i-1], aspath[i], -1);
			mkrel(aspath[i], aspath[i-1], 1);
		}
	}
}

static int cmpas(const void *as1, const void *as2)
{
	return n24[*(int *)as2] - n24[*(int *)as1];
}

int main(int argc, char *argv[])
{
	int ch, i, j, k;
	char *p;
	FILE *f;
	struct dump_entry entry;
	int aspathes;
	asn_t asn;
	struct rib_t *prefix, *prevprefix;

	while ((ch = getopt(argc, argv, "sd:ht:n:p")) != -1) {
		switch (ch) {
			case 's':	strict = 1; break;
			case 'd':	debuglevel = atoi(optarg); break;
			case 'p':	progress = 1; break;
			case 'h':	usage(); exit(0);
			case 't':	if ((p=strchr(optarg, '.'))) {
						*p++ = '\0';
						asn = (atoi(optarg)<<16) + atoi(p);
					} else
						asn = atoi(optarg);
					asn = htonl(asn);
					tier1_arr[ntier1_hints++] = asn;
					if (asndx(asn) == 0) {
						nas++;
						*as(&ndx, asn) = -1;
					}
					break;
			case 'n':	desc_fname = strdup(optarg); break;
		}
	}
	if (argv[optind] && strcmp(argv[optind], "-")) {
		f = fopen(argv[optind], "r");
		if (f == NULL) {
			fprintf(stderr, "Cannot open file %s: %s!\n", argv[optind], strerror(errno));
			exit(1);
		}
	} else
		f = stdin;
	if (open_dump(f)) {
		fprintf(stderr, "Cannot open dump\n");
		if (f != stdin) fclose(f);
		exit(1);
	}
	debug(1, "Parsing input file");
	aspathes = 0;
	while (read_dump(f, &entry) == 0) {
		int norigins;
		int origins[MAXPATHES];

		if (entry.preflen > 24 || entry.preflen == 0)
			continue;
		norigins = 0;
		prefix = malloc(sizeof(struct rib_t) + entry.pathes*sizeof(struct rib_pathes));
		if (rib_head)
			prevprefix->next = prefix;
		else
			rib_head = prefix;
		prevprefix = prefix;
#ifdef SAVE_PREFIX
		prefix->prefix = entry.prefix;
#endif
		prefix->preflen = entry.preflen;
		prefix->npathes = 0;
		for (i=0; i<entry.pathes; i++) {
			int pathlen;
			asn_t path[MAXPATHLEN];
			asn_t prevas;
			struct aspath *curpath;

			if (debuglevel >= 6) {
				char aspath[4096], *p;
				p = aspath;
				*p = '\0';
				for (j=0; entry.aspath[i][j]; j++) {
					if (j>0) *p++ = ' ';
					strcpy(p, printas(ntohl(entry.aspath[i][j])));
					p += strlen(p);
					if (p - aspath >= sizeof(aspath)-12)
						break;
				}
				debug(6, "%s/%d|%s|%s", printip(entry.prefix), entry.preflen, printas(entry.origas[i]), aspath);
			}
			if (entry.pathes == 0 && debuglevel >= 6)
				debug(6, "%s/%d|%s| <no data>", printip(entry.prefix), entry.preflen, printas(entry.origas[i]));
			/* exclude the same origins */
			if (norigins >= MAXPATHES) {
				warning("Too many routes for %s/%d", printip(entry.prefix), entry.preflen);
				continue;
			}
			if (*as(&origin, entry.origas[i])) continue;
			*as(&origin, entry.origas[i]) = 1;
			origins[norigins++] = entry.origas[i];
			/* remove prepends and loops */
			pathlen = 0;
			prevas = 0;
			for (j=0; entry.aspath[i][j]; j++) {
				if (prevas == entry.aspath[i][j])
					continue;
				prevas = entry.aspath[i][j];
				if (*as(&wasas, prevas)) {
					/* loop */
					int newpathlen;

					for (k=0; k<pathlen; k++)
						if (path[k] == prevas)
							break;
					newpathlen = ++k;
					for (; k<pathlen; k++)
						*as(&wasas, path[k]) = 0;
					pathlen = newpathlen;
					continue;
				}
				*as(&wasas, prevas) = 1;
				path[pathlen++] = prevas;
			}
			curpath = &rootpath;
			for (j=0; j<pathlen; j++) {
				int left, right, new;

				left = 0; right = curpath->nnei-1;
				while (left <= right) {
					new = (left + right)/2;
					if (curpath->next[new]->asn < path[j])
						left = new+1;
					else if (curpath->next[new]->asn > path[j])
						right = new-1;
					else
						break;
				}
				if (left > right) {
					/* new */
					curpath->next = realloc(curpath->next, ++(curpath->nnei) * sizeof(curpath->next[0]));
					new = left;
					bcopy(&(curpath->next[new]), &(curpath->next[new+1]), (curpath->nnei-new-1)*sizeof(curpath->next[0]));
					curpath->next[new] = calloc(1, sizeof(curpath->next[0][0]));
					curpath->next[new]->prev = curpath;
					curpath->next[new]->asn = path[j];
				}
				curpath = curpath->next[new];
				curpath->pathes++;
			}
			if (!curpath->leaf) {
				aspathes++;
				curpath->leaf = 1;
			}
			prefix->pathes[prefix->npathes++].path = curpath;
			for (j=0; j<pathlen; j++) {
				*as(&wasas, path[j]) = 0;
				if (asndx(path[j]) == 0) {
					nas++;
					*as(&ndx, path[j]) = -1;
				}
			}
		}
		for (i=0; i<norigins; i++)
			*as(&origin, origins[i]) = 0;
		fullview++;
		if (progress && fullview % 3000 == 0) {
			printf("#");
			fflush(stdout);
		}
	}
	if (f != stdin) fclose(f);
	if (progress) printf("\n");
	freeas(&origin);
	freeas(&wasas);
	debug(1, "RIB table parsed, %d prefixes, %d pathes", fullview, aspathes);
	/* foreach_aspath(printtree); */

	asnum = calloc(nas, sizeof(asn_t));
	nas = 0;
	foreach_aspath(fill_asndx);

	routes = calloc(nas, sizeof(routes[0]));
	proutes = calloc(nas, sizeof(proutes[0]));
	rel = calloc(nas, sizeof(*rel));
	maxroutes(&rootpath);
	ntier1 = ntier1_hints;
	tier1 = calloc(nas, sizeof(tier1[0]));
	tier1_bad = calloc(nas, sizeof(tier1_bad[0]));
	for (ntier1=0; ntier1<ntier1_hints; ntier1++)
		tier1[asndx(tier1_arr[ntier1])] = ntier1+1;
	for (i=0; i<nas; i++) {
		if (ntier1 >= sizeof(tier1_arr)/sizeof(tier1_arr[0])) {
			warning("Too many tier1 candidates found");
			break;
		}
		if (routes[i] > fullview/2 && proutes[i] < fullview/2) {
			if (tier1[i] == 0) {
				tier1_arr[ntier1++] = asnum[i];
				tier1[i] = ntier1;
			}
		}
	}
	free(routes);
	free(proutes);
	debug(1, "Found %d tier1 candidates", ntier1);

	npath = calloc(nas, sizeof(npath[0]));
	foreach_aspath(get_npath);

	for (;;) {
		int maxndx;
		double rate, maxrate;

		inv_pathes = 0;
		foreach_aspath(check_valid_path);
		if (inv_pathes == 0) break;
		debug(2, "Found %d invalid pathes", inv_pathes);
		/* remove one as from tier1 list */
		maxrate = 0;
		maxndx = -1;
		for (i=ntier1_hints; i<ntier1; i++) {
			if (tier1_arr[i] == 0) continue;
			rate = (double)tier1_bad[asndx(tier1_arr[i])] / npath[asndx(tier1_arr[i])];
			if (rate > maxrate) {
				maxrate = rate;
				maxndx = i;
			}
		}
		if (maxndx == -1) {
			warning("Only specified Tier1 rest, but invalid pathes exists");
			break;
		}
		debug(2, "%s is not tier1 (%d rate, %d pathes)", printas(ntohl(tier1_arr[maxndx])),
		      tier1_bad[asndx(tier1_arr[maxndx])], npath[asndx(tier1_arr[maxndx])]);
		for (i=0; i<ntier1; i++)
			if (tier1_arr[i])
				tier1_bad[asndx(tier1_arr[i])] = 0;
		tier1[asndx(tier1_arr[maxndx])] = 0;
		tier1_arr[maxndx] = 0;
	}

	debug(1, "Tier1 list created");
	for (i=0; i<ntier1; i++) {
		if (tier1_arr[i])
			debug(1, "  %s", printas(ntohl(tier1_arr[i])));
	}

	foreach_aspath(make_rel1);
	/* if relations is less then 90% assurance, then discard it */
	for (i=0; i<nas; i++)
		for (j=0; j<rel[i].nas_rel; j++)
			if (abs(rel[i].as_rel[j].val)*10 < rel[i].as_rel[j].cnt*9)
				rel[i].as_rel[j].val = 0;
	/* add relations for "a - b > c"  ->   a > b and others like this? */
	debug(1, "AS relations built");

	/* ok, now calculate rating */
	n24 = calloc(nas, sizeof(*n24));
	npref = calloc(nas, sizeof(*npref));
	coneas = calloc(nas, sizeof(*coneas));
	upstreams = calloc(nas, sizeof(*upstreams));
	upstreams_arr = calloc(nas, sizeof(*upstreams_arr));
	nupstreams = 0;
	for (prefix = rib_head; prefix; prefix = prefix->next) {
		for (i=0; i<prefix->npathes; i++) {
			int aspathlen, jlast, crel, inc;
			struct aspath *pt;
			asn_t aspath[MAXPATHLEN];

			aspathlen = 0;
			for (pt = prefix->pathes[i].path; pt->asn; pt = pt->prev) {
				aspath[aspathlen++] = pt->asn;
			}
			/* aspath is in reverse order! */
			jlast = 0;
			inc = 1; /* 1 - going up, 2 - going down, -1 - invalid path (up after down) */
			for (j=1; j<aspathlen; j++) {
				mkrel(aspath[j], aspath[j-1], 0); /* define */
				crel = mkrel(aspath[j-1], aspath[j], 0);
				if (crel>0) {
					if (inc == 1)
						jlast = j;
					else
						inc = -1;
				}
				else if (crel<0) {
					if (inc != -1) inc = 2;
				}
			}
			for (j=0; j<=jlast; j++) {
				addconeas(asndx(aspath[j]), aspath[0]);
				if (upstreams[asndx(aspath[j])] == 0) {
					upstreams[asndx(aspath[j])] = 1;
					upstreams_arr[nupstreams++] = asndx(aspath[j]);
				}
			}
			if (debuglevel >= 3) {
				/* revert aspath direction */
				asn_t tmp_asn;
				char pathstr[MAXPATHLEN*6], *p;

				for (j=aspathlen/2-1; j>=0; j--) {
					tmp_asn = aspath[j];
					aspath[j] = aspath[aspathlen-1-j];
					aspath[aspathlen-1-j] = tmp_asn;
				}
				/* make aspath string */
				p = pathstr;
				for (j=0; j<aspathlen; j++) {
					if (j) {
						crel = mkrel(aspath[j-1], aspath[j], 0);
						if (crel>0)
							*p++ = '>';
						else if (crel<0)
							*p++ = '<';
						else
							*p++ = '-';
					}
					strcpy(p, printas(ntohl(aspath[j])));
					p += strlen(p);
				}
				if (inc == -1) strcpy(p, " (!)");
#ifdef SAVE_PREFIX
				debug(3, "%s/%d: %s", printip(prefix->prefix), prefix->preflen, pathstr);
#else
				debug(3, "?.?.?.?/%d: %s", prefix->preflen, pathstr);
#endif
			}
		}
		for (i=0; i<nupstreams; i++) {
			n24[upstreams_arr[i]] += (1<<(24-prefix->preflen));
			npref[upstreams_arr[i]]++;
			upstreams[upstreams_arr[i]] = 0;
		}
		nupstreams = 0;
	}
	/* Ok, now sort and output statistics */
	free(upstreams);
	asorder = calloc(nas, sizeof(*asorder));
	for (i=0; i<nas; i++)
		asorder[i] = i;
	qsort(asorder, nas, sizeof(*asorder), cmpas);
	for (i=0; i<nas; i++)
		printf("%5d. %7s  %9d  %7d  %5d %4d\n", i+1, printas(ntohl(asnum[asorder[i]])),
		       n24[asorder[i]], npref[asorder[i]], coneas[asorder[i]].nas, rel[asorder[i]].nas_rel);
	return 0;
}

void debug(int level, char *format, ...)
{
	va_list ap;
	char buf[1024];
	char buftime[64];
	time_t curtime;

	if (level > debuglevel) return;
	curtime = time(NULL);
	strftime(buftime, sizeof(buftime), "%b %e %T", localtime(&curtime));
	va_start(ap, format);
	vsnprintf(buf, sizeof(buf), format, ap);
	va_end(ap);
	printf("%s %s\n", buftime, buf);
}

void warning(char *format, ...)
{
	va_list ap;
	char buf[1024];

	va_start(ap, format);
	vsnprintf(buf, sizeof(buf), format, ap);
	va_end(ap);
	fprintf(stderr, "%s\n", buf);
}

void error(char *format, ...)
{
	va_list ap;
	char buf[1024];

	va_start(ap, format);
	vsnprintf(buf, sizeof(buf), format, ap);
	va_end(ap);
	fprintf(stderr, "%s\n", buf);
}

