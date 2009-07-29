#include <sys/types.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <ctype.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include "asrank.h"

int strict = 0;
int debuglevel = 0;
int progress = 0;
char *desc_fname;
typedef uint32_t asn_t;
typedef u_char peerndx_t;

typedef struct {
	int as16[65536];
	int *as32[65536];
} asarr;

struct aspath {
	struct aspath *prev;
	struct aspath **next;
	asn_t asn;
	int pathes:24;
	int noinv:8;
	uint16_t nnei;
	uint16_t leaf;
} rootpath;

int npeers;
uint32_t *peers;

#define peer(a)	((peerndx_t *)&((a)->pathes[(a)->npathes]))
struct rib_t {
	struct rib_t *left, *right;
	u_char npathes;
	struct aspath *pathes[0];
	/* peerndx_t peer[]; */
} *rib_root;

void debug(int level, char *format, ...);

asarr origin, wasas, ndx;
int *tier1, *routes, *proutes, *npath, *tier1_bad, *n24, *npref, *asorder, *group;
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
int nas, ntier1, ntier1_hints, inv_pathes, fullview, aspathes, nupstreams;
asn_t tier1_arr[2048]; /* array for connections between tier1s should not be too large */
uint32_t mask[24];
int ngroups;
struct {
	int nas;
	asn_t *asn;
} *asgroup;
int horlinks, totier1, viatier1;

static void usage(void)
{
	printf("Usage: asrank [-s] [-p] [-d level] [-n fname] [-t asn] [-g fname] [-w fname] [file]\n");
	printf("  Options:\n");
	printf("-s          - no euristic, use only strict relations\n");
	printf("-t asn      - hint that asn is tier1\n");
	printf("-d level    - set debug level\n");
	printf("-p          - show progress bar\n");
	printf("-n fname    - get AS names from fname (format: \"asn: desc\")\n");
	printf("-g fname    - file defined sibling groups, one group per line, comma separated\n");
	printf("-w fname    - write result table to fname for future processing\n");
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

	asn = ntohl(asn);
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
		strcpy(p, printas(aspath[i]));
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
		bcopy(&(coneas[as1].asn[new]), &(coneas[as1].asn[new+1]), (coneas[as1].nas-new-1) * sizeof(coneas[as1].asn[0]));
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
		bcopy(&(p->as_rel[new]), &(p->as_rel[new+1]), (p->nas_rel-new-1) * sizeof(p->as_rel[0]));
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
		} else {
			mkrel(aspath->asn, aspath->next[i]->asn, 0);
			mkrel(aspath->next[i]->asn, aspath->asn, 0);
		}
		maxroutes(aspath->next[i]);
	}
}

static void add_tier1(struct aspath *aspath)
{
	int i;

	for (i=0; i<aspath->nnei; i++) {
		if (tier1[asndx(aspath->asn)] == 1 && tier1[asndx(aspath->next[i]->asn)] != 1) {
			if (tier1[asndx(aspath->next[i]->asn)] == 0 &&
			    proutes[asndx(aspath->next[i]->asn)] < fullview/2 &&
			    routes[asndx(aspath->next[i]->asn)] > fullview/20 &&
			    rel[asndx(aspath->next[i]->asn)].nas_rel > 20) {
				if (ntier1 >= sizeof(tier1_arr)/sizeof(tier1_arr[0])) {
					warning("Too many Tier1 candidates found");
					break;
				}
				tier1_arr[ntier1++] = aspath->next[i]->asn;
				tier1[asndx(aspath->next[i]->asn)] = 2;
			}
		} else
			add_tier1(aspath->next[i]);
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
		if (level+1 < MAXPATHLEN)
			foreach_aspath_rec(aspath->next[i], func, level+1);
	}
}

static void foreach_aspath(void (*func)(asn_t *aspath, int pathlen))
{
	foreach_aspath_rec(&rootpath, func, 0);
}

static int check_valid_path(asn_t *aspath, int pathlen)
{
	int i, seqlen, ret;

	seqlen = ret = 0;
	for (i=0; i<pathlen; i++) {
		if (tier1[asndx(aspath[i])])
			seqlen++;
		else {
			if (seqlen > 2) {
				tier1_bad[asndx(aspath[i-1])]++;
				tier1_bad[asndx(aspath[i-seqlen])]++;
				inv_pathes++;
				ret = 1;
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
		ret = 1;
		if (debuglevel >= 4) {
			char *p = strdup(printaspath(aspath+i-seqlen, seqlen));
			debug(4, "Invalid path: %s (tier1 part: %s)", printaspath(aspath, pathlen), p);
			free(p);
		}
	}
	return ret;
}

static int check_valid_path_recurs(struct aspath *aspath, int level)
{
	static asn_t path[MAXPATHLEN];
	int i, ret;

	ret = 0;
	for (i=0; i<aspath->nnei; i++) {
		path[level] = aspath->next[i]->asn;
		if (aspath->next[i]->leaf)
			ret |= check_valid_path(path, level+1);
		if (level+1 < MAXPATHLEN)
			if (!aspath->next[i]->noinv)
				ret |= check_valid_path_recurs(aspath->next[i], level+1);
	}
	if (!ret)
		aspath->noinv = 1;
	return ret;
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
	if (!first) {
		horlinks++;
		return;
	}
	if (!last) last = first;
	if (last == pathlen)
		totier1++;
	else if (first != 1)
		viatier1++;
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

static int collect_stats(struct rib_t *route, int preflen)
{
	static asn_t route_aspath[MAXPATHLEN];
	static uint32_t curip;
	int nets;
	/* following vars can be not local in this recursive function */
	/* but recursion depth is not high (only 24), so I think this local vars are ok */
	int i, j, aspathlen, jlast, crel, inc, ups;
	struct aspath *pt;
	
	nets = 0;
	if (route == NULL) return 0;
	if (route->left)
		nets += collect_stats(route->left, preflen+1);
	if (route->right) {
		curip |= mask[preflen];
		nets += collect_stats(route->right, preflen+1);
		curip &= ~mask[preflen];
	}
	if (!route->npathes)
		return nets;
	nets = (1<<(24-preflen)) - nets; /* value of the current route */
	for (i=0; i<route->npathes; i++) {
		aspathlen = 0;
		for (pt = route->pathes[i]; pt->asn; pt = pt->prev)
			route_aspath[aspathlen++] = pt->asn;
		/* aspath is in reverse order! */
		jlast = 0;
		inc = 1; /* 1 - going up, 2 - going down, -1 - invalid path (up after down) */
		for (j=1; j<aspathlen; j++) {
			crel = mkrel(route_aspath[j-1], route_aspath[j], 0);
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
			ups = asndx(route_aspath[j]);
			if (group[ups]) ups=asndx(asgroup[group[ups]-1].asn[0]);
			addconeas(ups, route_aspath[0]);
			if (upstreams[ups] == 0) {
				upstreams[ups] = 1;
				upstreams_arr[nupstreams++] = ups;
			}
		}
		if (debuglevel >= 3) {
			/* revert aspath direction */
			static char pathstr[MAXPATHLEN*6];
			char *p;
			asn_t tmp_asn;

			for (j=aspathlen/2-1; j>=0; j--) {
				tmp_asn = route_aspath[j];
				route_aspath[j] = route_aspath[aspathlen-1-j];
				route_aspath[aspathlen-1-j] = tmp_asn;
			}
			/* make aspath string */
			p = pathstr;
			for (j=0; j<aspathlen; j++) {
				if (j) {
					crel = mkrel(route_aspath[j-1], route_aspath[j], 0);
					if (crel>0)
						*p++ = '>';
					else if (crel<0)
						*p++ = '<';
					else
						*p++ = '-';
				}
				strcpy(p, printas(route_aspath[j]));
				p += strlen(p);
			}
			if (inc == -1) strcpy(p, " (!)");
			debug(3, "%s/%d: %s", printip(curip), preflen, pathstr);
		}
	}
	for (i=0; i<nupstreams; i++) {
		n24[upstreams_arr[i]] += nets;
		npref[upstreams_arr[i]]++;
		upstreams[upstreams_arr[i]] = 0;
	}
	nupstreams = 0;
	return (1<<(24-preflen));
}

static int cmpas(const void *as1, const void *as2)
{
	if (n24[*(int *)as2] != n24[*(int *)as1])
		return n24[*(int *)as2] - n24[*(int *)as1];
	if (coneas[*(int *)as2].nas != coneas[*(int *)as1].nas)
		return coneas[*(int *)as2].nas - coneas[*(int *)as1].nas;
	if (npref[*(int *)as2] != npref[*(int *)as1])
		return npref[*(int *)as2] - npref[*(int *)as1];
	return rel[*(int *)as2].nas_rel - rel[*(int *)as1].nas_rel;
}

asn_t readasn(char *str)
{
	char *p;
	asn_t asn;

	if ((p=strchr(str, '.'))) {
		*p = '\0';
		asn = (atoi(str)<<16) + atoi(p+1);
		*p = '.';
	} else
		asn = atoi(str);
	return htonl(asn);
}

peerndx_t peerndx(uint32_t ip)
{
	int left, right, new;

	left=0, right=npeers-1;
	while (left <= right) {
		new = (left+right)/2;
		if (peers[new] > ip)
			right = new-1;
		else if (peers[new] < ip)
			left = new+1;
		else
			break;
	}
	if (left > right) {
		if ((peerndx_t)left == (peerndx_t)-1) {
			error("Too many peers, increase sizeof(peerndx_t)");
			return 0;
		}
		new = left;
		peers = realloc(peers, ++npeers*sizeof(*peers));
		bcopy(&(peers[new]), &(peers[new+1]), (npeers-new-1)*sizeof(*peers));
		peers[new] = ip;
	}
	return (peerndx_t)new;
}

static void save_table_recurs(FILE *fout, struct rib_t *route, u_char preflen)
{
	static struct dump_entry entry;
	static uint32_t curip;
	int aspathlen, i, j, size;
	struct aspath *pt;
	uint32_t i32;
	uint16_t i16;
	u_char i8;
	asn_t tmp_asn;

	if (route == NULL) return;
	if (route->left)
		save_table_recurs(fout, route->left, preflen+1);
	if (route->right) {
		curip |= mask[preflen];
		save_table_recurs(fout, route->right, preflen+1);
		curip &= ~mask[preflen];
	}
	if (!route->npathes)
		return;
	size = 0;
	for (i=0; i<route->npathes; i++) {
		aspathlen = 0;
		for (pt = route->pathes[i]; pt->asn; pt = pt->prev) {
			tmp_asn = ntohl(pt->asn);
			entry.aspath[i][aspathlen++] = tmp_asn;
			if (tmp_asn < 0xf000)
				size += 2;
			else if (tmp_asn < 0xf0000)
				size += 3;
			else
				size += 5;
		}
		entry.aspath[i][aspathlen] = 0;
		if (aspathlen >= 255) {
			error("Too long aspath trunkated");
			entry.aspath[i][255] = 0;
		}
		/* revert aspath direction */
		for (j=aspathlen/2-1; j>=0; j--) {
			tmp_asn = entry.aspath[i][j];
			entry.aspath[i][j] = entry.aspath[i][aspathlen-1-j];
			entry.aspath[i][aspathlen-1-j] = tmp_asn;
		}
	}
	i32 = htonl(time(NULL));
	fwrite(&i32, 4, 1, fout);
	i32 = htonl(BGPDUMP_TYPE_ASRANK_PREF);
	fwrite(&i32, 4, 1, fout);
	i32 = htonl(1+(preflen+7)/8+1+route->npathes*(npeers>=256 ? 3 : 2)+size);
	fwrite(&i32, 4, 1, fout);
	fwrite(&preflen, 1, 1, fout);
	fwrite(&curip, 1, (preflen+7)/8, fout);
	i8 = route->npathes;
	fwrite(&i8, 1, 1, fout);
	for (i=0; i<route->npathes; i++) {
		if (npeers>=256) {
			i16 = htons(peer(route)[i]);
			fwrite(&i16, 2, 1, fout);
		} else {
			i8 = peer(route)[i];
			fwrite(&i8, 1, 1, fout);
		}
		for (i8=0; entry.aspath[i][i8]; i8++);
		fwrite(&i8, 1, 1, fout);
		for (j=0; entry.aspath[i][j]; j++) {
			if (entry.aspath[i][j] < 0xf000) {
				i16 = htons(entry.aspath[i][j]);
				fwrite(&i16, 2, 1, fout);
			}
			else if (entry.aspath[i][j] < 0xf0000) {
				i8 = (entry.aspath[i][j] >> 16) | 0xf0;
				fwrite(&i8, 1, 1, fout);
				i16 = htons(entry.aspath[i][j] & 0xffff);
				fwrite(&i16, 2, 1, fout);
			} else {
				i8 = 0xff;
				fwrite(&i8, 1, 1, fout);
				i32 = htonl(entry.aspath[i][j]);
				fwrite(&i32, 4, 1, fout);
			}
		}
	}
}

static void save_table(char *fname)
{
	FILE *fout;
	uint32_t i32;
	uint16_t i16;

	fout=fopen(fname, "w");
	if (fout == NULL) {
		error("Cannot open %s: %s", fname, strerror(errno));
		return;
	}
	/* write peer table */
	i32 = htonl(time(NULL));
	fwrite(&i32, 4, 1, fout);
	i32 = htonl(BGPDUMP_TYPE_ASRANK_PEERLIST);
	fwrite(&i32, 4, 1, fout);
	i32 = htonl(2+npeers*4);
	fwrite(&i32, 4, 1, fout);
	i16 = htons(npeers);
	fwrite(&i16, 2, 1, fout);
	fwrite(peers, 4, npeers, fout);

	save_table_recurs(fout, rib_root, 0);
	fclose(fout);
}

int main(int argc, char *argv[])
{
	int ch, i, j, k;
	char *p;
	FILE *f;
	struct dump_entry entry;
	char *groupfile;
	char str[1024];
	int progress_cnt;
	char *save_fname;

	save_fname = groupfile = NULL;
	while ((ch = getopt(argc, argv, "sd:ht:n:pg:w:")) != -1) {
		switch (ch) {
			case 's':	strict = 1; break;
			case 'd':	debuglevel = atoi(optarg); break;
			case 'p':	progress = 1; break;
			case 'h':	usage(); exit(0);
			case 't':	tier1_arr[ntier1_hints++] = readasn(optarg); break;
			case 'g':	groupfile = strdup(optarg); break;
			case 'n':	desc_fname = strdup(optarg); break;
			case 'w':	save_fname = strdup(optarg); break;
		}
	}
	if (groupfile) {
		f = fopen(groupfile, "r");
		if (f == NULL) {
			error("Cannot open %s: %s", groupfile, strerror(errno));
		} else {
			while (fgets(str, sizeof(str), f)) {
				if (!isdigit(str[0])) continue;
				asgroup = realloc(asgroup, (ngroups+1) * sizeof(*asgroup));
				for (i=0, p=str; *p; p++)
					if (*p == ',') i++;
				asgroup[ngroups].asn = calloc(sizeof(asn_t), i+1);
				for (asgroup[ngroups].nas=0, p=strtok(str, ","); p; p=strtok(NULL, ",")) {
					while (*p && isspace(*p)) p++;
					asgroup[ngroups].asn[asgroup[ngroups].nas++] = readasn(p);
				}
				ngroups++;
			}
			fclose(f);
		}
		debug(3, "groups file %s read, %d groups found", groupfile, ngroups);
	}
	if (argv[optind] && strcmp(argv[optind], "-")) {
		if (strlen(argv[optind]) > 4 && strcmp(argv[optind]+strlen(argv[optind])-4, ".bz2") == 0) {
			static char cmd[1024];
			snprintf(cmd, sizeof(cmd)-1, "bunzip2 < %s |", argv[optind]);
			f = popen(cmd, "r");
		} else
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
	for (i=0; i<24; i++)
		mask[i] = htonl(1u<<(31-i));

	debug(1, "Parsing input file");
	progress_cnt = 0;
	while (read_dump(f, &entry) == 0) {
		int norigins;
		int origins[MAXPATHES];
		struct rib_t *prefix, **pprefix;
		struct aspath *ap, *prevap;

		if (progress && ++progress_cnt % 3000 == 0) {
			printf("#");
			fflush(stdout);
		}

		if (entry.preflen > 24 || entry.preflen == 0)
			continue;

		norigins = 0;
		pprefix = &rib_root;
		for (i=0; i<entry.preflen; i++) {
			if (*pprefix == NULL) {
				if (entry.withdraw)
					break;
				else
					*pprefix = calloc(1, sizeof(struct rib_t));
			}
			pprefix = (entry.prefix & mask[i]) ? &(pprefix[0]->right) : &(pprefix[0]->left);
		}
		if (entry.withdraw) {
			if (!*pprefix) {
				debug(3, "Withdraw prefix not found: %s/%d from %s", printip(entry.prefix), entry.preflen, printas(entry.origas[0]));
				continue;
			}
			for (i=0; i<pprefix[0]->npathes; i++)
				if (peers[peer(*pprefix)[i]] == entry.peerip[0])
					break;
			if (i == pprefix[0]->npathes) {
				debug(3, "Withdraw origin as %s for prefix %s/%d not found", printas(entry.origas[0]), printip(entry.prefix), entry.preflen);
				continue;
			}
			if (debuglevel >= 6)
				debug(6, "Withdraw %s/%d from %s found", printip(entry.prefix), entry.preflen, printas(entry.origas[0]));
			ap = pprefix[0]->pathes[i];
			if (ap->leaf == 0) {
				error("Internal error in data structures (leaf==0 for existing prefix)");
				continue;
			}
			if (--(ap->leaf) == 0)
				aspathes--;
			/* decrease pathes for each aspath objects in this path */
			/* free unused aspath structures to delete withdrawed as relations */
			while (ap && ap->asn) {
				if (ap->pathes-- == 0) {
					error("Internal error in data structures (path==0 for existing aspath), as%s", printas(ap->asn));
					break;
				}
				prevap = ap->prev;
				if (ap->pathes == 0) {
					debug(5, "Free aspath");
					if (ap->nnei || ap->next) {
						error("Internal error in data structures (nnei==%d for unused aspath)", ap->nnei);
						break;
					}
					if (prevap) {
						if (!prevap->next) {
							error("Internal error in data structures: asymmetric aspath tree");
							break;
						}
						for (j=0; j<prevap->nnei; j++)
							if (prevap->next[j] == ap)
								break;
						if (j == prevap->nnei) {
							error("Internal error in data structures: asymmetric aspath tree");
							break;
						}
						if (prevap->nnei == 1) {
							free(prevap->next);
							prevap->next = NULL;
						} else
							bcopy(&prevap->next[j+1], &prevap->next[j], (prevap->nnei-j-1)*sizeof(ap->next[0]));
						prevap->nnei--;
					}
				}
				ap = prevap;
			}
			pprefix[0]->npathes--;
			bcopy(&pprefix[0]->pathes[i+1], &pprefix[0]->pathes[i], (pprefix[0]->npathes-i)*sizeof(pprefix[0]->pathes[0]));
			bcopy(&pprefix[0]->pathes[pprefix[0]->npathes+1], &pprefix[0]->pathes[pprefix[0]->npathes], i*sizeof(peerndx_t));
			bcopy((peerndx_t *)&pprefix[0]->pathes[pprefix[0]->npathes+1]+i+1,
			      (peerndx_t *)&pprefix[0]->pathes[pprefix[0]->npathes]+i, (pprefix[0]->npathes-i)*sizeof(peerndx_t));
			if (pprefix[0]->npathes == 0) {
				debug(5, "Prefix %s/%d withdrawed", printip(entry.prefix), entry.preflen);
				fullview--;
			}
			/* do not shrink allocated mamory and do not free prefix structure */
			continue;
		} else if (!*pprefix) {
			*pprefix = calloc(sizeof(struct rib_t) + entry.pathes*(sizeof(pprefix[0]->pathes[0])+sizeof(peerndx_t)), 1);
			fullview++;
		} else if (pprefix[0]->npathes == 0) {
			*pprefix = realloc(*pprefix, sizeof(struct rib_t) + entry.pathes*(sizeof(pprefix[0]->pathes[0])+sizeof(peerndx_t)));
			fullview++;
		} else if (entry.pathes > 1) {
			warning("The same prefix %s/%d ignored", printip(entry.prefix), entry.preflen);
			continue;
		} else {
			/* neighbor AS already exists for this prefix? */
			for (i=0; i<pprefix[0]->npathes; i++) {
				uint32_t firstas;
				struct aspath *pas;

				firstas = 0;
				for (pas = pprefix[0]->pathes[i]; pas->asn; pas=pas->prev)
					firstas = pas->asn;
				if (firstas == entry.aspath[0][0])
					break;
			}
			if (i<pprefix[0]->npathes)
				continue;
			/* new origin, add it */
			if (pprefix[0]->npathes >= MAXPATHES) {
				warning("Too many pathes for %s/%d, rest ignored", printip(entry.prefix), entry.preflen);
				continue;
			}
			*pprefix = realloc(*pprefix, sizeof(struct rib_t) + (pprefix[0]->npathes+1)*(sizeof(pprefix[0]->pathes[0])+sizeof(peerndx_t)));
			bcopy(&pprefix[0]->pathes[pprefix[0]->npathes], &pprefix[0]->pathes[pprefix[0]->npathes+1], pprefix[0]->npathes*sizeof(peerndx_t));
		}
		prefix = *pprefix;
		for (i=0; i<entry.pathes; i++) {
			int pathlen;
			asn_t path[MAXPATHLEN];
			asn_t prevas;
			struct aspath *curpath;

			if (debuglevel >= 6) {
				for (j=0; entry.aspath[i][j]; j++);
				debug(6, "%s/%d|%s|%s", printip(entry.prefix), entry.preflen, printas(entry.origas[i]), printaspath(entry.aspath[i], j));
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
					curpath->next = realloc(curpath->next, ++(curpath->nnei)*sizeof(curpath->next[0]));
					new = left;
					bcopy(&(curpath->next[new]),&(curpath->next[new+1]),(curpath->nnei-new-1)*sizeof(curpath->next[0]));
					curpath->next[new] = calloc(1, sizeof(curpath->next[0][0]));
					curpath->next[new]->prev = curpath;
					curpath->next[new]->asn = path[j];
				}
				curpath = curpath->next[new];
				curpath->pathes++;
			}
			if (!curpath->leaf)
				aspathes++;
			if (curpath->leaf == (1ul<<(sizeof(curpath->leaf)*8))-1)
				error("Too many prefixes for same aspath (%u), increase sizeof(leaf)!", curpath->leaf);
			else
				curpath->leaf++;
			prefix->pathes[prefix->npathes++] = curpath;
			peer(prefix)[prefix->npathes-1] = peerndx(entry.peerip[i]);
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
	}
	if (f != stdin) fclose(f);
	if (progress) {
		printf("\n");
		fflush(stdout);
	}
	freeas(&origin);
	freeas(&wasas);
	debug(1, "RIB table parsed, %d prefixes, %d pathes", fullview, aspathes);
	/* foreach_aspath(printtree); */

	/* group leaders should be indexed */
	for (i=0; i<ngroups; i++) {
		if (!asndx(asgroup[i].asn[0])) {
			warning("No AS %s which listed in group %d", printas(asgroup[i].asn[0]), i);
			*as(&ndx, asgroup[i].asn[0]) = -1;
			nas++;
		}
	}
	asnum = calloc(nas, sizeof(asn_t));
	nas = 0;
	foreach_aspath(fill_asndx);
	for (i=0; i<ngroups; i++) {
		if (asndx(asgroup[i].asn[0]) == -1) {
			*as(&ndx, asgroup[i].asn[0]) = nas;
			asnum[nas++] = asgroup[i].asn[0];
		}
	}

	routes = calloc(nas, sizeof(routes[0]));
	proutes = calloc(nas, sizeof(proutes[0]));
	rel = calloc(nas, sizeof(*rel));
	maxroutes(&rootpath);
	ntier1 = ntier1_hints;
	tier1 = calloc(nas, sizeof(tier1[0]));
	tier1_bad = calloc(nas, sizeof(tier1_bad[0]));
	for (ntier1=0; ntier1<ntier1_hints; ntier1++) {
		if (asndx(tier1_arr[ntier1]) == 0 && asnum[0] != tier1_arr[ntier1])
			warning("No AS %s, exclude from tier1 list", printas(tier1_arr[ntier1]));
		else
			tier1[asndx(tier1_arr[ntier1])] = 1;
	}
	for (i=0; i<nas; i++) {
		if (ntier1 >= sizeof(tier1_arr)/sizeof(tier1_arr[0])) {
			warning("Too many tier1 candidates found");
			break;
		}
		if (routes[i] > fullview/2 && proutes[i] < fullview/2) {
			if (tier1[i] == 0) {
				tier1_arr[ntier1++] = asnum[i];
				tier1[i] = 1;
			}
		}
	}
	free(routes);
	free(proutes);
	debug(1, "Found %d tier1 candidates", ntier1);

	/* next AS after tier1 candidate is candidate also */
	add_tier1(&rootpath);
	debug(1, "Added candidated, now %d", ntier1);

	npath = calloc(nas, sizeof(npath[0]));
	foreach_aspath(get_npath);

	for (;;) {
		int maxndx;
		double rate, maxrate;

		inv_pathes = 0;
		check_valid_path_recurs(&rootpath, 0);
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
		debug(2, "%s is not tier1 (%d rate, %d pathes)", printas(tier1_arr[maxndx]),
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
			debug(1, "  %s", printas(tier1_arr[i]));
	}

	foreach_aspath(make_rel1);
	/* if relations is less then 90% assurance, then discard it */
	for (i=0; i<nas; i++)
		for (j=0; j<rel[i].nas_rel; j++)
			if (abs(rel[i].as_rel[j].val)*10 < rel[i].as_rel[j].cnt*9)
				rel[i].as_rel[j].val = 0;
	/* add relations for "a - b > c"  ->   a > b and others like this? */
	debug(1, "AS relations built");
	debug(1, "%d pathes to tier1, %d pathes via tier1, %d pathes avoid tier1", totier1, viatier1, horlinks);

	/* calculate rating */
	group = calloc(nas, sizeof(*group));
	n24 = calloc(nas, sizeof(*n24));
	npref = calloc(nas, sizeof(*npref));
	coneas = calloc(nas, sizeof(*coneas));
	upstreams = calloc(nas, sizeof(*upstreams));
	upstreams_arr = calloc(nas, sizeof(*upstreams_arr));
	nupstreams = 0;
	for (i=0; i<ngroups; i++) {
		for (j=0; j<asgroup[i].nas; j++) {
			if (asndx(asgroup[i].asn[j]) != 0 || asnum[0] == asgroup[i].asn[j]) {
				if (group[asndx(asgroup[i].asn[j])])
					warning("AS %s included to more then one group", printas(asgroup[i].asn[j]));
				else
					group[asndx(asgroup[i].asn[j])] = i+1;
			} else
				warning("No AS %s which listed in group %d", printas(asgroup[i].asn[j]), i);
		}
	}
	collect_stats(rib_root, 0);
	free(upstreams);
	debug(1, "Rating calculated");

	/* calculate degree for groups */
	if (ngroups) {
		char *hasrel;
		int *asrel;

		hasrel = calloc(nas, sizeof(*hasrel));
		asrel = calloc(nas, sizeof(*asrel)); /* too many, it's only list of neighbors */
		for (i=0; i<ngroups; i++) {
			int nasrel, relas;

			nasrel = 0;
			for (j=0; j<asgroup[i].nas; j++) {
				if (asndx(asgroup[i].asn[j])==0 && asnum[0]!=asgroup[i].asn[j])
					continue;
				for (k=0; k<rel[asndx(asgroup[i].asn[j])].nas_rel; k++) {
					relas = asndx(rel[asndx(asgroup[i].asn[j])].as_rel[k].asn);
					if (hasrel[relas] == 0) {
						hasrel[relas] = 1;
						asrel[nasrel++] = relas;
					}
				}
			}
			rel[asndx(asgroup[i].asn[0])].nas_rel = nasrel;
			for (j=0; j<nasrel; j++)
				hasrel[asrel[j]] = 0;
		}
		free(hasrel);
		free(asrel);
		debug(1, "degree for groups calculated");
	}
	for (i=0; i<nas; i++)
		if (rel[i].as_rel) {
			free(rel[i].as_rel);
			rel[i].as_rel = NULL;
		}

	/* sort and output statistics */
	asorder = calloc(nas, sizeof(*asorder));
	debug(1, "AS list sorted");
	for (i=0; i<nas; i++)
		asorder[i] = i;
	qsort(asorder, nas, sizeof(*asorder), cmpas);
	for (i=0; i<nas; i++) {
		if (group[asorder[i]]) {
			if (asgroup[group[asorder[i]]-1].asn[0] != asnum[asorder[i]]) continue;
			str[0] = 0;
			p = str;
			for (j=0; j<asgroup[group[asorder[i]]-1].nas; j++) {
				if (p != str) *p++ = ',';
				strcpy(p, printas(asgroup[group[asorder[i]]-1].asn[j]));
				p += strlen(p);
				if (p-str+15 >= sizeof(str)) break;
			}
			p = str;
		} else
			p = printas(asnum[asorder[i]]);
		printf("%5d. %32s  %9d  %7d  %5d %4d\n", i+1, p,
			       n24[asorder[i]], npref[asorder[i]], coneas[asorder[i]].nas, rel[asorder[i]].nas_rel);
	}
	if (save_fname) {
		debug(1, "Saving table to %s", save_fname);
		save_table(save_fname);
	}
	debug(1, "All done");
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
	if (level <= 2) fflush(stdout);
}

void warning(char *format, ...)
{
	va_list ap;
	char buf[1024];

	va_start(ap, format);
	vsnprintf(buf, sizeof(buf), format, ap);
	va_end(ap);
	fflush(stdout);
	fprintf(stderr, "%s\n", buf);
	fflush(stderr);
}

void error(char *format, ...)
{
	va_list ap;
	char buf[1024];

	va_start(ap, format);
	vsnprintf(buf, sizeof(buf), format, ap);
	va_end(ap);
	fflush(stdout);
	fprintf(stderr, "%s\n", buf);
	fflush(stderr);
}

