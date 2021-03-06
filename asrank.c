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

/* asn n24/own npref/own nas degree/upstreams/peering updates/withdraw */
#define FORMAT "%32s  %d/%d  %d/%d  %d  %d/%d/%d  %d/%d\n"
#define ALLUPDATES 1 /* count all updates, not only withdraw */

int debuglevel = 0;
int progress = 0;
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
	int pathes:22;
	int noinv:1;
	int leak:1;
	int clientspart:8;
	time_t create_time;
	uint16_t nnei;
	uint16_t leaf;
} rootpath;

int npeers;
uint32_t *peers;
peerndx_t *peerorder;
peerndx_t *peerindex;

#define peer(a)	((peerndx_t *)&((a)->pathes[(a)->npathes]))
#define peerip(a, i) peers[peerindex[peer(a)[i]]]

struct rib_t {
	struct rib_t *left, *right;
	u_char npathes;
	struct aspath *pathes[0];
	/* peerndx_t peer[]; */
} *rib_root;

asarr origin, wasas, ndx, updates, upd_n24, withdraw, withdr_n24, group, ix;
asarr *trace;
int *tier1, *routes, *proutes, *npath, *tier1_bad, *n24, *npref, *nextas;
int *n24_gr, *npref_gr, *group_rel;
int *updates_gr, *withdraw_gr, *upd_n24_gr, *withdr_n24_gr, *wasgroup;
int *own_n24, *own_n24_gr, *own_npref, *own_npref_gr;
int *nuplinks, *npeerings, *nclients, *nuplinks_gr, *npeering_gr, *nclients_gr;
char *upstreams, *ups_group;
int *upstreams_arr, *ups_group_arr;
struct trace_t {
	int nrel;
	asn_t *rel;
} *trace_arr;
int ntrace;
asn_t *asnum, as_reserved;
struct rel_t {
	int nas_rel;
	struct rel_lem_t {
		asn_t asn;
		int n24;
		int self;
		int prefs:24;
		int sure:5; /* -1 - leak, 0 - no pathes (downlink or p2p), 2 - route found, 3 - valid routes exists, 4 - upstream */
		int pass2:1; /* upstream after excluding route-leaks */
		int upstream:1; /* upstream after all checking, include network rate */
		int sibling:1;  /* members of one group */
	} *as_rel;
} *rel;
struct coneas_t {
	int nas;
	int *asn;
} *coneas, *coneas_gr;
int nas, old_nas, ntier1, ntier1_hints, inv_pathes, fullview, aspathes;
int *tier1_linked;
asn_t tier1_arr[2048]; /* array for connections between tier1s should not be too large */
uint32_t mask[24];
int ngroups, nix;
struct group_t {
	int nas;
	asn_t *asn;
} *asgroup, *asix;
int horlinks, totier1, viatier1;
char printasbuf1[20], printasbuf2[20];

#define printas(a)	printasbuf(a, printasbuf1, sizeof(printasbuf1))
#define printas2(a)	printasbuf(a, printasbuf2, sizeof(printasbuf2))

static void usage(void)
{
	printf("Usage: asrank [-p] [-d level] [-t asn] [-x <asn|@fname>] [-g fname] [-w fname] [-u fname[,fname...]] [file ...]\n");
	printf("  Options:\n");
	printf("-t asn       - hint that asn is tier1\n");
	printf("-x asn       - asn is internet exchange point\n");
	printf("-x @fname    - file with IX list (one IX per line, comma separated for sibling)\n");
	printf("-d level     - set debug level (5 and more cause huge output)\n");
	printf("-p           - show progress bar\n");
	printf("-g fname     - file defined sibling groups, one group per line, comma separated\n");
	printf("-w fname     - write result table to fname for future processing\n");
	printf("-u fname     - process file(s) with updates and generate separate statistics after it\n");
	printf("-T as1[:as2] - trace (debug level 4) relations for as1 or between as1 and as2\n");
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

char *printasbuf(asn_t asn, char *buf, int bufsize)
{
	asn = ntohl(asn);
	if (asn < 65536)
		snprintf(buf, bufsize-1, "%u", asn);
	else
		snprintf(buf, bufsize-1, "%u.%u", asn>>16, asn % 65536);
	return buf;
}

char *printaspath(asn_t *aspath, int aspathlen)
{
	static char printaspathbuf[4096], prasbuf[32];
	char *p;
	int i;

	p = printaspathbuf;
	*p = '\0';
	for (i=0; i<aspathlen; i++) {
		if (i) *p++ = ' ';
		strncpy(p, printasbuf(aspath[i], prasbuf, sizeof(prasbuf)), sizeof(printaspathbuf)-(p-printaspathbuf)-1);
		p += strlen(p);
		if ((p-printaspathbuf) + 3 > sizeof(printaspathbuf)) break;
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
	debug(10, "%s", printaspath(aspath, pathlen));
}

static void get_npath(asn_t *aspath, int pathlen)
{
	int i;

	for (i=0; i<pathlen; i++)
		npath[asndx(aspath[i])]++;
}

static void addconeas(struct coneas_t *coneas, int as1, asn_t as2)
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

static int needtrace(asn_t as1, asn_t as2)
{
	int i, j;

	if (!trace) return 0;
	if ((i=*as(trace, as1)) == 0) return 0;
	if (i == -1) return 1;
	if (*as(trace, as2) == -1) return 1;
	for (j=trace_arr[--i].nrel-1; j>=0; j--)
		if (as2 == trace_arr[i].rel[j])
			return 1;
	return 0;
}

static struct rel_lem_t *mkrel(asn_t as1, asn_t as2, int val)
{
	int left, right, new;
	struct rel_t *p;

	if (asndx(as1) == 0) {
		error("Internal error: mkrel for unknown AS %s", printas(as1));
		return NULL;
	}
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
		if (p->as_rel == NULL) {
			error("Internal error: cannot realloc as_rel, needed %d bytes", p->nas_rel * sizeof(p->as_rel[0]));
			return NULL;
		}
		new = left;
		bcopy(&(p->as_rel[new]), &(p->as_rel[new+1]), (p->nas_rel-new-1) * sizeof(p->as_rel[0]));
		memset(&(p->as_rel[new]), 0, sizeof(p->as_rel[0]));
		p->as_rel[new].asn = as2;
	}
	if (val != 0) {
		if (val == -1) {
			if (needtrace(as1, as2))
				debug(4, "Set relations %s > %s, sure = %d", printas(as1), printas2(as2), val);
			p->as_rel[new].sure = -1; /* leak */
		} else if (val > p->as_rel[new].sure) {
			if (needtrace(as1, as2))
				debug(4, "Set relations %s > %s, sure = %d", printas(as1), printas2(as2), val);
			p->as_rel[new].sure = val;
		}
	}
	return &(p->as_rel[new]);
}

static void maxroutes(struct aspath *aspath)
{
	int i;

	for (i=0; i<aspath->nnei; i++) {
		if (routes && routes[asndx(aspath->next[i]->asn)] < aspath->next[i]->pathes)
			routes[asndx(aspath->next[i]->asn)] = aspath->next[i]->pathes;
		if (aspath->asn) {
			if (proutes && proutes[asndx(aspath->asn)] < aspath->next[i]->pathes)
				proutes[asndx(aspath->asn)] = aspath->next[i]->pathes;
			if (aspath->next[i]->pathes > fullview/3 &&
			    aspath->asn != as_reserved && aspath->next[i]->asn != as_reserved) {
				if (needtrace(aspath->next[i]->asn, aspath->asn))
					if (mkrel(aspath->next[i]->asn, aspath->asn, 0)->sure < 4)
						debug(4, "%s is upstream for %s (sure=4), >fullview/3 prefixes",
						      printas(aspath->next[i]->asn), printas(aspath->asn));
				mkrel(aspath->next[i]->asn, aspath->asn, 4);
			} else {
				mkrel(aspath->next[i]->asn, aspath->asn, 0);
			}
			mkrel(aspath->asn, aspath->next[i]->asn, 0);
		}
		aspath->clientspart = aspath->leak = aspath->noinv = 0;
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
				debug(6, "Add tier1 candidate: %s", printas(aspath->next[i]->asn));
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
	int i, seqlen, ret, firsttier1, lasttier1, maxseq;
	char s[64];

	if (pathlen == 0)
		return 0;
	ret = 0;
	seqlen = firsttier1 = lasttier1 = maxseq = 0;
	if (tier1[asndx(aspath[0])])
		seqlen = firsttier1 = lasttier1 = maxseq = 1;
	for (i=1; i<pathlen; i++) {
		if (tier1[asndx(aspath[i])]) {
			seqlen++;
			if (!firsttier1) firsttier1 = i+1;
			lasttier1 = i+1;
			if (seqlen > maxseq) maxseq = seqlen;
			if (seqlen > 1) {
				tier1_linked[tier1[asndx(aspath[i])]-1] = 1;
				if (seqlen == 2)
					tier1_linked[tier1[asndx(aspath[i-1])]-1] = 1;
			}
		} else {
			if (seqlen > 2) {
				tier1_bad[asndx(aspath[i-1])]++;
				tier1_bad[asndx(aspath[i-seqlen])]++;
				inv_pathes++;
				ret = 1;
				if (debuglevel >= 7) {
					strncpy(s, printaspath(aspath+i-seqlen, seqlen), sizeof(s));
					s[sizeof(s)-1] = '\0';
					debug(7, "Invalid path: %s (tier1 part: %s)", printaspath(aspath, pathlen), s);
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
		if (debuglevel >= 7) {
			strncpy(s, printaspath(aspath+i-seqlen, seqlen), sizeof(s));
			s[sizeof(s)-1] = '\0';
			debug(7, "Invalid path: %s (tier1 part: %s)", printaspath(aspath, pathlen), s);
		}
	}
	if (firsttier1 && lasttier1-firsttier1 > maxseq-1) {
		tier1_bad[asndx(aspath[firsttier1-1])]++;
		tier1_bad[asndx(aspath[lasttier1-1])]++;
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

static void clean_noinv(struct aspath *aspath)
{
	int i;

	aspath->noinv = 0;
	for (i=0; i<aspath->nnei; i++)
		clean_noinv(aspath->next[i]);
}

static void make_rel1(asn_t *aspath, int pathlen)
{
	int i, t1, first, last;
	struct rel_lem_t *rel;

	first = last = t1 = 0;
	for (i=0; i<pathlen; i++) {
		if (tier1[asndx(aspath[i])]) {
			if (!first)
				first = i+1;
			else
				last = i+1;
			t1 = 1;
		}
		if ((i != 0 && i != pathlen-1 && *as(&ix, aspath[i]))) {
			if (!first)
				first = i+1;
			else
				last = i+1;
			/* sure, IX is upstream */
			if (aspath[i-1] != as_reserved) {
				mkrel(aspath[i], aspath[i-1], 4)->pass2 = 1;
				if (needtrace(aspath[i], aspath[i-1]))
					debug(4, "Set pass2 (IX) %s > %s (aspath %s)", printas(aspath[i]), printas2(aspath[i-1]), printaspath(aspath, pathlen));
			}
			if (aspath[i+1] != as_reserved) {
				mkrel(aspath[i], aspath[i+1], 4)->pass2 = 1;
				if (needtrace(aspath[i], aspath[i+1]))
					debug(4, "Set pass2 (IX) %s > %s (aspath %s)", printas(aspath[i]), printas2(aspath[i+1]), printaspath(aspath, pathlen));
			}
		}
		if (i>0 &&
		    ((*as(&group, aspath[i-1]) && *as(&group, aspath[i-1]) == *as(&group, aspath[i])) ||
		    (*as(&ix, aspath[i-1]) && *as(&ix, aspath[i-1]) == *as(&ix, aspath[i])))) {
			mkrel(aspath[i-1], aspath[i], 0)->sibling = 1;
			mkrel(aspath[i], aspath[i-1], 0)->sibling = 1;
		}
	}
	if (!t1) horlinks++;
	if (!first) return;
	if (!last) last = first;
	if (tier1[asndx(aspath[pathlen-1])])
		totier1++;
	else if (!tier1[asndx(aspath[0])])
		viatier1++;
	for (i=1; i<pathlen; i++) {
		if (aspath[i] == as_reserved || aspath[i-1] == as_reserved)
			continue;
		if (i+1<first || (i+1==first && last==first+1) ||
		    (i+1==first && *as(&ix, aspath[i]))) {
			rel = mkrel(aspath[i], aspath[i-1], 0);
			if (needtrace(aspath[i], aspath[i-1]) && rel->sure < (rel->sibling ? 3 : 2))
				debug(4, "Set sure=%d (tier1 or IX) %s > %s (aspath %s)",
				      rel->sibling ? 3 : 2,
				      printas(aspath[i]), printas2(aspath[i-1]), printaspath(aspath, pathlen));
			if (rel->sibling) {
				if (rel->sure < 3) rel->sure = 3;
			} else {
				if (rel->sure < 2) rel->sure = 2;
			}
		}
		if (i>last || (i == last && last == first+1) ||
		    (i == last && *as(&ix, aspath[i-1]))) {
			rel = mkrel(aspath[i-1], aspath[i], 0);
			if (needtrace(aspath[i-1], aspath[i]) && rel->sure < (rel->sibling ? 3 : 2))
				debug(4, "Set sure=%d (tier1 or IX) %s > %s (aspath %s)",
				      rel->sibling ? 3 : 2,
				      printas(aspath[i-1]), printas2(aspath[i]), printaspath(aspath, pathlen));
			if (rel->sibling) {
				if (rel->sure < 3) rel->sure = 3;
			} else {
				if (rel->sure < 2) rel->sure = 2;
			}
		}
	}
}

static int make_rel2(struct rib_t *route, int preflen)
{
	static struct aspath *scan_pathes[MAXPATHES];
	static int nextas_arr[MAXPATHES];
	int i, j, nnext, nets, asx;
	asn_t asn, newasn;
	static uint32_t curip;

	if (route == NULL) return 0;
	nets = 0;
	if (route->left)
		nets += make_rel2(route->left, preflen+1);
	if (route->right) {
		curip |= mask[preflen];
		nets += make_rel2(route->right, preflen+1);
		curip &= ~mask[preflen];
	}
	if (!route->npathes)
		return nets;
#if 0
	if (route->npathes == 1 && rootpath.nnei > 1)
		/* only single path for this prefix - ignore (error?) */
#else
	if (route->npathes*2 < rootpath.nnei)
		/* route exists less then on half points of view - ignore */
#endif
		return nets;
	nets = (1<<(24-preflen)) - nets; /* value of the current route */
	for (i=0; i<route->npathes; i++)
		scan_pathes[i] = route->pathes[i];
	newasn = 0;
	for (;;) {
		if ((asn = newasn))
			asx = asndx(asn);
		nnext = 0;
		for (i=0; i<route->npathes; i++) {
			if (!scan_pathes[i]) continue;
			if (!scan_pathes[i]->asn) {
				scan_pathes[i] = NULL;
				continue;
			}
			j = asndx(scan_pathes[i]->asn);
			if (nextas[j] == 0)
				nextas_arr[nnext++] = j;
			nextas[j]++;
		}
		newasn = 0;
		for (j=0; j<nnext; j++) {
			if (nextas[nextas_arr[j]]*2 > route->npathes) {
				newasn = asnum[nextas_arr[j]];
				i = nextas[nextas_arr[j]];
			}
			nextas[nextas_arr[j]] = 0;
		}
		if (newasn == 0)
			break;
		if (asn && asn != as_reserved && newasn != as_reserved) {
			if (needtrace(newasn, asn) && mkrel(newasn, asn, 0)->sure<3)
				debug(4, "Set %s > %s sure=3: %s/%d seen from %d of %d pathes",
				      printas(newasn), printas2(asn), printip(curip), preflen, i, route->npathes);
			mkrel(newasn, asn, 3);
			if (*as(&ix, newasn))
				break;
		}
		for (i=0; i<route->npathes; i++) {
			if (!scan_pathes[i]) continue;
			if (scan_pathes[i]->asn != newasn)
				scan_pathes[i] = NULL;
			else
				scan_pathes[i] = scan_pathes[i]->prev;
		}
	}
	asn = route->pathes[0]->asn;
	asx = asndx(asn);
	if (asn != as_reserved) {
		own_npref[asx]++;
		own_n24[asx] += nets;
	}
	if (!tier1[asx]) {
		/* now check only pathes with tier1 */
		for (i=0; i<route->npathes; i++) {
			for (scan_pathes[i] = route->pathes[i]; scan_pathes[i]; scan_pathes[i] = scan_pathes[i]->prev) {
				if (scan_pathes[i]->asn && tier1[asndx(scan_pathes[i]->asn)])
					break;
				if (scan_pathes[i]->asn && scan_pathes[i]->prev && scan_pathes[i]->prev->asn && scan_pathes[i] != route->pathes[i]) {
					if (mkrel(scan_pathes[i]->asn, scan_pathes[i]->prev->asn, 0)->sure > 0) {
						scan_pathes[i] = NULL;
						break;
					}
				}
			}
		}
		nnext = 0;
		for (i=0; i<route->npathes; i++) {
			if (!scan_pathes[i]) continue;
			if (!(newasn = route->pathes[i]->prev->asn)) continue;
			if (nextas[j=asndx(newasn)] == 0) {
				nextas_arr[nnext++] = j;
				nextas[j] = 1;
				if (newasn != as_reserved && route->pathes[i]->asn != as_reserved)
					mkrel(newasn, route->pathes[i]->asn, 0)->self += nets;
			}
		}
		for (i=0; i<nnext; i++)
			nextas[nextas_arr[i]] = 0;
	}
	return (1<<(24-preflen));
}

static void make_rel4(struct rib_t *route)
{
	int i, j, noinv;
	struct aspath *p, *p1;

	if (route == NULL) return;
	if (route->left)
		make_rel4(route->left);
	if (route->right)
		make_rel4(route->right);
	if (!route->npathes)
		return;
	noinv = 1;
	for (i=0; i<route->npathes; i++) {
		if (route->pathes[i]->noinv)
			continue;
		if (!route->pathes[i]->asn)
			continue;
		for (p=route->pathes[i]; p->prev->asn; p=p->prev) {
			if (mkrel(p->prev->asn, p->asn, 0)->sure != 4 ||
			    mkrel(p->asn, p->prev->asn, 0)->sure != 2)
				continue;
			/* are there pathes avoid p->prev->asn for this prefix? */
			for (j=0; j<route->npathes; j++) {
				if (i==j) continue;
				for (p1=route->pathes[j]; p1->asn; p1=p1->prev)
					if (p1->asn == p->prev->asn)
						break;
				if (!p1->asn) break;
			}
			if (j != route->npathes) {
				debug(needtrace(p->asn, p->prev->asn) ? 4 : 6,
				      "Route leak: from %s to %s", printas(p->prev->asn), printas2(p->asn));
				mkrel(p->asn, p->prev->asn, -1);
			} else
				noinv = 0;
		}
		if (noinv)
			route->pathes[i]->noinv = 1;
	}
}

static void make_rel5(asn_t *aspath, int pathlen)
{
	int i, first, last;
	int ab, ba;

	first = last = -1;
	for (i=0; i<pathlen; i++) {
		if (tier1[asndx(aspath[i])] ||
		    (i != 0 && i != pathlen-1 && *as(&ix, aspath[i]))) {
			if (first==-1)
				first = i;
			else
				last = i;
		}
	}
	if (first==-1) return;
	if (last==-1) last = first;
	for (i=1; i<first; i++) {
		if ((ab = mkrel(aspath[i], aspath[i-1], 0)->sure) == -1) {
			first = i-1;
			break;
		}
		if (ab == 4) continue;
		if ((ba = mkrel(aspath[i-1], aspath[i], 0)->sure) >= 3) {
			first = i-1;
			break;
		}
		if (ab == 2 && ba == 2) {
			first = i-1;
			break;
		}
	}
	for (i=pathlen-1; i>last; i--) {
		if ((ab = mkrel(aspath[i-1], aspath[i], 0)->sure) == -1) {
			last = i;
			break;
		}
		if (ab == 4) continue;
		if ((ba = mkrel(aspath[i], aspath[i-1], 0)->sure) >= 3) {
			last = i;
			break;
		}
		if (ab == 2 && ba == 2) {
			last = i;
			break;
		}
	}
	/* relations for IX already set */
	for (i=1; i<pathlen; i++) {
		if (aspath[i] == as_reserved || aspath[i-1] == as_reserved)
			continue;
		if (i<first || (i==first && last==first+1)) {
			mkrel(aspath[i], aspath[i-1], 0)->pass2 = 1;
			if (needtrace(aspath[i], aspath[i-1]))
				debug(4, "Set pass2 %s > %s (aspath %s)",
				      printas(aspath[i]), printas2(aspath[i-1]), printaspath(aspath, pathlen));
		}
		if (i>last+1 || (i == last+1 && last == first+1)) {
			mkrel(aspath[i-1], aspath[i], 0)->pass2 = 1;
			if (needtrace(aspath[i-1], aspath[i]))
				debug(4, "Set pass2 %s > %s (aspath %s)",
				      printas(aspath[i-1]), printas2(aspath[i]), printaspath(aspath, pathlen));
		}
	}
}

static void make_rel6(asn_t *aspath, int pathlen)
{
	int i, ifirst, ilast, inc;
	struct rel_lem_t *crel1, *crel2;

	/* process only pathes without tier1 */
	for (i=0; i<pathlen; i++)
		if (tier1[asndx(aspath[i])] || *as(&ix, aspath[i]))
			return;
	inc = 1;
	ifirst = 0;
	ilast = pathlen-1;
	/*  if A>B-C>D then B>C, only one unknown hop between two known
	 *  and only for completely valid pathes */
	for (i=1; i<pathlen; i++) {
		crel1= mkrel(aspath[i-1], aspath[i], 0);
		crel2= mkrel(aspath[i], aspath[i-1], 0);
		if (!crel1->pass2 && crel2->pass2) {
			if ((inc == 1 || inc == 2) && crel1->sure<-0) {
				ifirst = i;
				inc = 1;
			}
			ilast = pathlen-1;
		} else if (crel1->pass2 && !crel2->pass2) {
			inc = 3;
			if (crel2->sure<=0)
				ilast = i-1;
		} else if (crel1->pass2 && crel2->pass2) {
			inc = 3;
			ilast = pathlen-1;
		} else {
			if (inc == 4)
				ilast = pathlen -1;
			inc++;
		}
	}
	for (i=1; i<pathlen; i++) {
		if (aspath[i] == as_reserved || aspath[i-1] == as_reserved)
			continue;
		if (i<=ifirst) {
			if (needtrace(aspath[i], aspath[i-1]) && mkrel(aspath[i], aspath[i-1], 0)->sure == 0)
				debug(4, "Set sure=1 %s > %s (aspath %s)",
				      printas(aspath[i]), printas2(aspath[i-1]), printaspath(aspath, pathlen));
			mkrel(aspath[i], aspath[i-1], 1);
		} else if (i>ilast) {
			if (needtrace(aspath[i-1], aspath[i]) && mkrel(aspath[i-1], aspath[i], 0)->sure == 0)
				debug(4, "Set sure=1 %s > %s (aspath %s)",
				      printas(aspath[i-1]), printas2(aspath[i]), printaspath(aspath, pathlen));
			mkrel(aspath[i-1], aspath[i], 1);
		}
	}
}

static void addclients(int n24, int upstream, asn_t client)
{
	int left, right, new;
	struct rel_t *p;

	if (client == 0) {
		error("Internal error: client's AS number 0");
		return;
	}
	p = &(rel[upstream]);
	left = 0; right = p->nas_rel-1;
	while (left <= right) {
		new = (left + right) / 2;
		if (p->as_rel[new].asn > client)
			right = new-1;
		else if (p->as_rel[new].asn < client)
			left = new+1;
		else
			break;
	}
	if (left > right) {
		/* new */
		if (asnum[upstream] != client)
			warning("New relations in addclients()");
		p->nas_rel++;
		p->as_rel = realloc(p->as_rel, p->nas_rel * sizeof(p->as_rel[0]));
		new = left;
		bcopy(&(p->as_rel[new]), &(p->as_rel[new+1]), (p->nas_rel-new-1) * sizeof(p->as_rel[0]));
		memset(&(p->as_rel[new]), 0, sizeof(p->as_rel[0]));
		p->as_rel[new].asn = client;
	}
	p->as_rel[new].n24 += n24;
	p->as_rel[new].prefs += 1;
}

static int clientspart(asn_t *aspath, int aspathlen, int *leak)
{
	int i, ilast, inc, incleak;
	struct rel_lem_t *crel1, *crel2;

	ilast = 0;
	inc = 1; /* 1 - going up, 3 - going down */
	incleak = 1; /* 1 - going up, 3 - going down */
	if (leak) *leak = 0;
	if (!asndx(aspath[0]) || asndx(aspath[0]) >= old_nas)
		return 0;
	for (i=1; i<aspathlen; i++) {
		if (!asndx(aspath[i]) || asndx(aspath[i]) >= old_nas)
			break; /* new (unknown) as number */
		crel1 = mkrel(aspath[i], aspath[i-1], 0);
		crel2 = mkrel(aspath[i-1], aspath[i], 0);
		if (crel1->pass2 && !crel2->pass2) {
			if (inc == 1)
				ilast = i;
			if (leak && incleak == 3 && crel2->sure < 3) {
				*leak = 1;
				break;
			}
		} else if (crel2->pass2 && !crel1->pass2) {
			if (!leak) break;
			inc = 3;
			if (crel1->sure < 3) incleak = 3;
		} else if (crel1->sibling && inc == 1) {
			ilast = i;
#if 0 /* treat peering as unknown */
		} else if (!crel1->pass2 && !crel2->passw) {
			if (inc == 1)
				inc = 2;
			else
				inc = -1;
#endif
		}
		if ((tier1 && tier1[asndx(aspath[i])]) || *as(&ix, aspath[i])) {
			if (!leak) break;
			inc = incleak = 3;
		}
	}
	return ilast;
}

static int collect_stats(struct rib_t *route, int preflen)
{
	static asn_t route_aspath[MAXPATHLEN];
	static uint32_t curip;
	int nets;
	/* following vars can be not local in this recursive function */
	/* but recursion depth is not high (only 24), so I think this local vars are ok */
	int i, j, aspathlen, jlast, ups, leak;
	int nupstreams, nups_group;
	struct aspath *pt, *prevpt;
	struct rel_lem_t *crel1, *crel2;
	
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
	if (route->npathes == 1 && rootpath.nnei > 1) {
		/* assume error, ignore */
		debug(5, "%s/%d has only one path, ignore", printip(curip), preflen);
		return nets;
	}
	nets = (1<<(24-preflen)) - nets; /* value of the current route */
	nupstreams = nups_group = 0;
	for (i=0; i<route->npathes; i++) {
		aspathlen = 0;
		if (route->pathes[i]->clientspart) {
			jlast = route->pathes[i]->clientspart-1;
			leak = route->pathes[i]->leak;
		} else {
			for (pt = route->pathes[i]; pt->asn; pt = pt->prev)
				route_aspath[aspathlen++] = pt->asn;
			/* aspath is in reverse order! */
			leak = 0;
			jlast = clientspart(route_aspath, aspathlen, &leak);
			route->pathes[i]->leak = leak;
			route->pathes[i]->clientspart = jlast+1;
		}
		pt = route->pathes[i];
		prevpt = NULL;
		for (j=0; j<=jlast; j++) {
			ups = asndx(pt->asn);
			addconeas(coneas, ups, route->pathes[i]->asn);
			if (upstreams[ups] == 0) {
				upstreams[ups] = 1;
				upstreams_arr[nupstreams++] = ups;
				addclients(nets, ups, prevpt ? prevpt->asn : pt->asn);
			}
			if ((ups = *as(&group, asnum[ups]))) {
				if (ups_group[--ups] == 0) {
					ups_group[ups] = 1;
					ups_group_arr[nups_group++] = ups;
				}
				addconeas(coneas_gr, ups, route->pathes[i]->asn);
			}
			prevpt = pt;
			pt = pt->prev;
		}
		if (debuglevel >= 5 || (leak && debuglevel >= 4)) {
			/* revert aspath direction */
			static char pathstr[MAXPATHLEN*12]; /* ASN32 has maximum length 11 chars in dot notation */
			char *p;
			asn_t tmp_asn;

			if (!aspathlen)
				for (pt = route->pathes[i]; pt->asn; pt = pt->prev)
					route_aspath[aspathlen++] = pt->asn;
			for (j=aspathlen/2-1; j>=0; j--) {
				tmp_asn = route_aspath[j];
				route_aspath[j] = route_aspath[aspathlen-1-j];
				route_aspath[aspathlen-1-j] = tmp_asn;
			}
			/* make aspath string */
			p = pathstr;
			for (j=0; j<aspathlen; j++) {
				if (j) {
					crel1 = mkrel(route_aspath[j], route_aspath[j-1], 0);
					crel2 = mkrel(route_aspath[j-1], route_aspath[j], 0);
					if (crel1->pass2 && crel2->pass2) {
						if (crel1->sibling)
							*p++ = '=';
						else
							*p++ = '<', *p++='>';
					} else if (crel1->pass2) {
						*p++ = '<';
						if (crel1->sibling)
							*p++ = '=';
					} else if (crel2->pass2) {
						*p++ = '>';
						if (crel2->sibling)
							*p++ = '=';
						if (j<aspathlen-jlast-1) {
							crel2 = mkrel(route_aspath[j], route_aspath[j+1], 0);
							if (!crel2->pass2
							    /* && (crel1->sure == -1 || crel2->sure == -1) */)
								*p++ = '!';
						}
					}
					else
						*p++ = crel1->sibling ? '=' : '-';
				}
				if (j == aspathlen-jlast-1)
					*p++ = '{';
				strncpy(p, printas(route_aspath[j]), sizeof(pathstr) - (p-pathstr) - 1);
				p += strlen(p);
				if ((p-pathstr) > sizeof(pathstr)-3) break;
			}
			if (leak) strncpy(p, " (!)", sizeof(pathstr) - (p-pathstr) - 1);
			debug(leak ? 4 : 5, "%s/%d: %s %lu", printip(curip), preflen, pathstr, (unsigned long)route->pathes[i]->create_time);
		}
	}
	for (i=0; i<nupstreams; i++) {
		n24[upstreams_arr[i]] += nets;
		npref[upstreams_arr[i]]++;
		upstreams[upstreams_arr[i]] = 0;
	}
	for (i=0; i<nups_group; i++) {
		n24_gr[ups_group_arr[i]] += nets;
		npref_gr[ups_group_arr[i]]++;
		ups_group[ups_group_arr[i]] = 0;
	}
	if ((ups = *as(&group, route->pathes[0]->asn))) {
		own_n24_gr[--ups] += nets;
		own_npref_gr[ups]++;
	}
	return (1<<(24-preflen));
}

asn_t readasn(char *str)
{
	char *p;
	asn_t asn;

	for (p=str; isdigit(*p); p++);
	if (*p == '.')
		asn = (atoi(str)<<16) + atoi(p+1);
	else
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
		peerorder = realloc(peerorder, npeers*sizeof(*peerorder));
		peerindex = realloc(peerindex, npeers*sizeof(*peerindex));
		bcopy(&(peers[new]), &(peers[new+1]), (npeers-new-1)*sizeof(*peers));
		bcopy(&(peerorder[new]), &(peerorder[new+1]), (npeers-new-1)*sizeof(*peerorder));
		peers[new] = ip;
		peerorder[new] = npeers-1;
		for (left=0; left<npeers-1; left++)
			if (peerindex[left] >= new)
				peerindex[left]++;
		peerindex[npeers-1] = new;
	}
	return peerorder[new];
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
			i16 = htons(peerindex[peer(route)[i]]);
			fwrite(&i16, 2, 1, fout);
		} else {
			i8 = peerindex[peer(route)[i]];
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

static int weight(struct rib_t *pref, int preflen)
{
	if (pref->npathes) return (1<<(24-preflen));
	return (pref->left  ? weight(pref->left,  preflen+1) : 0) +
	       (pref->right ? weight(pref->right, preflen+1) : 0);
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

void readaslist(char *fname, asarr *group, struct group_t **asgroup, int *ngroups)
{
	FILE *f;
	char str[1024], *p;
	int i;
	asn_t asn;

	f = fopen(fname, "r");
	if (f == NULL) {
		error("Cannot open %s: %s", fname, strerror(errno));
		return;
	}
	while (fgets(str, sizeof(str), f)) {
		if (!isdigit(str[0])) continue;
		*asgroup = realloc(*asgroup, (*ngroups+1) * sizeof(**asgroup));
		for (i=0, p=str; *p; p++)
			if (*p == ',') i++;
		asgroup[0][*ngroups].asn = calloc(sizeof(asn_t), i+1);
		for (asgroup[0][*ngroups].nas=0, p=strtok(str, ","); p; p=strtok(NULL, ",")) {
			while (*p && isspace(*p)) p++;
			asn = readasn(p);
			asgroup[0][*ngroups].asn[asgroup[0][*ngroups].nas++] = asn;
			if (*as(group, asn))
				warning("AS%s included to more then one group", printas(asn));
			else
				*as(group, asn) = *ngroups+1;
		}
		ngroups[0]++;
	}
	fclose(f);
}

static void addtrace(asn_t as1, asn_t as2)
{
	int i;
	if ((i = *as(trace, as1)) == -1)
		return;
	if (i == 0) {
		i = ntrace++;
		*as(trace, as1) = ntrace;
		trace_arr = realloc(trace_arr, ntrace * sizeof(*trace_arr));
		trace_arr[i].nrel = 0;
		trace_arr[i].rel = NULL;
	} else
		i--;
	trace_arr[i].rel = realloc(trace_arr[i].rel, (trace_arr[i].nrel+1) * sizeof(trace_arr[i].rel[0]));
	trace_arr[i].rel[trace_arr[i].nrel++] = as2;
}

int main(int argc, char *argv[])
{
	int ch, i, j, k;
	char *p;
	FILE *f;
	struct dump_entry entry;
	char *groupfile, *ixfile;
	int progress_cnt, num_size;
	char *save_fname;
	char *arrstdin[] = {"-", NULL};
	char **inputfiles;
	char ***pinputfiles;
	int npinputfiles;
	peerndx_t *peerlist;
	static asn_t aspath[MAXPATHLEN];
	char str[1024], cmd[1024];

	save_fname = groupfile = ixfile = NULL;
	npinputfiles = 1;
	pinputfiles = calloc(npinputfiles+1, sizeof(*pinputfiles));
	while ((ch = getopt(argc, argv, "sd:ht:pg:w:u:x:T:")) != -1) {
		switch (ch) {
			case 'd':	debuglevel = atoi(optarg); break;
			case 'p':	progress = 1; break;
			case 'h':	usage(); exit(0);
			case 't':	tier1_arr[ntier1_hints++] = readasn(optarg); break;
			case 'x':	if (*optarg != '@') {
						for (i=1, p=optarg+1; *p; p++)
							if (*p==',') i++;
						asix=realloc(asix, (nix+1) * sizeof(*asix));
						asix[nix].nas = i;
						asix[nix].asn = calloc(i, sizeof(asix->asn[0]));
						for (i=0, p=strtok(strdup(optarg), ","); i<asix[nix].nas; i++, p=strtok(NULL, ",")) {
							asix[nix].asn[i] = readasn(p);
							*as(&ix, asix[nix].asn[i]) = nix+1;
						}
						nix++;
					} else
						ixfile = strdup(optarg+1);
					break;
			case 'g':	groupfile = strdup(optarg); break;
			case 'w':	save_fname = strdup(optarg); break;
			case 'u':	for (i=2, p=optarg; *p; p++)
						if (*p==',') i++;
					inputfiles = calloc(i, sizeof(*inputfiles));
					for (inputfiles[i=0]=strtok(strdup(optarg), ","); inputfiles[i++]; inputfiles[i]=strtok(NULL, ","));
					pinputfiles = realloc(pinputfiles, (npinputfiles+2)*sizeof(*pinputfiles));
					pinputfiles[npinputfiles++] = inputfiles;
					pinputfiles[npinputfiles] = NULL;
					break;
			case 'T':	if (!trace) trace = calloc(1, sizeof(asarr));
					if ((p = strchr(optarg, ':'))) {
						asn_t as1, as2;
						as1 = readasn(optarg);
						as2 = readasn(p+1);
						addtrace(as1, as2);
						addtrace(as2, as1);
					} else
						*as(trace, readasn(optarg)) = -1;
					break;
		}
	}
	debug(1, "ASRANK ver %d.%d", MAJVER, MINVER);
	if (groupfile) {
		readaslist(groupfile, &group, &asgroup, &ngroups);
		debug(3, "groups file %s read, %d groups found", groupfile, ngroups);
	}
	if (ixfile) {
		readaslist(ixfile, &ix, &asix, &nix);
		debug(3, "ix list file %s read, %d ix found", ixfile, nix);
	}
	if (argv[optind])
		inputfiles = argv + optind;
	else
		inputfiles = arrstdin;
	pinputfiles[0] = inputfiles;

	for (i=0; i<24; i++)
		mask[i] = htonl(1u<<(31-i));
	if (ngroups)
		wasgroup = calloc(ngroups, sizeof(*wasgroup));
	progress_cnt = 0;
	nas = 1;
	num_size = 65536;
	asnum = malloc(num_size * sizeof(*asnum));
	as_reserved = htonl(23456);

	for (; *pinputfiles; pinputfiles++) {
		/* first loop - process params (RIB tables and updates) */
		/* then process each updates file in each loop */
		if (ngroups) {
			updates_gr = calloc(ngroups, sizeof(*updates_gr));
			upd_n24_gr = calloc(ngroups, sizeof(*upd_n24_gr));
			withdraw_gr = calloc(ngroups, sizeof(*withdraw_gr));
			withdr_n24_gr = calloc(ngroups, sizeof(*withdr_n24_gr));
		}
	for (; **pinputfiles; pinputfiles[0]++) {
		cmd[0] = '\0';
		if (strcmp(**pinputfiles, "-")) {
			if (strlen(**pinputfiles) > 4 && strcmp(**pinputfiles+strlen(**pinputfiles)-4, ".bz2") == 0) {
				snprintf(cmd, sizeof(cmd)-1, "bunzip2 < %s", **pinputfiles);
				debug(2, "Executing command '%s'", cmd);
				f = popen(cmd, "r");
			} else
				f = fopen(**pinputfiles, "r");
			if (f == NULL) {
				fprintf(stderr, "Cannot open file %s: %s!\n", **pinputfiles, strerror(errno));
				continue;
			}
		} else
			f = stdin;
		if (open_dump(f)) {
			fprintf(stderr, "Cannot open dump\n");
			if (f != stdin) fclose(f);
			continue;
		}

		debug(1, "Parsing input file %s", **pinputfiles);
		while (read_dump(f, &entry) == 0) {
			int norigins, aspathlen, pref_n24, leak;
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
					if (entry.withdraw == 1)
						break;
					else
						*pprefix = calloc(1, sizeof(struct rib_t));
				}
				pprefix = (entry.prefix & mask[i]) ? &(pprefix[0]->right) : &(pprefix[0]->left);
			}
			pref_n24 = (1 << (24-entry.preflen));
			if (*pprefix) {
				if (pprefix[0]->left)  pref_n24 -= weight(pprefix[0]->left,  entry.preflen+1);
				if (pprefix[0]->right) pref_n24 -= weight(pprefix[0]->right, entry.preflen+1);
			}
			if (entry.withdraw && *pprefix) {
				for (i=0; i<pprefix[0]->npathes; i++)
					if (peerip(*pprefix, i) == entry.peerip[0])
						break;
				if (i < pprefix[0]->npathes) {
					if (debuglevel >= 7)
						debug(7, "%s %s/%d from %s found", entry.withdraw == 1 ? "Withdraw" : "Update", printip(entry.prefix), entry.preflen, printas(entry.origas[0]));
					ap = pprefix[0]->pathes[i];
					if (ap->leaf == 0) {
						error("Internal error in data structures (leaf==0 for existing prefix)");
						continue;
					}
					leak = 0;
					if (--(ap->leaf) == 0) {
						aspathes--;
						if (ap->leak)
							leak = 1;
					}
					/* decrease pathes for each aspath objects in this path */
					/* free unused aspath structures to delete withdrawed as relations */
					aspathlen = 0;
					while (ap && ap->asn) {
						if (ap->pathes-- == 0) {
							error("Internal error in data structures (path==0 for existing aspath), as%s", printas(ap->asn));
							break;
						}
						if (entry.withdraw == 1 || leak || debuglevel >= 6)
							aspath[aspathlen++] = ap->asn;
						prevap = ap->prev;
						if (ap->pathes == 0) {
							if (debuglevel >= 6) debug(6, "Free aspath %s", printaspath(aspath, aspathlen));
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
					if (entry.withdraw == 1) {
						if ((j = pprefix[0]->pathes[i]->clientspart))
							j--;
						else
							j = clientspart(aspath, aspathlen, NULL);
						for (; j>=0; j--) {
							*as(&withdraw, aspath[j]) += 1;
							*as(&withdr_n24, aspath[j]) += pref_n24;
							if ((k = *as(&group, aspath[j]))) {
								if (!wasgroup[--k]) {
									withdraw_gr[k]++;
									withdr_n24_gr[k] += pref_n24;
									wasgroup[k] = 1;
								}
							}
						}
						for (j=0; j<ngroups; j++)
							wasgroup[j] = 0;
					}
					pprefix[0]->npathes--;
					bcopy(&pprefix[0]->pathes[i+1], &pprefix[0]->pathes[i], (pprefix[0]->npathes-i)*sizeof(pprefix[0]->pathes[0]));
					bcopy(&pprefix[0]->pathes[pprefix[0]->npathes+1], &pprefix[0]->pathes[pprefix[0]->npathes], i*sizeof(peerndx_t));
					bcopy((peerndx_t *)&pprefix[0]->pathes[pprefix[0]->npathes+1]+i+1,
					      (peerndx_t *)&pprefix[0]->pathes[pprefix[0]->npathes]+i, (pprefix[0]->npathes-i)*sizeof(peerndx_t));
					if (leak && debuglevel >= 4)
						debug(4, "Route-leak removed: %s (%lu)", printaspath(aspath, aspathlen), (unsigned long)entry.create_time[i]);
					if (pprefix[0]->npathes == 0) {
						debug(6, "Prefix %s/%d removed (%s)", printip(entry.prefix), entry.preflen, entry.withdraw==1 ? "withdraw" : "update");
						fullview--;
					}
					/* do not shrink allocated mamory and do not free prefix structure */
					if (entry.withdraw == 1)
						continue;
				} else if (entry.withdraw == 1) {
					debug(5, "Withdraw origin ASN %s for prefix %s/%d not found", printas(entry.origas[0]), printip(entry.prefix), entry.preflen);
					debug(8, "  Origin peer %s, known origins:", printip(entry.peerip[0]));
					for (i=0; i<pprefix[0]->npathes; i++)
						debug(8, "   %s (index %d)", printip(peerip(*pprefix, i)), peer(*pprefix)[i]);
					continue;
				}
			} else if (entry.withdraw == 1) {
				debug(5, "Withdraw prefix not found: %s/%d from %s", printip(entry.prefix), entry.preflen, printas(entry.origas[0]));
				continue;
			}
			if (!*pprefix) {
				*pprefix = calloc(sizeof(struct rib_t) + entry.pathes*(sizeof(pprefix[0]->pathes[0])+sizeof(peerndx_t)), 1);
				fullview++;
				peerlist = (peerndx_t *)&pprefix[0]->pathes[entry.pathes];
			} else if (pprefix[0]->npathes == 0) {
				*pprefix = realloc(*pprefix, sizeof(struct rib_t) + entry.pathes*(sizeof(pprefix[0]->pathes[0])+sizeof(peerndx_t)));
				fullview++;
				peerlist = (peerndx_t *)&pprefix[0]->pathes[entry.pathes];
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
				if (i<pprefix[0]->npathes) {
					for (j=0; entry.aspath[i][j]; j++);
					debug(8, "%s/%d|%s|%s - neighbor as already exists for this prefix, skipped",
					   printip(entry.prefix), entry.preflen, printas(entry.origas[0]), printaspath(entry.aspath[0], j));
					continue;
				}
				/* new origin, add it */
				if (pprefix[0]->npathes >= MAXPATHES) {
					warning("Too many pathes for %s/%d, rest ignored", printip(entry.prefix), entry.preflen);
					continue;
				}
				*pprefix = realloc(*pprefix, sizeof(struct rib_t) + (pprefix[0]->npathes+entry.pathes)*(sizeof(pprefix[0]->pathes[0])+sizeof(peerndx_t)));
				bcopy(&pprefix[0]->pathes[pprefix[0]->npathes], &pprefix[0]->pathes[pprefix[0]->npathes+entry.pathes], pprefix[0]->npathes*sizeof(peerndx_t));
				peerlist = (peerndx_t *)&pprefix[0]->pathes[pprefix[0]->npathes+entry.pathes];
			}
			prefix = *pprefix;
			if (entry.pathes == 0 && debuglevel >= 8)
				debug(8, "%s/%d|%s| <no data>", printip(entry.prefix), entry.preflen, printas(entry.origas[i]));
			for (i=0; i<entry.pathes; i++) {
				int pathlen;
				asn_t path[MAXPATHLEN];
				asn_t prevas;
				struct aspath *curpath;

				if (debuglevel >= 8) {
					for (j=0; entry.aspath[i][j]; j++);
					debug(8, "%s/%d|%s|%s", printip(entry.prefix), entry.preflen, printas(entry.origas[i]), printaspath(entry.aspath[i], j));
				}
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
				if (entry.withdraw) {
					for (j=0; j<pathlen; j++)
						aspath[j] = path[pathlen-j-1];
					for (j=clientspart(aspath, pathlen, NULL); j>=0; j--) {
						*as(&updates, aspath[j]) += 1;
						*as(&upd_n24, aspath[j]) += pref_n24;
						if ((k = *as(&group, aspath[j]))) {
							if (!wasgroup[--k]) {
								updates_gr[k]++;
								upd_n24_gr[k] += pref_n24;
								wasgroup[k] = 1;
							}
						}
					}
					for (j=0; j<ngroups; j++)
						wasgroup[j] = 0;
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
				if (!curpath->leaf) {
					aspathes++;
					curpath->create_time = entry.create_time[i];
				}
				if (curpath->leaf == (1ul<<(sizeof(curpath->leaf)*8))-1)
					error("Too many prefixes for same aspath (%u), increase sizeof(leaf)!", curpath->leaf);
				else
					curpath->leaf++;
				prefix->pathes[prefix->npathes++] = curpath;
				peerlist[prefix->npathes-1] = peerndx(entry.peerip[i]);
				for (j=0; j<pathlen; j++) {
					*as(&wasas, path[j]) = 0;
					if (asndx(path[j]) == 0) {
						if (num_size == nas) {
							num_size *= 2;
							asnum = realloc(asnum, num_size*sizeof(*asnum));
						}
						*as(&ndx, path[j]) = nas;
						asnum[nas++] = path[j];
						if (ntier1)
							debug(5, "New ASN in update: %s", printas(path[j]));
					}
				}
				if (pathlen == 0)
					debug(5, "Empty aspath for %s/%d", printip(entry.prefix), entry.preflen);
			}
			if (peer(prefix) != peerlist)
				bcopy(peerlist, peer(prefix), prefix->npathes*sizeof(peerndx_t));
			for (i=0; i<norigins; i++)
				*as(&origin, origins[i]) = 0;
		}
		if (cmd[0]) pclose(f);
		else if (f != stdin) fclose(f);
	}
	if (progress) {
		printf("\n");
		fflush(stdout);
	}
	freeas(&origin);
	freeas(&wasas);
	if (!ntier1)
		debug(1, "RIB table parsed, %d prefixes, %d pathes, %d asn", fullview, aspathes, nas-1);
	else
		debug(2, "Updates files processed, now %d prefixes, %d pathes, %d asn", fullview, aspathes, nas-1);
	if (debuglevel >= 10) foreach_aspath(printtree);

	if (rel) {
		for (i=1; i<old_nas; i++)
			if (rel[i].nas_rel)
				free(rel[i].as_rel);
		free(rel); /* more simple then realloc and clean */
	}
	rel = calloc(nas, sizeof(*rel));
	old_nas = nas;

	if (!ntier1) {
		routes = calloc(nas, sizeof(routes[0]));
		proutes = calloc(nas, sizeof(proutes[0]));
	}
	maxroutes(&rootpath);
	if (tier1) free(tier1);
	tier1 = calloc(nas, sizeof(tier1[0]));
	if (ntier1) {
		for (i=0; i<ntier1; i++)
			if (tier1_arr[i])
				tier1[asndx(tier1_arr[i])] = 1;
	} else {
		ntier1 = ntier1_hints;
		tier1_bad = calloc(nas, sizeof(tier1_bad[0]));
		for (ntier1=0; ntier1<ntier1_hints; ntier1++) {
			if (asndx(tier1_arr[ntier1]) == 0)
				warning("No AS %s, exclude from tier1 list", printas(tier1_arr[ntier1]));
			else
				tier1[asndx(tier1_arr[ntier1])] = 1;
		}
		for (i=1; i<nas; i++) {
			if (ntier1 >= sizeof(tier1_arr)/sizeof(tier1_arr[0])) {
				warning("Too many tier1 candidates found");
				break;
			}
			if (routes[i] > fullview/2 && proutes[i] < fullview/2) {
				if (tier1[i] == 0) {
					tier1_arr[ntier1++] = asnum[i];
					tier1[i] = 1;
					debug(6, "Add tier1 candidate: %s", printas(asnum[i]));
				}
			}
		}
		debug(1, "Found %d tier1 candidates", ntier1);

		/* next AS after tier1 candidate is candidate also */
		add_tier1(&rootpath);
		debug(1, "Added candidates, now %d", ntier1);
		free(routes);
		free(proutes);
		routes = proutes = NULL;
		for (i=0; i<ntier1; i++)
			tier1[asndx(tier1_arr[i])] = i+1;

		npath = calloc(nas, sizeof(npath[0]));
		foreach_aspath(get_npath);
		tier1_linked = calloc(ntier1, sizeof(tier1_linked[0]));

		for (;;) {
			int maxndx;
			double rate, maxrate;

			inv_pathes = 0;
			check_valid_path_recurs(&rootpath, 0);
			if (inv_pathes == 0) break;
			debug(5, "Found %d invalid pathes", inv_pathes);
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
			debug(5, "%s is not tier1 (%d rate, %d pathes)", printas(tier1_arr[maxndx]),
			      tier1_bad[asndx(tier1_arr[maxndx])], npath[asndx(tier1_arr[maxndx])]);
			tier1[asndx(tier1_arr[maxndx])] = 0;
			tier1_arr[maxndx] = 0;
			for (i=0; i<ntier1; i++) {
				if (!tier1_arr[i]) continue;
				tier1_bad[asndx(tier1_arr[i])] = 0;
				if (!tier1_linked[i]) {
					debug(5, "%s is not tier1 (not linked to any other candidated)", printas(tier1_arr[i]));
					tier1[asndx(tier1_arr[i])] = 0;
					tier1_arr[i] = 0;
				} else
					tier1_linked[i] = 0;
			}
		}
		free(tier1_bad);
		free(tier1_linked);
		free(npath);

		debug(1, "Tier1 list created");
		for (i=0; i<ntier1; i++) {
			if (tier1_arr[i])
				debug(1, "  %s", printas(tier1_arr[i]));
		}
	}

	totier1 = viatier1 = horlinks = 0;
	foreach_aspath(make_rel1);
	debug(1, "Pass 1 complete");
	/* second path - search for route leaks */
	nextas = calloc(nas, sizeof(*nextas));
	own_n24 = calloc(nas, sizeof(*own_n24));
	own_npref = calloc(nas, sizeof(*own_npref));
	make_rel2(rib_root, 0);
	free(nextas);
	debug(1, "Pass 2 complete");
	for (i=1; i<nas; i++) {
		if (asnum[i] == as_reserved)
			continue;
		for (j=0; j<rel[i].nas_rel; j++) {
			struct rel_lem_t *r;

			if (rel[i].as_rel[j].asn == as_reserved)
				continue;
			if (rel[i].as_rel[j].sure <= 0)
				continue;
			if ((r = mkrel(rel[i].as_rel[j].asn, asnum[i], 0)) <= 0)
				continue;
			if (r->self == 0) {
				if (rel[i].as_rel[j].self*2 > own_n24[asndx(rel[i].as_rel[j].asn)]) {
					if (needtrace(asnum[i], rel[i].as_rel[j].asn))
						if (rel[i].as_rel[j].sure < 4)
							debug(4, "Set relations %s > %s sure=4 - >1/2 self prefixes",
							      printas(asnum[i]), printas2(rel[i].as_rel[j].asn));
					rel[i].as_rel[j].sure = 4;
				} else if (rel[i].as_rel[j].self > 0 && rel[i].as_rel[j].sure != 4) {
					if (rel[i].as_rel[j].sure < 3) {
						if (needtrace(asnum[i], rel[i].as_rel[j].asn))
							debug(4, "Set relations %s > %s sure=3 - self prefixes",
							      printas(asnum[i]), printas2(rel[i].as_rel[j].asn));
						rel[i].as_rel[j].sure = 3;
					}
				}
			} else if (rel[i].as_rel[j].sure == 0) {
				if (r->self*2 > own_n24[i]) {
					if (needtrace(rel[i].as_rel[j].asn, asnum[i]))
						if (r->sure < 4)
							debug(4, "Set relations %s > %s sure=4 - >1/2 self prefixes",
							      printas(rel[i].as_rel[j].asn), printas2(asnum[i]));
					r->sure = 4;
				} else {
					if (r->sure < 3) {
						if (needtrace(rel[i].as_rel[j].asn, asnum[i]))
							debug(4, "Set relations %s > %s sure=4 - >1/2 self prefixes",
							      printas(rel[i].as_rel[j].asn), printas2(asnum[i]));
						r->sure = 3;
					}
				}
			}
		}
	}
	debug(1, "Pass 3 complete");
	clean_noinv(&rootpath);
	make_rel4(rib_root);
	debug(1, "Pass 4 complete");
	foreach_aspath(make_rel5);
	debug(1, "Pass 5 complete");
	foreach_aspath(make_rel6);
	for (i=1; i<nas; i++) {
		if (asnum[i] == as_reserved)
			continue;
		for (j=0; j<rel[i].nas_rel; j++) {
			struct rel_lem_t *r;

			if (rel[i].as_rel[j].sure != 1)
				continue;
			if (rel[i].as_rel[j].asn == as_reserved)
				continue;
			if ((r=mkrel(rel[i].as_rel[j].asn, asnum[i], 0))->sure == 1)
				continue;
			if (r->pass2)
				continue;
			/* relations determined - set pass2 */
			rel[i].as_rel[j].pass2 = 1;
		}
	}
	/* repeat pass 6? */
	debug(1, "Pass 6 complete");
	/* add relations for "a - b > c"  ->   a > b and others like this? */
	debug(1, "AS relations built");
	debug(1, "%d pathes to tier1, %d pathes via tier1, %d pathes avoid tier1", totier1, viatier1, horlinks);

	/* calculate rating */
	n24 = calloc(nas, sizeof(*n24));
	npref = calloc(nas, sizeof(*npref));
	coneas = calloc(nas, sizeof(*coneas));
	upstreams = calloc(nas, sizeof(*upstreams));
	upstreams_arr = calloc(nas, sizeof(*upstreams_arr));
	if (ngroups) {
		ups_group = calloc(ngroups, sizeof(*ups_group));
		ups_group_arr = calloc(ngroups, sizeof(*ups_group));
		n24_gr = calloc(ngroups, sizeof(*n24_gr));
		npref_gr = calloc(ngroups, sizeof(*npref_gr));
		coneas_gr = calloc(ngroups, sizeof(*coneas_gr));
		own_n24_gr = calloc(ngroups, sizeof(*own_n24_gr));
		own_npref_gr = calloc(ngroups, sizeof(*own_npref_gr));
	}
	collect_stats(rib_root, 0);
	free(upstreams);
	free(upstreams_arr);
	if (ngroups) {
		free(ups_group);
		free(ups_group_arr);
	}
	debug(1, "Rating calculated");

	/* count nupstreams, npeerings, nclients */
	nuplinks = calloc(nas, sizeof(*nuplinks));
	npeerings = calloc(nas, sizeof(*npeerings));
	nclients = calloc(nas, sizeof(*nclients));
	for (i=1; i<nas; i++) {
		if (asnum[i] == as_reserved)
			continue;
		for (j=0; j<rel[i].nas_rel; j++) {
			struct rel_lem_t *r;

			if (asnum[i] == rel[i].as_rel[j].asn) continue;
			if (rel[i].as_rel[j].asn == as_reserved) continue;
			r = mkrel(rel[i].as_rel[j].asn, asnum[i], 0);
			if (rel[i].as_rel[j].sure > r->sure &&
			    rel[i].as_rel[j].pass2 &&
			    rel[i].as_rel[j].n24*64 > n24[asndx(rel[i].as_rel[j].asn)]) {
				debug(4, "%s is upstream for %s", printas(asnum[i]), printas2(rel[i].as_rel[j].asn));
				nclients[i]++;
				nuplinks[asndx(rel[i].as_rel[j].asn)]++;
				rel[i].as_rel[j].upstream = 1;
			} else if (rel[i].as_rel[j].sure <= 0 && r->sure <= 0) {
				debug(4, "peering %s-%s", printas(asnum[i]), printas2(rel[i].as_rel[j].asn));
				npeerings[i]++;
			}
		}
	}

	/* count degree for groups */
	if (ngroups) {
		char *hasrel, *hasuplink, *haspeering, *hasclients;
		int *asrel, *asuplink, *aspeering, *asclients;

		group_rel = calloc(ngroups, sizeof(*group_rel));
		nuplinks_gr = calloc(ngroups, sizeof(*nuplinks_gr));
		npeering_gr = calloc(ngroups, sizeof(*npeering_gr));
		nclients_gr = calloc(ngroups, sizeof(*nclients_gr));
		hasrel = calloc(nas, sizeof(*hasrel));
		asrel = calloc(nas, sizeof(*asrel)); /* too many, it's only list of neighbors */
		hasuplink = calloc(nas, sizeof(*hasuplink));
		asuplink = calloc(nas, sizeof(*asuplink)); /* too many, it's only list of neighbors */
		haspeering = calloc(nas, sizeof(*haspeering));
		aspeering = calloc(nas, sizeof(*aspeering)); /* too many, it's only list of neighbors */
		hasclients = calloc(nas, sizeof(*hasclients));
		asclients = calloc(nas, sizeof(*asclients)); /* too many, it's only list of neighbors */
		for (i=0; i<ngroups; i++) {
			int nasrel, relas, nasuplink, naspeering, nasclients;
			asn_t relasn;

			nasrel = nasuplink = naspeering = nasclients = 0;
			for (j=0; j<asgroup[i].nas; j++) {
				if (asndx(asgroup[i].asn[j])==0)
					continue;
				for (k=0; k<rel[asndx(asgroup[i].asn[j])].nas_rel; k++) {
					if (*as(&group, (relasn=rel[asndx(asgroup[i].asn[j])].as_rel[k].asn)) == i+1)
						continue; /* do not count inter-group relations */
					relas = asndx(relasn);
					if (hasrel[relas] == 0) {
						hasrel[relas] = 1;
						asrel[nasrel++] = relas;
					}
					if (rel[asndx(asgroup[i].asn[j])].as_rel[k].upstream && hasuplink[relas] == 0) {
						hasuplink[relas] = 1;
						asuplink[nasuplink++] = relas;
					}
					if (mkrel(relasn, asgroup[i].asn[j], 0)->upstream &&
					    hasclients[relas] == 0) {
						hasclients[relas] = 1;
						asclients[nasclients++] = relas;
					}
					if (rel[asndx(asgroup[i].asn[j])].as_rel[k].sure <= 0 &&
					    mkrel(relasn, asgroup[i].asn[j], 0)->sure <= 0 &&
					    haspeering[relas] == 0) {
						haspeering[relas] = 1;
						aspeering[naspeering++] = relas;
					}
				}
			}
			group_rel[i] = nasrel;
			nuplinks_gr[i] = nasuplink;
			npeering_gr[i] = naspeering;
			nclients_gr[i] = nasclients;
			for (j=0; j<nasrel; j++) hasrel[asrel[j]] = 0;
			for (j=0; j<nasuplink; j++) hasuplink[asuplink[j]] = 0;
			for (j=0; j<naspeering; j++) haspeering[aspeering[j]] = 0;
			for (j=0; j<nasclients; j++) hasclients[asclients[j]] = 0;
		}
		free(hasrel);
		free(asrel);
		free(hasuplink);
		free(asuplink);
		free(haspeering);
		free(aspeering);
		free(hasclients);
		free(asclients);
		debug(1, "degree for groups accounted");
	}
	if (debuglevel >= 6 || (debuglevel >= 4 && trace)) {
		for (i=1; i<nas; i++) {
			char s[16];

			if (debuglevel < 6 && !*as(trace, asnum[i])) continue;
			strncpy(s, printas(asnum[i]), sizeof(s));
			s[sizeof(s)-1] = '\0';
			for (j=0; j<rel[i].nas_rel; j++) {
				if (rel[i].as_rel[j].sure == 0) continue;
				debug(needtrace(rel[i].as_rel[j].asn, asnum[i]) ? 4 : 6,
				      "Relations %s > %s: sure %d, pass2: %d, n24: %d, prefs: %d, self: %d, sibling: %d, upstream: %d",
				      s, printas(rel[i].as_rel[j].asn), rel[i].as_rel[j].sure,
				      rel[i].as_rel[j].pass2 ? 1 : 0, rel[i].as_rel[j].n24, rel[i].as_rel[j].prefs,
				      rel[i].as_rel[j].self, rel[i].as_rel[j].sibling ? 1 : 0,
				      rel[i].as_rel[j].upstream ? 1 : 0);
			}
		}
	}

	/* output statistics */
	printf("==========\n");
	for (i=0; i<ngroups; i++) {
		int ndx, existgroup;

		existgroup=0;
		str[0] = 0;
		p = str;
		if (*as(&ix, asgroup[i].asn[0])) continue;
		for (j=0; j<asgroup[i].nas; j++) {
			if (p != str) *p++ = ',';
			strncpy(p, printas(asgroup[i].asn[j]), sizeof(str) - (p-str) - 1);
			p += strlen(p);
			if (p-str+10 >= sizeof(str)) break;
			ndx = asndx(asgroup[i].asn[j]);
			if (ndx && (rel[ndx].nas_rel || own_n24[ndx]))
				existgroup = 1;
		}
		if (existgroup)
			printf(FORMAT, str, n24_gr[i], own_n24_gr[i], npref_gr[i],
			       own_npref_gr[i], coneas_gr[i].nas, group_rel[i],
			       nuplinks_gr[i], npeering_gr[i], upd_n24_gr[i],
			       withdr_n24_gr[i]);
	}
	for (i=1; i<nas; i++) {
		if (*as(&ix, asnum[i])) continue;
		if (asnum[i] != as_reserved && (rel[i].nas_rel || own_n24[i]))
			printf(FORMAT, printas(asnum[i]), n24[i], own_n24[i],
			       npref[i], own_npref[i], coneas[i].nas, rel[i].nas_rel - 1,
			       nuplinks[i], npeerings[i], *as(&upd_n24, asnum[i]),
			       *as(&withdr_n24, asnum[i]));
	}

	for (i=1; i<nas; i++) {
		*as(&updates, asnum[i]) = 0;
		*as(&upd_n24, asnum[i]) = 0;
		*as(&withdraw, asnum[i]) = 0;
		*as(&withdr_n24, asnum[i]) = 0;
		if (coneas[i].asn) free(coneas[i].asn);
	}
	free(n24);
	free(npref);
	free(coneas);
	free(own_n24);
	free(own_npref);
	free(nuplinks);
	free(npeerings);
	free(nclients);
	if (ngroups) {
		free(n24_gr);
		free(npref_gr);
		free(coneas_gr);
		free(own_n24_gr);
		free(own_npref_gr);
		free(group_rel);
		free(nuplinks_gr);
		free(npeering_gr);
		free(updates_gr);
		free(upd_n24_gr);
		free(withdraw_gr);
		free(withdr_n24_gr);
	}
	}
	if (ngroups)
		free(wasgroup);
	if (rel) {
		for (i=1; i<nas; i++)
			if (rel[i].nas_rel)
				free(rel[i].as_rel);
		free(rel);
	}
	if (tier1) free(tier1);
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
	char spaces[20];
	time_t curtime;

	if (level > debuglevel) return;
	curtime = time(NULL);
	strftime(buftime, sizeof(buftime), "%b %e %T", localtime(&curtime));
	va_start(ap, format);
	vsnprintf(buf, sizeof(buf), format, ap);
	va_end(ap);
	memset(spaces, ' ', sizeof(spaces));
	spaces[level >= sizeof(spaces) ? sizeof(spaces)-1 : level] = '\0';
	printf("%s%s%s\n", buftime, spaces, buf);
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

