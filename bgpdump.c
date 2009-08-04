#include <sys/types.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include "asrank.h"

#define BGPDUMP_TYPE_MRTD_BGP		 5
#define BGPDUMP_TYPE_MRTD_TABLE_DUMP	12
#define BGPDUMP_TYPE_ZEBRA_BGP		16
#define BGPDUMP_TYPE_TABLE_DUMP_V2_PEER_INDEX_TABLE	((13ul << 16) | 1)
#define BGPDUMP_TYPE_TABLE_DUMP_V2_RIB_IPV4_UNICAST	((13ul << 16) | 2)
#define BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP		((12ul << 16) | 1)
#define BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP_32BIT_AS	((12ul << 16) | 3)
#define BGPDUMP_TYPE_ZEBRA_BGP_MESSAGE			((16ul << 16) | 1)
#define BGPDUMP_TYPE_ZEBRA_BGP_MESSAGE_AS4		((16ul << 16) | 4)

#define BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AFI_IP6	1
#define BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AS4	2

#define BGP_ATTR_AS_PATH	2
#define BGP_ATTR_FLAG_EXTLEN	0x10

#define BGP_ZEBRA_UPDATE	2

#define AS_SET			1
#define AS_SEQUENCE		2
#define AS_CONFED_SEQUENCE	3
#define AS_CONFED_SET		4

#define AFI_IP			1

static struct buf_t {
	char *data;
	int bufsize;
	int len;
	int pos;
} buf;

static struct {
	uint32_t as;
	uint32_t ip;
} *peer;

static struct preflist {
	int len;
	uint32_t ip;
} *announce, *withdraw;
static int pref_ndx, pref_num, pref_max;
static int wthdr_ndx, wthdr_num, wthdr_max;

int open_dump(FILE *f)
{
	return 0;
}

static int get_buf(struct buf_t *buf, int len, void *data)
{
	if (len == 0) return 0;
	if (buf->len - buf->pos < len) {
		warning("Buffer too small");
		return -1;
	}
	if (data)
		memcpy(data, buf->data + buf->pos, len);
	buf->pos += len;
	return 0;
}

static int process_attr(int assize, uint32_t *aspath)
{
	uint16_t i16;
	int attr_len, len, aspathlen;
	u_char flag, type, aslen, i8;

	if (get_buf(&buf, 2, &i16)) return 0;
	if (i16 == 0) return 0;
	attr_len = ntohs(i16);
	while (attr_len >= 3) {
		if (get_buf(&buf, 1, &flag)) break;
		if (get_buf(&buf, 1, &type)) break;
		attr_len -= 2;
		if (flag & BGP_ATTR_FLAG_EXTLEN) {
			if (attr_len<2) break;
			if (get_buf(&buf, 2, &i16)) break;
			len = ntohs(i16);
			attr_len -= 2;
		} else {
			if (get_buf(&buf, 1, &i8)) break;
			len = i8;
			attr_len--;
		}
		if (attr_len < len) break;
		attr_len -= len;
		switch (type) {
			case BGP_ATTR_AS_PATH:
				aspathlen = 0;
				while (len > 0) {
					if (get_buf(&buf, 1, &type)) break;
					if (get_buf(&buf, 1, &aslen)) break;
					len -= 2;
					if (aslen * assize > len) {
						warning("Bad attr: aslen %d, len %d", aslen, len);
						break;
					}
					/* ignore confederations */
					if (type == AS_CONFED_SET || type == AS_CONFED_SEQUENCE) {
						if (get_buf(&buf, assize*aslen, NULL)) break;
						len -= assize*aslen;
						continue;
					}
					if (type != AS_SET && type != AS_SEQUENCE) {
						debug(2, "Unknown attr type %d ignored", type);
						break;
					}
					if (aspathlen + aslen >= MAXPATHLEN) {
						warning("Too long aspath: %d", aspathlen+aslen);
						break;
					}
					/* process AS_SET as AS_SEQUENCE */
					if (assize == 4) {
						if (get_buf(&buf, 4*aslen, aspath+aspathlen))
							break;
					} else {
						int i;
						for (i=0; i<aslen; i++) {
							if (get_buf(&buf, 2, &i16)) break;
							aspath[aspathlen+i] = htonl(ntohs(i16));
						}
					}
					aspathlen += aslen;
					len -= assize*aslen;
				}
				if (get_buf(&buf, len, NULL)) break;
				aspath[aspathlen] = 0;
				continue;
			default:get_buf(&buf, len, NULL); break;
		}
	}
	return aspathlen ? 1 : 0;
}

static int read_prefix_list(struct buf_t *buf, int len, struct preflist **preflist, int *preflist_size)
{
	u_char i8;
	int n;
	uint32_t i32;

	n = 0;
	while (len > 0) {
		if (get_buf(buf, 1, &i8)) return n;
		i32 = 0;
		if (get_buf(buf, (i8+7)/8, &i32)) return n;
		if (*preflist_size <= n) {
			*preflist_size = (*preflist_size+4)*2;
			*preflist = realloc(*preflist, *preflist_size * sizeof(**preflist));
		}
		preflist[0][n].len = i8;
		preflist[0][n].ip  = i32;
		n++;
		len -= 1+(i8+7)/8;
	}
	return n;
}

static int read_next_update(struct dump_entry *entry)
{
	/* return filled entry structure! */
	if (wthdr_ndx < wthdr_num) {
		entry->preflen = withdraw[wthdr_ndx].len;
		entry->prefix = withdraw[wthdr_ndx++].ip;
		entry->withdraw = 1;
		return 1;
	}
	if (pref_ndx < pref_num) {
		entry->preflen = announce[pref_ndx].len;
		entry->prefix = announce[pref_ndx++].ip;
		entry->withdraw = 2;
		return 1;
	}
	return 0;
}

int read_dump(FILE *f, struct dump_entry *entry)
{
	uint32_t i32, etype, elen;
	uint16_t i16, entry_count;
	static uint16_t peer_count;
	u_char preflen, peer_type, i8, c;
	int i, j, assize, aspathlen;
	u_char marker[16];

	if (read_next_update(entry))
		return 0;
	for (;;) {
		if (fread(&i32,   4, 1, f) != 1) return -1; /* time */
		if (fread(&etype, 4, 1, f) != 1) return -1;
		if (fread(&elen,  4, 1, f) != 1) return -1;
		buf.len = ntohl(elen);
		buf.pos = 0;
		if (buf.bufsize < buf.len) {
			buf.data = realloc(buf.data, buf.len);
			if (buf.data == NULL) {
				error("Cannot allocate %u bytes of memory", buf.len);
				return 1;
			}
			buf.bufsize = buf.len;
		}
		if (fread(buf.data, 1, buf.len, f) != buf.len) {
			error("Unexpected EOF");
			return -1;
		}
		etype = ntohl(etype);
		switch (etype) {
			case BGPDUMP_TYPE_TABLE_DUMP_V2_PEER_INDEX_TABLE:
				get_buf(&buf, 4, NULL);
				get_buf(&buf, 2, &i16);	/* view name len */
				get_buf(&buf, ntohs(i16), NULL);	/* view name */
				get_buf(&buf, 2, &peer_count);	/* peer count */
				peer_count = ntohs(peer_count);
				if (peer) free(peer);
				peer = calloc(sizeof(*peer), peer_count);
				for (i=0; i<peer_count; i++) {
					if (get_buf(&buf, 1, &peer_type)) break;
					get_buf(&buf, 4, NULL);	/* peer route-id */
					if (peer_type & BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AFI_IP6)
						get_buf(&buf, 16, NULL); /* peer IPv6 */ 
					else
						get_buf(&buf, 4, &(peer[i].ip));
					if (peer_type & BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AS4) {
						if (get_buf(&buf, 4, &(peer[i].as))) break;
					} else {
						if (get_buf(&buf, 2, &i16)) break;
						peer[i].as = htonl(ntohs(i16));
					}
				}
				peer_count = i;
				debug(3, "Peer index table processed, found %d peers", peer_count);
				continue;
			case BGPDUMP_TYPE_ASRANK_PEERLIST:
				get_buf(&buf, 2, &i16);
				peer_count = ntohs(i16);
				if (peer) free(peer);
				peer = calloc(sizeof(*peer), peer_count);
				for (i=0; i<peer_count; i++)
					if (get_buf(&buf, 4, &(peer[i].ip)))
						break;
				debug(3, "Peer index table processed, found %d peers", peer_count);
				continue;
			case BGPDUMP_TYPE_TABLE_DUMP_V2_RIB_IPV4_UNICAST:
				get_buf(&buf, 4, NULL); /* seq */
				if (get_buf(&buf, 1, &preflen)) break;
				entry->preflen = preflen;
				entry->prefix = 0;
				if (get_buf(&buf, (preflen+7)/8, &entry->prefix)) break;
				if (get_buf(&buf, 2, &entry_count)) break;
				entry_count = ntohs(entry_count);
				entry->pathes = 0;
				for (i=0; i<entry_count; i++) {
					if (get_buf(&buf, 2, &i16)) break;	/* peer index */
					i16 = ntohs(i16);
					if (i16 < peer_count) {
						entry->origas[entry->pathes] = peer[i16].as;
						entry->peerip[entry->pathes] = peer[i16].ip;
					} else
						warning("Too big peer index %d", i16);
					get_buf(&buf, 4, NULL);	/* originated time */
					/* process attribute */
					if (process_attr(4, entry->aspath[entry->pathes]) == 1) {
						if (entry->pathes >= MAXPATHES) {
							warning("Too many aspath for prefix, rest ignored");
							break;
						}
						entry->pathes++;
					}
				}
				if (entry->pathes == 0) continue;
				entry->withdraw = 0;
				return 0;
			case BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP:
			case BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP_32BIT_AS:
				if (get_buf(&buf, 4, NULL)) break;	/* view, sequence */
				if (get_buf(&buf, 4, &entry->prefix)) break;
				if (get_buf(&buf, 1, &preflen)) break;
				entry->preflen = preflen;
				if (get_buf(&buf, 5, NULL)) break; /* status, time */
				if (get_buf(&buf, 4, &(entry->peerip[0]))) break;
				if (etype == BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP_32BIT_AS) {
					assize = 4;
					get_buf(&buf, 4, &(entry->origas[0]));
				} else {
					assize = 2;
					get_buf(&buf, 2, &i16);
					entry->origas[0] = htonl(ntohs(i16));
				}
				if (process_attr(assize, entry->aspath[0]) != 1)
					continue;
				entry->pathes = 1;
				entry->withdraw = 0;
				return 0;
			case BGPDUMP_TYPE_ZEBRA_BGP_MESSAGE:
			case BGPDUMP_TYPE_ZEBRA_BGP_MESSAGE_AS4:
				if (etype == BGPDUMP_TYPE_ZEBRA_BGP_MESSAGE_AS4) {
					assize = 4;
					get_buf(&buf, 4, &(entry->origas[0]));
				} else {
					assize = 2;
					get_buf(&buf, 2, &i16);
					entry->origas[0] = htonl(ntohs(i16));
				}
				if (get_buf(&buf, assize, NULL)) break;	/* dest as */
				if (get_buf(&buf, 2, NULL)) break;	/* iface_index */
				if (get_buf(&buf, 2, &i16)) break;
				i16 = ntohs(i16);
				if (i16 != AFI_IP) {
					error("Unsupported address family 0x%04x, ignoring", i16);
					continue;
				}
				if (get_buf(&buf, 4, &(entry->peerip[0]))) break;
				if (get_buf(&buf, 4, NULL)) break;	/* dest_ip */
				if (get_buf(&buf, 16, marker)) break;
				if (memcmp(marker, "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff", 16)) {
					error("bgp message: bad marker, ignoring");
					continue;
				}
				if (get_buf(&buf, 2, &i16)) break;	/* message size */
				if (get_buf(&buf, 1, &i8)) break;	/* message type */
				if (i8 != BGP_ZEBRA_UPDATE) {
					warning("Unknown BGP message type %d, ignoring", i8);
					continue;
				}
				i16 = ntohs(i16) - 19;
				if (buf.len-buf.pos != i16) {
					error("bgp message bad length (%d != %d)", buf.len-buf.pos, i16);
					continue;
				}
				if (get_buf(&buf, 2, &i16)) break;
				wthdr_num = read_prefix_list(&buf, ntohs(i16), &withdraw, &wthdr_max);
				process_attr(assize,  entry->aspath[0]);
				pref_num = read_prefix_list(&buf, buf.len-buf.pos, &announce, &pref_max);
				wthdr_ndx = pref_ndx = 0;
				entry->pathes = 1;
				if (read_next_update(entry))
					return 0;
				else
					continue;
			case BGPDUMP_TYPE_ASRANK_PREF:
				if (get_buf(&buf, 1, &preflen)) break;
				entry->preflen = preflen;
				entry->prefix = 0;
				if (get_buf(&buf, (preflen+7)/8, &entry->prefix)) break;
				if (get_buf(&buf, 1, &i8)) break;
				if (i8==0) continue;
				entry->pathes = i8;
				for (i=0; i<entry->pathes; i++) {
					if (peer_count < 256) {
						get_buf(&buf, 1, &i8);
						j = i8;
					} else {
						get_buf(&buf, 2, &i16);
						j = ntohs(i16);
					}
					if (j < peer_count)
						entry->peerip[entry->pathes] = peer[j].ip;
					else
						error("Too big peer index");
					if (get_buf(&buf, 1, &i8))
						break;
					aspathlen = i8;
					for (j=0; j<aspathlen; j++) {
						get_buf(&buf, 1, &i8);
						if (i8 == 0xff) {
							get_buf(&buf, 4, &entry->aspath[i][j]);
						} else if (i8 < 0xf0) {
							get_buf(&buf, 1, &c);
							entry->aspath[i][j] = htonl(i8*256+c);
						} else {
							get_buf(&buf, 2, &i16);
							entry->aspath[i][j] = htonl((i8 & 0xf) * 65536 + ntohs(i16));
						}
					}
					entry->origas[i] = entry->aspath[i][0];
					entry->aspath[i][j] = 0;
				}
				return 0;
			default:error("Unsupported format: type %d, subtype %d", etype>>16, etype & 0xffff);
				return 1;
		}
		break;
	}
	return 0;
}

