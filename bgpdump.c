#include <sys/types.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include "asrank.h"

#define BGPDUMP_TYPE_MRTD_BGP		 5
#define BGPDUMP_TYPE_MRTD_TABLE_DUMP	12
#define BGPDUMP_TYPE_TABLE_DUMP_V2_PEER_INDEX_TABLE	((13ul << 16) | 1)
#define BGPDUMP_TYPE_TABLE_DUMP_V2_RIB_IPV4_UNICAST	((13ul << 16) | 2)
#define	BGPDUMP_TYPE_ZEBRA_BGP		16

#define BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AFI_IP6	1
#define BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AS4	2

#define BGP_ATTR_AS_PATH	2
#define BGP_ATTR_FLAG_EXTLEN	0x10

#define AS_SET			1
#define AS_SEQUENCE		2
#define AS_CONFED_SEQUENCE	3
#define AS_CONFED_SET		4

static struct buf_t {
	char *data;
	int bufsize;
	int len;
	int pos;
} buf;

static struct {
	uint32_t as;
} *peer;

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

int read_dump(FILE *f, struct dump_entry *entry)
{
	uint32_t i32, etype, elen;
	uint16_t i16, entry_count;
	static uint16_t peer_count;
	u_char preflen, peer_type, i8, flag, type, aslen;
	int attr_len, len, i, aspathlen;

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
		if (fread(buf.data, 1, buf.len, f) != buf.len) return -1;
		etype = ntohl(etype);
		switch (etype) {
			case BGPDUMP_TYPE_TABLE_DUMP_V2_PEER_INDEX_TABLE:
				get_buf(&buf, 4, NULL);
				get_buf(&buf, 2, &i16);	/* view name len */
				get_buf(&buf, ntohs(i16), NULL);	/* view name */
				get_buf(&buf, 2, &peer_count);	/* peer count */
				peer_count = ntohs(peer_count);
				if (peer) free(peer);
				peer = malloc(peer_count * sizeof(*peer));
				for (i=0; i<peer_count; i++) {
					if (get_buf(&buf, 1, &peer_type)) break;
					get_buf(&buf, 4, NULL);	/* peer route-id */
					if (peer_type & BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AFI_IP6)
						get_buf(&buf, 16, NULL); /* peer IPv6 */ 
					else
						get_buf(&buf, 4, NULL);	/* peer IP */
					if (peer_type & BGPDUMP_PEERTYPE_TABLE_DUMP_V2_AS4) {
						if (get_buf(&buf, 4, &i32)) break;
						peer[i].as = ntohl(i32);
					} else {
						if (get_buf(&buf, 2, &(peer[i].as))) break;
					}
				}
				peer_count = i;
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
					if (i16 < peer_count)
						entry->origas[entry->pathes] = peer[i16].as;
					else
						warning("Too big peer index %d", i16);
					get_buf(&buf, 4, NULL);	/* originated time */
					/* process attribute */
					if (get_buf(&buf, 2, &i16)) break;
					if (i16 == 0) continue;
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
								if (entry->pathes >= MAXPATHES) {
									warning("Too many aspath for prefix, rest ignored");
									get_buf(&buf, len, NULL);
									break;
								}
								aspathlen = 0;
								while (len > 0) {
									if (get_buf(&buf, 1, &type)) break;
									if (get_buf(&buf, 1, &aslen)) break;
									len -= 2;
									if (aslen * 4 > len) {
										warning("Bad attr: aslen %d, len %d", aslen, len);
										break;
									}
									/* ignore confederations */
									if (type == AS_CONFED_SET || type == AS_CONFED_SEQUENCE) {
										if (get_buf(&buf, 4*aslen, NULL)) break;
										len -= 4*aslen;
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
									if (get_buf(&buf, 4*aslen, entry->aspath[entry->pathes]+aspathlen))
										break;
									aspathlen += aslen;
									len -= 4*aslen;
								}
								if (get_buf(&buf, len, NULL)) break;
								entry->aspath[entry->pathes][aspathlen] = 0;
								entry->pathes++;
								break;
							default:get_buf(&buf, len, NULL); break;
						}
					}
				}
				return 0;
			default:error("Unsupported format: type %d, subtype %d", etype>>16, etype & 0xffff);
				return 1;
		}
		break;
	}
	return 0;
}

