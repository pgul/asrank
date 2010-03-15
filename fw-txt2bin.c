#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <stdarg.h>
#include <ctype.h>
#include <time.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

/*
*  4.0.0.0          205.238.48.3                         0 2914 1 i
*                   144.228.240.93                       0 1239 1 i
*                   134.24.127.3                         0 1740 1 i
*                   194.68.130.254                       0 5459 5413 1 i
*                   158.43.133.48                        0 1849 702 701 1 i
*                   193.0.0.242                          0 3333 286 1 i
*                   204.212.44.128                       0 234 266 237 3561 1 i
*                   202.232.1.8                          0 2497 2914 1 i
*                   204.70.4.89                          0 3561 1 i
*                   131.103.20.49                        0 1225 2548 1 i

*  3.0.0.0          134.55.24.6                            0 293 701 80 ?
*                   194.68.130.254                         0 5459 5413 701 80 ?
*                   206.157.77.11          155             0 1673 701 80 ?
*                   202.232.1.8                            0 2497 701 80 ?
*                   144.228.240.93           4             0 1239 701 80 ?
*                   204.70.4.89                            0 3561 701 80 ?
*                   193.0.0.56                             0 3333 286 701 80 ?
*                   158.43.206.96                          0 1849 702 701 80 ?
*                   134.24.127.3                           0 1740 701 80 ?
*>                  129.250.0.1              2             0 2914 701 80 ?
*                   129.250.0.3              5             0 2914 701 80 ?
*                   204.212.44.129                         0 234 2914 701 80 ?
*                   204.42.253.253                         0 267 234 2914 701 80 ?
*  4.0.0.0          134.55.24.6                            0 293 1 i
*/

static char buf[1500];
static int ibuf;

static void debug(char *format, ...)
{
  va_list ap;
  static char debug_buf[1024];

  va_start(ap, format);
  vsnprintf(debug_buf, sizeof(debug_buf)-2, format, ap);
  va_end(ap);
  if (strchr(debug_buf, '\n') == NULL)
    strcat(debug_buf, "\n");
  //fputs(debug_buf, stderr);
}

static void putbuf(void *data, int size)
{
  if (ibuf + size > sizeof(buf))
    debug("Buf too small, truncated!");
  else {
    memcpy(buf+ibuf, data, size);
    ibuf+=size;
  }
}

static void putbuf1(unsigned char i)
{
  putbuf(&i, 1);
}

static void putbuf2(uint16_t i)
{
  putbuf(&i, 2);
}

static void putbuf4(uint32_t i)
{
  putbuf(&i, 4);
}

static void putbufas(unsigned int i, int asn32)
{
  if (asn32)
    putbuf4(htonl(i));
  else
    putbuf2(htons(i));
}

int main(int argc, char *argv[])
{
  int line;
  char str[1024];
  char *pip, *nexthop, *aspath, *p, *p1, c;
  in_addr_t ip, peer;
  unsigned int asn[255];
  int pathlen, asn32, i, attrlen, attrhdrlen;
  unsigned char preflen;
  FILE *f;
  uint32_t seconddword, seconddword4;

  if (argv[1]) {
    f = fopen(argv[1], "r");
    if (f == 0) {
      fprintf(stderr, "Cannot open %s: %s\n", argv[1], strerror(errno));
      return 1;
    }
  } else
    f = stdin;
  seconddword  = htonl(0xc0001); /* BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP */
  seconddword4 = htonl(0xc0003); /* BGPDUMP_TYPE_MRTD_TABLE_DUMP_AFI_IP_32BIT_AS */
  line = 0;
  ip = INADDR_NONE;
  preflen = 0;
  while (fgets(str, sizeof(str), f)) {
    line++;
    /* parse line */
    if (strlen(str) < 61) {
cannotparse:
      debug("Cannot parse line number %d: %s", line, str);
      continue;
    }
    pip=str+3;
    p=str+19;
    while (*p && isdigit(*p)) p++;
    if (!isspace(*p) || !isdigit(p[1])) goto cannotparse;
    nexthop = p+1;
    /* p+1 - nexthop */
    if (strlen(nexthop) < 30) goto cannotparse;
    p = nexthop+30;
    if (!isspace(*p) || !isspace(p[1])) goto cannotparse;
    p += 2;
    while (isspace(*p)) p++;
    if (!isdigit(*p)) goto cannotparse;
    while (isdigit(*p)) p++;
    if (!isspace(*p)) goto cannotparse;
    aspath = p+1;
    for (p=pip; *p && !isspace(*p); p++);
    c = *p;
    *p='\0';
    if (*pip) {
      if ((p1=strchr(pip, '/')) != NULL) {
        *p1 = '\0';
        ip = inet_addr(pip);
        preflen = (unsigned char)atoi(p1+1);
        *p1 = '/';
      } else {
        ip = inet_addr(pip);
        i = *(unsigned char *)&ip;
        if (i==0)
          preflen = 0;
        else if (i<127)
          preflen = 8;
        else if (i<192)
          preflen = 16;
        else
          preflen = 24;
      }
    } else if (ip == INADDR_NONE) {
      debug("Unknown prefix in line %u: %s", line, str);
      continue;
    }
    *p = c;
    if (ip == INADDR_NONE)
      goto cannotparse;
    for (p=nexthop; *p && !isspace(*p); p++);
    c = *p;
    *p='\0';
    peer = inet_addr(nexthop);
    *p = c;
    if (peer == INADDR_NONE)
      goto cannotparse;
    asn32 = 0;
    asn[0] = 0;
    for (p=aspath+strlen(aspath)-1; p>aspath && isspace(*p); *p--='\0');
    if (*aspath == '\0') {
badaspath:
      debug("Bad aspath in line %d: %s", line, aspath);
      continue;
    } else if (aspath[1] == '\0') {
      pathlen = 0;
    } else {
      p--;
      if (!isspace(*p)) goto badaspath;
      *p--='\0';
      /* $aspath =~ s/\{(\d+)(,\d+)*\}/$1/g; */
      while ((p = strchr(aspath, '{'))) {
        p1 = strchr(p, '}');
        if (!p1) goto badaspath;
        while (isdigit(p[1])) {
          p[0] = p[1];
          p++;
        }
        if (isdigit(p1[1]))
          *p++ = ' ';
        strcpy(p, p1+1);
      }
      for (p=aspath; *p; p++)
        if (!isdigit(*p) && *p!=' ' && *p!='.')
          goto badaspath;
      for (pathlen=0, p=aspath; *p && isdigit(*p);) {
        if (pathlen >= sizeof(asn)/sizeof(asn[0])) {
          debug("Too long aspath truncated in line %u: %s", line, aspath);
          break;
        }
        asn[pathlen] = (unsigned int)strtoul(p, &p1, 10);
        if (asn[pathlen] == 0) goto badaspath;
        if (*p1 == '.') {
          asn[pathlen] = (asn[pathlen] << 16) + (unsigned int)strtoul(p1+1, &p1, 10);
          asn32 = 1;
        } else if (asn[pathlen] > 0x10000ul)
          asn32 = 1;
        pathlen++;
        if (*p1 == '\0') break;
        p = p1+1;
      }
    }
    putbuf4(htonl(time(NULL)));
    putbuf4(asn32 ? seconddword4 : seconddword);
    attrlen = 1+1+pathlen*(asn32 ? 4 : 2);
    attrhdrlen = 1+1+(attrlen<256 ? 1 : 2);
    putbuf4(htonl(4+4+1+1+4+4+(asn32 ? 4 : 2)+2+attrhdrlen+attrlen));
    putbuf4(0); /* view, seq */
    putbuf(&ip, 4);
    putbuf1(preflen);
    putbuf1(0); /* status */
    putbuf4(0); /* uptime */
    putbuf(&peer, 4);
    putbufas(asn[0], asn32);
    putbuf2(htons(attrlen+attrhdrlen));
    putbuf1(attrlen<256 ? 0 : 0x10); /* flag, 0x10 - BGP_ATTR_FLAG_EXTLEN */
    putbuf1(2); /* type=BGP_ATTR_AS_PATH */
    if (attrlen<256)
      putbuf1(attrlen);
    else
      putbuf2(htons(attrlen));
    putbuf1(2); /* type=AS_SEQUENCE */
    putbuf1(pathlen);
    for (i=0; i<pathlen; i++)
      putbufas(asn[i], asn32);
    fwrite(buf, ibuf, 1, stdout);
    ibuf=0;
  }
  if (f != stdin) fclose(f);
  fflush(stdout);
  return 0;
}

