
#define MAXPATHLEN	256
#define MAXPATHES	255

#define MAJVER		0
#define MINVER		3

struct dump_entry {
	uint32_t prefix;
	int preflen;
	int pathes;
	int withdraw;
	uint32_t origas[MAXPATHES];
	uint32_t peerip[MAXPATHES];
	uint32_t aspath[MAXPATHES][MAXPATHLEN];
	time_t create_time[MAXPATHES];
};

int open_dump(FILE *f);
int read_dump(FILE *f, struct dump_entry *entry);
void debug(int level, char *format, ...);
void warning(char *format, ...);
void error(char *format, ...);

#define BGPDUMP_TYPE_ASRANK_PEERLIST	((71ul<<16) | 1)
#define BGPDUMP_TYPE_ASRANK_PREF	((71ul<<16) | 2)
