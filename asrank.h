
#define MAXPATHLEN	256
#define MAXPATHES	255

struct dump_entry {
	uint32_t prefix;
	int preflen;
	int pathes;
	uint32_t origas[MAXPATHES];
	uint32_t aspath[MAXPATHES][MAXPATHLEN];
};

int open_dump(FILE *f);
int read_dump(FILE *f, struct dump_entry *entry);
void debug(int level, char *format, ...);
void warning(char *format, ...);
void error(char *format, ...);

