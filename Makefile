
prefix=/usr/local
CC=gcc
COPT=-Wall -funsigned-char -fno-strict-aliasing -pipe -I/usr/local/include -g -DSAVE_PREFIX=1
LDOPT=-g

SRCS=asrank.c bgpdump.c
OBJS=${SRCS:.c=.o}

.c.o:
	@echo Compiling $*.c...
	@$(CC) -c $(COPT) -o $*.o $*.c

all:    asrank

asrank: $(OBJS)
	@echo Linking $@...
	@$(CC) $(LDOPT) -o $@ $(OBJS) -L/usr/local/lib

asrank.o:	asrank.c asrank.h Makefile
bgpdump.o:	bgpdump.c asrank.h Makefile

clean:
	rm -f *.o
