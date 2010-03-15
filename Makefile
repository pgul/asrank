
prefix=/usr/local
CC=gcc
COPT=-Wall -funsigned-char -fno-strict-aliasing -pipe -I/usr/local/include -O3
#LDOPT=-g

SRCS=asrank.c bgpdump.c
OBJS=${SRCS:.c=.o}

.c.o:
	@echo Compiling $*.c...
	@$(CC) -c $(COPT) -o $*.o $*.c

all:    asrank fw-txt2bin

asrank: $(OBJS)
	@echo Linking $@...
	@$(CC) $(LDOPT) -o $@ $(OBJS) -L/usr/local/lib

fw-txt2bin:	fw-txt2bin.o
	@echo Linking $@...
	@$(CC) $(LDOPT) -o $@ fw-txt2bin.o -L/usr/local/lib

asrank.o:	asrank.c asrank.h Makefile
bgpdump.o:	bgpdump.c asrank.h Makefile
fw-txt2bin.o:	fw-txt2bin.c Makefile

clean:
	rm -f *.o
