CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra

.PHONY: all clean
all: replay movieinfo

replay movieinfo bfs: %: %.c nes.c nes.h state.h movie.h
	$(CC) $(CPPFLAGS) $(CFLAGS) nes.c $< $(LDFLAGS) $(LDLIBS) -o $@

clean:
	rm -f replay movieinfo bfs
