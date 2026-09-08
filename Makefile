CC ?= clang
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -pedantic
LDFLAGS ?= -framework Cocoa

.PHONY: all run clean

all: tetris

tetris: main.c
	$(CC) $(CFLAGS) main.c -o $@ $(LDFLAGS)

run: tetris
	./tetris

clean:
	rm -f tetris
