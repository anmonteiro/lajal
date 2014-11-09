CC = cc
CFLAGS = -std=c99 -Wall
LFLAGS = 
DEBUGFLAGS = -DDEBUG -g
FILES = repl
PLATFORM = $(shell uname)

ifeq ($(findstring Linux,$(PLATFORM)),Linux)
	LFLAGS += -ledit -lm
	#FILES += prompt_unix
endif

ifeq ($(findstring Darwin,$(PLATFORM)),Darwin)
	LFLAGS += -ledit -lm
	#FILES += prompt_unix
endif

ifeq ($(findstring MINGW,$(PLATFORM)),MINGW)
	#FILES += prompt_windows
endif

all: $(FILES)

debug: CC += $(DEBUGFLAGS)
debug: all

%: %.c mpc.c
	$(CC) $(CFLAGS) $^ $(LFLAGS) -o $@

clean:
	rm -rf *.o repl