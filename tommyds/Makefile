# Compiler and flags
CC = gcc
CFLAGS = -O2 -g -Wall -I.
AR = ar

# Source files
SOURCES = tommyalloc.c tommyarray.c tommyarrayblk.c tommyarrayblkof.c tommyarrayof.c tommyhash.c tommyhashdyn.c tommyhashlin.c tommyhashtbl.c tommylist.c tommytrie.c tommytrieinp.c

# Object files
OBJECTS = $(SOURCES:.c=.o)

# Target library
TARGET = libtommy.a

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(AR) rcs $(TARGET) $(OBJECTS)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJECTS) $(TARGET)

.PHONY: all clean
