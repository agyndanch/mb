#
# A simple Makefile to build the shell
#
TREE_SITTER_DIR=$(realpath ../tree-sitter)
TREE_SITTER_BASH_DIR=$(realpath ../tree-sitter-bash)

CC=clang
LDFLAGS=-L../tommyds
#LDFLAGS=-L${TREE_SITTER_DIR}
LDLIBS=-lreadline $(TREE_SITTER_DIR)/libtree-sitter.a -ltommy
# The use of -Wall, -Werror, and -Wmissing-prototypes is mandatory 
# for this assignment
BASE_CFLAGS=-Wall -Werror -gdwarf-4 -O0 -fsanitize=undefined -I${TREE_SITTER_DIR}/lib/include -I${TREE_SITTER_BASH_DIR}/src -DPLAIN -I..
CFLAGS=-Wmissing-prototypes $(BASE_CFLAGS)
#CFLAGS=-Wall -Werror -g -O2 -fsanitize=undefined -I${TREE_SITTER_DIR}/lib/include

TREE_SITTER_OBJECTS=parser.o scanner.o
OBJECTS=signal_support.o list.o utils.o
HEADERS=$(patsubst %.o,%.h,$(OBJECTS))

default: minibash

$(OBJECTS) minibash.o: $(HEADERS)

scanner.o parser.o: CFLAGS=$(BASE_CFLAGS)

# build the shell
minibash: $(OBJECTS) $(TREE_SITTER_OBJECTS) minibash.o $(HEADERS)
	$(CC) $(CFLAGS) -o $@ $(LDFLAGS) minibash.o $(OBJECTS) $(TREE_SITTER_OBJECTS) $(LDLIBS)

clean:
	rm -f $(OBJECTS) $(TREE_SITTER_OBJECTS) minibash minibash.o \
		core.*

