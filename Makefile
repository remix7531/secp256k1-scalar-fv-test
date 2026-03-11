CC      ?= gcc
AR      ?= ar
NPROC   := $(shell nproc)

ifeq ($(CC),ccomp)
  CFLAGS = -std=c99 -Wall -O2 -Isrc -Wp,-w
else
  CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O2 -Isrc
endif

LIB      = libsecp256k1_scalar.a
LIB_SRCS = src/scalar_4x64.c
LIB_OBJS = $(LIB_SRCS:.c=.o)

TST_SRCS = test/main.c
TST_OBJS = $(TST_SRCS:.c=.o)
TARGET   = out

# Top-level targets

all: lib test clight proof

lib: $(LIB)

test: $(TARGET)
	./$(TARGET)

clight: proof/Source_scalar_4x64.v

proof: Makefile.coq proof/Source_scalar_4x64.v
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq
	@printf '\033[1;34m✓ All Verifications Succeeded\033[0m\n'

# Build rules

src/%.o: src/%.c src/scalar_4x64.h
	$(CC) $(CFLAGS) -c $< -o $@

test/%.o: test/%.c src/scalar_4x64.h
	$(CC) $(CFLAGS) -c $< -o $@

$(LIB): $(LIB_OBJS)
	$(AR) rcs $@ $^

$(TARGET): $(TST_OBJS) $(LIB)
	$(CC) $(CFLAGS) -o $@ $(TST_OBJS) $(LIB)

proof/Source_scalar_4x64.v: src/scalar_4x64.c src/scalar_4x64.h
	clightgen -normalize -Isrc -Wp,-w -o $@ $<

Makefile.coq: _RocqProject
	@rocq makefile -f _RocqProject -o Makefile.coq

# Cleanup

clean:
	@if [ -e Makefile.coq ]; then $(MAKE) --no-print-directory -f Makefile.coq cleanall 2>/dev/null; fi
	@rm -f $(LIB_OBJS) $(TST_OBJS) $(LIB) $(TARGET)
	@rm -f Makefile.coq Makefile.coq.conf proof/Source_scalar_4x64.v

.PHONY: all lib test clight proof clean
