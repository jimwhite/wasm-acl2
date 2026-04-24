# Certify all books in this directory with cert.pl.
#
#   ACL2  - path to the ACL2 image (default: $ACL2 env var, or /opt/acl2/bin/acl2)
#   CERT  - path to books/build/cert.pl (default: /home/acl2/books/build/cert.pl)
#   JOBS  - parallelism for cert.pl -j (default: 4)
#
# Usage:
#   make             # certify top + every proof + every test
#   make top         # certify just the library (execution + validation)
#   make proofs      # certify every proofs/*.lisp book
#   make tests       # certify every tests/*.lisp book
#   make clean       # remove .cert and related build artifacts

ACL2 ?= /opt/acl2/bin/acl2
CERT ?= /home/acl2/books/build/cert.pl
JOBS ?= 4

PROOF_BOOKS := $(patsubst %.lisp,%,$(wildcard proofs/proof-*.lisp))
TEST_BOOKS  := $(patsubst %.lisp,%,$(wildcard tests/test-*.lisp))

WAT_SOURCES := $(wildcard tests/oracle/*.wat)
WASM_BINARIES := $(patsubst %.wat,%.wasm,$(WAT_SOURCES))

.PHONY: all top proofs tests clean wasm wasm-vm1 oracle-verified-m1

# Single cert.pl invocation so its internal dependency tracker avoids races
# on shared prerequisites like execution.cert.
all:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) top $(PROOF_BOOKS) $(TEST_BOOKS)

top:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) top

proofs:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(PROOF_BOOKS)

tests:
	$(CERT) --acl2 $(ACL2) -j $(JOBS) $(TEST_BOOKS)

# Compile .wat oracle programs to .wasm with the local JS-based wat2wasm.
# Requires `npm install` in tools/ (run once: `make tools/node_modules`).
wasm: $(WASM_BINARIES)

tests/oracle/%.wasm: tests/oracle/%.wat tools/wat2wasm.mjs | tools/node_modules
	node tools/wat2wasm.mjs $< -o $@

tools/node_modules:
	cd tools && npm install

# ---- ATC-generated WASM VM (M1 PoC) ---------------------------------------
#
# atc/wasm-vm1.cert produces atc/wasm-vm1.c + atc/wasm-vm1.h via the Kestrel
# ATC code generator.  main.c wraps them into a runnable binary.

CC      ?= cc
CFLAGS  ?= -O2 -std=c17 -Wall -Wextra -Wno-unused-parameter

atc/wasm-vm1.cert atc/wasm-vm1.c atc/wasm-vm1.h: atc/wasm-vm1.lisp atc/cert.acl2
	$(CERT) --acl2 $(ACL2) -j $(JOBS) atc/wasm-vm1

atc/wasm-vm1: atc/wasm-vm1.c atc/wasm-vm1.h atc/main.c
	$(CC) $(CFLAGS) -Iatc atc/wasm-vm1.c atc/main.c -o $@

wasm-vm1: atc/wasm-vm1

# Oracle check: run the VM on gcd.wasm and compare against V8 for a handful of
# (a,b) pairs.  The ACL2/ATC word "gcd" appears nowhere in our source — only
# in the runtime wasm file path and the export-name CLI argument.
ORACLE_CASES := 48:18 35:14 17:0 0:5 1:1
ORACLE_WASM  := tests/oracle/gcd.wasm
ORACLE_NAME  := gcd

oracle-verified-m1: atc/wasm-vm1 $(ORACLE_WASM)
	@set -e; \
	for pair in $(ORACLE_CASES); do \
	  a=$${pair%:*}; b=$${pair#*:}; \
	  ours=$$(./atc/wasm-vm1 $(ORACLE_WASM) $(ORACLE_NAME) $$a $$b); \
	  v8=$$(node tools/oracle-invoke.mjs $(ORACLE_WASM) $(ORACLE_NAME) $$a $$b); \
	  printf "%-7s a=%-4s b=%-4s ours=%-5s v8=%-5s " \
	         "$(ORACLE_NAME)" "$$a" "$$b" "$$ours" "$$v8"; \
	  if [ "$$ours" = "$$v8" ]; then echo OK; else echo FAIL; exit 1; fi; \
	done

clean:
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' \
	       -o -name '*.lx64fsl' -o -name '*.fasl' -o -name '*.pcert0' \
	       -o -name '*.pcert1' -o -name 'Makefile-tmp' \
	       -o -name '*.cert.time' -o -name '*.out' \
	       -o -name '*.lx86cl64fsl' -o -name '*.dx64fsl' \) -delete
	rm -f atc/wasm-vm1 atc/wasm-vm1.c atc/wasm-vm1.h
