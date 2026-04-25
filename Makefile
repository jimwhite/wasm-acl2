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
#   make wasm-vm1    # build the hand-written ATC VM binary
#   make codegen-demo  # cert + build the generated dispatch-loop binary
#   make codegen-run   # run it against the gcd/fact/is_prime/collatz oracle
#   make clean       # remove .cert and related build artifacts

ACL2 ?= /opt/acl2/bin/acl2
CERT ?= /home/acl2/books/build/cert.pl
JOBS ?= 4

PROOF_BOOKS := $(patsubst %.lisp,%,$(wildcard proofs/proof-*.lisp))
TEST_BOOKS  := $(patsubst %.lisp,%,$(wildcard tests/test-*.lisp))

WAT_SOURCES := $(wildcard tests/oracle/*.wat)
WASM_BINARIES := $(patsubst %.wat,%.wasm,$(WAT_SOURCES))

.PHONY: all top proofs tests clean wasm wasm-vm1 oracle-verified-m1 \
        codegen-demo codegen-run codegen-oracle codegen-vm2 codegen-dump-cfg \
        codegen-run-vm2

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

# ---- ATC-generated dispatch-loop demo (18-opcode codegen) -----------------
#
# codegen/integration-demo.cert produces codegen/run.c + run.h via the
# spec-driven template family in codegen/{loop,templates}.lisp.
# run_main.c is the CLI wrapper that mirrors atc/main.c's arg convention.
# See codegen/README.md for the full pipeline description.

CODEGEN_FIXTURES := \
    tests/oracle/gcd.wasm:gcd:48:18:6                    \
    tests/oracle/gcd.wasm:gcd:1000000:999983:1           \
    tests/oracle/factorial.wasm:fac:5:0:120              \
    tests/oracle/factorial.wasm:fac:10:0:3628800         \
    tests/oracle/is_prime.wasm:is_prime:7:0:1            \
    tests/oracle/is_prime.wasm:is_prime:9:0:0            \
    tests/oracle/collatz.wasm:collatz:27:0:111           \
    tests/oracle/collatz.wasm:collatz:97:0:118

codegen/integration-demo.cert codegen/run.c codegen/run.h: \
        codegen/integration-demo.lisp codegen/loop.lisp \
        codegen/templates.lisp codegen/state-model.lisp \
        codegen/wasm-vm1.lisp codegen/cert.acl2
	$(CERT) --acl2 $(ACL2) -j $(JOBS) codegen/integration-demo

codegen/wasm-vm2.cert codegen/wasm-vm2.c codegen/wasm-vm2.h: \
        codegen/wasm-vm2.lisp codegen/cert.acl2
	$(CERT) --acl2 $(ACL2) -j $(JOBS) codegen/wasm-vm2

codegen-vm2: codegen/wasm-vm2.cert

codegen/dump_cfg: codegen/wasm-vm2.c codegen/wasm-vm2.h codegen/dump_cfg_main.c
	$(CC) $(CFLAGS) -Icodegen codegen/wasm-vm2.c codegen/dump_cfg_main.c -o $@

codegen-dump-cfg: codegen/dump_cfg $(WASM_BINARIES)
	@for w in tests/oracle/gcd.wasm tests/oracle/factorial.wasm \
	          tests/oracle/is_prime.wasm tests/oracle/collatz.wasm; do \
	  echo "=== $$w ==="; ./codegen/dump_cfg $$w; \
	done

codegen/run_demo: codegen/run.c codegen/run.h codegen/run_main.c
	$(CC) $(CFLAGS) -Icodegen codegen/run.c codegen/run_main.c -o $@

codegen-demo: codegen/run_demo

codegen-run: codegen/run_demo $(WASM_BINARIES)
	@set -e; for f in $(CODEGEN_FIXTURES); do \
	  wasm=$$(echo $$f | cut -d: -f1); \
	  name=$$(echo $$f | cut -d: -f2); \
	  a=$$(echo $$f | cut -d: -f3); \
	  b=$$(echo $$f | cut -d: -f4); \
	  exp=$$(echo $$f | cut -d: -f5); \
	  got=$$(./codegen/run_demo $$wasm $$name $$a $$b); \
	  printf "%-9s %-16s a=%-7s b=%-4s got=%-8s exp=%-8s " \
	         "$$name" "`basename $$wasm`" "$$a" "$$b" "$$got" "$$exp"; \
	  if [ "$$got" = "$$exp" ]; then echo OK; else echo FAIL; exit 1; fi; \
	done

codegen-oracle: codegen-run

# ---- wasm-vm2 runner ------------------------------------------------------
#
# run_vm2 links against codegen/wasm-vm2.c and dispatches into invoke_v2
# (block-structured, default) or invoke (flat, kept for reference) based on
# a `--vm v1|v2` flag.

codegen/run_vm2: codegen/wasm-vm2.c codegen/wasm-vm2.h codegen/run_vm2_main.c
	$(CC) $(CFLAGS) -Icodegen codegen/wasm-vm2.c codegen/run_vm2_main.c -o $@

codegen-run-vm2: codegen/run_vm2 $(WASM_BINARIES)
	@set -e; \
	for vm in v2 v1; do \
	  echo "=== --vm $$vm ==="; \
	  for f in $(CODEGEN_FIXTURES); do \
	    wasm=$$(echo $$f | cut -d: -f1); \
	    name=$$(echo $$f | cut -d: -f2); \
	    a=$$(echo $$f | cut -d: -f3); \
	    b=$$(echo $$f | cut -d: -f4); \
	    exp=$$(echo $$f | cut -d: -f5); \
	    got=$$(./codegen/run_vm2 --vm $$vm $$wasm $$name $$a $$b); \
	    printf "%-9s %-16s a=%-7s b=%-4s got=%-8s exp=%-8s " \
	           "$$name" "`basename $$wasm`" "$$a" "$$b" "$$got" "$$exp"; \
	    if [ "$$got" = "$$exp" ]; then echo OK; else echo FAIL; fi; \
	  done; \
	done

clean:
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.port' \
	       -o -name '*.lx64fsl' -o -name '*.fasl' -o -name '*.pcert0' \
	       -o -name '*.pcert1' -o -name 'Makefile-tmp' \
	       -o -name '*.cert.time' -o -name '*.out' \
	       -o -name '*.lx86cl64fsl' -o -name '*.dx64fsl' \) -delete
	rm -f atc/wasm-vm1 atc/wasm-vm1.c atc/wasm-vm1.h
	rm -f codegen/run_demo codegen/run.c codegen/run.h \
	      codegen/wasm-vm1.c codegen/wasm-vm1.h \
	      codegen/wasm-vm2.c codegen/wasm-vm2.h \
	      codegen/dump_cfg \
	      codegen/run_vm2 \
	      codegen/demo.c codegen/demo.h \
	      codegen/loop-demo.c codegen/loop-demo.h \
	      codegen/run_sanity
