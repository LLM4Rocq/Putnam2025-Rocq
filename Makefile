# Build the three A5 solution modules (new_proof_a5, a5_bridge, proof_a5).
#
# A5 is the only library-backed problem: it reuses LLM4Rocq/mathcomp-eulerian,
# which is installed separately as an opam dependency (see README "Setup").
# Its modules must be compiled to .vo before `python verify.py a5` can run.
# All other problems are self-contained and need no build step.
#
#   make            # build the A5 solution modules (produces .vo files)
#   make clean      # remove build artifacts
#
# Requires `coqc` / `coq_makefile` on PATH (Rocq/Coq 9.x), MathComp, and the
# rocq-mathcomp-eulerian opam package (see README).

.DEFAULT_GOAL := all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
