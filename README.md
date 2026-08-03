# Putnam 2025 — Rocq Formalization

Formal statements and proofs of the 2025 Putnam Competition problems in Rocq.

## First phase

Produced with Claude Code + Opus 4.6 (High effort) and the
[Rocq-MCP](https://github.com/LLM4Rocq/rocq-mcp); this is the result reported in
the [paper](#citation), as of commit `470f674` (2026-03-24):

| Problem | Status | Axioms      |
|---------|--------|-------------|
| putnam_2025_a1 | ✅ | Classical_Prop.classic |
| putnam_2025_a2 | ✅ | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep, Classical_Prop.classic |
| putnam_2025_a3 | ✅ |  |
| putnam_2025_a4 | ✅ | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep, Classical_Prop.classic |
| putnam_2025_a5 | ❌ |  |
| putnam_2025_a6 | ✅ |  |
| putnam_2025_b1 | ✅ | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep, Classical_Prop.classic |
| putnam_2025_b2 | ✅ | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep |
| putnam_2025_b3 | ✅ | Classical_Prop.classic |
| putnam_2025_b4 | ✅ |  |
| putnam_2025_b5 | ✅ |  |
| putnam_2025_b6 | ❌ |  |

**10/12 verified.**

## Second phase

A later phase (Claude Code + Opus 4.8) completed the two remaining problems,
bringing the repository to **12/12 verified**:

| Problem | Status | Axioms |
|---------|--------|--------|
| putnam_2025_a5 | ✅ | _(none — axiom-free)_ |
| putnam_2025_b6 | ✅ | ClassicalDedekindReals.sig_not_dec, ClassicalDedekindReals.sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep, Classical_Prop.classic |

A5 is proved axiom-free via the
[mathcomp-eulerian](https://github.com/LLM4Rocq/mathcomp-eulerian) library;
B6 via a direct `r = 1/4` argument.

## Structure

```
problems/       Formal problem statements (with Admitted)
solutions/      Proofs
verify.py       Verification script
```

A5 is library-backed: it reuses [LLM4Rocq/mathcomp-eulerian](https://github.com/LLM4Rocq/mathcomp-eulerian)
— installed from git via opam (see Setup) — and needs MathComp; the header of
[solutions/proof_a5.v](solutions/proof_a5.v) explains the reduction. All other
problems are self-contained and use only the Rocq standard library.

## Verification

To relaunch the verification step (check that the solutions match the original problems, check axioms etc.):

### Setup

Everything the proofs need fits in one dedicated opam switch. Using a fresh
switch keeps these versions from colliding with the rest of your setup — in
particular, A5 pulls in MathComp, which the other eleven problems do not use.

```bash
opam switch create putnam25 ocaml-base-compiler.5.2.1 --no-switch
opam repo add rocq-released https://rocq-prover.org/opam/released \
  --switch=putnam25 --rank=1

# register the pin without installing, so the solver sees every constraint at once
opam pin add --switch=putnam25 -n rocq-mathcomp-eulerian \
  git+https://github.com/LLM4Rocq/mathcomp-eulerian.git#v0.1.0

opam install --switch=putnam25 \
  rocq-core.9.1.1 rocq-stdlib.9.0.0 \
  rocq-mathcomp-ssreflect.2.5.0 rocq-mathcomp-algebra.2.5.0 \
  coq-coquelicot.3.4.4 coq-lsp.0.2.5+9.1 \
  rocq-mathcomp-eulerian

opam switch putnam25 && eval $(opam env)   # activate it
```

`coq-lsp` is in there not as an editor tool but because it ships the `pet`
binary that `verify.py` drives.

The versions are not incidental. `coq-coquelicot` (needed by B2) requires
`coq-mathcomp-ssreflect >= 1.6` with no upper bound, but does **not** build
against MathComp 2.6.0 — `theories/Rcomplements.v` fails with *"Goal is not an
equation"*. Holding MathComp at 2.5.0 is what makes Coquelicot and A5's
`mathcomp-eulerian` coexist, and 2.5.0 is also the version A5 was verified
against.

And the Python side (3.11+):

```bash
pip install -r requirements.txt
```

### Check the solutions
```bash
python verify.py        # all 12
python verify.py a5 b6  # a subset
```

## Citation

The first-phase experiment is described in:

> Guillaume Baudart, Marc Lelarge, Tristan Stérin, Jules Viennot.
> *Putnam 2025 Problems in Rocq using Opus 4.6 and Rocq-MCP.*
> arXiv:2603.20405, 2026.

```bibtex
@misc{baudart2026putnam,
  title         = {Putnam 2025 Problems in {Rocq} using {Opus} 4.6 and {Rocq-MCP}},
  author        = {Baudart, Guillaume and Lelarge, Marc and St{\'e}rin, Tristan and Viennot, Jules},
  year          = {2026},
  eprint        = {2603.20405},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LG},
  url           = {https://arxiv.org/abs/2603.20405}
}
```
