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
[mathcomp-eulerian](https://github.com/LLM4Rocq/mathcomp-eulerian) library
(see [solutions/A5_NOTES.md](solutions/A5_NOTES.md)); B6 via a direct `r = 1/4`
argument.

## Structure

```
problems/       Formal problem statements (with Admitted)
solutions/      Proofs
_CoqProject     Build config for A5's solution modules
Makefile        coq_makefile wrapper (builds A5's .vo modules)
verify.py       Verification script
```

A5 is library-backed: it reuses [LLM4Rocq/mathcomp-eulerian](https://github.com/LLM4Rocq/mathcomp-eulerian)
— installed from git via opam (see Setup) — and needs MathComp; see
[solutions/A5_NOTES.md](solutions/A5_NOTES.md). All other problems are
self-contained and use only the Rocq standard library.

## Verification

To relaunch the verification step (check that the solutions match the original problems, check axioms etc.):

### Setup

- **Rocq / Coq** — `coqc` on your `PATH`
- **MathComp** — required for A5 only (`all_ssreflect`, `fingroup`, `perm`, …)
- **mathcomp-eulerian** — required for A5 only; installed from git via opam (below)
- **pet** (from [coq-lsp](https://github.com/ejgallego/coq-lsp))
- **Python 3.11+**

```bash
pip install -r requirements.txt
```

### Build A5's dependencies

A5 reuses the [`mathcomp-eulerian`](https://github.com/LLM4Rocq/mathcomp-eulerian)
library. Install it from git with opam (pinned for reproducibility), then build
A5's solution modules. The other eleven problems need no build step.

```bash
opam pin add rocq-mathcomp-eulerian \
  git+https://github.com/LLM4Rocq/mathcomp-eulerian.git#v0.1.0
make
```

### Check the solutions
```bash
python verify.py        # all 12 (run `make` first so a5 can resolve its library)
python verify.py a5     # just A5
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
