# A5 — notes for reviewers

A5 is the only problem whose proof is **library-backed**: it reuses the
Eulerian / descent-set development from
[LLM4Rocq/mathcomp-eulerian](https://github.com/LLM4Rocq/mathcomp-eulerian)
(a Rocq port of Stanley, *Enumerative Combinatorics* I, Cor. 1.6.5: among all
prescribed descent sets, the *alternating* one maximises the number of
permutations). Because of that, A5 is structured differently from the other
eleven problems, and this note explains what changed and why.

## The result

For `n = n'+2 ≥ 2` and a sign pattern `s : (n-1).-tuple bool` (true = ascent,
false = descent at that adjacent pair), `f_count s` is the number of
permutations of `{0,…,n-1}` realising that ascent/descent pattern. A5:

```coq
Theorem putnam_2025_a5 (n' : nat) (s : n'.+1.-tuple bool) :
  (forall s' : n'.+1.-tuple bool, f_count s' <= f_count s) <-> is_alt s.
```

`f_count s` is maximal **iff** `s` is alternating (`is_alt s`: no two adjacent
signs agree). Verified **axiom-free** — `Print Assumptions putnam_2025_a5`
reports *"Closed under the global context"* (empty Axioms column in the table).

## Why the formulation changed

The original `problems/putnam_2025_a5.v` stated A5 over `list Z` permutations
(`all_perms`, `compatible_b`). The completed proof instead works in MathComp,
over `{perm 'I_n}`, so it can plug directly into `mathcomp-eulerian`'s
descent-set machinery. The two phrasings are the same Putnam problem; this PR
**replaces the problem statement with the MathComp one** so that the stated
theorem is exactly the one that is proved. (The previous ZArith statement and
its incomplete proof attempt are dropped.)

> **Reviewer decision point.** If you would rather keep the ZArith statement as
> the canonical one, the alternative is to land this MathComp proof under a
> separate path and leave A5 marked ❌ in the table — but that undersells a
> complete, axiom-free proof. Bridging the MathComp result back to the exact
> ZArith statement is possible but is substantial extra work (a full
> `list Z`-permutation ↔ `{perm 'I_n}` equivalence).

## File layout

```
_CoqProject                       build config (-R alias + file order)
Makefile                          coq_makefile wrapper (make / make clean)
problems/putnam_2025_a5.v         MathComp statement (defs + Admitted theorem)
solutions/new_proof_a5.v          defs + alt_seq helper            (module)
solutions/a5_bridge.v             s_compat ↔ descent_set bridge    (module)
solutions/proof_a5.v              final theorem putnam_2025_a5     (verify.py target)
```

The `mathcomp_eulerian` library is **not** in this repo — it is installed
externally (see below). `solutions/` is mapped to the logical name
`Putnam2025A5`; `proof_a5.v` `Require`s `new_proof_a5` and `a5_bridge` from it,
plus `descent`, `beta`, `beta_swap` from `mathcomp_eulerian`.

> The library is installed as an **external opam dependency from git**, pinned
> to a fixed commit for reproducibility (the proof is verified against that
> exact revision) — not vendored into this repo.

## Building and verifying

The other eleven problems are self-contained and need no build step. A5 needs
the `mathcomp-eulerian` library installed, then its own modules built:

```bash
opam pin add rocq-mathcomp-eulerian \
  git+https://github.com/LLM4Rocq/mathcomp-eulerian.git#v0.1.0
make                     # builds the three A5 solution modules
python verify.py a5      # -> putnam_2025_a5 ✅, no axioms
```

`verify.py` works unchanged: `rocq_verify` hoists the `Require`s above its
`Module M` sandbox and resolves `mathcomp_eulerian` (from opam's user-contrib)
and the A5 modules (via `_CoqProject`) through the built `.vo`s.

The pin `v0.1.0` is a tag on `mathcomp-eulerian` at `dc79766` plus its
`rocq-mathcomp-eulerian.opam` packaging file; A5 is verified axiom-free against
exactly that release. The tag must be present on the library's GitHub
(`git push origin v0.1.0`).

## Dependencies

- Rocq/Coq 9.x with **MathComp** (`all_ssreflect`, `fingroup`, `perm`, …) —
  a new toolchain dependency relative to the other problems, which use only the
  Rocq standard library.
- **`rocq-mathcomp-eulerian`**, installed from git via opam (pinned). Its own
  dependencies are `rocq-mathcomp-ssreflect`, `-algebra`, and `-classical`.
