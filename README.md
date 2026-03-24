# Putnam 2025 — Rocq Formalization

Formal statements and proofs of the 2025 Putnam Competition problems in Rocq.

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

**10/12 verified**

We used Claude code with Opus 4.6 (High effort) and the [Rocq-MCP](https://github.com/LLM4Rocq/rocq-mcp).
More details about our experiment in [Putnam 2025 Problems in Rocq using Opus 4.6 and Rocq-MCP](https://arxiv.org/abs/2603.20405)

## Structure

```
problems/       Formal problem statements (with Admitted)
solutions/      Proofs
verify.py       Verification script
```

## Verification

To relaunch the verification step (check that the solutions match the original problems, check axioms etc.):

### Setup

- **Rocq / Coq** — `coqc` on your `PATH`
- **pet** (from [coq-lsp](https://github.com/ejgallego/coq-lsp))
- **Python 3.11+**

```bash
pip install -r requirements.txt
```

### Check the solutions
```bash
python verify.py
```
