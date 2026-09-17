# Repository instructions

The canonical mathematical source is `xz_mathieu_su2_counterexamples.tex`, corresponding to arXiv v1. Compile with `latexmk -pdf xz_mathieu_su2_counterexamples.tex` and check for undefined references and citations if the manuscript changes.

Do not silently change theorem statements, hypotheses, conclusions, notation, or parameter ranges. Document genuine mathematical discrepancies explicitly. Distinguish manuscript mathematics, Lean formalization, and editorial/repository changes. Preserve the canonical manuscript and PDF unless a legitimate correction is authorized.

All Lean proof work must be free of placeholders, project axioms, unsafe proof escapes, native_decide, implemented_by, and extern. Use mathlib and kernel proofs. Keep a faithful exhaustive ledger in FORMALIZATION_STATUS.md. On resumption reread this file, the ledger, and the repository state. A partial statement is never PROVED coverage of a full statement.

Run `python3 scripts/verify_xz_mathieu_counterexamples.py` for the independent finite exact checks. Lean validation commands are `python3 scripts/fetch_mathlib_cache.py`, `python3 scripts/audit_source.py`, `lake build`, and `lake env lean scripts/audit_lean.lean`. Perform a clean project rebuild before release.

Use a feature branch, stable checkpoint commits, a PR, passing CI, and squash merge. The compiled PDF may be tracked; LaTeX auxiliaries, Lean build products, and caches may not. Keep auxiliary tooling under scripts/. Maintain README coverage claims consistent with the ledger. Do not describe full coverage until every targeted proof-bearing obligation is proved.
