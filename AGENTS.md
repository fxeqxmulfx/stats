# Project instructions

Write source comments, documentation, notebooks, and commit messages in English.

## Lean declaration search

Use `dt` (discrtree) as the primary tool for finding Lean declarations by name,
statement shape, constants, or text. Check `dt status`, use `dt find` to locate
candidates, and inspect their exact types and required imports with `dt show`.
The project configuration is in `discrtree.toml`. If the index is missing or
stale, build the relevant modules and use `dt dump`, `dt index`, or `dt refresh`
as appropriate. Text-only search results are not elaborated declarations. If
`dt` cannot be made usable, explain the concrete limitation before falling back
to other declaration-search tools.

## Comparison with the papers

Before every commit that implements or describes a paper's mathematical claim,
reread the corresponding statement and definitions in the original paper under
`papers/`. Check parameters, hypotheses, support, integrability, normalization,
and the conclusion against the Lean statement. In particular, distinguish an
actual probabilistic quantity from a formula or proxy defined to have the
desired value. Record the source location and any remaining gaps in `REVIEW.md`.
If a source statement needs correction, document the corrected claim explicitly
instead of presenting it as a literal formalization of the printed statement.

## Module size and compilation

Split large Lean files into smaller modules organized around definitions and
related results. Prefer adding a focused module to extending an already large
file. Keep imports narrow and dependencies acyclic; expose the modules through
the appropriate umbrella file. This should reduce the amount of code that must
be recompiled after a change. When splitting an existing file, preserve its
public declarations and check the downstream imports and default build.

## Commits and verification

Make frequent, small commits for completed repairs. Commit each mathematical
change together with its relevant review updates and regression certificates.
Run the Lean checks appropriate to the change before committing. Do not add
unfinished proofs (`sorry` or `admit`) or extra axioms. After a group of repairs,
run the default `lake build` and the project's transitive axiom audit.
