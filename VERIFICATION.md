# Verification provenance

All 58 Lean source files in the supplied supplementary archive match the
previously verified proof payload byte-for-byte. The original verification used
Lean 4.19.0 / Mathlib v4.19.0 and a fresh project build, reusing only third-party
dependency packages. It finished with exit code 0, 1052 axiom-audit records,
no errors or `sorryAx`, and 55 existing style/linter warnings.

The project-wide axiom union was `propext`, `Classical.choice`, `Quot.sound`,
and `NCSCPureStochasticLB.PaperExact.importedLemmaB1Certificate` only.

This GitHub packaging preserves all supplied Lean sources, build scripts,
toolchain, Lake configuration and dependency lockfile without changes. It adds
repository instructions, a GitHub Actions workflow and an axiom-log checker,
and replaces this provenance document. No proof is removed or renamed.

The new checker is tested against the recorded full audit and deliberately
invalid audit samples. Archive structure and source preservation are checked
locally. These packaging checks are not a new Lean compilation and are not a
GitHub-hosted workflow run. Check the first workflow run after pushing.

No historical server logs or dependency caches are committed. The CI workflow
produces fresh build/audit logs and uploads them as artifacts. No repository
access token or secret is needed. See README.md for local commands and layout.

Trust and manuscript-alignment limitations remain documented in
FORMALIZATION_SCOPE.md and CHECKLIST_STATUS.md. Verification of Lean statements
does not certify every informal manuscript convention or external comparison.
