# Tight Lower Bounds for Stochastic Nonconvex Strongly Concave Minimax Optimization

Lean formalization and supplementary proof sources. Start with
`ManuscriptPaperStatements.lean` for Theorem 4.1, Theorem 5.1 and Corollary 5.2.
See `FORMALIZATION_SCOPE.md` and `CHECKLIST_STATUS.md` for precise coverage,
assumptions and remaining manuscript-alignment checks.

## Repository layout

The contents of this distribution belong directly at the repository root:

```text
.github/workflows/verify.yml
scripts/check_axioms.py
lakefile.toml
lake-manifest.json
lean-toolchain
ManuscriptPaperStatements.lean
AxiomAudit.lean
... other Lean sources ...
```

Do not put another `NCSCPureStochasticLB` directory above these files inside the
repository. Include hidden files and directories, especially `.github` and
`.gitignore`. Upload/extract the ZIP contents, not the ZIP itself, for GitHub to
run the workflow. No pre-existing Git history, remote URL or author identity is
included. The repository can be named as desired.

## Local verification

Install [elan](https://github.com/leanprover/elan), and ensure `lake` is on PATH.
Lean 4.19.0 and Mathlib v4.19.0 are selected by the included toolchain and lockfile.
Internet access is required to download dependencies. CPU only; no GPU is needed.

Linux/macOS:

```bash
lake exe cache get
bash verify.sh
python3 scripts/check_axioms.py axiom_audit.log
```

Windows PowerShell:

```powershell
lake exe cache get
./Build.ps1
python scripts/check_axioms.py axiom_audit.log
```

Stop if any command fails. The scripts generate `build.log` and `axiom_audit.log`.
These outputs and dependency/build caches are ignored by Git.

## GitHub Actions

`.github/workflows/verify.yml` runs on pushes, pull requests and manual dispatch.
It installs elan, obtains the pinned toolchain and Mathlib cache, builds all
default targets, runs the complete axiom audit, and checks its allowed dependencies.
Build/audit logs are saved as workflow artifacts, including on failure when available.
All commands run at the repository root; no nested working-directory setting is needed.

No repository secrets are required. The workflow requests read-only repository
contents access. Its first hosted execution must still be checked in the Actions
tab; preparing this repository does not constitute a successful GitHub-hosted run.

## Proof preservation and trust

All 58 Lean files from the supplied supplementary archive are retained without
modification. Supporting and historical-numbered modules are part of the proof
distribution, not disposable drafts. Build configuration and dependency locks
are also preserved.

The sole nonstandard mathematical input is
`NCSCPureStochasticLB.PaperExact.importedLemmaB1Certificate`.
The audit allows this together with `propext`, `Classical.choice` and `Quot.sound`,
and rejects `sorryAx`. Compilation does not certify complete manuscript alignment;
the exact Lean hypotheses and scope documents remain authoritative.

The supplied archive did not contain a LICENSE file. No new license or author
identity has been selected as part of this packaging. Choose an appropriate
license deliberately if you wish to grant reuse rights.

If anonymous review is ongoing, a public repository or its commit/account metadata
may reveal identity even when the source files do not. Choose repository visibility
and author metadata accordingly before publishing.
