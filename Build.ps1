$ErrorActionPreference = "Stop"

lake build 2>&1 | Tee-Object -FilePath build.log
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

lake env lean AxiomAudit.lean 2>&1 | Tee-Object -FilePath axiom_audit.log
exit $LASTEXITCODE
