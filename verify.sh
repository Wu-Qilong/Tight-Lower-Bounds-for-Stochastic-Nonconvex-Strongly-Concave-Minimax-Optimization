#!/usr/bin/env bash
set -euo pipefail

lake build 2>&1 | tee build.log
lake env lean AxiomAudit.lean 2>&1 | tee axiom_audit.log
