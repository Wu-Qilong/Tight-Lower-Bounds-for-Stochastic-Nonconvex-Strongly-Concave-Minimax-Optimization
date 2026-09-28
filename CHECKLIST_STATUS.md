# Alignment status

This file records the current claim boundary, not a development history.
All Lean source proofs and audit declarations from the verified input are retained.

## Implemented

- BV, AS and Moreau lower-bound entry points for the declared kernel algorithm
  class, with explicit parameter assumptions and both norm criteria.
- Standard-Borel kernel-to-random-tape representation, including finite histories
  and private memory, full execution-law preservation, and the uniform family,
  legality, risk and complexity connection. This fulfills checklist E3(a).
- Oracle-uniform causal repair with complete legal-trace preservation and
  pathwise support/budget guarantees for the declared finite-budget interface.
- Arbitrary-seed operational progress and primal risk bounds, including the
  exact 1-pR/T probability expression without an extra K factor.
- General lift, oracle transfer, population and Moreau constructions and the
  paper-facing statements indexed in `FORMALIZATION_SCOPE.md`.

## Remaining alignment checks

Successful compilation and the presence of these core results are not a
certificate that every manuscript statement has exactly the same hypotheses
and presentation. The following checks are not signed off by this distribution:

- Comprehensive function/oracle-class, regularity and well-posedness assumption
  parity, including which integrability conditions are derived rather than assumed.
- Final protocol, stopping and support presentation across all paper-facing APIs.
- Exact progress-lemma wrapper and its 3/4 consequence assembled from the same
  general proof, and the complete Proposition C.2 numerical presentation.
- Full equation/constant/parameter-range audit, including slack constants,
  actual condition numbers, endpoints and the Moreau proof-route correspondence.
- Final manuscript-wide numbering, quantifier and statement/assumption sign-off.

These qualifications are retained deliberately; document cleanup does not prove
additional mathematical claims. The authorized B.1 external input remains explicit.

## Manuscript version

The correspondence work used the manuscript with SHA256
`c8f81b8d4702d2b70ea1ecc8abee1f8cad9ba9492c29d8307a42fe3e497474b7`.
The manuscript itself is not modified or bundled. If its contents change, the
alignment assessment must be revisited.
