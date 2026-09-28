# Formalization scope and theorem index

The main entry point is `ManuscriptPaperStatements.lean`. Declarations below
are in `NCSCPureStochasticLB.PaperExact`, with subnamespaces as indicated.

## Main endpoints

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 4.1, bounded variance, K=1 | `theorem41_paper` |
| Theorem 5.1, averaged smoothness, fixed finite K>=1 | `theorem51_paper` |
| Corollary 5.2, BV Moreau criterion | `corollary52_bv_paper` |
| Corollary 5.2, AS Moreau criterion | `corollary52_as_paper` |
| Proposition 3.1, C2 base function and actual gradient | `GeneralLift.proposition31_paper` |
| Independent variance and averaged-smoothness transfers | `GeneralLift.proposition31_variance_paper`, `GeneralLift.proposition31_AS_paper` |
| Proposition F.1, Hessian and primal smoothness | `GeneralLift.propositionF1_paper`, `GeneralLift.propositionF1_calibrated_paper` |
| Lemma F.2, both comparison inequalities | `lemmaF2_paper`, `lemmaF2_calibrated_paper` |

The four lower-bound endpoints use `KernelModel.complexity`. They accept the
explicit `ManuscriptBVProblem` / `ManuscriptASProblem` parameter conditions,
require jointly measurable oracles, and allow either expected norm or expected
squared norm. Their precise numerical constants and admissible ranges are in
the source definitions; asymptotic notation is not a substitute for those conditions.

## Supporting proof components

- Quadratic lift: smoothness, strong concavity, primal construction, initial
  gap and stationarity transfer; joint C1 correspondence and oracle transfer.
- Concrete BV/AS hard instances, calibration, integer dimension choices and
  lower-bound rates, supported by the explicit external base-chain certificate.
- Measured common-event zero-chain conditions and an arbitrary-seed operational
  progress bound of 1-pR/T, with no batch-size factor. The proof derives actual
  trace progress rather than assuming a run-progress witness, and integrates
  terminal-gradient barriers into norm and squared-norm risk bounds.
- Standard-Borel kernel sampling, randomized private-memory execution, and
  complete trace-law preservation under an independent random tape.
- An oracle-independent, dimension-indexed family representative preserving
  valid-instance trace laws and risks, with pathwise termination, support and
  call-budget guarantees. This connects kernel algorithms to the main bounds.
- General Moreau-envelope existence, differentiability and gradient results,
  plus the calibrated hard-instance and same-output comparison results.

Supporting modules and older internal declarations are all included. In particular,
the large foundational source and older numbered results are not omitted simply
because newer paper-facing statements are available.

## Algorithm and probability conventions

The kernel class includes standard-Borel private memory, random initialization,
history-dependent decisions and response-dependent randomized updates. Finite
Euclidean query/response histories are explicitly included. The compiler depends
on the algorithm, not the oracle instance or its hidden seed law.

Batches are selected before current responses; each batch uses a fresh shared
oracle seed that is not exposed to decision rules. Algorithm families may depend
on dimensions and fixed class parameters. The lower bounds allow almost-surely
legal kernel executions; their guarded representatives satisfy support and budget
constraints on every path while preserving the law. They therefore also cover
the pathwise-legal subclass. The complexity transfer is a proved inequality in
the direction needed for lower bounds, not an asserted equality of every possible
algorithm model.

Oracle seeds retain an arbitrary probability-space interface. Standard-Borel
randomization is not a theorem for arbitrary measurable target spaces. General
set-measure statements use Lean's measure-on-all-sets convention; under the joint
measurability interface, the operational output-progress event is measurable.

## Trust boundary and limitations

The only nonstandard mathematical assumption is
`importedLemmaB1Certificate`, including the base-chain C2 clause. All other
axiom dependencies must be standard logical axioms. The audit excludes `sorryAx`.

No claim is made that all intermediate equations, literature comparisons or
informal conventions have been checked. The general curvature theorem retains
its C2 hypothesis and uses continuous linear operators. Legacy declarations such
as `canonicalTheorem33` are supporting results, not replacements for the current
paper entry points. Outstanding statement/assumption/constant presentation checks
are recorded concisely in `CHECKLIST_STATUS.md`.
