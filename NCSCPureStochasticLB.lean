import Mathlib

/-!
# Concise Zero-Respecting Lower Bounds for Purely Stochastic NCSC Minimax Optimization

Paper-synchronised Lean 4 statement layer for the September 2026 note.

The PDF is the source of truth for every definition, parameter choice, numbered
identity and rate appearing below.  The only analytic input imported by the
paper is the Carmon--Arjevani single-level zero-chain estimate (paper Lemma 2.1),
represented here by the explicit-chain certificate in the paper-exact layer.

Important modelling point: all primal/dual vectors use finite Euclidean spaces,
so `‖·‖` is the ℓ₂ norm used in the PDF.
-/

noncomputable section

namespace NCSCPureStochasticLB

/-! ## Section 1. Lower-bound framework -/

/-- `T`-dimensional real Euclidean space, with the ℓ₂ norm. -/
abbrev Vec (T : ℕ) := EuclideanSpace ℝ (Fin T)

/-- Paper Definition 1.2/1.3 pair support: coordinate `i` is active in either block. -/
def psupp {T : ℕ} (x y : Vec T) : Set (Fin T) :=
  {i | x i ≠ 0 ∨ y i ≠ 0}

/-- Paper Section 1.3: `prog_a(u) = max ({0} ∪ {i : |u_i| > a})`. -/
def prog {T : ℕ} (a : ℝ) (u : Vec T) : ℕ :=
  Nat.findGreatest
    (fun n => ∃ i : Fin T, i.1 + 1 = n ∧ a < |u i|) T


/-- Paper Theorem 3.3 rate, ignoring only universal multiplicative constants. -/
def bvRate (L Δ ε κ σ : ℝ) : ℝ :=
  (L * Δ / ε ^ 2) * max 1 (κ * σ ^ 2 / ε ^ 2)

/-- Paper Theorem 4.4 chain rate, ignoring only universal multiplicative constants. -/
def asChainRate (Lbar Δ ε κ p : ℝ) : ℝ :=
  (Lbar * Δ / ε ^ 2) * min (1 / p) (κ / Real.sqrt p)

/-- Paper equation (32), writing `κ^{3/2}` as `κ * √κ` for nonnegative `κ`. -/
def asMixedRate (Lbar Δ ε κ σ : ℝ) : ℝ :=
  Lbar * Δ * min (κ * σ ^ 2 / ε ^ 4)
    (κ * Real.sqrt κ * σ / ε ^ 3)

/-- Paper Section 4.3 independent estimation rate. -/
def estimationRate (σ ε : ℝ) : ℝ := σ ^ 2 / ε ^ 2

/-! ## Section 2. Common hard instance and quadratic lift -/

/-- Paper Lemma 2.1 constants. -/
def Δ₀ : ℝ := 12

def ℓ₀ : ℝ := 152

def g₀ : ℝ := 23


/-- Paper equation (7) parameter block. -/
structure LiftParameters where
  μ : ℝ
  h : ℝ
  q : ℝ
  γ : ℝ
  μ_pos : 0 < μ
  h_pos : 0 < h
  q_pos : 0 < q
  γ_pos : 0 < γ

namespace LiftParameters

/-- Paper equation (7): `β := h/q`. -/
def β (P : LiftParameters) : ℝ := P.h / P.q

/-- Paper equation (7): `α := q²/h`. -/
def α (P : LiftParameters) : ℝ := P.q ^ 2 / P.h

/-- Paper equation (7): `ν := μ + ℓ₀ h`. -/
def ν (P : LiftParameters) : ℝ := P.μ + ℓ₀ * P.h

theorem q_ne_zero (P : LiftParameters) : P.q ≠ 0 := ne_of_gt P.q_pos

theorem h_ne_zero (P : LiftParameters) : P.h ≠ 0 := ne_of_gt P.h_pos

/-- Paper equation (7): `αβ = q`. -/
theorem alpha_mul_beta (P : LiftParameters) : P.α * P.β = P.q := by
  rw [α, β]
  field_simp [P.h_ne_zero, P.q_ne_zero]
  ring

/-- Paper equation (7): `qβ = h`. -/
theorem q_mul_beta (P : LiftParameters) : P.q * P.β = P.h := by
  rw [β]
  field_simp [P.q_ne_zero]


/-- Paper equations (17)/(19): for `h = μ/(4ℓ₀)`, `ν = 5μ/4`. -/
theorem nu_bv (μ : ℝ) :
    let h := μ / (4 * ℓ₀)
    let ν := μ + ℓ₀ * h
    ν = 5 * μ / 4 := by
  dsimp [ℓ₀]
  ring

/-- Paper equation (19): `ℓ₀ h / ν = 1/5` for the BV choice. -/
theorem transfer_ratio_bv (μ : ℝ) (hμ : 0 < μ) :
    let h := μ / (4 * ℓ₀)
    let ν := μ + ℓ₀ * h
    ℓ₀ * h / ν = 1 / 5 := by
  dsimp [ℓ₀]
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  field_simp [hμ0]
  ring

end LiftParameters



/-! ## Section 3. Bounded-variance case -/

/-- Paper equations (17)--(18) parameter data. -/
structure BVParameters where
  L : ℝ
  μ : ℝ
  ε : ℝ
  σ : ℝ
  Δ : ℝ
  κ : ℝ
  γ : ℝ
  q : ℝ
  p : ℝ
  L_pos : 0 < L
  μ_pos : 0 < μ
  ε_pos : 0 < ε
  κ_def : κ = L / μ
  γ_sq : γ ^ 2 = κ / 4
  γ_pos : 0 < γ
  q_def : q = 2 * ε / γ
  p_def : p = if σ = 0 then 1 else min 1 (q ^ 2 * g₀ ^ 2 / σ ^ 2)

namespace BVParameters

/-- Paper equation (17): `h = μ/(4ℓ₀)`. -/
def h (P : BVParameters) : ℝ := P.μ / (4 * ℓ₀)

/-- Paper equation (17): `ν = 5μ/4`. -/
def ν (P : BVParameters) : ℝ := 5 * P.μ / 4

/-- Paper equation (18): `α = q²/h`. -/
def α (P : BVParameters) : ℝ := P.q ^ 2 / P.h

/-- Paper equation (18): `T = floor(Δ/(4Δ₀α))`, represented by its real precursor. -/
def chainScale (P : BVParameters) : ℝ := P.Δ / (4 * Δ₀ * P.α)

/-- Paper equation (19): `q² = 16ε²/κ`. -/
theorem q_sq (P : BVParameters) : P.q ^ 2 = 16 * P.ε ^ 2 / P.κ := by
  have hκpos : 0 < P.κ := by
    rw [P.κ_def]
    exact div_pos P.L_pos P.μ_pos
  have hκ : P.κ ≠ 0 := ne_of_gt hκpos
  have hγ : P.γ ≠ 0 := ne_of_gt P.γ_pos
  rw [P.q_def]
  field_simp [hγ, hκ]
  nlinarith [P.γ_sq]

/-- Paper equation (19): `α = 64ℓ₀ ε²/L`. -/
theorem alpha_value (P : BVParameters) :
    P.α = 64 * ℓ₀ * P.ε ^ 2 / P.L := by
  rw [α, h, P.q_sq, P.κ_def]
  have hL : P.L ≠ 0 := ne_of_gt P.L_pos
  have hμ : P.μ ≠ 0 := ne_of_gt P.μ_pos
  norm_num [ℓ₀]
  field_simp [hL, hμ]
  ring

end BVParameters




/-! ## Section 4. Averaged-smooth case -/

/-- Paper equation (24): a sufficient universal square constant. -/
def s₀sq (mΓ : ℝ) : ℝ := 4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2

/-- Paper equations (25)--(26) parameter data. -/
structure ASParameters where
  Lbar : ℝ
  μ : ℝ
  ε : ℝ
  σ : ℝ
  Δ : ℝ
  κ : ℝ
  γ : ℝ
  q : ℝ
  p : ℝ
  s₀ : ℝ
  Lbar_pos : 0 < Lbar
  μ_pos : 0 < μ
  ε_pos : 0 < ε
  p_pos : 0 < p
  s₀_pos : 0 < s₀
  κ_def : κ = Lbar / μ
  γ_sq : γ ^ 2 = κ / 4
  γ_pos : 0 < γ
  q_def : q = 2 * ε / γ
  p_def : p = if σ = 0 then 1 else min 1 (q ^ 2 * g₀ ^ 2 / σ ^ 2)

namespace ASParameters

/-- Paper equation (26): `h = min{μ/(4ℓ₀), L̄√p/(4s₀)}`. -/
def h (P : ASParameters) : ℝ :=
  min (P.μ / (4 * ℓ₀)) (P.Lbar * Real.sqrt P.p / (4 * P.s₀))

/-- Paper equation (26): `ν = μ + ℓ₀ h`. -/
def ν (P : ASParameters) : ℝ := P.μ + ℓ₀ * P.h

/-- Paper equation (26): `α = q²/h`. -/
def α (P : ASParameters) : ℝ := P.q ^ 2 / P.h

/-- Paper equation (26): real precursor of `T = floor(Δ/(4Δ₀α))`. -/
def chainScale (P : ASParameters) : ℝ := P.Δ / (4 * Δ₀ * P.α)

/-- Paper equation (27): `q² = 16ε²/κ`. -/
theorem q_sq (P : ASParameters) : P.q ^ 2 = 16 * P.ε ^ 2 / P.κ := by
  have hκpos : 0 < P.κ := by
    rw [P.κ_def]
    exact div_pos P.Lbar_pos P.μ_pos
  have hκ : P.κ ≠ 0 := ne_of_gt hκpos
  have hγ : P.γ ≠ 0 := ne_of_gt P.γ_pos
  rw [P.q_def]
  field_simp [hγ, hκ]
  nlinarith [P.γ_sq]

end ASParameters






/-! ## Statement-final layer

The definitions below are the authoritative paper-aligned formulation.  Earlier temporary
certificate placeholders and non-uniform comparison wrappers have been removed; only reusable
parameter identities and scaling functions are retained above.
-/

/-! ## v10 paper-exact statement layer

This namespace removes the semantic shortcuts of the earlier arithmetic scaffold.
Every object below is stated with the formulas that appear in the PDF.  Analytic
or probabilistic facts that are not yet reproved from Mathlib primitives are
packaged as certificates whose *fields are the actual paper formulas*, never
bare `Prop` placeholders.
-/

namespace PaperExact

open MeasureTheory
open scoped BigOperators

/-- Squared product norm used for `(x,y)` and `(Gx,Gy)`. -/
def pairNormSq {T : ℕ} (x y : Vec T) : ℝ := ‖x‖ ^ 2 + ‖y‖ ^ 2

/-- Product norm on a primal--dual pair. -/
def pairNorm {T : ℕ} (x y : Vec T) : ℝ := Real.sqrt (pairNormSq x y)

/-- Support of one vector. -/
def supp {T : ℕ} (x : Vec T) : Set (Fin T) := {i | x i ≠ 0}

/-- Largest active pair coordinate, using the paper's one-based progress index. -/
def pairProg {T : ℕ} (x y : Vec T) : ℕ := max (prog 0 x) (prog 0 y)

/-- Standard Fréchet/Euclidean gradient relation.  Mathlib's `HasGradientAt` is equivalent to
`HasFDerivAt F (InnerProductSpace.toDual ℝ (Vec T) g) x`, so this matches the paper's ordinary differentiability
and gradient notation rather than merely postulating directional derivatives. -/
def IsEuclideanGradientAt {T : ℕ} (F : Vec T → ℝ) (g : Vec T) (x : Vec T) : Prop :=
  HasGradientAt F g x

/-! ### Definitions 1.1--1.2 -/

/-- Data for a differentiable minimax population objective and its value function. -/
structure PopulationObjective (T : ℕ) where
  f : Vec T → Vec T → ℝ
  gradX : Vec T → Vec T → Vec T
  gradY : Vec T → Vec T → Vec T
  Phi : Vec T → ℝ
  gradPhi : Vec T → Vec T
  gradX_spec : ∀ x y, IsEuclideanGradientAt (fun x' => f x' y) (gradX x y) x
  gradY_spec : ∀ x y, IsEuclideanGradientAt (fun y' => f x y') (gradY x y) y
  gradPhi_spec : ∀ x, IsEuclideanGradientAt Phi (gradPhi x) x
  value_is_max : ∀ x, ∃ ystar : Vec T,
    Phi x = f x ystar ∧ ∀ y : Vec T, f x y ≤ Phi x

/-- Paper Definition 1.1(i): joint `M`-smoothness. -/
def JointSmooth {T : ℕ} (I : PopulationObjective T) (M : ℝ) : Prop :=
  ∀ x y x' y',
    pairNorm (I.gradX x y - I.gradX x' y') (I.gradY x y - I.gradY x' y') ≤
      M * pairNorm (x - x') (y - y')

/-- Paper Definition 1.1(ii): `μ`-strong concavity in the dual variable. -/
def StronglyConcaveY {T : ℕ} (I : PopulationObjective T) (μ : ℝ) : Prop :=
  ∀ x y y',
    I.f x y' ≤ I.f x y + @inner ℝ (Vec T) _ (I.gradY x y) (y' - y) -
      μ / 2 * ‖y' - y‖ ^ 2

/-- Paper Definition 1.1(iii): initial value-function gap. -/
def InitialGap {T : ℕ} (I : PopulationObjective T) (Δ : ℝ) : Prop :=
  I.Phi 0 - sInf (Set.range I.Phi) ≤ Δ

/-- Manuscript Section 3.1: finite primal infimum is an explicit class requirement. -/
def InNCSCClass {T : ℕ} (I : PopulationObjective T) (M μ Δ : ℝ) : Prop :=
  JointSmooth I M ∧ StronglyConcaveY I μ ∧ InitialGap I Δ ∧ BddBelow (Set.range I.Phi)

/-- A stochastic first-order oracle.  The same seed is fed to both blocks. -/
structure StochasticOracle (T : ℕ) (Seed : Type) where
  Gx : Vec T → Vec T → Seed → Vec T
  Gy : Vec T → Vec T → Seed → Vec T

/-- Abstract expectation/probability interface.  Concrete Bernoulli constructions below do not
need any hidden seed convention. -/
structure Law (Seed : Type) where
  expectReal : (Seed → ℝ) → ℝ
  expectVec : ∀ {T : ℕ}, (Seed → Vec T) → Vec T
  probability : Set Seed → ℝ

/-- Minimal probability-law coherence used by the paper statements.  The explicit Bernoulli and
Gaussian constructions below are the intended concrete laws; this structure prevents a generic
`Law` from being treated as an unconstrained triple of functions. -/
structure LawAxioms {Seed : Type} (E : Law Seed) : Prop where
  probability_nonneg : ∀ A : Set Seed, 0 ≤ E.probability A
  probability_le_one : ∀ A : Set Seed, E.probability A ≤ 1
  probability_empty : E.probability ∅ = 0
  probability_univ : E.probability Set.univ = 1
  probability_disjoint_union : ∀ A B : Set Seed, Disjoint A B →
    E.probability (A ∪ B) = E.probability A + E.probability B
  expect_indicator : ∀ A : Set Seed,
    E.expectReal (A.indicator (fun _ => (1 : ℝ))) = E.probability A
  expect_const : ∀ c : ℝ, E.expectReal (fun _ => c) = c
  expect_add : ∀ X Y : Seed → ℝ,
    E.expectReal (fun ξ => X ξ + Y ξ) = E.expectReal X + E.expectReal Y
  expect_smul : ∀ (c : ℝ) (X : Seed → ℝ),
    E.expectReal (fun ξ => c * X ξ) = c * E.expectReal X
  /-- Positivity of expectation.  This is needed for the generic (not merely
  two-point Bernoulli) form of Lemma 2.3. -/
  expect_nonneg : ∀ X : Seed → ℝ, (∀ ξ, 0 ≤ X ξ) → 0 ≤ E.expectReal X
  /-- The probability-normalized Cauchy--Schwarz/Jensen inequality used to
  pass from a second-moment bound to a first-moment bound. -/
  sq_expect_le_expect_sq : ∀ X : Seed → ℝ,
    (E.expectReal X) ^ 2 ≤ E.expectReal (fun ξ => (X ξ) ^ 2)
  expectVec_coord : ∀ {T : ℕ} (X : Seed → Vec T) (i : Fin T),
    (E.expectVec X) i = E.expectReal (fun ξ => X ξ i)

namespace LawAxioms

theorem expect_mono {Seed : Type} {E : Law Seed} (H : LawAxioms E)
    (X Y : Seed → ℝ) (hXY : ∀ ξ, X ξ ≤ Y ξ) :
    E.expectReal X ≤ E.expectReal Y := by
  have hn : 0 ≤ E.expectReal (fun ξ => Y ξ - X ξ) :=
    H.expect_nonneg _ (fun ξ => sub_nonneg.mpr (hXY ξ))
  have hadd := H.expect_add X (fun ξ => Y ξ - X ξ)
  have hid : (fun ξ => X ξ + (Y ξ - X ξ)) = Y := by funext ξ; ring
  rw [hid] at hadd
  linarith

theorem probability_mono {Seed : Type} {E : Law Seed} (H : LawAxioms E)
    {A B : Set Seed} (hAB : A ⊆ B) : E.probability A ≤ E.probability B := by
  rw [← H.expect_indicator A, ← H.expect_indicator B]
  apply H.expect_mono
  intro ξ
  by_cases hA : ξ ∈ A
  · have hB := hAB hA
    simp [Set.indicator_of_mem hA, Set.indicator_of_mem hB]
  · simp [Set.indicator_of_not_mem hA]
    by_cases hB : ξ ∈ B <;> simp [hB]

theorem probability_union_le {Seed : Type} {E : Law Seed} (H : LawAxioms E)
    (A B : Set Seed) : E.probability (A ∪ B) ≤ E.probability A + E.probability B := by
  classical
  let C := B \ A
  have hdis : Disjoint A C := Set.disjoint_sdiff_right
  have hunion : A ∪ B = A ∪ C := by
    ext ξ
    simp [C]
  rw [hunion, H.probability_disjoint_union A C hdis]
  exact add_le_add_left (H.probability_mono (Set.diff_subset)) _

end LawAxioms

/-- Definition 1.2: unbiasedness. -/
def OracleUnbiased {T : ℕ} {Seed : Type} (I : PopulationObjective T)
    (E : Law Seed) (O : StochasticOracle T Seed) : Prop :=
  ∀ x y,
    E.expectVec (fun ξ => O.Gx x y ξ) = I.gradX x y ∧
    E.expectVec (fun ξ => O.Gy x y ξ) = I.gradY x y

/-- Definition 1.2: bounded variance with parameter `σ²`. -/
def OracleBoundedVariance {T : ℕ} {Seed : Type} (I : PopulationObjective T)
    (E : Law Seed) (O : StochasticOracle T Seed) (σ : ℝ) : Prop :=
  ∀ x y,
    E.expectReal (fun ξ =>
      ‖O.Gx x y ξ - I.gradX x y‖ ^ 2 +
      ‖O.Gy x y ξ - I.gradY x y‖ ^ 2) ≤ σ ^ 2

/-- Definition 1.2: averaged smoothness, with the *same* seed on the two query points. -/
def OracleAveragedSmooth {T : ℕ} {Seed : Type} (E : Law Seed)
    (O : StochasticOracle T Seed) (Lbar : ℝ) : Prop :=
  ∀ x y x' y',
    E.expectReal (fun ξ =>
      ‖O.Gx x y ξ - O.Gx x' y' ξ‖ ^ 2 +
      ‖O.Gy x y ξ - O.Gy x' y' ξ‖ ^ 2) ≤
      Lbar ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)

/-! ### Definition 1.3: same-seed batches and pair-zero-respecting traces -/

/-- A realised `R`-round trace with at most `K` query slots per round. `none` means the slot
is unused. -/
structure InteractionTrace (T R K : ℕ) where
  query : Fin R → Fin K → Option (Vec T × Vec T)
  response : Fin R → Fin K → Option (Vec T × Vec T)
  output : Vec T

/-- Number `K_t` of used query slots in round `t`. -/
def batchSize {T R K : ℕ} (tr : InteractionTrace T R K) (t : Fin R) : ℕ :=
  ∑ k : Fin K, if (tr.query t k).isSome then 1 else 0

/-- Total number `N = ∑_t K_t` of returned gradient vectors. -/
def returnedGradientCount {T R K : ℕ} (tr : InteractionTrace T R K) : ℕ :=
  ∑ t : Fin R, batchSize tr t

/-- The paper's protocol uses `K_t ∈ [K]`, i.e. at least one and at most `K` queries per round. -/
def ValidBatchSizes {T R K : ℕ} (tr : InteractionTrace T R K) : Prop :=
  ∀ t : Fin R, 1 ≤ batchSize tr t ∧ batchSize tr t ≤ K

/-- Paper Section 1.2 accounting statement `R ≤ N ≤ K R`. -/
def GradientCountAccountingStatement : Prop :=
  ∀ (T R K : ℕ) (tr : InteractionTrace T R K),
    ValidBatchSizes tr →
      R ≤ returnedGradientCount tr ∧ returnedGradientCount tr ≤ K * R

/-- First successful round count `inf {R : risk ≤ ε²}` for one algorithm/instance pair. -/
noncomputable def firstSuccessRound {Algorithm Instance : Type}
    (risk : Algorithm → Instance → ℕ → ℝ) (ε : ℝ)
    (A : Algorithm) (I : Instance) : ENNReal :=
  sInf {r : ENNReal | ∃ R : ℕ, r = (R : ENNReal) ∧ risk A I R ≤ ε ^ 2}

/-- Paper Section 1.3 complexity `C^{zr,K}_ε`: infimum over admissible pair-zero-respecting
algorithms, supremum over admissible instances, then the first round meeting the risk target.
The concrete expectation/oracle semantics are supplied by `risk`. -/
noncomputable def CzrKε {Algorithm Instance : Type}
    (validAlgorithm : ℕ → Algorithm → Prop) (admissibleInstance : Instance → Prop)
    (risk : Algorithm → Instance → ℕ → ℝ) (K : ℕ) (ε : ℝ) : ENNReal :=
  sInf (Set.range (fun A : {A : Algorithm // validAlgorithm K A} =>
    sSup (Set.range (fun I : {I : Instance // admissibleInstance I} =>
      firstSuccessRound risk ε A.1 I.1))))

/-- Elementary bridge used in Theorems 3.3 and 4.4: a round lower bound is automatically a
returned-gradient lower bound because `N ≥ R`. -/
theorem roundLowerBound_implies_gradientLowerBound
    (b : ℝ) (R N : ℕ) (hround : b ≤ R) (hcount : R ≤ N) : b ≤ N := by
  exact le_trans hround (by exact_mod_cast hcount)

/-- Pair support already revealed strictly before round `t`. -/
def revealedBefore {T R K : ℕ} (tr : InteractionTrace T R K) (t : Fin R) : Set (Fin T) :=
  {i | ∃ s : Fin R, s.1 < t.1 ∧ ∃ k : Fin K, ∃ r : Vec T × Vec T,
    tr.response s k = some r ∧ i ∈ psupp r.1 r.2}

/-- Pair support revealed by the end of the run. -/
def revealedAll {T R K : ℕ} (tr : InteractionTrace T R K) : Set (Fin T) :=
  {i | ∃ s : Fin R, ∃ k : Fin K, ∃ r : Vec T × Vec T,
    tr.response s k = some r ∧ i ∈ psupp r.1 r.2}

/-- Paper Definition 1.3, pathwise. -/
def PairZeroRespectingTrace {T R K : ℕ} (tr : InteractionTrace T R K) : Prop :=
  (∀ t k q, tr.query t k = some q → psupp q.1 q.2 ⊆ revealedBefore tr t) ∧
  supp tr.output ⊆ revealedAll tr

/-- Exact same-seed oracle consistency.  A used query slot receives exactly the oracle
response for the unique seed of that round, while an unused slot receives no response.  The
reverse implication is important: responses can never appear without an actual query. -/
def OracleConsistentTrace {T R K : ℕ} {Seed : Type}
    (O : StochasticOracle T Seed) (seed : Fin R → Seed)
    (tr : InteractionTrace T R K) : Prop :=
  ∀ t k,
    tr.response t k =
      match tr.query t k with
      | none => none
      | some q => some (O.Gx q.1 q.2 (seed t), O.Gy q.1 q.2 (seed t))

/-! ### Definition 1.4 and Lemma 1.5 -/

/-- Paper Definition 1.4 exactly at the event level. -/
def ProbabilityPZeroChain {T : ℕ} {Seed : Type} (E : Law Seed)
    (g : Vec T → Seed → Vec T) (p : ℝ) : Prop :=
  E.probability {Z | ∃ u : Vec T,
      prog 0 (g u Z) = prog (1 / 4) u + 1} ≤ p ∧
  E.probability {Z | ∃ u : Vec T,
      prog (0 : ℝ) (g u Z) > prog (1 / 4) u + 1} = 0


/-! ### Section 2.1: explicit Carmon--Arjevani chain -/

/-- Paper Section 2.1 smooth activation `Ψ`. -/
def Psi (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then 0 else Real.exp (1 - 1 / (2 * t - 1) ^ 2)

/-- Paper Section 2.1 Gaussian primitive `Φ₀(t) = √e ∫_{-∞}^t exp(-τ²/2)dτ`. -/
noncomputable def Phi0 (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) *
    (∫ τ in Set.Iic t, Real.exp (- τ ^ 2 / 2))

/-- Previous coordinate of a positive finite index. -/
def prevFin {T : ℕ} (i : Fin T) (_hi : 0 < i.1) : Fin T :=
  ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩

/-- Paper equation (1), with Lean's zero-based `Fin T` indices. -/
noncomputable def explicitFT (T : ℕ) (hT : 0 < T) (u : Vec T) : ℝ :=
  - Psi 1 * Phi0 (u ⟨0, hT⟩) +
    ∑ i : Fin T,
      if hi : 0 < i.1 then
        Psi (-u (prevFin i hi)) * Phi0 (-u i) -
          Psi (u (prevFin i hi)) * Phi0 (u i)
      else 0

/-- Paper Lemma 2.1 with the missing v6.1 relation `gradF = ∇F` restored and with `F`
identified with the explicit equation-(1) chain. -/
structure ExplicitZeroChainCertificate (T : ℕ) where
  dim_pos : 0 < T
  gradF : Vec T → Vec T
  grad_is_gradient : ∀ u, IsEuclideanGradientAt (explicitFT T dim_pos) (gradF u) u
  gap_bound : explicitFT T dim_pos 0 - sInf (Set.range (explicitFT T dim_pos)) ≤ Δ₀ * T
  grad_lipschitz : ∀ u v, ‖gradF u - gradF v‖ ≤ ℓ₀ * ‖u - v‖
  grad_coord_bound : ∀ u i, |(gradF u) i| ≤ g₀
  zero_chain : ∀ u, prog 0 (gradF u) ≤ prog (1 / 2) u + 1
  terminal_gradient : ∀ u, prog 1 u < T → 1 < ‖gradF u‖
  origin_grad_bound : ‖gradF 0‖ ≤ g₀
  /-- The explicit chain has finite infimum.  This is implicit in the paper's finite gap bound
  and is bundled with the imported Lemma 2.1 certificate so that Lean's totalised `sInf`
  cannot hide an unbounded-below branch. -/
  bddBelow : BddBelow (Set.range (explicitFT T dim_pos))

/-- Paper Lemma B.1, equations (39)--(42), using the actual gradient of the
explicit function. Boundedness below is the preceding paragraph's finite-infimum
convention. The origin norm bound is derived below, not an extra imported field. -/
structure PaperLemmaB1 (T : ℕ) (hT : 0 < T) : Prop where
  contDiff : ContDiff ℝ 2 (explicitFT T hT)
  bddBelow : BddBelow (Set.range (explicitFT T hT))
  gap_bound : explicitFT T hT 0 - sInf (Set.range (explicitFT T hT)) ≤ 12 * T
  grad_lipschitz : ∀ u v, ‖gradient (explicitFT T hT) u - gradient (explicitFT T hT) v‖ ≤
    152 * ‖u - v‖
  grad_coord_bound : ∀ u i, |gradient (explicitFT T hT) u i| ≤ 23
  zero_chain : ∀ u, prog 0 (gradient (explicitFT T hT) u) ≤ prog (1 / 2) u + 1
  terminal_gradient : ∀ u, prog 1 u < T → 1 < ‖gradient (explicitFT T hT) u‖

/-- Sole nonstandard external analytic input: the published Lemma B.1.
Unlike the legacy input, this explicitly includes the paper's C2 clause.
This clause is imported, not asserted to have been proved inside Lean. -/
axiom importedLemmaB1Certificate (T : ℕ) (hT : 2 ≤ T) :
  PaperLemmaB1 T (by omega)

/-- Equation (41) and the coordinate bound imply the origin norm bound. -/
theorem PaperLemmaB1.origin_grad_bound {T : ℕ} {hT : 0 < T} (C : PaperLemmaB1 T hT) :
    ‖gradient (explicitFT T hT) 0‖ ≤ 23 := by
  classical
  let v := gradient (explicitFT T hT) 0
  let first : Fin T := ⟨0, hT⟩
  have hp : prog 0 v ≤ 1 := by
    have hz0 : prog (1 / 2) (0 : Vec T) = 0 := by
      norm_num [prog, Nat.findGreatest_eq_zero_iff]
    simpa only [hz0, zero_add] using C.zero_chain 0
  have hz (i : Fin T) (hi : i ≠ first) : v i = 0 := by
    apply Classical.byContradiction
    intro hne
    have ha : 0 < |v i| := abs_pos.mpr hne
    have hle : i.1 + 1 ≤ prog 0 v := by
      unfold prog
      exact Nat.le_findGreatest (Nat.succ_le_iff.mpr i.2) ⟨i, rfl, ha⟩
    have hiv : i.1 ≠ 0 := by
      intro he
      apply hi
      apply Fin.ext
      exact he
    omega
  have hnorm : ‖v‖ ^ 2 = ‖v first‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_eq_single first
    · intro i _ hi
      simp [hz i hi]
    · simp
  have hc := C.grad_coord_bound 0 first
  change |v first| ≤ 23 at hc
  rw [Real.norm_eq_abs] at hnorm
  nlinarith [norm_nonneg v, abs_nonneg (v first)]

/-- Derived compatibility data for internal proofs retaining historical numbering. -/
def PaperLemmaB1.toLegacy {T : ℕ} {hT : 0 < T} (C : PaperLemmaB1 T hT) :
    ExplicitZeroChainCertificate T where
  dim_pos := hT
  gradF := gradient (explicitFT T hT)
  grad_is_gradient := fun u => (C.contDiff.differentiable (by norm_num) u).hasGradientAt
  gap_bound := C.gap_bound
  grad_lipschitz := C.grad_lipschitz
  grad_coord_bound := C.grad_coord_bound
  zero_chain := C.zero_chain
  terminal_gradient := C.terminal_gradient
  origin_grad_bound := C.origin_grad_bound
  bddBelow := C.bddBelow

/-- Legacy compatibility theorem, not an additional axiom. -/
theorem importedLemma21Certificate (T : ℕ) (hT : 2 ≤ T) :
    Nonempty (ExplicitZeroChainCertificate T) :=
  ⟨(importedLemmaB1Certificate T hT).toLegacy⟩

/-- Current paper-facing entry for the sole external analytic result. -/
theorem lemmaB1_paper (T : ℕ) (hT : 2 ≤ T) : PaperLemmaB1 T (by omega) :=
  importedLemmaB1Certificate T hT

/-- The manuscript's conservative 155 bound follows from the imported 152 bound. -/
theorem PaperLemmaB1.grad_lipschitz_slack {T : ℕ} {hT : 0 < T}
    (C : PaperLemmaB1 T hT) (u v : Vec T) :
    ‖gradient (explicitFT T hT) u - gradient (explicitFT T hT) v‖ ≤ 155 * ‖u - v‖ := by
  have := C.grad_lipschitz u v
  nlinarith [norm_nonneg (u - v)]


/-! ### v43: derive the descent inequalities from Lemma 2.1(3)

The paper lists Lipschitz continuity of the explicit-chain gradient as Lemma 2.1(3).  Earlier
formalisation snapshots bundled the two standard descent-lemma inequalities into the imported
certificate.  In v43 we close that small formalisation boundary: the next theorem proves the
two-sided quadratic remainder estimate directly from the gradient identity and its Lipschitz bound.
-/

/-- Two-sided descent-lemma remainder bound for the explicit chain.  This is the usual line-segment
proof: subtract the first-order model at `u`, differentiate along `u + t(v-u)`, bound the derivative
by `ℓ₀ t ‖v-u‖²`, and fence it against `(ℓ₀/2)t²‖v-u‖²` on `[0,1]`. -/
theorem explicitFT_smooth_remainder_bounds {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (u v : Vec T) :
    -(ℓ₀ / 2 * ‖v - u‖ ^ 2) ≤
        explicitFT T C.dim_pos v - explicitFT T C.dim_pos u -
          @inner ℝ (Vec T) _ (C.gradF u) (v - u) ∧
      explicitFT T C.dim_pos v - explicitFT T C.dim_pos u -
          @inner ℝ (Vec T) _ (C.gradF u) (v - u) ≤
        ℓ₀ / 2 * ‖v - u‖ ^ 2 := by
  let d : Vec T := v - u
  let r : ℝ → ℝ := fun t =>
    explicitFT T C.dim_pos (u + t • d) - explicitFT T C.dim_pos u -
      t * @inner ℝ (Vec T) _ (C.gradF u) d
  let rp : ℝ → ℝ := fun t =>
    @inner ℝ (Vec T) _ (C.gradF (u + t • d) - C.gradF u) d
  let B : ℝ → ℝ := fun t => ℓ₀ / 2 * t ^ 2 * ‖d‖ ^ 2
  let Bp : ℝ → ℝ := fun t => ℓ₀ * t * ‖d‖ ^ 2

  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u + s • d) d t := by
    intro t
    simpa using HasDerivAt.const_add u ((hasDerivAt_id t).smul_const d)

  have hFpath : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => explicitFT T C.dim_pos (u + s • d))
        (@inner ℝ (Vec T) _ (C.gradF (u + t • d)) d) t := by
    intro t
    have hcomp := (C.grad_is_gradient (u + t • d)).hasFDerivAt.comp_hasDerivAt t (hpath t)
    convert hcomp using 1 <;> simp [Function.comp_def]

  have hr : ∀ t : ℝ, HasDerivAt r (rp t) t := by
    intro t
    have hlin : HasDerivAt
        (fun s : ℝ => s * @inner ℝ (Vec T) _ (C.gradF u) d)
        (@inner ℝ (Vec T) _ (C.gradF u) d) t := by
      simpa only [id_eq, one_mul] using
        (hasDerivAt_id t).mul_const (@inner ℝ (Vec T) _ (C.gradF u) d)
    have h := ((hFpath t).sub_const (explicitFT T C.dim_pos u)).sub hlin
    have hinner :
        @inner ℝ (Vec T) _ (C.gradF (u + t • d)) d -
            @inner ℝ (Vec T) _ (C.gradF u) d = rp t := by
      simp [rp, inner_sub_left]
    rw [hinner] at h
    simpa [r] using h

  have hB : ∀ t : ℝ, HasDerivAt B (Bp t) t := by
    intro t
    have h := ((hasDerivAt_pow 2 t).const_mul (ℓ₀ / 2)).mul_const (‖d‖ ^ 2)
    change HasDerivAt B (ℓ₀ / 2 * (↑2 * t ^ (2 - 1)) * ‖d‖ ^ 2) t at h
    have hderiv : ℓ₀ / 2 * (↑2 * t ^ (2 - 1)) * ‖d‖ ^ 2 = Bp t := by
      simp only [Bp, Nat.reduceSub, pow_one, Nat.cast_ofNat]
      ring
    rw [hderiv] at h
    exact h

  have hr_cont : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hr t).continuousAt
  have hB_cont : Continuous B := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hB t).continuousAt

  have hderiv_bound : ∀ t ∈ Set.Ico (0 : ℝ) 1, rp t ≤ Bp t := by
    intro t ht
    have hdiff : u + t • d - u = t • d := by module
    have hLip := C.grad_lipschitz (u + t • d) u
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hLip
    calc
      rp t = @inner ℝ (Vec T) _ (C.gradF (u + t • d) - C.gradF u) d := by rfl
      _ ≤ ‖C.gradF (u + t • d) - C.gradF u‖ * ‖d‖ :=
        real_inner_le_norm _ _
      _ ≤ (ℓ₀ * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hLip (norm_nonneg d)
      _ = Bp t := by simp [Bp]; ring

  have hneg_deriv_bound : ∀ t ∈ Set.Ico (0 : ℝ) 1, -rp t ≤ Bp t := by
    intro t ht
    have hdiff : u + t • d - u = t • d := by module
    have hLip := C.grad_lipschitz (u + t • d) u
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hLip
    calc
      -rp t ≤ |rp t| := neg_le_abs _
      _ = |@inner ℝ (Vec T) _ (C.gradF (u + t • d) - C.gradF u) d| := by rfl
      _ ≤ ‖C.gradF (u + t • d) - C.gradF u‖ * ‖d‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (ℓ₀ * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hLip (norm_nonneg d)
      _ = Bp t := by simp [Bp]; ring

  have hupper0 : r 0 ≤ B 0 := by simp [r, B]
  have hupper : r 1 ≤ B 1 := by
    exact image_le_of_deriv_right_le_deriv_boundary
      hr_cont.continuousOn
      (fun t ht => (hr t).hasDerivWithinAt)
      hupper0
      hB_cont.continuousOn
      (fun t ht => (hB t).hasDerivWithinAt)
      hderiv_bound
      (by simp)

  have hrneg : ∀ t : ℝ, HasDerivAt (fun s => -r s) (-rp t) t := by
    intro t
    simpa using (hr t).neg
  have hrneg_cont : Continuous (fun t => -r t) := hr_cont.neg
  have hlower0 : -r 0 ≤ B 0 := by simp [r, B]
  have hlower : -r 1 ≤ B 1 := by
    exact image_le_of_deriv_right_le_deriv_boundary
      hrneg_cont.continuousOn
      (fun t ht => (hrneg t).hasDerivWithinAt)
      hlower0
      hB_cont.continuousOn
      (fun t ht => (hB t).hasDerivWithinAt)
      hneg_deriv_bound
      (by simp)

  have hendpoint : u + (1 : ℝ) • d = v := by
    dsimp [d]
    module
  have hupper' :
      explicitFT T C.dim_pos v - explicitFT T C.dim_pos u -
          @inner ℝ (Vec T) _ (C.gradF u) (v - u) ≤
        ℓ₀ / 2 * ‖v - u‖ ^ 2 := by
    rw [show r 1 =
        explicitFT T C.dim_pos v - explicitFT T C.dim_pos u -
          @inner ℝ (Vec T) _ (C.gradF u) (v - u) by
          simp [r, d, hendpoint],
      show B 1 = ℓ₀ / 2 * ‖v - u‖ ^ 2 by simp [B, d]] at hupper
    exact hupper
  have hlower' :
      -(ℓ₀ / 2 * ‖v - u‖ ^ 2) ≤
        explicitFT T C.dim_pos v - explicitFT T C.dim_pos u -
          @inner ℝ (Vec T) _ (C.gradF u) (v - u) := by
    rw [show r 1 =
        explicitFT T C.dim_pos v - explicitFT T C.dim_pos u -
          @inner ℝ (Vec T) _ (C.gradF u) (v - u) by
          simp [r, d, hendpoint],
      show B 1 = ℓ₀ / 2 * ‖v - u‖ ^ 2 by simp [B, d]] at hlower
    linarith
  exact ⟨hlower', hupper'⟩

/-- Standard smooth upper model, now derived internally from Lemma 2.1(3). -/
theorem explicitFT_smooth_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (u v : Vec T) :
    explicitFT T C.dim_pos v ≤ explicitFT T C.dim_pos u +
      @inner ℝ (Vec T) _ (C.gradF u) (v - u) + ℓ₀ / 2 * ‖v - u‖ ^ 2 := by
  have h := (explicitFT_smooth_remainder_bounds C u v).2
  linarith

/-- Reverse smooth model, now derived internally from Lemma 2.1(3). -/
theorem explicitFT_smooth_lower {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (u v : Vec T) :
    explicitFT T C.dim_pos u + @inner ℝ (Vec T) _ (C.gradF u) (v - u) -
        ℓ₀ / 2 * ‖v - u‖ ^ 2 ≤ explicitFT T C.dim_pos v := by
  have h := (explicitFT_smooth_remainder_bounds C u v).1
  linarith

/-! ### Bernoulli seed model used in Sections 3--4 -/

/-- Bernoulli seed as a real `0/1` value. -/
def bernoulliZ (z : Bool) : ℝ := if z then 1 else 0

/-- Expectation under `Z ~ Bernoulli(p)` for real-valued quantities. -/
def bernoulliExpectReal (p : ℝ) (X : Bool → ℝ) : ℝ :=
  p * X true + (1 - p) * X false

/-- Expectation under `Z ~ Bernoulli(p)` for Euclidean vectors. -/
def bernoulliExpectVec {T : ℕ} (p : ℝ) (X : Bool → Vec T) : Vec T :=
  p • X true + (1 - p) • X false

/-- Probability of a Boolean-seed event. -/
noncomputable def bernoulliProb (p : ℝ) (A : Bool → Prop) : ℝ := by
  classical
  exact p * (if A true then 1 else 0) + (1 - p) * (if A false then 1 else 0)

/-- Concrete probability/expectation law for the Bernoulli seed.  The range assumptions
`0 ≤ p ≤ 1` are stated where probabilistic conclusions are invoked. -/
noncomputable def bernoulliLaw (p : ℝ) : Law Bool where
  expectReal := bernoulliExpectReal p
  expectVec := fun X => bernoulliExpectVec p X
  probability := fun A => bernoulliProb p (fun z => z ∈ A)

/-- Generic stochastic base oracle used by the paper's Lemma 2.3 before any Bernoulli
specialisation. -/
structure GenericBaseOracle (T : ℕ) (Seed : Type) where
  g : Vec T → Seed → Vec T

/-- Generic unbiasedness hypothesis from the opening sentence of Lemma 2.3. -/
def GenericBaseUnbiased {T : ℕ} {Seed : Type} (C : ExplicitZeroChainCertificate T)
    (E : Law Seed) (B : GenericBaseOracle T Seed) : Prop :=
  ∀ u, E.expectVec (fun ξ => B.g u ξ) = C.gradF u

/-- Generic version of Lemma 2.3(iii)'s base variance hypothesis. -/
def GenericBaseVarianceHypothesis {T : ℕ} {Seed : Type}
    (C : ExplicitZeroChainCertificate T) (E : Law Seed)
    (B : GenericBaseOracle T Seed) (p v₀ : ℝ) : Prop :=
  ∀ u, E.expectReal (fun ξ => ‖B.g u ξ - C.gradF u‖ ^ 2) ≤
    v₀ ^ 2 * (1 - p) / p

/-- Generic same-seed averaged-smooth hypothesis from Lemma 2.3(iv). -/
def GenericBaseAveragedSmoothHypothesis {T : ℕ} {Seed : Type}
    (E : Law Seed) (B : GenericBaseOracle T Seed) (p s₀ : ℝ) : Prop :=
  ∀ u v, E.expectReal (fun ξ => ‖B.g u ξ - B.g v ξ‖ ^ 2) ≤
    s₀ ^ 2 / p * ‖u - v‖ ^ 2

/-- Sections 3--4 specialise the generic Lemma-2.3 oracle to one Bernoulli bit. -/
abbrev BaseOracle (T : ℕ) := GenericBaseOracle T Bool

/-- Unbiasedness of a Bernoulli base oracle. -/
def BaseUnbiased {T : ℕ} (C : ExplicitZeroChainCertificate T) (B : BaseOracle T)
    (p : ℝ) : Prop :=
  ∀ u, bernoulliExpectVec p (fun Z => B.g u Z) = C.gradF u

/-- The paper's variance hypothesis in Lemma 2.3(iii). -/
def BaseVarianceHypothesis {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (p v₀ : ℝ) : Prop :=
  ∀ u, bernoulliExpectReal p (fun Z => ‖B.g u Z - C.gradF u‖ ^ 2) ≤
    v₀ ^ 2 * (1 - p) / p

/-- The paper's same-seed averaged-smooth hypothesis in Lemma 2.3(iv). -/
def BaseAveragedSmoothHypothesis {T : ℕ} (B : BaseOracle T) (p s₀ : ℝ) : Prop :=
  ∀ u v, bernoulliExpectReal p (fun Z => ‖B.g u Z - B.g v Z‖ ^ 2) ≤
    s₀ ^ 2 / p * ‖u - v‖ ^ 2

/-- Equation (8) using the explicit chain certificate. -/
noncomputable def liftedF {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : LiftParameters) (x y : Vec T) : ℝ :=
  P.α * explicitFT T C.dim_pos (P.β • y) - P.ν / 2 * ‖y - P.γ • x‖ ^ 2

/-- Equation (9). -/
def liftedGx {T : ℕ} (P : LiftParameters) (x y : Vec T) (_Z : Bool) : Vec T :=
  (P.ν * P.γ) • (y - P.γ • x)

/-- Equation (10), now with the actual stochastic base oracle rather than only its mean. -/
def liftedGy {T : ℕ} (B : BaseOracle T) (P : LiftParameters)
    (x y : Vec T) (Z : Bool) : Vec T :=
  P.q • B.g (P.β • y) Z - P.ν • (y - P.γ • x)

/-- Equations (9)--(10) as a stochastic pair oracle. -/
def liftedOracle {T : ℕ} (B : BaseOracle T) (P : LiftParameters) : StochasticOracle T Bool where
  Gx := liftedGx P
  Gy := liftedGy B P

/-- Equation (9) with an arbitrary stochastic seed. -/
def genericLiftedGx {T : ℕ} {Seed : Type} (P : LiftParameters)
    (x y : Vec T) (_ξ : Seed) : Vec T :=
  (P.ν * P.γ) • (y - P.γ • x)

/-- Equation (10) with an arbitrary stochastic base oracle. -/
def genericLiftedGy {T : ℕ} {Seed : Type} (B : GenericBaseOracle T Seed)
    (P : LiftParameters) (x y : Vec T) (ξ : Seed) : Vec T :=
  P.q • B.g (P.β • y) ξ - P.ν • (y - P.γ • x)

/-- Equations (9)--(10) for the generic seed space used in Lemma 2.3. -/
def genericLiftedOracle {T : ℕ} {Seed : Type} (B : GenericBaseOracle T Seed)
    (P : LiftParameters) : StochasticOracle T Seed where
  Gx := genericLiftedGx P
  Gy := genericLiftedGy B P

/-- Strong concavity with a specified modulus for the lifted dual objective. -/
def LiftStrongConcavity {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : LiftParameters) (m : ℝ) : Prop :=
  ∀ x y y',
    liftedF C P x y' ≤ liftedF C P x y +
      @inner ℝ (Vec T) _ (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
      m / 2 * ‖y' - y‖ ^ 2

/-- Generic support/probability interpretation of Lemma 2.3(vi).  The second clause is
an almost-sure statement, matching Definition 1.4: a farther-than-one reveal may occur only on
a null seed event rather than being ruled out pointwise for every representative of the law. -/
def GenericLiftCanRevealAtMostOnePair {T : ℕ} {Seed : Type}
    (E : Law Seed) (B : GenericBaseOracle T Seed) (P : LiftParameters) (p : ℝ) : Prop :=
  E.probability {ξ | ∃ x y,
    pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) =
      pairProg x y + 1} ≤ p ∧
  E.probability {ξ | ∃ x y,
    pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) >
      pairProg x y + 1} = 0

/-- Paper Lemma 2.3 in its generic-seed form.  This is the authoritative statement-level
interface: Sections 3--4 below are simply the Bernoulli specialisation `Seed := Bool`. -/
structure GenericLiftPropertiesCertificate (T : ℕ) {Seed : Type}
    (C : ExplicitZeroChainCertificate T) (E : Law Seed)
    (B : GenericBaseOracle T Seed) (P : LiftParameters) where
  base_unbiased : GenericBaseUnbiased C E B
  Phi : Vec T → ℝ
  gradPhi : Vec T → Vec T
  yStar : Vec T → Vec T
  gradX_formula : ∀ x y,
    IsEuclideanGradientAt (fun x' => liftedF C P x' y)
      ((P.ν * P.γ) • (y - P.γ • x)) x
  gradY_formula : ∀ x y,
    IsEuclideanGradientAt (fun y' => liftedF C P x y')
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) y
  maximizer : ∀ x y, liftedF C P x y ≤ liftedF C P x (yStar x)
  maximizer_unique : ∀ x y, liftedF C P x y = liftedF C P x (yStar x) → y = yStar x
  Phi_def : ∀ x, Phi x = liftedF C P x (yStar x)
  gradPhi_spec : ∀ x, IsEuclideanGradientAt Phi (gradPhi x) x
  mu_strong_concavity : LiftStrongConcavity C P P.μ
  /-- Paper Lemma 2.3(i), stated as the upper bracket on every valid uniform strong-concavity
  modulus.  This avoids postulating attainment of a largest modulus while proving exactly the
  `μ_act ≤ ν+ℓ₀h` estimate used in the condition-number calculation. -/
  strong_modulus_upper : ∀ m, LiftStrongConcavity C P m → m ≤ P.ν + ℓ₀ * P.h
  joint_smoothness : ∀ x y x' y',
    pairNorm
      ((P.ν * P.γ) • (y - P.γ • x) - (P.ν * P.γ) • (y' - P.γ • x'))
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x'))) ≤
      (P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h) * pairNorm (x - x') (y - y')
  primal_gap : Phi 0 - sInf (Set.range Phi) ≤
    P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ)
  variance_transfer : ∀ p v₀, GenericBaseVarianceHypothesis C E B p v₀ →
    ∀ x y, E.expectReal (fun ξ =>
      ‖genericLiftedGx P x y ξ - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
      ‖genericLiftedGy B P x y ξ -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2) ≤
      P.q ^ 2 * v₀ ^ 2 * (1 - p) / p
  averaged_smooth_transfer : ∀ p s₀, 0 < p → p ≤ 1 → 0 ≤ s₀ →
    GenericBaseAveragedSmoothHypothesis E B p s₀ →
    ∀ x y x' y', E.expectReal (fun ξ =>
      ‖genericLiftedGx P x y ξ - genericLiftedGx P x' y' ξ‖ ^ 2 +
      ‖genericLiftedGy B P x y ξ - genericLiftedGy B P x' y' ξ‖ ^ 2) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * s₀ / Real.sqrt p) ^ 2 *
        (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  stationarity_transfer : ∀ x,
    P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) *
      ‖C.gradF ((P.β * P.γ) • x)‖ ≤ ‖gradPhi x‖
  zero_chain_transfer : ∀ p, 0 ≤ p → p ≤ 1 →
    ProbabilityPZeroChain E B.g p → GenericLiftCanRevealAtMostOnePair E B P p

/-- Quantifier-level statement of Lemma 2.3 for an arbitrary seed space and stochastic base oracle. -/
def Lemma23Statement : Prop :=
  ∀ (T : ℕ) (Seed : Type) (C : ExplicitZeroChainCertificate T)
    (E : Law Seed) (B : GenericBaseOracle T Seed) (P : LiftParameters),
    LawAxioms E → GenericBaseUnbiased C E B →
      Nonempty (GenericLiftPropertiesCertificate T C E B P)

/-- Bernoulli specialization of the support/probability interpretation in Lemma 2.3(vi). -/
def LiftCanRevealAtMostOnePair {T : ℕ} (B : BaseOracle T) (P : LiftParameters)
    (p : ℝ) : Prop :=
  bernoulliProb p (fun Z => ∃ x y,
    pairProg (liftedGx P x y Z) (liftedGy B P x y Z) = pairProg x y + 1) ≤ p ∧
  bernoulliProb p (fun Z => ∃ x y,
    pairProg (liftedGx P x y Z) (liftedGy B P x y Z) > pairProg x y + 1) = 0

/-- Paper Lemma 2.3 with every v6.1 bare-`Prop` field replaced by its displayed formula. -/
structure LiftPropertiesCertificate (T : ℕ) (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters) where
  Phi : Vec T → ℝ
  gradPhi : Vec T → Vec T
  yStar : Vec T → Vec T
  gradX_formula : ∀ x y,
    IsEuclideanGradientAt (fun x' => liftedF C P x' y)
      ((P.ν * P.γ) • (y - P.γ • x)) x
  gradY_formula : ∀ x y,
    IsEuclideanGradientAt (fun y' => liftedF C P x y')
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) y
  maximizer : ∀ x y, liftedF C P x y ≤ liftedF C P x (yStar x)
  maximizer_unique : ∀ x y, liftedF C P x y = liftedF C P x (yStar x) → y = yStar x
  Phi_def : ∀ x, Phi x = liftedF C P x (yStar x)
  gradPhi_spec : ∀ x, IsEuclideanGradientAt Phi (gradPhi x) x
  mu_strong_concavity : LiftStrongConcavity C P P.μ
  /-- Bernoulli specialization of the paper's actual strong-concavity bracket.  As in the
  generic-seed interface above, we record the upper bound on every admissible uniform modulus
  rather than postulating that a largest modulus is attained. -/
  strong_modulus_upper : ∀ m, LiftStrongConcavity C P m → m ≤ P.ν + ℓ₀ * P.h
  joint_smoothness : ∀ x y x' y',
    pairNorm
      ((P.ν * P.γ) • (y - P.γ • x) - (P.ν * P.γ) • (y' - P.γ • x'))
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x'))) ≤
      (P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h) * pairNorm (x - x') (y - y')
  primal_gap : Phi 0 - sInf (Set.range Phi) ≤
    P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ)
  variance_transfer : ∀ p v₀, BaseVarianceHypothesis C B p v₀ →
    ∀ x y, bernoulliExpectReal p (fun Z =>
      ‖liftedGx P x y Z - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
      ‖liftedGy B P x y Z -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2) ≤
      P.q ^ 2 * v₀ ^ 2 * (1 - p) / p
  averaged_smooth_transfer : ∀ p s₀, 0 < p → p ≤ 1 → 0 ≤ s₀ →
    BaseAveragedSmoothHypothesis B p s₀ →
    ∀ x y x' y',
      bernoulliExpectReal p (fun Z =>
        ‖liftedGx P x y Z - liftedGx P x' y' Z‖ ^ 2 +
        ‖liftedGy B P x y Z - liftedGy B P x' y' Z‖ ^ 2) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * s₀ / Real.sqrt p) ^ 2 *
        (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  stationarity_transfer : ∀ x,
    P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) *
      ‖C.gradF ((P.β * P.γ) • x)‖ ≤ ‖gradPhi x‖
  zero_chain_transfer : ∀ p, 0 ≤ p → p ≤ 1 →
    ProbabilityPZeroChain (bernoulliLaw p) B.g p →
      LiftCanRevealAtMostOnePair B P p

/-- The population objective determined by equations (8)--(10) and a Lemma 2.3 certificate.
This is the object used by the v10 class-membership statements, so the instance cannot be replaced
by an unrelated objective. -/
def populationFromLift {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) : PopulationObjective T where
  f := liftedF C P
  gradX := fun x y => (P.ν * P.γ) • (y - P.γ • x)
  gradY := fun x y => P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)
  Phi := L.Phi
  gradPhi := L.gradPhi
  gradX_spec := L.gradX_formula
  gradY_spec := L.gradY_formula
  gradPhi_spec := L.gradPhi_spec
  value_is_max := by
    intro x
    refine ⟨L.yStar x, L.Phi_def x, ?_⟩
    intro y
    rw [L.Phi_def x]
    exact L.maximizer x y

/-- Bracketing certificate for the *actual* condition number.  `Mlo/Mhi` bracket every
valid joint-gradient Lipschitz constant from below/above, while `muLo/muHi` bracket every valid
uniform strong-concavity modulus.  This is the precise content proved in Lemma 3.2 and avoids
assuming that the infimum/supremum moduli are attained. -/
structure ActualConditionNumberCertificate {T : ℕ} (I : PopulationObjective T) where
  Mlo : ℝ
  Mhi : ℝ
  muLo : ℝ
  muHi : ℝ
  Mlo_pos : 0 < Mlo
  Mhi_pos : 0 < Mhi
  muLo_pos : 0 < muLo
  muHi_pos : 0 < muHi
  smooth_upper : JointSmooth I Mhi
  smooth_lower : ∀ M : ℝ, 0 ≤ M → JointSmooth I M → Mlo ≤ M
  strong_lower : StronglyConcaveY I muLo
  strong_upper : ∀ m : ℝ, StronglyConcaveY I m → m ≤ muHi

/-- Averaged-smooth analogue of the bracketing condition-number certificate. -/
structure ActualAveragedConditionNumberCertificate {T : ℕ} {Seed : Type}
    (I : PopulationObjective T) (E : Law Seed) (O : StochasticOracle T Seed) where
  LbarLo : ℝ
  LbarHi : ℝ
  muLo : ℝ
  muHi : ℝ
  LbarLo_pos : 0 < LbarLo
  LbarHi_pos : 0 < LbarHi
  muLo_pos : 0 < muLo
  muHi_pos : 0 < muHi
  averaged_smooth_upper : OracleAveragedSmooth E O LbarHi
  averaged_smooth_lower : ∀ L : ℝ, 0 ≤ L → OracleAveragedSmooth E O L → LbarLo ≤ L
  strong_lower : StronglyConcaveY I muLo
  strong_upper : ∀ m : ℝ, StronglyConcaveY I m → m ≤ muHi

/-! ### Proposition 2.4, now stated with the actual risk conclusion -/

/-- A finite-round world of independent Bernoulli oracle seeds. -/
abbrev RoundWorld (R : ℕ) := Fin R → Bool

/-- Product Bernoulli weight for independent fresh seeds across rounds. -/
def roundWeight (p : ℝ) {R : ℕ} (w : RoundWorld R) : ℝ :=
  ∏ t : Fin R, if w t then p else 1 - p

/-- Product Bernoulli expectation across `R` independent rounds. -/
def roundExpect (p : ℝ) {R : ℕ} (X : RoundWorld R → ℝ) : ℝ :=
  ∑ w : RoundWorld R, roundWeight p w * X w

/-- A causal same-seed-per-round run.  This represents one fixed realization of any
internal algorithmic randomness.  Crucially, round-`t` queries may depend on *past oracle
responses*, but not on hidden oracle seeds.  Conditioning on internal random coins therefore
covers randomized algorithms without granting them seed access. -/
structure BernoulliRun (T R K : ℕ) (O : StochasticOracle T Bool) where
  trace : RoundWorld R → InteractionTrace T R K
  causal_queries : ∀ w w' t,
    (∀ s : Fin R, s.1 < t.1 → ∀ k : Fin K,
      (trace w).response s k = (trace w').response s k) →
    (trace w).query t = (trace w').query t
  causal_output : ∀ w w',
    (∀ t : Fin R, ∀ k : Fin K,
      (trace w).response t k = (trace w').response t k) →
    (trace w).output = (trace w').output
  response_consistent : ∀ w,
    OracleConsistentTrace O (fun t => w t) (trace w)
  zero_respecting : ∀ w, PairZeroRespectingTrace (trace w)

/-- Probability of an event in the independent Bernoulli round world. -/
noncomputable def roundProb (p : ℝ) {R : ℕ} (A : Set (RoundWorld R)) : ℝ := by
  classical
  exact roundExpect p (fun w => if w ∈ A then 1 else 0)

/-- Replace only the seed used in round `t`. -/
def setRoundSeed {R : ℕ} (w : RoundWorld R) (t : Fin R) (z : Bool) : RoundWorld R :=
  fun s => if s = t then z else w s

/-- Adaptedness of a progress increment: increment `t` depends only on seeds through round `t`. -/
def ProgressAdapted {R : ℕ} (inc : Fin R → RoundWorld R → ℕ) : Prop :=
  ∀ w w' t,
    (∀ s : Fin R, s.1 ≤ t.1 → w s = w' s) → inc t w = inc t w'

/-- Conditional reveal probability in the Bernoulli construction, after fixing the past. -/
def oneRoundRevealProb {R : ℕ} (p : ℝ)
    (inc : Fin R → RoundWorld R → ℕ) (t : Fin R) (w : RoundWorld R) : ℝ :=
  p * (if inc t (setRoundSeed w t true) = 1 then 1 else 0) +
    (1 - p) * (if inc t (setRoundSeed w t false) = 1 then 1 else 0)

/-- Lemma 1.5 in the concrete independent-Bernoulli world used by Sections 3--4.
Unlike the earlier certificate, the reveal bound is attached to the actual increment event. -/
def ProgressBoundStatement : Prop :=
  ∀ (R T : ℕ) (p : ℝ) (inc : Fin R → RoundWorld R → ℕ),
    0 ≤ p → p ≤ 1 →
    (∀ t w, inc t w = 0 ∨ inc t w = 1) →
    ProgressAdapted inc →
    (∀ t w, oneRoundRevealProb p inc t w ≤ p) →
    8 ≤ T →
    (R : ℝ) ≤ (T : ℝ) / (4 * p) →
    1 / 2 < roundProb p {w | (∑ t : Fin R, inc t w) < T}

/-- Squared stationarity risk of a run. -/
def stationarityRisk {T R K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (gradPhi : Vec T → Vec T) (A : BernoulliRun T R K O) : ℝ :=
  roundExpect p (fun w => ‖gradPhi ((A.trace w).output)‖ ^ 2)

/-- Paper Proposition 2.4 as a complete mathematical statement.  The missing v7.3
probability-`p` zero-chain premise is explicit here. -/
def Proposition24Statement {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters) (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) : Prop :=
  0 < p → p ≤ 1 →
  ProbabilityPZeroChain (bernoulliLaw p) B.g p →
  P.γ * P.q = 2 * ε →
  ℓ₀ * P.h / P.ν ≤ 1 / 5 →
  8 ≤ T →
  ∀ (K R : ℕ), 0 < K →
    ∀ A : BernoulliRun T R K (liftedOracle B P),
      (R : ℝ) ≤ (T : ℝ) / (4 * p) →
      ε ^ 2 < stationarityRisk p L.gradPhi A

/-! ### Section 3.1: equation (16) and Lemma 3.1 -/

/-- Indicator `1{i > prog_{1/4}(u)}` with Lean's zero-based coordinates. -/
def frontierIndicator {T : ℕ} (u : Vec T) (i : Fin T) : ℝ :=
  if prog (1 / 4) u < i.1 + 1 then 1 else 0

/-- Paper equation (16), exactly. -/
def bvBaseOracle {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) : Vec T :=
  fun i => (C.gradF u) i *
    (1 + frontierIndicator u i * (bernoulliZ Z / p - 1))

/-- Lemma 3.1 statement for the explicit oracle (16). -/
structure BVBaseOracleCertificate (T : ℕ) (C : ExplicitZeroChainCertificate T)
    (p : ℝ) where
  p_pos : 0 < p
  p_le_one : p ≤ 1
  law_valid : LawAxioms (bernoulliLaw p)
  unbiased : ∀ u,
    bernoulliExpectVec p (fun Z => bvBaseOracle C p u Z) = C.gradF u
  probability_zero_chain :
    ProbabilityPZeroChain (bernoulliLaw p)
      (bvBaseOracle C p) p
  variance : ∀ u,
    bernoulliExpectReal p (fun Z => ‖bvBaseOracle C p u Z - C.gradF u‖ ^ 2) ≤
      g₀ ^ 2 * (1 - p) / p

/-! ### Section 3.2: exact `p` semantics and Lemma 3.2 -/

/-- Exact identity used in Lemma 3.2(v), including the `σ=0` branch.  This replaces the
non-uniform scalar-comparison shortcut from the early scaffold. -/
def BVInvPScalingExact (p κ σ ε : ℝ) : Prop :=
  (σ = 0 ∧ p = 1) ∨
  (σ ≠ 0 ∧ 1 / p = max 1 (κ * σ ^ 2 / (16 * g₀ ^ 2 * ε ^ 2)))

/-- Exact witness tying Lemma 3.2 to equations (8)--(10), (16), and (17)--(18). -/
structure BVConstructionWitness {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : BVParameters) where
  LP : LiftParameters
  lift_mu : LP.μ = P.μ
  lift_h : LP.h = P.h
  lift_q : LP.q = P.q
  lift_gamma : LP.γ = P.γ
  B : BaseOracle T
  base_oracle_def : ∀ u Z, B.g u Z = bvBaseOracle C P.p u Z
  lift_properties : LiftPropertiesCertificate T C B LP

/-- The exact population objective produced by a bounded-variance construction witness. -/
def bvConstructedPopulation {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P) : PopulationObjective T :=
  populationFromLift C W.B W.LP W.lift_properties

/-- The exact oracle produced by a bounded-variance construction witness. -/
def bvConstructedOracle {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P) : StochasticOracle T Bool :=
  liftedOracle W.B W.LP

/-- Complete conclusions of Lemma 3.2 for the *specific* constructed instance. -/
structure Lemma32Conclusion {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : BVParameters) (W : BVConstructionWitness C P)
    (c₁ cκLo cκHi : ℝ) where
  base_certificate : BVBaseOracleCertificate T C P.p
  p_pos : 0 < P.p
  p_le_one : P.p ≤ 1
  ncsc : InNCSCClass (bvConstructedPopulation W) P.L P.μ P.Δ
  unbiased : OracleUnbiased (bvConstructedPopulation W) (bernoulliLaw P.p)
    (bvConstructedOracle W)
  bounded_variance : OracleBoundedVariance (bvConstructedPopulation W)
    (bernoulliLaw P.p) (bvConstructedOracle W) P.σ
  chain_floor :
    (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1
  T_ge_eight : 8 ≤ T
  chain_length : c₁ * (P.L * P.Δ / P.ε ^ 2) ≤ T
  inv_p_exact : BVInvPScalingExact P.p P.κ P.σ P.ε
  actual : ActualConditionNumberCertificate (bvConstructedPopulation W)
  actual_condition_number :
    cκLo * P.κ ≤ actual.Mlo / actual.muHi ∧
      actual.Mhi / actual.muLo ≤ cκHi * P.κ

/-- Lemma 3.2 with universal constants outside problem parameters and with the hard instance
forced to be the lift of the explicit chain with oracle (16). -/
def Lemma32Statement : Prop :=
  ∃ c₀ c₁ cκLo cκHi : ℝ,
    0 < c₀ ∧ 0 < c₁ ∧ 0 < cκLo ∧ 0 < cκHi ∧
    ∀ (P : BVParameters), 8 ≤ P.κ → P.ε ^ 2 ≤ c₀ * P.L * P.Δ →
      ∃ (T : ℕ) (C : ExplicitZeroChainCertificate T)
        (W : BVConstructionWitness C P),
        Nonempty (Lemma32Conclusion C P W c₁ cκLo cκHi)

/-! ### Section 4.1: equations (20)--(24) and Lemma 4.1 -/

/-- Paper's compactly supported bump `Λ`. -/
def LambdaGate (s : ℝ) : ℝ :=
  if 1 / 4 < s ∧ s < 1 / 2 then
    Real.exp (-1 / (100 * (s - 1 / 4) * (1 / 2 - s)))
  else 0

/-- Paper smooth step `Γ`. -/
noncomputable def GammaGate (t : ℝ) : ℝ :=
  (∫ s in (1 / 4 : ℝ)..t, LambdaGate s) /
    (∫ s in (1 / 4 : ℝ)..(1 / 2 : ℝ), LambdaGate s)

/-- Coordinatewise gated tail used in `Θᵢ`. -/
noncomputable def gatedTail {T : ℕ} (u : Vec T) (i : Fin T) : Vec T :=
  fun j => if i.1 ≤ j.1 then GammaGate |u j| else 0

/-- Paper definition of `Θᵢ(u)`. -/
noncomputable def ThetaGate {T : ℕ} (u : Vec T) (i : Fin T) : ℝ :=
  GammaGate (1 - ‖gatedTail u i‖)

/-- Equation (20) and the smooth-step properties used by the proof. -/
structure SmoothGateCertificate (mΓ : ℝ) where
  mΓ_nonneg : 0 ≤ mΓ
  gamma_zero : ∀ t, t ≤ 1 / 4 → GammaGate t = 0
  gamma_one : ∀ t, 1 / 2 ≤ t → GammaGate t = 1
  gamma_range : ∀ t, 0 ≤ GammaGate t ∧ GammaGate t ≤ 1
  gamma_lipschitz : ∀ s t, |GammaGate s - GammaGate t| ≤ mΓ * |s - t|
  theta_sandwich : ∀ {T : ℕ} (u : Vec T) (i : Fin T),
    (if prog (1 / 4) u < i.1 + 1 then (1 : ℝ) else 0) ≤ ThetaGate u i ∧
    ThetaGate u i ≤ (if prog (1 / 2) u < i.1 + 1 then (1 : ℝ) else 0)

/-- The paper's fixed universal `s₀`, determined once the universal Lipschitz constant `mΓ`
is fixed.  Equation (24) specifies its square. -/
noncomputable def universalS0 (mΓ : ℝ) : ℝ := Real.sqrt (4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2)

/-- Paper equation (21), exactly. -/
noncomputable def asBaseOracle {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) : Vec T :=
  fun i => (C.gradF u) i *
    (1 + ThetaGate u i * (bernoulliZ Z / p - 1))

/-- Lemma 4.1 statement, including equations (22)--(24). -/
structure ASBaseOracleCertificate (T : ℕ) (C : ExplicitZeroChainCertificate T)
    (p mΓ s₀ : ℝ) (Gate : SmoothGateCertificate mΓ) where
  p_pos : 0 < p
  p_le_one : p ≤ 1
  law_valid : LawAxioms (bernoulliLaw p)
  s0sq : s₀ ^ 2 = 4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2
  unbiased : ∀ u,
    bernoulliExpectVec p (fun Z => asBaseOracle C p u Z) = C.gradF u
  probability_zero_chain :
    ProbabilityPZeroChain (bernoulliLaw p)
      (asBaseOracle C p) p
  variance : ∀ u,
    bernoulliExpectReal p (fun Z => ‖asBaseOracle C p u Z - C.gradF u‖ ^ 2) ≤
      g₀ ^ 2 * (1 - p) / p
  averaged_smooth : ∀ u v,
    bernoulliExpectReal p (fun Z => ‖asBaseOracle C p u Z - asBaseOracle C p v Z‖ ^ 2) ≤
      s₀ ^ 2 / p * ‖u - v‖ ^ 2

/-! ### Section 4.2: corrected `p` semantics and Lemma 4.3 -/

/-- Exact version of equation (27).  In particular, `σ=0` gives `p=1`, rather than Lean's
`ε²/(κ·0)=0` artefact. -/
def ASPScalingExact (p κ σ ε : ℝ) : Prop :=
  (σ = 0 ∧ p = 1) ∨
  (σ ≠ 0 ∧ p = min 1 (16 * g₀ ^ 2 * ε ^ 2 / (κ * σ ^ 2)))

/-- Exact witness tying Lemma 4.3 to equations (8)--(10), (21), and (25)--(26). -/
structure ASConstructionWitness {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : ASParameters) where
  LP : LiftParameters
  lift_mu : LP.μ = P.μ
  lift_h : LP.h = P.h
  lift_q : LP.q = P.q
  lift_gamma : LP.γ = P.γ
  B : BaseOracle T
  base_oracle_def : ∀ u Z, B.g u Z = asBaseOracle C P.p u Z
  lift_properties : LiftPropertiesCertificate T C B LP

/-- The exact population objective produced by an averaged-smooth construction witness. -/
def asConstructedPopulation {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) : PopulationObjective T :=
  populationFromLift C W.B W.LP W.lift_properties

/-- The exact oracle produced by an averaged-smooth construction witness. -/
def asConstructedOracle {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) : StochasticOracle T Bool :=
  liftedOracle W.B W.LP

/-- Complete conclusions of Lemma 4.3 for the specific construction. -/
structure Lemma43Conclusion {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : ASParameters) (W : ASConstructionWitness C P)
    (mΓ : ℝ) (Gate : SmoothGateCertificate mΓ)
    (c₂ cκLo cκHi : ℝ) where
  base_certificate : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate
  p_pos : 0 < P.p
  p_le_one : P.p ≤ 1
  fixed_s0 : P.s₀ = universalS0 mΓ
  ncsc : InNCSCClass (asConstructedPopulation W) P.Lbar P.μ P.Δ
  strong_concavity : StronglyConcaveY (asConstructedPopulation W) P.μ
  unbiased : OracleUnbiased (asConstructedPopulation W) (bernoulliLaw P.p)
    (asConstructedOracle W)
  variance : OracleBoundedVariance (asConstructedPopulation W)
    (bernoulliLaw P.p) (asConstructedOracle W) P.σ
  averaged_smooth : OracleAveragedSmooth
    (bernoulliLaw P.p) (asConstructedOracle W) P.Lbar
  initial_gap : InitialGap (asConstructedPopulation W) P.Δ
  chain_floor :
    (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1
  T_ge_eight : 8 ≤ T
  eq29 : c₂ * (P.Lbar * P.Δ / P.ε ^ 2) *
    min 1 (P.κ * Real.sqrt P.p) ≤ T
  eq30 : c₂ * (P.Lbar * P.Δ / P.ε ^ 2) *
    min (1 / P.p) (P.κ / Real.sqrt P.p) ≤ (T : ℝ) / P.p
  p_scaling : ASPScalingExact P.p P.κ P.σ P.ε
  actual : ActualAveragedConditionNumberCertificate (asConstructedPopulation W)
    (bernoulliLaw P.p) (asConstructedOracle W)
  actual_condition_number :
    cκLo * P.κ ≤ actual.LbarLo / actual.muHi ∧
      actual.LbarHi / actual.muLo ≤ cκHi * P.κ

/-- Lemma 4.3 with `mΓ` and hence `s₀` fixed universally before all problem parameters. -/
def Lemma43Statement : Prop :=
  ∃ mΓ s₀ c₀ c₁ c₂ cκLo cκHi : ℝ,
    ∃ Gate : SmoothGateCertificate mΓ,
      0 < s₀ ∧ s₀ = universalS0 mΓ ∧
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < cκLo ∧ 0 < cκHi ∧
      ∀ (P : ASParameters), P.s₀ = s₀ → 0 ≤ P.σ → 8 ≤ P.κ →
        P.ε ^ 2 ≤ c₀ * P.Lbar * P.Δ →
        P.ε * P.σ ≤ c₁ * P.Lbar * P.Δ * Real.sqrt P.κ →
        ∃ (T : ℕ) (C : ExplicitZeroChainCertificate T)
          (W : ASConstructionWitness C P),
          Nonempty (Lemma43Conclusion C P W mΓ Gate c₂ cκLo cκHi)

/-! ### Theorems 3.3 and 4.4 with algorithm/risk quantifiers restored -/

/-- Match a bounded-variance parameter record to the theorem's external parameters. -/
def BVParameterMatch (P : BVParameters) (L μ Δ σ ε : ℝ) : Prop :=
  P.L = L ∧ P.μ = μ ∧ P.Δ = Δ ∧ P.σ = σ ∧ P.ε = ε

/-- Match an averaged-smooth parameter record to the theorem's external parameters. -/
def ASParameterMatch (P : ASParameters) (Lbar μ Δ σ ε s₀ : ℝ) : Prop :=
  P.Lbar = Lbar ∧ P.μ = μ ∧ P.Δ = Δ ∧ P.σ = σ ∧ P.ε = ε ∧ P.s₀ = s₀

/-- Paper Theorem 3.3 with the fixed hard instance tied to equations (8)--(10), (16), and
(17)--(18), and with algorithms represented by response-causal pair-zero-respecting runs. -/
def Theorem33Statement : Prop :=
  ∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧
    ∀ (K : ℕ), 0 < K →
    ∀ (L μ Δ σ ε : ℝ), 0 < L → 0 < μ → 0 < ε → 0 ≤ σ → 0 ≤ Δ →
      8 ≤ L / μ → ε ^ 2 ≤ c₀ * L * Δ →
      ∃ (P : BVParameters) (T : ℕ) (C : ExplicitZeroChainCertificate T)
        (W : BVConstructionWitness C P),
        BVParameterMatch P L μ Δ σ ε ∧
        Nonempty (BVBaseOracleCertificate T C P.p) ∧
        InNCSCClass (bvConstructedPopulation W) L μ Δ ∧
        OracleUnbiased (bvConstructedPopulation W) (bernoulliLaw P.p)
          (bvConstructedOracle W) ∧
        OracleBoundedVariance (bvConstructedPopulation W) (bernoulliLaw P.p)
          (bvConstructedOracle W) σ ∧
        BVInvPScalingExact P.p (L / μ) σ ε ∧
        ∀ (R : ℕ) (A : BernoulliRun T R K (bvConstructedOracle W)),
          (∀ w, ValidBatchSizes (A.trace w)) →
          stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ ε ^ 2 →
          c * bvRate L Δ ε (L / μ) σ ≤ (R : ℝ) ∧
          ∀ w, c * bvRate L Δ ε (L / μ) σ ≤
            (returnedGradientCount (A.trace w) : ℝ)

/-- Paper Theorem 4.4 with the universal smooth gate fixed before problem parameters and the
hard instance tied to equations (8)--(10), (21), and (25)--(26). -/
def Theorem44Statement : Prop :=
  ∃ c c₀ c₁ mΓ s₀ : ℝ,
    ∃ Gate : SmoothGateCertificate mΓ,
      0 < c ∧ 0 < c₀ ∧ 0 < c₁ ∧ 0 < s₀ ∧ s₀ = universalS0 mΓ ∧
      ∀ (K : ℕ), 0 < K →
      ∀ (Lbar μ Δ σ ε : ℝ),
        0 < Lbar → 0 < μ → 0 < ε → 0 ≤ σ → 0 ≤ Δ →
        8 ≤ Lbar / μ →
        ε ^ 2 ≤ c₀ * Lbar * Δ →
        ε * σ ≤ c₁ * Lbar * Δ * Real.sqrt (Lbar / μ) →
        ∃ (P : ASParameters) (T : ℕ) (C : ExplicitZeroChainCertificate T)
          (W : ASConstructionWitness C P),
          ASParameterMatch P Lbar μ Δ σ ε s₀ ∧
          Nonempty (ASBaseOracleCertificate T C P.p mΓ s₀ Gate) ∧
          InNCSCClass (asConstructedPopulation W) Lbar μ Δ ∧
          OracleUnbiased (asConstructedPopulation W) (bernoulliLaw P.p)
            (asConstructedOracle W) ∧
          OracleBoundedVariance (asConstructedPopulation W) (bernoulliLaw P.p)
            (asConstructedOracle W) σ ∧
          OracleAveragedSmooth (bernoulliLaw P.p) (asConstructedOracle W) Lbar ∧
          ASPScalingExact P.p (Lbar / μ) σ ε ∧
          ∀ (R : ℕ) (A : BernoulliRun T R K (asConstructedOracle W)),
            (∀ w, ValidBatchSizes (A.trace w)) →
            stationarityRisk P.p (asConstructedPopulation W).gradPhi A ≤ ε ^ 2 →
            c * asChainRate Lbar Δ ε (Lbar / μ) P.p ≤ (R : ℝ) ∧
            ∀ w, c * asChainRate Lbar Δ ε (Lbar / μ) P.p ≤
              (returnedGradientCount (A.trace w) : ℝ)

/-- Equation (32), as the mixed stochastic branch stated by the paper. -/
def Equation32Statement (R Lbar Δ ε κ σ c : ℝ) : Prop :=
  c * asMixedRate Lbar Δ ε κ σ ≤ R

/-! ### Proposition 4.6: Gaussian-location statement and algorithm-to-statistic reduction -/

/-- The one-dimensional population objective used in Proposition 4.6. -/
def gaussianLocationF (Lbar μ θ x y : ℝ) : ℝ :=
  Lbar / 2 * (x - θ) ^ 2 - μ / 2 * y ^ 2

/-- Its value function. -/
def gaussianLocationPhi (Lbar θ x : ℝ) : ℝ :=
  Lbar / 2 * (x - θ) ^ 2

/-- The exact deterministic gradient used in the risk reduction. -/
def gaussianLocationGradPhi (Lbar θ x : ℝ) : ℝ := Lbar * (x - θ)

/-- Paper's two-point separation parameter `a = 4ε/L̄`. -/
def gaussianA (Lbar ε : ℝ) : ℝ := 4 * ε / Lbar

/-- Gaussian-location stochastic oracle used in Proposition 4.6. -/
def gaussianOracleX (Lbar θ x ζ : ℝ) : ℝ := Lbar * (x - θ) + ζ

def gaussianOracleY (μ y : ℝ) : ℝ := - μ * y

/-- Nonnegative variance parameter passed to Mathlib's genuine Gaussian measure. -/
def gaussianVariance (σ : ℝ) : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩

/-- The actual scalar noise law `N(0,σ²)` used in Proposition 4.6. -/
noncomputable def gaussianNoiseMeasure (σ : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (gaussianVariance σ)

/-- The one-round sufficient statistic law after subtracting the known term `L̄ x`. -/
noncomputable def gaussianStatisticMeasure (Lbar θ σ : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal (-Lbar * θ) (gaussianVariance σ)

/-- Convert a genuine Mathlib measure into the expectation/probability interface used by the
oracle-class definitions.  No global `LawAxioms` are imposed here: Gaussian facts are stated
only for the measurable/integrable quantities actually used in Proposition 4.6. -/
noncomputable def measureLaw {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) : Law Ω where
  expectReal := fun X => ∫ ω, X ω ∂μ
  expectVec := fun X => ∫ ω, X ω ∂μ
  probability := fun A => (μ A).toReal

/-- Gaussian noise law in the generic oracle interface. -/
noncomputable def gaussianLaw (σ : ℝ) : Law ℝ := measureLaw (gaussianNoiseMeasure σ)

/-- The sole coordinate of `Vec 1`. -/
def scalarOfVec1 (x : Vec 1) : ℝ := x ⟨0, by decide⟩

/-- Embed a scalar into the one-dimensional Euclidean space. -/
def vecOfScalar1 (x : ℝ) : Vec 1 := fun _ => x

/-- Exact class membership and oracle identification for the two one-dimensional family members in
Proposition 4.6.  In v10 the Gaussian interface no longer asks for finite additivity or integral
linearity on *all* sets/functions; it records only the concrete Gaussian facts the proof uses. -/
structure GaussianFamilyCertificate (Lbar μ Δ σ ε : ℝ) where
  plusI : PopulationObjective 1
  minusI : PopulationObjective 1
  plusO : StochasticOracle 1 ℝ
  minusO : StochasticOracle 1 ℝ
  plus_f_def : ∀ x y, plusI.f x y =
    gaussianLocationF Lbar μ (gaussianA Lbar ε) (scalarOfVec1 x) (scalarOfVec1 y)
  minus_f_def : ∀ x y, minusI.f x y =
    gaussianLocationF Lbar μ (-gaussianA Lbar ε) (scalarOfVec1 x) (scalarOfVec1 y)
  plus_phi_def : ∀ x, plusI.Phi x =
    gaussianLocationPhi Lbar (gaussianA Lbar ε) (scalarOfVec1 x)
  minus_phi_def : ∀ x, minusI.Phi x =
    gaussianLocationPhi Lbar (-gaussianA Lbar ε) (scalarOfVec1 x)
  plus_gradPhi_def : ∀ x, plusI.gradPhi x =
    vecOfScalar1 (gaussianLocationGradPhi Lbar (gaussianA Lbar ε) (scalarOfVec1 x))
  minus_gradPhi_def : ∀ x, minusI.gradPhi x =
    vecOfScalar1 (gaussianLocationGradPhi Lbar (-gaussianA Lbar ε) (scalarOfVec1 x))
  plus_oracle_x_def : ∀ x y ζ, plusO.Gx x y ζ =
    vecOfScalar1 (gaussianOracleX Lbar (gaussianA Lbar ε) (scalarOfVec1 x) ζ)
  minus_oracle_x_def : ∀ x y ζ, minusO.Gx x y ζ =
    vecOfScalar1 (gaussianOracleX Lbar (-gaussianA Lbar ε) (scalarOfVec1 x) ζ)
  plus_oracle_y_def : ∀ x y ζ, plusO.Gy x y ζ =
    vecOfScalar1 (gaussianOracleY μ (scalarOfVec1 y))
  minus_oracle_y_def : ∀ x y ζ, minusO.Gy x y ζ =
    vecOfScalar1 (gaussianOracleY μ (scalarOfVec1 y))
  plus_ncsc : InNCSCClass plusI Lbar μ Δ
  minus_ncsc : InNCSCClass minusI Lbar μ Δ
  plus_unbiased : OracleUnbiased plusI (gaussianLaw σ) plusO
  minus_unbiased : OracleUnbiased minusI (gaussianLaw σ) minusO
  plus_variance : OracleBoundedVariance plusI (gaussianLaw σ) plusO σ
  minus_variance : OracleBoundedVariance minusI (gaussianLaw σ) minusO σ
  plus_averaged_smooth : OracleAveragedSmooth (gaussianLaw σ) plusO Lbar
  minus_averaged_smooth : OracleAveragedSmooth (gaussianLaw σ) minusO Lbar
  noise_probability : gaussianNoiseMeasure σ Set.univ = 1
  initial_gap_value :
    Lbar * (gaussianA Lbar ε) ^ 2 / 2 = 8 * ε ^ 2 / Lbar
  initial_gap_bound : Lbar * (gaussianA Lbar ε) ^ 2 / 2 ≤ Δ
  noise_mean_zero : (∫ ζ : ℝ, ζ ∂(gaussianNoiseMeasure σ)) = 0
  noise_second_moment : (∫ ζ : ℝ, ζ ^ 2 ∂(gaussianNoiseMeasure σ)) = σ ^ 2
  same_seed_difference : ∀ x x' θ ζ,
    gaussianOracleX Lbar θ x ζ - gaussianOracleX Lbar θ x' ζ = Lbar * (x - x')

/-- A genuine two-point transcript model for the sufficient statistics `S_t`.
The two measures are probability measures; each coordinate has the paper's Gaussian location law,
and the round coordinates are independent. -/
structure GaussianTranscriptExperiment (R : ℕ) (Lbar a σ : ℝ) where
  plusMeasure : Measure (Fin R → ℝ)
  minusMeasure : Measure (Fin R → ℝ)
  plus_probability : plusMeasure Set.univ = 1
  minus_probability : minusMeasure Set.univ = 1
  plus_marginal : ∀ t : Fin R,
    Measure.map (fun s : Fin R → ℝ => s t) plusMeasure =
      gaussianStatisticMeasure Lbar a σ
  minus_marginal : ∀ t : Fin R,
    Measure.map (fun s : Fin R → ℝ => s t) minusMeasure =
      gaussianStatisticMeasure Lbar (-a) σ
  plus_independent : ProbabilityTheory.iIndepFun
    (fun t : Fin R => fun s : Fin R → ℝ => s t) plusMeasure
  minus_independent : ProbabilityTheory.iIndepFun
    (fun t : Fin R => fun s : Fin R → ℝ => s t) minusMeasure
  KL_value : (InformationTheory.klDiv plusMeasure minusMeasure).toReal =
    (R : ℝ) * (2 * Lbar * a) ^ 2 / (2 * σ ^ 2)

/-- A measurable estimator/test based on the `R` sufficient statistics. -/
structure MeasurableEstimator (R : ℕ) where
  toFun : (Fin R → ℝ) → ℝ
  measurable_toFun : Measurable toFun

/-- Average probability of inferring the wrong sign from a measurable estimator of `x`. -/
noncomputable def gaussianAverageSignError {R : ℕ} {Lbar a σ : ℝ}
    (E : GaussianTranscriptExperiment R Lbar a σ)
    (A : MeasurableEstimator R) : ℝ :=
  ((E.plusMeasure {s | A.toFun s * a ≤ 0}).toReal +
    (E.minusMeasure {s | A.toFun s * (-a) ≤ 0}).toReal) / 2

/-- Squared stationarity risk of an estimator, written as a nonnegative extended integral so that
non-integrable estimators correctly have infinite risk rather than Lean's totalized ordinary
integral value. -/
noncomputable def gaussianEstimatorRisk {R : ℕ} {Lbar a σ : ℝ}
    (E : GaussianTranscriptExperiment R Lbar a σ)
    (positive : Bool) (A : MeasurableEstimator R) : ENNReal :=
  if positive then
    ∫⁻ s, ENNReal.ofReal ((Lbar * (A.toFun s - a)) ^ 2) ∂E.plusMeasure
  else
    ∫⁻ s, ENNReal.ofReal ((Lbar * (A.toFun s + a)) ^ 2) ∂E.minusMeasure

/-- A run indexed directly by the sufficient-statistic sequence.  For parameter `θ`, the actual
Gaussian oracle noise in round `t` is recovered as `ζ_t = S_t + L̄ θ`.  Queries and the final
output are response-causal, so the run cannot inspect the hidden statistic/noise except through
oracle responses. -/
structure GaussianStatisticRun (R K : ℕ) (O : StochasticOracle 1 ℝ)
    (Lbar θ : ℝ) where
  trace : (Fin R → ℝ) → InteractionTrace 1 R K
  causal_queries : ∀ s s' t,
    (∀ r : Fin R, r.1 < t.1 → ∀ k : Fin K,
      (trace s).response r k = (trace s').response r k) →
    (trace s).query t = (trace s').query t
  causal_output : ∀ s s',
    (∀ t : Fin R, ∀ k : Fin K,
      (trace s).response t k = (trace s').response t k) →
    (trace s).output = (trace s').output
  response_consistent : ∀ s,
    OracleConsistentTrace O (fun t => s t + Lbar * θ) (trace s)
  output_measurable : Measurable (fun s => scalarOfVec1 ((trace s).output))

/-- The plus/minus interactions are executions of the same response-causal algorithm.  The cross
conditions rule out choosing a different policy after learning which hidden family member is in
force. -/
structure GaussianTwoPointRun (R K : ℕ) (Lbar a : ℝ)
    (plusO minusO : StochasticOracle 1 ℝ) where
  plus : GaussianStatisticRun R K plusO Lbar a
  minus : GaussianStatisticRun R K minusO Lbar (-a)
  shared_queries : ∀ sp sm t,
    (∀ r : Fin R, r.1 < t.1 → ∀ k : Fin K,
      (plus.trace sp).response r k = (minus.trace sm).response r k) →
    (plus.trace sp).query t = (minus.trace sm).query t
  shared_output : ∀ sp sm,
    (∀ t : Fin R, ∀ k : Fin K,
      (plus.trace sp).response t k = (minus.trace sm).response t k) →
    (plus.trace sp).output = (minus.trace sm).output

/-- Actual squared stationarity risk of a legal two-point algorithm run, evaluated with the
`gradPhi` fields of the two concrete population objectives.  This is the direct formal analogue of
`E ‖∇Φ(x̂)‖²` in Proposition 4.6. -/
noncomputable def gaussianRunRisk {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO)
    (positive : Bool) : ENNReal :=
  if positive then
    ∫⁻ s, ENNReal.ofReal
      (‖F.plusI.gradPhi ((A.plus.trace s).output)‖ ^ 2) ∂E.plusMeasure
  else
    ∫⁻ s, ENNReal.ofReal
      (‖F.minusI.gradPhi ((A.minus.trace s).output)‖ ^ 2) ∂E.minusMeasure


/-- v43 wrapper for an algorithm with an explicit internal random seed `ω`.  For each fixed
seed realization the algorithm is a legal shared plus/minus response-causal run.  The two risk
functions are required to be measurable in the internal seed; this is the minimal measurability
condition needed to average the conditional risks.  The same seed law is used under both hidden
instances, so the internal randomness is independent of the choice `θ = ±a`. -/
structure GaussianInternalRandomRun (Ω : Type*) [MeasurableSpace Ω]
    (ρ : Measure Ω) {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ) where
  run : Ω → GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO
  plus_risk_measurable :
    Measurable (fun ω => gaussianRunRisk F E (run ω) true)
  minus_risk_measurable :
    Measurable (fun ω => gaussianRunRisk F E (run ω) false)

/-- Squared-stationarity risk after averaging over both the oracle transcript and the algorithm's
independent internal seed. -/
noncomputable def gaussianInternalRandomRisk {Ω : Type*} [MeasurableSpace Ω]
    {R K : ℕ} {Lbar μ Δ σ ε : ℝ} (ρ : Measure Ω)
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (A : GaussianInternalRandomRun Ω ρ (R := R) (K := K) F E)
    (positive : Bool) : ENNReal :=
  ∫⁻ ω, gaussianRunRisk F E (A.run ω) positive ∂ρ

/-- The paper's key reduction: after subtracting the known `L̄x` term, one same-seed batch reveals
only the scalar statistic `S_t`.  Hence one *single measurable estimator* of the `R` statistics
reproduces the output under both signs.  Risk equalities explicitly connect the statistical
experiment back to the original oracle algorithm. -/
structure GaussianAlgorithmToStatisticReduction {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO) where
  estimator : MeasurableEstimator R
  plus_output : ∀ s,
    scalarOfVec1 ((A.plus.trace s).output) = estimator.toFun s
  minus_output : ∀ s,
    scalarOfVec1 ((A.minus.trace s).output) = estimator.toFun s
  plus_risk_eq : gaussianRunRisk F E A true = gaussianEstimatorRisk E true estimator
  minus_risk_eq : gaussianRunRisk F E A false = gaussianEstimatorRisk E false estimator

/-- Statistical ingredients in Proposition 4.6, now attached to the actual Gaussian transcript
measures and quantified only over measurable estimators. -/
structure GaussianLocationProofCertificate
    (R : ℕ) (Lbar σ ε : ℝ) where
  Lbar_pos : 0 < Lbar
  epsilon_pos : 0 < ε
  sigma_pos : 0 < σ
  experiment : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ
  mean_separation : 2 * Lbar * gaussianA Lbar ε = 8 * ε
  KL_formula :
    (InformationTheory.klDiv experiment.plusMeasure experiment.minusMeasure).toReal =
      (R : ℝ) * (8 * ε) ^ 2 / (2 * σ ^ 2)
  pinsker_sign_error : ∀ A : MeasurableEstimator R,
    1 / 4 ≤ gaussianAverageSignError experiment A
  wrong_sign_gradient : ∀ x θ,
    (θ = gaussianA Lbar ε ∨ θ = -gaussianA Lbar ε) → x * θ ≤ 0 →
      4 * ε ≤ |gaussianLocationGradPhi Lbar θ x|
  risk_endpoint : ε ^ 2 < (1 / 4 : ℝ) * (4 * ε) ^ 2
  every_estimator : ∀ A : MeasurableEstimator R,
    ENNReal.ofReal (ε ^ 2) <
      max (gaussianEstimatorRisk experiment true A)
        (gaussianEstimatorRisk experiment false A)

/-- Paper Proposition 4.6 with the missing algorithm-to-statistic reduction restored.  For every
legal same-seed adaptive algorithm (represented by one shared plus/minus response-causal run), a
single measurable estimator of the `R` Gaussian sufficient statistics reproduces both outputs, and
therefore at least one member of the two-point NCSC family has stationarity risk above `ε²`. -/
def Proposition46Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (Lbar μ Δ σ ε : ℝ),
      0 < Lbar → 0 < μ → μ ≤ Lbar → 0 < ε → 0 < σ →
      ε ^ 2 ≤ Lbar * Δ / 8 →
      ∃ F : GaussianFamilyCertificate Lbar μ Δ σ ε,
        ∀ R : ℕ, (R : ℝ) ≤ c * σ ^ 2 / ε ^ 2 →
          ∃ P : GaussianLocationProofCertificate R Lbar σ ε,
            ∀ (K : ℕ), 0 < K →
              ∀ A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO,
                ∃ Red : GaussianAlgorithmToStatisticReduction
                    (R := R) (K := K) (Lbar := Lbar) (μ := μ) (Δ := Δ)
                    (σ := σ) (ε := ε) F P.experiment A,
                  (ENNReal.ofReal (ε ^ 2) <
                    max (gaussianEstimatorRisk P.experiment true Red.estimator)
                      (gaussianEstimatorRisk P.experiment false Red.estimator)) ∧
                  ENNReal.ofReal (ε ^ 2) <
                    max (gaussianRunRisk F P.experiment A true)
                      (gaussianRunRisk F P.experiment A false)


universe uΩ

/-- v43 paper-exact randomized form of Proposition 4.6.  Unlike the deterministic-response-causal
statement above, this version quantifies an arbitrary measurable internal seed space and probability
law.  Each seed realization is a legal response-causal algorithm, and the final risk is averaged
over that independent internal randomness. -/
def Proposition46RandomizedStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (Lbar μ Δ σ ε : ℝ),
      0 < Lbar → 0 < μ → μ ≤ Lbar → 0 < ε → 0 < σ →
      ε ^ 2 ≤ Lbar * Δ / 8 →
      ∃ F : GaussianFamilyCertificate Lbar μ Δ σ ε,
        ∀ R : ℕ, (R : ℝ) ≤ c * σ ^ 2 / ε ^ 2 →
          ∃ P : GaussianLocationProofCertificate R Lbar σ ε,
            ∀ (Ω : Type uΩ) [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ],
              ∀ (K : ℕ), 0 < K →
                ∀ A : GaussianInternalRandomRun Ω ρ (R := R) (K := K) F P.experiment,
                  ENNReal.ofReal (ε ^ 2) <
                    max (gaussianInternalRandomRisk ρ F P.experiment A true)
                      (gaussianInternalRandomRisk ρ F P.experiment A false)

/-- Equation (32) as an explicit consequence schema of the chain rate together with the exact
`p`-scaling on the stochastic branch `p<1`.  The universal constants are quantified before all
problem parameters. -/
def Equation32ConsequenceStatement : Prop :=
  ∃ cChain cMixed : ℝ, 0 < cChain ∧ 0 < cMixed ∧
    ∀ (R Lbar Δ ε κ σ p : ℝ),
      0 < Lbar → 0 ≤ Δ → 0 < ε → 0 < κ → 0 < σ → 0 < p → p < 1 →
      ASPScalingExact p κ σ ε →
      cChain * asChainRate Lbar Δ ε κ p ≤ R →
      cMixed * asMixedRate Lbar Δ ε κ σ ≤ R

/-- Paper Remark 4.5 piecewise interpretation, using `κ * √κ` for `κ^{3/2}`.  The two
thresholds are the nominal regime boundaries; universal-constant slack is carried by the
consequence statement below. -/
def asPiecewiseRate (Lbar Δ ε κ σ : ℝ) : ℝ :=
  if σ ≤ ε / Real.sqrt κ then
    Lbar * Δ / ε ^ 2
  else if σ ≤ Real.sqrt κ * ε then
    Lbar * Δ * κ * σ ^ 2 / ε ^ 4
  else
    Lbar * Δ * κ * Real.sqrt κ * σ / ε ^ 3

/-- Remark 4.5 as a universal-constant consequence of the exact `p` scaling and chain rate. -/
def Remark45ConsequenceStatement : Prop :=
  ∃ cChain cPiece : ℝ, 0 < cChain ∧ 0 < cPiece ∧
    ∀ (R Lbar Δ ε κ σ p : ℝ),
      0 < Lbar → 0 ≤ Δ → 0 < ε → 0 < κ → 8 ≤ κ →
      0 ≤ σ → 0 < p → p ≤ 1 →
      ASPScalingExact p κ σ ε →
      cChain * asChainRate Lbar Δ ε κ p ≤ R →
      cPiece * asPiecewiseRate Lbar Δ ε κ σ ≤ R

/-- Paper Remark 4.7: if worst-case complexity dominates the chain and independent estimation
lower bounds separately, it dominates their sum up to the factor two displayed in the paper. -/
theorem remark47_additive_combination
    (C chain estimation : ℝ) (hchain : chain ≤ C) (hest : estimation ≤ C) :
    (chain + estimation) / 2 ≤ C := by
  linarith

/-- Quantifier-level form of Remark 4.7. -/
def Remark47Statement : Prop :=
  ∀ (C chain estimation : ℝ),
    chain ≤ C → estimation ≤ C → (chain + estimation) / 2 ≤ C

/-- Paper Remark 4.7, closed at its fully quantified statement. -/
theorem canonicalRemark47 : Remark47Statement :=
  remark47_additive_combination

/-! ### Section 5 exact scope -/

/-- Section 5 scope marker: the two chain theorems are pair-zero-respecting statements, while
Proposition 4.6 is the separate unrestricted response-causal Gaussian estimation lower bound. -/
def ScopeStatement : Prop :=
  Theorem33Statement ∧ Theorem44Statement ∧ Proposition46Statement

/-- v43 strengthened scope: the two chain theorems plus Proposition 4.6 with explicit internal
algorithmic randomness.  The legacy `ScopeStatement` is retained for backwards compatibility. -/
def ScopeStatementV43 : Prop :=
  Theorem33Statement ∧ Theorem44Statement ∧ Proposition46RandomizedStatement.{uΩ}


/-! ## v11 proof-completion layer: core lemmas, phase I

This section starts replacing statement/certificate-only obligations by actual Lean proofs.
It deliberately proves only facts that follow directly from the definitions and the imported
Lemma-2.1 certificate.  No `sorry`, `admit`, or new axiom is introduced.
-/

/-- Section 1.2: the bookkeeping identity `R ≤ N ≤ K R` is now an actual theorem. -/
theorem gradientCountAccounting : GradientCountAccountingStatement := by
  intro T R K tr hvalid
  constructor
  · calc
      R = ∑ _t : Fin R, 1 := by simp
      _ ≤ ∑ t : Fin R, batchSize tr t := by
        exact Finset.sum_le_sum fun t _ => (hvalid t).1
      _ = returnedGradientCount tr := rfl
  · calc
      returnedGradientCount tr = ∑ t : Fin R, batchSize tr t := rfl
      _ ≤ ∑ _t : Fin R, K := by
        exact Finset.sum_le_sum fun t _ => (hvalid t).2
      _ = K * R := by simp [Nat.mul_comm]

/-! ### Progress-index facts used in Lemma 3.1 -/

/-- If coordinate `i` lies strictly beyond `prog_a(u)`, then its magnitude is at most `a`. -/
theorem abs_coord_le_of_prog_lt {T : ℕ} (a : ℝ) (u : Vec T) (i : Fin T)
    (h : prog a u < i.1 + 1) : |u i| ≤ a := by
  by_contra hnot
  have ha : a < |u i| := lt_of_not_ge hnot
  have hib : i.1 + 1 ≤ T := Nat.succ_le_iff.mpr i.2
  have hle : i.1 + 1 ≤ prog a u := by
    unfold prog
    exact Nat.le_findGreatest hib ⟨i, rfl, ha⟩
  omega

/-- Zero-threshold specialization of `abs_coord_le_of_prog_lt`. -/
theorem coord_eq_zero_of_prog_lt {T : ℕ} (u : Vec T) (i : Fin T)
    (h : prog 0 u < i.1 + 1) : u i = 0 := by
  have habs_le : |u i| ≤ 0 := abs_coord_le_of_prog_lt 0 u i h
  have habs : |u i| = 0 := le_antisymm habs_le (abs_nonneg _)
  exact abs_eq_zero.mp habs

/-- Increasing the threshold can only decrease progress. -/
theorem prog_antitone_threshold {T : ℕ} (u : Vec T) {a b : ℝ} (hab : a ≤ b) :
    prog b u ≤ prog a u := by
  unfold prog
  exact Nat.findGreatest_mono_left (fun n hn => by
    rcases hn with ⟨i, hi, hb⟩
    exact ⟨i, hi, lt_of_le_of_lt hab hb⟩) T

/-- Converse support lemma: if every coordinate beyond `m` is zero then `prog_0 ≤ m`. -/
theorem prog_zero_le_of_zero_above {T : ℕ} (u : Vec T) (m : ℕ)
    (hzero : ∀ i : Fin T, m < i.1 + 1 → u i = 0) : prog 0 u ≤ m := by
  unfold prog
  by_contra hnot
  have hlt : m < Nat.findGreatest
      (fun n => ∃ i : Fin T, i.1 + 1 = n ∧ (0 : ℝ) < |u i|) T :=
    Nat.lt_of_not_ge hnot
  have hne : Nat.findGreatest
      (fun n => ∃ i : Fin T, i.1 + 1 = n ∧ (0 : ℝ) < |u i|) T ≠ 0 := by
    omega
  have hP : ∃ i : Fin T,
      i.1 + 1 = Nat.findGreatest
        (fun n => ∃ j : Fin T, j.1 + 1 = n ∧ (0 : ℝ) < |u j|) T ∧
      (0 : ℝ) < |u i| := by
    exact ((Nat.findGreatest_eq_iff).1 rfl).2.1 hne
  rcases hP with ⟨i, hi, hpos⟩
  have hm : m < i.1 + 1 := by omega
  rw [hzero i hm] at hpos
  simp at hpos

/-- Lemma 2.1(5) implies that the population gradient vanishes beyond the single
`1/4`-frontier coordinate. -/
theorem gradF_zero_beyond_quarter_frontier {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (u : Vec T) (i : Fin T)
    (hi : prog (1 / 4) u + 1 < i.1 + 1) : C.gradF u i = 0 := by
  have hmono : prog (1 / 2) u ≤ prog (1 / 4) u := by
    apply prog_antitone_threshold u
    norm_num
  have hprog : prog 0 (C.gradF u) < i.1 + 1 := by
    have hz := C.zero_chain u
    omega
  exact coord_eq_zero_of_prog_lt (C.gradF u) i hprog

/-! ### Bernoulli identities used in Lemmas 2.3, 3.1 and 4.1 -/

/-- `E[Z/p-1]=0` for `Z ~ Bernoulli(p)`. -/
theorem bernoulli_centered_mean (p : ℝ) (hp : p ≠ 0) :
    bernoulliExpectReal p (fun Z => bernoulliZ Z / p - 1) = 0 := by
  simp [bernoulliExpectReal, bernoulliZ, hp]
  field_simp [hp]

/-- `E[(Z/p-1)^2]=(1-p)/p`. -/
theorem bernoulli_centered_second_moment (p : ℝ) (hp : p ≠ 0) :
    bernoulliExpectReal p (fun Z => (bernoulliZ Z / p - 1) ^ 2) = (1 - p) / p := by
  simp [bernoulliExpectReal, bernoulliZ, hp]
  field_simp [hp]
  ring

/-- Explicit Bernoulli expectation is linear under scalar multiplication. -/
theorem bernoulliExpectReal_mul (p c : ℝ) (X : Bool → ℝ) :
    bernoulliExpectReal p (fun Z => c * X Z) = c * bernoulliExpectReal p X := by
  unfold bernoulliExpectReal
  ring

/-- Equation (16) is unbiased.  This is the first substantive field of paper Lemma 3.1. -/
theorem bvBaseOracle_unbiased {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (hp : p ≠ 0) (u : Vec T) :
    bernoulliExpectVec p (fun Z => bvBaseOracle C p u Z) = C.gradF u := by
  ext i
  simp [bernoulliExpectVec, bvBaseOracle, bernoulliZ]
  field_simp [hp]
  ring

/-- Equation (21) is unbiased.  This proves the unbiasedness field of paper Lemma 4.1,
independently of the smooth-gate estimates. -/
theorem asBaseOracle_unbiased {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (hp : p ≠ 0) (u : Vec T) :
    bernoulliExpectVec p (fun Z => asBaseOracle C p u Z) = C.gradF u := by
  ext i
  simp [bernoulliExpectVec, asBaseOracle, bernoulliZ, hp]
  field_simp [hp]
  ring

/-! ### Support part of Lemma 3.1 -/

/-- With `Z=0`, every coordinate above the current `1/4` progress is masked out. -/
theorem bvBaseOracle_false_zero_above {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (i : Fin T) (hi : prog (1 / 4) u < i.1 + 1) :
    bvBaseOracle C p u false i = 0 := by
  have hind : frontierIndicator u i = 1 := by
    unfold frontierIndicator
    rw [if_pos hi]
  rw [bvBaseOracle, hind]
  simp [bernoulliZ]

/-- For either Bernoulli outcome, no coordinate beyond the single frontier can appear. -/
theorem bvBaseOracle_zero_beyond_frontier {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) (i : Fin T)
    (hi : prog (1 / 4) u + 1 < i.1 + 1) :
    bvBaseOracle C p u Z i = 0 := by
  rw [bvBaseOracle]
  simp [gradF_zero_beyond_quarter_frontier C u i hi]

/-- On the `Z=0` branch the BV oracle cannot advance progress. -/
theorem bvBaseOracle_prog_false_le {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) :
    prog 0 (bvBaseOracle C p u false) ≤ prog (1 / 4) u := by
  apply prog_zero_le_of_zero_above
  intro i hi
  exact bvBaseOracle_false_zero_above C p u i hi

/-- On either branch the BV oracle can advance by at most one coordinate. -/
theorem bvBaseOracle_prog_le_succ {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) :
    prog 0 (bvBaseOracle C p u Z) ≤ prog (1 / 4) u + 1 := by
  apply prog_zero_le_of_zero_above
  intro i hi
  exact bvBaseOracle_zero_beyond_frontier C p u Z i hi

/-- The event-level probability-`p` zero-chain statement in Lemma 3.1. -/
theorem bvBaseOracle_probability_zero_chain {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    ProbabilityPZeroChain (bernoulliLaw p) (bvBaseOracle C p) p := by
  have hfalse : ¬ ∃ u : Vec T,
      prog 0 (bvBaseOracle C p u false) = prog (1 / 4) u + 1 := by
    intro h
    rcases h with ⟨u, hu⟩
    have hle := bvBaseOracle_prog_false_le C p u
    omega
  have hfar_true : ¬ ∃ u : Vec T,
      prog 0 (bvBaseOracle C p u true) > prog (1 / 4) u + 1 := by
    intro h
    rcases h with ⟨u, hu⟩
    have hle := bvBaseOracle_prog_le_succ C p u true
    omega
  have hfar_false : ¬ ∃ u : Vec T,
      prog 0 (bvBaseOracle C p u false) > prog (1 / 4) u + 1 := by
    intro h
    rcases h with ⟨u, hu⟩
    have hle := bvBaseOracle_prog_le_succ C p u false
    omega
  constructor
  · change bernoulliProb p (fun Z => ∃ u : Vec T,
      prog 0 (bvBaseOracle C p u Z) = prog (1 / 4) u + 1) ≤ p
    unfold bernoulliProb
    by_cases htrue : ∃ u : Vec T,
        prog 0 (bvBaseOracle C p u true) = prog (1 / 4) u + 1
    · rw [if_pos htrue, if_neg hfalse]
      simp
    · rw [if_neg htrue, if_neg hfalse]
      simpa using hp0
  · change bernoulliProb p (fun Z => ∃ u : Vec T,
      prog 0 (bvBaseOracle C p u Z) > prog (1 / 4) u + 1) = 0
    unfold bernoulliProb
    rw [if_neg hfar_true, if_neg hfar_false]
    ring



/-- Coordinate formula for the stochastic error of the BV oracle. -/
theorem bvBaseOracle_error_coord {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) (i : Fin T) :
    (bvBaseOracle C p u Z - C.gradF u) i =
      (C.gradF u) i * frontierIndicator u i * (bernoulliZ Z / p - 1) := by
  simp [bvBaseOracle]
  ring

/-- The unique possible stochastic frontier coordinate, when it lies in `[T]`. -/
def quarterFrontierIndex {T : ℕ} (u : Vec T) (h : prog (1 / 4) u < T) : Fin T :=
  ⟨prog (1 / 4) u, h⟩

/-- If the frontier lies inside the chain, the BV stochastic error is a one-coordinate vector. -/
theorem bvBaseOracle_error_eq_single {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) (hfront : prog (1 / 4) u < T) :
    bvBaseOracle C p u Z - C.gradF u =
      EuclideanSpace.single (quarterFrontierIndex u hfront)
        ((C.gradF u) (quarterFrontierIndex u hfront) * (bernoulliZ Z / p - 1)) := by
  ext i
  rw [bvBaseOracle_error_coord]
  by_cases hij : i = quarterFrontierIndex u hfront
  · subst i
    simp [frontierIndicator, quarterFrontierIndex]
  · have hneval : i.1 ≠ (quarterFrontierIndex u hfront).1 := by
      intro hval
      apply hij
      exact Fin.ext hval
    rcases lt_or_gt_of_ne hneval with hlt | hgt
    · have hle0 : i.1 + 1 ≤ (quarterFrontierIndex u hfront).1 :=
        Nat.succ_le_iff.mpr hlt
      have hle : i.1 + 1 ≤ prog (1 / 4) u := by
        simpa [quarterFrontierIndex] using hle0
      have hnot : ¬ prog (1 / 4) u < i.1 + 1 := Nat.not_lt.mpr hle
      have hind : frontierIndicator u i = 0 := by
        unfold frontierIndicator
        rw [if_neg hnot]
      rw [hind]
      simp [EuclideanSpace.single_apply, hij]
    · have hfar : prog (1 / 4) u + 1 < i.1 + 1 := by
        simpa [quarterFrontierIndex] using Nat.succ_lt_succ hgt
      have hgzero := gradF_zero_beyond_quarter_frontier C u i hfar
      simp [hgzero, EuclideanSpace.single_apply, hij]

/-- If the current `1/4` progress has already reached the end of the chain, the BV oracle is
fully deterministic. -/
theorem bvBaseOracle_error_eq_zero_of_frontier_full {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (u : Vec T) (Z : Bool)
    (hfront : ¬ prog (1 / 4) u < T) :
    bvBaseOracle C p u Z - C.gradF u = 0 := by
  have hprog_le : prog (1 / 4) u ≤ T := by
    unfold prog
    exact Nat.findGreatest_le T
  have hprog : prog (1 / 4) u = T := by omega
  ext i
  rw [bvBaseOracle_error_coord]
  have hi : i.1 + 1 ≤ T := Nat.succ_le_iff.mpr i.2
  have hnot : ¬ prog (1 / 4) u < i.1 + 1 := by omega
  have hind : frontierIndicator u i = 0 := by
    unfold frontierIndicator
    rw [if_neg hnot]
  simp [hind]

/-- Pointwise second-moment envelope used in Lemma 3.1. -/
theorem bvBaseOracle_error_norm_sq_le {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) :
    ‖bvBaseOracle C p u Z - C.gradF u‖ ^ 2 ≤
      g₀ ^ 2 * (bernoulliZ Z / p - 1) ^ 2 := by
  by_cases hfront : prog (1 / 4) u < T
  · rw [bvBaseOracle_error_eq_single C p u Z hfront,
        EuclideanSpace.norm_single, Real.norm_eq_abs, abs_mul, mul_pow]
    simp only [sq_abs]
    let j := quarterFrontierIndex u hfront
    have hg := C.grad_coord_bound u j
    have hg0 : 0 ≤ g₀ := by norm_num [g₀]
    have hprod : 0 ≤ (g₀ - |C.gradF u j|) * (g₀ + |C.gradF u j|) := by
      exact mul_nonneg (sub_nonneg.mpr hg) (add_nonneg hg0 (abs_nonneg _))
    have hsquare : (C.gradF u j) ^ 2 ≤ g₀ ^ 2 := by
      nlinarith [sq_abs (C.gradF u j)]
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  · rw [bvBaseOracle_error_eq_zero_of_frontier_full C p u Z hfront]
    simpa using mul_nonneg (sq_nonneg g₀) (sq_nonneg (bernoulliZ Z / p - 1))

/-- Equation (13)'s base-oracle calculation specialized to the explicit BV oracle: the exact
variance bound from paper Lemma 3.1. -/
theorem bvBaseOracle_variance {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (u : Vec T) :
    bernoulliExpectReal p (fun Z => ‖bvBaseOracle C p u Z - C.gradF u‖ ^ 2) ≤
      g₀ ^ 2 * (1 - p) / p := by
  have ht := bvBaseOracle_error_norm_sq_le C p u true
  have hf := bvBaseOracle_error_norm_sq_le C p u false
  have hpt := mul_le_mul_of_nonneg_left ht (le_of_lt hp0)
  have hpf := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hp1)
  calc
    bernoulliExpectReal p (fun Z => ‖bvBaseOracle C p u Z - C.gradF u‖ ^ 2)
        ≤ bernoulliExpectReal p (fun Z =>
            g₀ ^ 2 * (bernoulliZ Z / p - 1) ^ 2) := by
          unfold bernoulliExpectReal at ⊢
          linarith
    _ = g₀ ^ 2 * bernoulliExpectReal p (fun Z => (bernoulliZ Z / p - 1) ^ 2) := by
          exact bernoulliExpectReal_mul p (g₀ ^ 2)
            (fun Z => (bernoulliZ Z / p - 1) ^ 2)
    _ = g₀ ^ 2 * ((1 - p) / p) := by
          rw [bernoulli_centered_second_moment p (ne_of_gt hp0)]
    _ = g₀ ^ 2 * (1 - p) / p := by ring



/-- The concrete Bernoulli expectation/probability triple satisfies the elementary law axioms
used by the statement layer. -/
theorem bernoulliLaw_axioms (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    LawAxioms (bernoulliLaw p) := by
  classical
  refine
    { probability_nonneg := ?_
      probability_le_one := ?_
      probability_empty := ?_
      probability_univ := ?_
      probability_disjoint_union := ?_
      expect_indicator := ?_
      expect_const := ?_
      expect_add := ?_
      expect_smul := ?_
      expect_nonneg := ?_
      sq_expect_le_expect_sq := ?_
      expectVec_coord := ?_ }
  · intro A
    change 0 ≤ bernoulliProb p (fun z => z ∈ A)
    unfold bernoulliProb
    by_cases ht : true ∈ A <;> by_cases hf : false ∈ A <;>
      simp [ht, hf] <;> linarith
  · intro A
    change bernoulliProb p (fun z => z ∈ A) ≤ 1
    unfold bernoulliProb
    by_cases ht : true ∈ A <;> by_cases hf : false ∈ A <;>
      simp [ht, hf] <;> linarith
  · change bernoulliProb p (fun z => z ∈ (∅ : Set Bool)) = 0
    simp [bernoulliProb]
  · change bernoulliProb p (fun z => z ∈ (Set.univ : Set Bool)) = 1
    simp [bernoulliProb]
  · intro A B hdis
    change bernoulliProb p (fun z => z ∈ A ∪ B) =
      bernoulliProb p (fun z => z ∈ A) + bernoulliProb p (fun z => z ∈ B)
    have hdt : ¬ (true ∈ A ∧ true ∈ B) := by
      intro h
      exact Set.disjoint_left.1 hdis h.1 h.2
    have hdf : ¬ (false ∈ A ∧ false ∈ B) := by
      intro h
      exact Set.disjoint_left.1 hdis h.1 h.2
    unfold bernoulliProb
    by_cases hat : true ∈ A <;> by_cases haf : false ∈ A <;>
      by_cases hbt : true ∈ B <;> by_cases hbf : false ∈ B <;>
      simp_all [Set.mem_union]
  · intro A
    change bernoulliExpectReal p (A.indicator (fun _ => (1 : ℝ))) =
      bernoulliProb p (fun z => z ∈ A)
    unfold bernoulliExpectReal bernoulliProb
    by_cases ht : true ∈ A <;> by_cases hf : false ∈ A <;>
      simp [ht, hf]
  · intro c
    change bernoulliExpectReal p (fun _ : Bool => c) = c
    unfold bernoulliExpectReal
    ring
  · intro X Y
    change bernoulliExpectReal p (fun ξ => X ξ + Y ξ) =
      bernoulliExpectReal p X + bernoulliExpectReal p Y
    unfold bernoulliExpectReal
    ring
  · intro c X
    exact bernoulliExpectReal_mul p c X
  · intro X hX
    change 0 ≤ bernoulliExpectReal p X
    unfold bernoulliExpectReal
    have ht := hX true
    have hf := hX false
    have hpm : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    positivity
  · intro X
    change (bernoulliExpectReal p X) ^ 2 ≤
      bernoulliExpectReal p (fun ξ => (X ξ) ^ 2)
    unfold bernoulliExpectReal
    simp only
    have hpm : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hs : 0 ≤ p * (1 - p) * (X true - X false) ^ 2 := by positivity
    have hid :
        p * X true ^ 2 + (1 - p) * X false ^ 2 -
            (p * X true + (1 - p) * X false) ^ 2 =
          p * (1 - p) * (X true - X false) ^ 2 := by
      ring
    exact sub_nonneg.mp (by simpa [hid] using hs)
  · intro T X i
    change (bernoulliExpectVec p X) i = bernoulliExpectReal p (fun ξ => X ξ i)
    simp [bernoulliExpectVec, bernoulliExpectReal]

/-- Paper Lemma 3.1 is now an actual theorem: equation (16) is unbiased, is a
probability-`p` zero-chain, and has the stated variance. -/
theorem lemma31_bvBaseOracle_certificate {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    BVBaseOracleCertificate T C p := by
  refine
    { p_pos := hp0
      p_le_one := hp1
      law_valid := bernoulliLaw_axioms p (le_of_lt hp0) hp1
      unbiased := ?_
      probability_zero_chain := bvBaseOracle_probability_zero_chain C p (le_of_lt hp0) hp1
      variance := ?_ }
  · intro u
    exact bvBaseOracle_unbiased C p (ne_of_gt hp0) u
  · intro u
    exact bvBaseOracle_variance C p hp0 hp1 u

/-! ### Generic stochastic transfer identities in Lemma 2.3 -/

/-- The generic lifted primal block is deterministic, hence its stochastic error is zero. -/
theorem genericLiftedGx_error_zero {T : ℕ} {Seed : Type}
    (P : LiftParameters) (x y : Vec T) (ξ : Seed) :
    genericLiftedGx P x y ξ - (P.ν * P.γ) • (y - P.γ • x) = 0 := by
  simp [genericLiftedGx]

/-- In the generic-seed formulation, all stochastic error is again confined to the dual block. -/
theorem genericLiftedGy_error_identity {T : ℕ} {Seed : Type}
    (C : ExplicitZeroChainCertificate T) (B : GenericBaseOracle T Seed)
    (P : LiftParameters) (x y : Vec T) (ξ : Seed) :
    genericLiftedGy B P x y ξ -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) =
      P.q • (B.g (P.β • y) ξ - C.gradF (P.β • y)) := by
  simp [genericLiftedGy, smul_sub]

/-- Generic base unbiasedness transfers to equations (9)--(10).  This proves the stochastic
unbiasedness part of Lemma 2.3 before Bernoulli specialisation. -/
theorem genericLiftedOracle_unbiased_of_base {T : ℕ} {Seed : Type}
    (C : ExplicitZeroChainCertificate T) (E : Law Seed) (H : LawAxioms E)
    (B : GenericBaseOracle T Seed) (P : LiftParameters)
    (hbase : GenericBaseUnbiased C E B) (x y : Vec T) :
    E.expectVec (fun ξ => genericLiftedGx P x y ξ) =
        (P.ν * P.γ) • (y - P.γ • x) ∧
    E.expectVec (fun ξ => genericLiftedGy B P x y ξ) =
        P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x) := by
  constructor
  · ext i
    rw [H.expectVec_coord]
    simpa [genericLiftedGx] using
      H.expect_const (((P.ν * P.γ) • (y - P.γ • x)) i)
  · let d : Vec T := P.ν • (y - P.γ • x)
    have hb := hbase (P.β • y)
    ext i
    rw [H.expectVec_coord]
    have hbcoord : E.expectReal (fun ξ => B.g (P.β • y) ξ i) =
        C.gradF (P.β • y) i := by
      calc
        E.expectReal (fun ξ => B.g (P.β • y) ξ i) =
            (E.expectVec (fun ξ => B.g (P.β • y) ξ)) i := by
              symm
              exact H.expectVec_coord (fun ξ => B.g (P.β • y) ξ) i
        _ = C.gradF (P.β • y) i := by rw [hb]
    change E.expectReal (fun ξ => (P.q • B.g (P.β • y) ξ - d) i) =
      (P.q • C.gradF (P.β • y) - d) i
    calc
      E.expectReal (fun ξ => (P.q • B.g (P.β • y) ξ - d) i) =
          E.expectReal (fun ξ => P.q * (B.g (P.β • y) ξ i) + (- d i)) := by
            simp [sub_eq_add_neg]
      _ = E.expectReal (fun ξ => P.q * (B.g (P.β • y) ξ i)) +
            E.expectReal (fun _ : Seed => - d i) :=
              H.expect_add _ _
      _ = P.q * E.expectReal (fun ξ => B.g (P.β • y) ξ i) + (- d i) := by
            rw [H.expect_smul, H.expect_const]
      _ = (P.q • C.gradF (P.β • y) - d) i := by
            rw [hbcoord]
            simp [sub_eq_add_neg]

/-- Paper Lemma 2.3(iii), now proved for the generic seed/law interface. -/
theorem generic_lifted_variance_transfer {T : ℕ} {Seed : Type}
    (C : ExplicitZeroChainCertificate T) (E : Law Seed) (H : LawAxioms E)
    (B : GenericBaseOracle T Seed) (P : LiftParameters) (p v₀ : ℝ)
    (hvar : GenericBaseVarianceHypothesis C E B p v₀) :
    ∀ x y, E.expectReal (fun ξ =>
      ‖genericLiftedGx P x y ξ - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
      ‖genericLiftedGy B P x y ξ -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2) ≤
      P.q ^ 2 * v₀ ^ 2 * (1 - p) / p := by
  intro x y
  have hb := hvar (P.β • y)
  have hscale := mul_le_mul_of_nonneg_left hb (sq_nonneg P.q)
  calc
    E.expectReal (fun ξ =>
      ‖genericLiftedGx P x y ξ - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
      ‖genericLiftedGy B P x y ξ -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2) =
      E.expectReal (fun ξ =>
        P.q ^ 2 * ‖B.g (P.β • y) ξ - C.gradF (P.β • y)‖ ^ 2) := by
          congr 1
          funext ξ
          rw [genericLiftedGx_error_zero P x y ξ,
              genericLiftedGy_error_identity C B P x y ξ]
          simp [norm_smul, Real.norm_eq_abs]
          rw [mul_pow, sq_abs P.q]
    _ = P.q ^ 2 * E.expectReal (fun ξ =>
          ‖B.g (P.β • y) ξ - C.gradF (P.β • y)‖ ^ 2) :=
        H.expect_smul _ _
    _ ≤ P.q ^ 2 * (v₀ ^ 2 * (1 - p) / p) := hscale
    _ = P.q ^ 2 * v₀ ^ 2 * (1 - p) / p := by ring

/-! ### Stochastic transfer identities in Lemma 2.3 -/

/-- The lifted primal block is deterministic, hence has zero oracle error. -/
theorem liftedGx_error_zero {T : ℕ} (P : LiftParameters) (x y : Vec T) (Z : Bool) :
    liftedGx P x y Z - (P.ν * P.γ) • (y - P.γ • x) = 0 := by
  simp [liftedGx]

/-- The entire lifted stochastic error is the scaled base-oracle error in the dual block. -/
theorem liftedGy_error_identity {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters) (x y : Vec T) (Z : Bool) :
    liftedGy B P x y Z -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) =
      P.q • (B.g (P.β • y) Z - C.gradF (P.β • y)) := by
  simp [liftedGy, smul_sub]

/-- Base unbiasedness transfers to the complete lifted oracle. -/
theorem liftedOracle_unbiased_of_base {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters) (p : ℝ)
    (hbase : BaseUnbiased C B p) (x y : Vec T) :
    bernoulliExpectVec p (fun Z => liftedGx P x y Z) =
        (P.ν * P.γ) • (y - P.γ • x) ∧
    bernoulliExpectVec p (fun Z => liftedGy B P x y Z) =
        P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x) := by
  constructor
  · simp [bernoulliExpectVec, liftedGx]
  · have hb := hbase (P.β • y)
    ext i
    have hbi := congrArg (fun v : Vec T => v i) hb
    simp [bernoulliExpectVec, liftedGy] at hbi ⊢
    rw [← hbi]
    ring

/-- Lemma 2.3(iii), in the Bernoulli specialization used by Sections 3--4. -/
theorem lifted_variance_transfer {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters) (p v₀ : ℝ)
    (hvar : BaseVarianceHypothesis C B p v₀) :
    ∀ x y, bernoulliExpectReal p (fun Z =>
      ‖liftedGx P x y Z - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
      ‖liftedGy B P x y Z -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2) ≤
      P.q ^ 2 * v₀ ^ 2 * (1 - p) / p := by
  intro x y
  have hb := hvar (P.β • y)
  have hscale := mul_le_mul_of_nonneg_left hb (sq_nonneg P.q)
  calc
    bernoulliExpectReal p (fun Z =>
      ‖liftedGx P x y Z - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
      ‖liftedGy B P x y Z -
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2)
        = P.q ^ 2 * bernoulliExpectReal p (fun Z =>
            ‖B.g (P.β • y) Z - C.gradF (P.β • y)‖ ^ 2) := by
          calc
            bernoulliExpectReal p (fun Z =>
              ‖liftedGx P x y Z - (P.ν * P.γ) • (y - P.γ • x)‖ ^ 2 +
              ‖liftedGy B P x y Z -
                (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x))‖ ^ 2) =
                bernoulliExpectReal p (fun Z =>
                  P.q ^ 2 * ‖B.g (P.β • y) Z - C.gradF (P.β • y)‖ ^ 2) := by
                  congr 1
                  funext Z
                  rw [liftedGx_error_zero P x y Z,
                      liftedGy_error_identity C B P x y Z]
                  simp [norm_smul, Real.norm_eq_abs]
                  rw [mul_pow, sq_abs P.q]
            _ = P.q ^ 2 * bernoulliExpectReal p (fun Z =>
                  ‖B.g (P.β • y) Z - C.gradF (P.β • y)‖ ^ 2) :=
                bernoulliExpectReal_mul p (P.q ^ 2) _
    _ ≤ P.q ^ 2 * (v₀ ^ 2 * (1 - p) / p) := hscale
    _ = P.q ^ 2 * v₀ ^ 2 * (1 - p) / p := by ring





/-- Bernoulli specialization of the unbiasedness conclusion in Lemma 2.3, expressed through the
actual `PopulationObjective`/`StochasticOracle` interfaces used later. -/
theorem liftedOracle_unbiased {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (P : LiftParameters) (L : LiftPropertiesCertificate T C B P)
    (p : ℝ) (hbase : BaseUnbiased C B p) :
    OracleUnbiased (populationFromLift C B P L) (bernoulliLaw p) (liftedOracle B P) := by
  intro x y
  simpa [populationFromLift, liftedOracle, bernoulliLaw] using
    (liftedOracle_unbiased_of_base C B P p hbase x y)

/-- Bernoulli specialization of Lemma 2.3(iii) in the class-level oracle interface. -/
theorem liftedOracle_boundedVariance_of_base {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (p v₀ σ : ℝ)
    (hvar : BaseVarianceHypothesis C B p v₀)
    (hbudget : P.q ^ 2 * v₀ ^ 2 * (1 - p) / p ≤ σ ^ 2) :
    OracleBoundedVariance (populationFromLift C B P L) (bernoulliLaw p)
      (liftedOracle B P) σ := by
  intro x y
  have h := lifted_variance_transfer C B P p v₀ hvar x y
  have h' := le_trans h hbudget
  simpa [populationFromLift, liftedOracle, bernoulliLaw] using h'

/-! ### Support/unbiased core of Lemma 4.1 -/

/-- Equation (20): above the `1/4` frontier the gate is exactly one. -/
theorem thetaGate_eq_one_above_quarter {T : ℕ} {mΓ : ℝ}
    (Gate : SmoothGateCertificate mΓ) (u : Vec T) (i : Fin T)
    (hi : prog (1 / 4) u < i.1 + 1) : ThetaGate u i = 1 := by
  have hmono : prog (1 / 2) u ≤ prog (1 / 4) u := by
    apply prog_antitone_threshold u
    norm_num
  have hhalf : prog (1 / 2) u < i.1 + 1 := lt_of_le_of_lt hmono hi
  have hs := Gate.theta_sandwich u i
  have hlo : (1 : ℝ) ≤ ThetaGate u i := by
    have h := hs.1
    rw [if_pos hi] at h
    exact h
  have hup : ThetaGate u i ≤ 1 := by
    have h := hs.2
    rw [if_pos hhalf] at h
    exact h
  linarith

/-- Equation (20): at or before the `1/2` progress, the gate is zero. -/
theorem thetaGate_eq_zero_at_or_before_half {T : ℕ} {mΓ : ℝ}
    (Gate : SmoothGateCertificate mΓ) (u : Vec T) (i : Fin T)
    (hi : i.1 + 1 ≤ prog (1 / 2) u) : ThetaGate u i = 0 := by
  have hs := Gate.theta_sandwich u i
  have hnot : ¬ prog (1 / 2) u < i.1 + 1 := Nat.not_lt.mpr hi
  have hnonneg : 0 ≤ ThetaGate u i := by
    by_cases hq : prog (1 / 4) u < i.1 + 1
    · have hlo : (1 : ℝ) ≤ ThetaGate u i := by
        have h := hs.1
        rw [if_pos hq] at h
        exact h
      linarith
    · have h := hs.1
      rw [if_neg hq] at h
      exact h
  have hupper : ThetaGate u i ≤ 0 := by
    have h := hs.2
    rw [if_neg hnot] at h
    exact h
  linarith

/-- On `Z=0`, the smooth-gated oracle masks every coordinate above the `1/4` frontier. -/
theorem asBaseOracle_false_zero_above {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (u : Vec T) (i : Fin T) (hi : prog (1 / 4) u < i.1 + 1) :
    asBaseOracle C p u false i = 0 := by
  have htheta := thetaGate_eq_one_above_quarter Gate u i hi
  simp [asBaseOracle, htheta, bernoulliZ]

/-- No smooth-gated oracle coordinate can appear beyond the single population-gradient frontier. -/
theorem asBaseOracle_zero_beyond_frontier {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (u : Vec T) (Z : Bool)
    (i : Fin T) (hi : prog (1 / 4) u + 1 < i.1 + 1) :
    asBaseOracle C p u Z i = 0 := by
  simp [asBaseOracle, gradF_zero_beyond_quarter_frontier C u i hi]

/-- `Z=0` cannot advance the smooth-gated oracle progress. -/
theorem asBaseOracle_prog_false_le {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (u : Vec T) :
    prog 0 (asBaseOracle C p u false) ≤ prog (1 / 4) u := by
  apply prog_zero_le_of_zero_above
  intro i hi
  exact asBaseOracle_false_zero_above C Gate p u i hi

/-- The smooth-gated oracle advances by at most one coordinate for either seed. -/
theorem asBaseOracle_prog_le_succ {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) :
    prog 0 (asBaseOracle C p u Z) ≤ prog (1 / 4) u + 1 := by
  apply prog_zero_le_of_zero_above
  intro i hi
  exact asBaseOracle_zero_beyond_frontier C p u Z i hi

/-- The probability-`p` zero-chain part of paper Lemma 4.1. -/
theorem asBaseOracle_probability_zero_chain {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    ProbabilityPZeroChain (bernoulliLaw p) (asBaseOracle C p) p := by
  have hfalse : ¬ ∃ u : Vec T,
      prog 0 (asBaseOracle C p u false) = prog (1 / 4) u + 1 := by
    intro h
    rcases h with ⟨u, hu⟩
    have hle := asBaseOracle_prog_false_le C Gate p u
    omega
  have hfar_true : ¬ ∃ u : Vec T,
      prog 0 (asBaseOracle C p u true) > prog (1 / 4) u + 1 := by
    intro h
    rcases h with ⟨u, hu⟩
    have hle := asBaseOracle_prog_le_succ C p u true
    omega
  have hfar_false : ¬ ∃ u : Vec T,
      prog 0 (asBaseOracle C p u false) > prog (1 / 4) u + 1 := by
    intro h
    rcases h with ⟨u, hu⟩
    have hle := asBaseOracle_prog_le_succ C p u false
    omega
  constructor
  · change bernoulliProb p (fun Z => ∃ u : Vec T,
      prog 0 (asBaseOracle C p u Z) = prog (1 / 4) u + 1) ≤ p
    unfold bernoulliProb
    by_cases htrue : ∃ u : Vec T,
        prog 0 (asBaseOracle C p u true) = prog (1 / 4) u + 1
    · rw [if_pos htrue, if_neg hfalse]
      simp
    · rw [if_neg htrue, if_neg hfalse]
      simpa using hp0
  · change bernoulliProb p (fun Z => ∃ u : Vec T,
      prog 0 (asBaseOracle C p u Z) > prog (1 / 4) u + 1) = 0
    unfold bernoulliProb
    rw [if_neg hfar_true, if_neg hfar_false]
    ring



/-- Lemma 2.1(5) directly gives vanishing beyond the `1/2` frontier plus one. -/
theorem gradF_zero_beyond_half_frontier {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (u : Vec T) (i : Fin T)
    (hi : prog (1 / 2) u + 1 < i.1 + 1) : C.gradF u i = 0 := by
  have hprog : prog 0 (C.gradF u) < i.1 + 1 := lt_of_le_of_lt (C.zero_chain u) hi
  exact coord_eq_zero_of_prog_lt (C.gradF u) i hprog

/-- The gate sandwich implies `0 ≤ Θᵢ(u) ≤ 1`. -/
theorem thetaGate_range {T : ℕ} {mΓ : ℝ} (Gate : SmoothGateCertificate mΓ)
    (u : Vec T) (i : Fin T) : 0 ≤ ThetaGate u i ∧ ThetaGate u i ≤ 1 := by
  have hs := Gate.theta_sandwich u i
  constructor
  · by_cases hq : prog (1 / 4) u < i.1 + 1
    · have h := hs.1
      rw [if_pos hq] at h
      linarith
    · have h := hs.1
      rw [if_neg hq] at h
      exact h
  · by_cases hh : prog (1 / 2) u < i.1 + 1
    · have h := hs.2
      rw [if_pos hh] at h
      exact h
    · have h := hs.2
      rw [if_neg hh] at h
      linarith

/-- Coordinate formula for the stochastic error of the AS oracle. -/
theorem asBaseOracle_error_coord {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) (Z : Bool) (i : Fin T) :
    (asBaseOracle C p u Z - C.gradF u) i =
      (C.gradF u) i * ThetaGate u i * (bernoulliZ Z / p - 1) := by
  simp [asBaseOracle]
  ring

/-- The `1/2`-frontier index used in the variance proof of Lemma 4.1. -/
def halfFrontierIndex {T : ℕ} (u : Vec T) (h : prog (1 / 2) u < T) : Fin T :=
  ⟨prog (1 / 2) u, h⟩

/-- The AS stochastic error has at most one nonzero coordinate. -/
theorem asBaseOracle_error_eq_single {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (u : Vec T) (Z : Bool) (hfront : prog (1 / 2) u < T) :
    asBaseOracle C p u Z - C.gradF u =
      EuclideanSpace.single (halfFrontierIndex u hfront)
        ((C.gradF u) (halfFrontierIndex u hfront) *
          ThetaGate u (halfFrontierIndex u hfront) * (bernoulliZ Z / p - 1)) := by
  ext i
  rw [asBaseOracle_error_coord]
  by_cases hij : i = halfFrontierIndex u hfront
  · subst i
    simp [EuclideanSpace.single_apply]
  · have hneval : i.1 ≠ (halfFrontierIndex u hfront).1 := by
      intro hval
      apply hij
      exact Fin.ext hval
    rcases lt_or_gt_of_ne hneval with hlt | hgt
    · have hle0 : i.1 + 1 ≤ (halfFrontierIndex u hfront).1 :=
        Nat.succ_le_iff.mpr hlt
      have hle : i.1 + 1 ≤ prog (1 / 2) u := by
        simpa [halfFrontierIndex] using hle0
      have htheta := thetaGate_eq_zero_at_or_before_half Gate u i hle
      simp [htheta, EuclideanSpace.single_apply, hij]
    · have hfar : prog (1 / 2) u + 1 < i.1 + 1 := by
        simpa [halfFrontierIndex] using Nat.succ_lt_succ hgt
      have hgzero := gradF_zero_beyond_half_frontier C u i hfar
      simp [hgzero, EuclideanSpace.single_apply, hij]

/-- If the `1/2` progress already reaches the chain end, the AS stochastic error is zero. -/
theorem asBaseOracle_error_eq_zero_of_half_frontier_full {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (u : Vec T) (Z : Bool) (hfront : ¬ prog (1 / 2) u < T) :
    asBaseOracle C p u Z - C.gradF u = 0 := by
  have hprog_le : prog (1 / 2) u ≤ T := by
    unfold prog
    exact Nat.findGreatest_le T
  have hprog : prog (1 / 2) u = T := by omega
  ext i
  rw [asBaseOracle_error_coord]
  have hiT : i.1 + 1 ≤ T := Nat.succ_le_iff.mpr i.2
  have hi : i.1 + 1 ≤ prog (1 / 2) u := by omega
  have htheta := thetaGate_eq_zero_at_or_before_half Gate u i hi
  simp [htheta]

/-- Pointwise error envelope for equation (22). -/
theorem asBaseOracle_error_norm_sq_le {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (u : Vec T) (Z : Bool) :
    ‖asBaseOracle C p u Z - C.gradF u‖ ^ 2 ≤
      g₀ ^ 2 * (bernoulliZ Z / p - 1) ^ 2 := by
  by_cases hfront : prog (1 / 2) u < T
  · rw [asBaseOracle_error_eq_single C Gate p u Z hfront,
        EuclideanSpace.norm_single, Real.norm_eq_abs, abs_mul, abs_mul, mul_pow]
    simp only [sq_abs]
    let j := halfFrontierIndex u hfront
    have hg := C.grad_coord_bound u j
    have htheta := thetaGate_range Gate u j
    have htheta_abs : |ThetaGate u j| ≤ 1 := by
      rw [abs_of_nonneg htheta.1]
      exact htheta.2
    have hg0 : 0 ≤ g₀ := by norm_num [g₀]
    have hprod1 : 0 ≤ (g₀ - |C.gradF u j|) * (g₀ + |C.gradF u j|) := by
      exact mul_nonneg (sub_nonneg.mpr hg) (add_nonneg hg0 (abs_nonneg _))
    have hgrad_sq : (C.gradF u j) ^ 2 ≤ g₀ ^ 2 := by
      nlinarith [sq_abs (C.gradF u j)]
    have htheta_sq : (ThetaGate u j) ^ 2 ≤ 1 := by
      have ht0 : 0 ≤ |ThetaGate u j| := abs_nonneg _
      nlinarith [sq_abs (ThetaGate u j)]
    have hfirst : (C.gradF u j) ^ 2 * (ThetaGate u j) ^ 2 ≤ g₀ ^ 2 := by
      calc
        (C.gradF u j) ^ 2 * (ThetaGate u j) ^ 2
            ≤ g₀ ^ 2 * (ThetaGate u j) ^ 2 :=
              mul_le_mul_of_nonneg_right hgrad_sq (sq_nonneg _)
        _ ≤ g₀ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left htheta_sq (sq_nonneg g₀)
        _ = g₀ ^ 2 := by ring
    have hfirst_abs :
        (|C.gradF u j| * |ThetaGate u j|) ^ 2 ≤ g₀ ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]
      exact hfirst
    exact mul_le_mul_of_nonneg_right hfirst_abs (sq_nonneg _)
  · rw [asBaseOracle_error_eq_zero_of_half_frontier_full C Gate p u Z hfront]
    simpa using mul_nonneg (sq_nonneg g₀) (sq_nonneg (bernoulliZ Z / p - 1))

/-- Paper equation (22). -/
theorem asBaseOracle_variance {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (u : Vec T) :
    bernoulliExpectReal p (fun Z => ‖asBaseOracle C p u Z - C.gradF u‖ ^ 2) ≤
      g₀ ^ 2 * (1 - p) / p := by
  have ht := asBaseOracle_error_norm_sq_le C Gate p u true
  have hf := asBaseOracle_error_norm_sq_le C Gate p u false
  have hpt := mul_le_mul_of_nonneg_left ht (le_of_lt hp0)
  have hpf := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hp1)
  calc
    bernoulliExpectReal p (fun Z => ‖asBaseOracle C p u Z - C.gradF u‖ ^ 2)
        ≤ bernoulliExpectReal p (fun Z =>
            g₀ ^ 2 * (bernoulliZ Z / p - 1) ^ 2) := by
          unfold bernoulliExpectReal at ⊢
          linarith
    _ = g₀ ^ 2 * bernoulliExpectReal p (fun Z => (bernoulliZ Z / p - 1) ^ 2) := by
          exact bernoulliExpectReal_mul p (g₀ ^ 2)
            (fun Z => (bernoulliZ Z / p - 1) ^ 2)
    _ = g₀ ^ 2 * ((1 - p) / p) := by
          rw [bernoulli_centered_second_moment p (ne_of_gt hp0)]
    _ = g₀ ^ 2 * (1 - p) / p := by ring

/-- Three of the four substantive assertions of Lemma 4.1 (unbiasedness, probability zero-chain,
and equation (22)) can be separated from the harder same-seed Lipschitz estimate (23).  This
record is used to track the now-proved core without pretending that (23) is already complete. -/
structure ASBaseOracleCoreProof (T : ℕ) (C : ExplicitZeroChainCertificate T)
    (p mΓ : ℝ) (Gate : SmoothGateCertificate mΓ) where
  p_pos : 0 < p
  p_le_one : p ≤ 1
  law_valid : LawAxioms (bernoulliLaw p)
  unbiased : ∀ u,
    bernoulliExpectVec p (fun Z => asBaseOracle C p u Z) = C.gradF u
  probability_zero_chain : ProbabilityPZeroChain (bernoulliLaw p) (asBaseOracle C p) p
  variance : ∀ u,
    bernoulliExpectReal p (fun Z => ‖asBaseOracle C p u Z - C.gradF u‖ ^ 2) ≤
      g₀ ^ 2 * (1 - p) / p

/-- Construct the proved support/unbiased core of Lemma 4.1. -/
theorem lemma41_core_proof {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ASBaseOracleCoreProof T C p mΓ Gate := by
  refine
    { p_pos := hp0
      p_le_one := hp1
      law_valid := bernoulliLaw_axioms p (le_of_lt hp0) hp1
      unbiased := ?_
      probability_zero_chain := asBaseOracle_probability_zero_chain C Gate p (le_of_lt hp0) hp1
      variance := ?_ }
  · intro u
    exact asBaseOracle_unbiased C p (ne_of_gt hp0) u
  · intro u
    exact asBaseOracle_variance C Gate p hp0 hp1 u


/-- Equation (24) for the canonical choice `universalS0`. -/
theorem universalS0_sq (mΓ : ℝ) :
    (universalS0 mΓ) ^ 2 = 4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2 := by
  unfold universalS0
  exact Real.sq_sqrt (by positivity)

/-- Once the remaining same-seed Lipschitz estimate (23) is supplied, all fields of paper
Lemma 4.1 assemble into the full certificate.  The point is to leave exactly equation (23), and
not unbiasedness/zero-chain/variance, as the outstanding analytic obligation. -/
theorem lemma41_certificate_of_averaged_smooth {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (havg : ∀ u v,
      bernoulliExpectReal p (fun Z => ‖asBaseOracle C p u Z - asBaseOracle C p v Z‖ ^ 2) ≤
        (universalS0 mΓ) ^ 2 / p * ‖u - v‖ ^ 2) :
    ASBaseOracleCertificate T C p mΓ (universalS0 mΓ) Gate := by
  refine
    { p_pos := hp0
      p_le_one := hp1
      law_valid := bernoulliLaw_axioms p (le_of_lt hp0) hp1
      s0sq := universalS0_sq mΓ
      unbiased := ?_
      probability_zero_chain := asBaseOracle_probability_zero_chain C Gate p (le_of_lt hp0) hp1
      variance := ?_
      averaged_smooth := havg }
  · intro u
    exact asBaseOracle_unbiased C p (ne_of_gt hp0) u
  · intro u
    exact asBaseOracle_variance C Gate p hp0 hp1 u

/-! ### Parameter-verification pieces from Lemmas 3.2 and 4.3 -/

/-- The smoothness constant used in the proof of Lemma 3.2 is at most `L/2`. -/
theorem bv_lift_smooth_constant_le_half (P : BVParameters) (hκ : 8 ≤ P.κ) :
    P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h ≤ P.L / 2 := by
  have hκ' : 8 ≤ P.L / P.μ := by simpa [P.κ_def] using hκ
  have hLmu : 8 * P.μ ≤ P.L := (le_div_iff₀ P.μ_pos).mp hκ'
  have hμ0 : P.μ ≠ 0 := ne_of_gt P.μ_pos
  have hexact :
      P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h = 3 * P.μ / 2 + 5 * P.L / 16 := by
    rw [BVParameters.ν, BVParameters.h, P.γ_sq, P.κ_def]
    norm_num [ℓ₀]
    field_simp [hμ0]
    ring
  rw [hexact]
  nlinarith

/-- The origin-error contribution in Lemma 3.2 is exactly `8 g₀² ε²/L`. -/
theorem bv_origin_term_identity (P : BVParameters) :
    P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) = 8 * g₀ ^ 2 * P.ε ^ 2 / P.L := by
  rw [P.q_sq, P.κ_def]
  have hL0 : P.L ≠ 0 := ne_of_gt P.L_pos
  have hμ0 : P.μ ≠ 0 := ne_of_gt P.μ_pos
  field_simp [hL0, hμ0]
  ring

/-- Exact real precursor of the BV chain length used in Lemma 3.2. -/
theorem bv_chainScale_identity (P : BVParameters) :
    P.chainScale = P.L * P.Δ / (256 * Δ₀ * ℓ₀ * P.ε ^ 2) := by
  rw [BVParameters.chainScale, P.alpha_value]
  have hL0 : P.L ≠ 0 := ne_of_gt P.L_pos
  have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
  field_simp [hL0, hε0]
  ring

/-- The AS choice of `h` is no larger than the strong-concavity branch. -/
theorem as_h_le_mu_branch (P : ASParameters) :
    P.h ≤ P.μ / (4 * ℓ₀) := by
  exact min_le_left _ _

/-- The AS choice of `h` is no larger than the averaged-smooth branch. -/
theorem as_h_le_smooth_branch (P : ASParameters) :
    P.h ≤ P.Lbar * Real.sqrt P.p / (4 * P.s₀) := by
  exact min_le_right _ _

/-- Equation (27): `ℓ₀ h / ν ≤ 1/5` for the AS choice. -/
theorem as_transfer_ratio_le_one_fifth (P : ASParameters) :
    ℓ₀ * P.h / P.ν ≤ 1 / 5 := by
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  have hsqrt : 0 < Real.sqrt P.p := Real.sqrt_pos.2 P.p_pos
  have hbranch1 : 0 < P.μ / (4 * ℓ₀) := div_pos P.μ_pos (mul_pos (by norm_num) hℓ)
  have hbranch2 : 0 < P.Lbar * Real.sqrt P.p / (4 * P.s₀) := by
    exact div_pos (mul_pos P.Lbar_pos hsqrt) (mul_pos (by norm_num) P.s₀_pos)
  have hhpos : 0 < P.h := lt_min hbranch1 hbranch2
  have hνpos : 0 < P.ν := by
    rw [ASParameters.ν]
    exact add_pos P.μ_pos (mul_pos hℓ hhpos)
  have hupper := as_h_le_mu_branch P
  apply (div_le_iff₀ hνpos).2
  rw [ASParameters.ν]
  have hscaled : 4 * ℓ₀ * P.h ≤ P.μ := by
    have hden : 0 < 4 * ℓ₀ := mul_pos (by norm_num) hℓ
    have hh := (le_div_iff₀ hden).1 hupper
    simpa [mul_assoc, mul_left_comm, mul_comm] using hh
  nlinarith


/-! ## v12 proof phase II: deterministic assembly and Proposition 2.4 pathwise core

The theorems in this section are actual proof terms.  They do not replace the remaining
analytic obligations inside `LiftPropertiesCertificate`; rather, they close the deterministic
class/oracle assembly and the quantitative stationarity step used in Proposition 2.4.
-/

/-- A Lemma-2.3 certificate immediately gives the paper's `μ`-strong concavity statement for
its concrete population objective. -/
theorem populationFromLift_stronglyConcaveY {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) :
    StronglyConcaveY (populationFromLift C B P L) P.μ := by
  intro x y y'
  exact L.mu_strong_concavity x y y'

/-- Equation (11), transferred from the lift certificate to the Definition-1.1 class interface. -/
theorem populationFromLift_jointSmooth_of_bound {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (M : ℝ)
    (hM : P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h ≤ M) :
    JointSmooth (populationFromLift C B P L) M := by
  intro x y x' y'
  have h := L.joint_smoothness x y x' y'
  exact le_trans h (mul_le_mul_of_nonneg_right hM (Real.sqrt_nonneg _))

/-- Equation (12), transferred to the initial-gap class interface once its displayed RHS is
within the desired budget. -/
theorem populationFromLift_initialGap_of_bound {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (Δ : ℝ)
    (hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ Δ) :
    InitialGap (populationFromLift C B P L) Δ := by
  exact le_trans L.primal_gap hgap

/-- The diagonal competitor proves the finite-infimum requirement in manuscript equation (33). -/
theorem populationFromLift_bddBelow {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) :
    BddBelow (Set.range (populationFromLift C B P L).Phi) := by
  refine ⟨P.α * sInf (Set.range (explicitFT T C.dim_pos)), ?_⟩
  rintro z ⟨x, rfl⟩
  have ha : 0 ≤ P.α := div_nonneg (sq_nonneg _) (le_of_lt P.h_pos)
  have hlo := mul_le_mul_of_nonneg_left
    (csInf_le C.bddBelow (Set.mem_range_self (P.β • (P.γ • x)))) ha
  have hmax := L.maximizer x (P.γ • x)
  rw [← L.Phi_def x] at hmax
  simp only [liftedF, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero] at hmax
  exact le_trans hlo hmax

/-- The deterministic conclusions of Lemma 2.3 assemble into Definition 1.1 once the numerical
smoothness and gap budgets are available. -/
theorem populationFromLift_inNCSCClass_of_bounds {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (M Δ : ℝ)
    (hM : P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h ≤ M)
    (hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ Δ) :
    InNCSCClass (populationFromLift C B P L) M P.μ Δ := by
  refine ⟨populationFromLift_jointSmooth_of_bound C B P L M hM,
    populationFromLift_stronglyConcaveY C B P L,
    populationFromLift_initialGap_of_bound C B P L Δ hgap,
    populationFromLift_bddBelow C B P L⟩

/-- A construction witness whose base oracle has been certified by Lemma 3.1 is genuinely
unbiased at the base level. -/
theorem bvWitness_baseUnbiased {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P)
    (H : BVBaseOracleCertificate T C P.p) : BaseUnbiased C W.B P.p := by
  intro u
  have h := H.unbiased u
  simpa only [W.base_oracle_def] using h

/-- The same witness inherits the exact base variance inequality of Lemma 3.1. -/
theorem bvWitness_baseVariance {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P)
    (H : BVBaseOracleCertificate T C P.p) :
    BaseVarianceHypothesis C W.B P.p g₀ := by
  intro u
  have h := H.variance u
  simpa only [W.base_oracle_def] using h

/-- Lemma 3.1 plus the stochastic transfer part of Lemma 2.3 proves unbiasedness of the actual
bounded-variance lifted oracle. -/
theorem bvConstructedOracle_unbiased {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P)
    (H : BVBaseOracleCertificate T C P.p) :
    OracleUnbiased (bvConstructedPopulation W) (bernoulliLaw P.p)
      (bvConstructedOracle W) := by
  exact liftedOracle_unbiased C W.B W.LP W.lift_properties P.p
    (bvWitness_baseUnbiased W H)

/-- Positivity of the Bernoulli reveal probability chosen in equation (18). -/
theorem bv_p_pos (P : BVParameters) : 0 < P.p := by
  rw [P.p_def]
  by_cases hσ : P.σ = 0
  · simp [hσ]
  · simp only [hσ, if_false]
    apply lt_min (by norm_num)
    have hq : 0 < P.q := by
      rw [P.q_def]
      exact div_pos (mul_pos (by norm_num) P.ε_pos) P.γ_pos
    have hnum : 0 < P.q ^ 2 * g₀ ^ 2 := by
      have hg : 0 < g₀ := by norm_num [g₀]
      positivity
    have hden : 0 < P.σ ^ 2 := sq_pos_of_ne_zero hσ
    exact div_pos hnum hden

/-- The reveal probability chosen in equation (18) never exceeds one. -/
theorem bv_p_le_one (P : BVParameters) : P.p ≤ 1 := by
  rw [P.p_def]
  by_cases hσ : P.σ = 0
  · simp [hσ]
  · simp only [hσ, if_false]
    exact min_le_left _ _

/-- Paper Proposition 2.4, deterministic/pathwise quantitative core: on every output for which
the terminal chain coordinate is still unfinished, the stationarity norm exceeds `5ε/3`.
This is the part of Proposition 2.4 after the progress lemma and before taking expectation. -/
theorem proposition24_pathwise_stationarity {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (ε : ℝ) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε)
    (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (x : Vec T)
    (hprog : prog 1 ((P.β * P.γ) • x) < T) :
    (5 / 3 : ℝ) * ε < ‖L.gradPhi x‖ := by
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  have hν : 0 < P.ν := by
    rw [LiftParameters.ν]
    exact add_pos P.μ_pos (mul_pos hℓ P.h_pos)
  have hrnonneg : 0 ≤ ℓ₀ * P.h / P.ν := by
    exact div_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt P.h_pos)) (le_of_lt hν)
  have hden : 0 < 1 + ℓ₀ * P.h / P.ν := by linarith
  have hden_le : 1 + ℓ₀ * P.h / P.ν ≤ 6 / 5 := by linarith
  have hcoef : (5 / 3 : ℝ) * ε ≤
      P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) := by
    rw [hγq]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hcoef_pos : 0 < P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) := by
    exact div_pos (mul_pos P.γ_pos P.q_pos) hden
  have hterm : 1 < ‖C.gradF ((P.β * P.γ) • x)‖ := C.terminal_gradient _ hprog
  have hstrict : P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) <
      P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) *
        ‖C.gradF ((P.β * P.γ) • x)‖ := by
    nlinarith
  exact lt_of_le_of_lt hcoef (lt_of_lt_of_le hstrict (L.stationarity_transfer x))

/-- Squared version of the preceding pathwise estimate, matching the constant used in the paper's
`25/18` expectation calculation. -/
theorem proposition24_pathwise_stationarity_sq {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (ε : ℝ) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε)
    (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (x : Vec T)
    (hprog : prog 1 ((P.β * P.γ) • x) < T) :
    (25 / 9 : ℝ) * ε ^ 2 < ‖L.gradPhi x‖ ^ 2 := by
  have h := proposition24_pathwise_stationarity C B P L ε hε hγq hratio x hprog
  have hleft : 0 ≤ (5 / 3 : ℝ) * ε := by positivity
  nlinarith [sq_nonneg (‖L.gradPhi x‖ - (5 / 3 : ℝ) * ε)]

/-- Nonnegativity of every product-Bernoulli world weight.  This is the basic measure-theoretic
fact needed to turn the pathwise Proposition-2.4 estimate into an expectation bound. -/
theorem roundWeight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R : ℕ} (w : RoundWorld R) : 0 ≤ roundWeight p w := by
  unfold roundWeight
  apply Finset.prod_nonneg
  intro t ht
  split
  · exact hp0
  · linarith

/-- Every squared-stationarity integrand appearing in `stationarityRisk` is nonnegative after
multiplication by its Bernoulli world weight. -/
theorem roundWeight_mul_norm_sq_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T R K : ℕ} {O : StochasticOracle T Bool}
    (gradPhi : Vec T → Vec T) (A : BernoulliRun T R K O) (w : RoundWorld R) :
    0 ≤ roundWeight p w * ‖gradPhi ((A.trace w).output)‖ ^ 2 := by
  exact mul_nonneg (roundWeight_nonneg p hp0 hp1 w) (sq_nonneg _)



/-! ### v13 proof phase III: expectation assembly for Proposition 2.4 -/

/-- Generic finite-world lower-bound principle used in Proposition 2.4.  If the squared
stationarity loss is at least `c` on an event `E`, then its Bernoulli expectation is at least
`c` times the probability of `E`.  This is the finite-product analogue of integrating a
pointwise lower bound over an event. -/
theorem stationarityRisk_ge_event_mass
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T R K : ℕ} {O : StochasticOracle T Bool}
    (gradPhi : Vec T → Vec T) (A : BernoulliRun T R K O)
    (E : Set (RoundWorld R)) (c : ℝ) (_hc : 0 ≤ c)
    (hloss : ∀ w, w ∈ E → c ≤ ‖gradPhi ((A.trace w).output)‖ ^ 2) :
    c * roundProb p E ≤ stationarityRisk p gradPhi A := by
  classical
  unfold roundProb stationarityRisk roundExpect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  by_cases hmem : w ∈ E
  · have hweight : 0 ≤ roundWeight p w := roundWeight_nonneg p hp0 hp1 w
    have hpoint := mul_le_mul_of_nonneg_left (hloss w hmem) hweight
    simpa [hmem, mul_assoc, mul_left_comm, mul_comm] using hpoint
  · have hnonneg := roundWeight_mul_norm_sq_nonneg p hp0 hp1 gradPhi A w
    simpa [hmem] using hnonneg

/-- The unfinished-output event appearing in Proposition 2.4 after the progress lemma. -/
def unfinishedOutputEvent {T R K : ℕ} {O : StochasticOracle T Bool}
    (P : LiftParameters) (A : BernoulliRun T R K O) : Set (RoundWorld R) :=
  {w | prog 1 ((P.β * P.γ) • (A.trace w).output) < T}

/-- Proposition 2.4 after the probabilistic progress step: if the unfinished-output event has
probability greater than `1/2`, the pathwise `5ε/3` bound already proved above implies the full
expected squared-stationarity lower bound. -/
theorem proposition24_expectation_of_unfinished_probability {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε)
    (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (A : BernoulliRun T R K (liftedOracle B P))
    (hprob : 1 / 2 < roundProb p (unfinishedOutputEvent P A)) :
    ε ^ 2 < stationarityRisk p L.gradPhi A := by
  let c : ℝ := (25 / 9 : ℝ) * ε ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hloss : ∀ w, w ∈ unfinishedOutputEvent P A →
      c ≤ ‖L.gradPhi ((A.trace w).output)‖ ^ 2 := by
    intro w hw
    have hpath := proposition24_pathwise_stationarity_sq C B P L ε hε hγq hratio
      ((A.trace w).output) hw
    exact le_of_lt hpath
  have hlower := stationarityRisk_ge_event_mass p hp0 hp1 L.gradPhi A
    (unfinishedOutputEvent P A) c hc hloss
  have hmul := mul_lt_mul_of_pos_left hprob hcpos
  have htarget : ε ^ 2 < c * roundProb p (unfinishedOutputEvent P A) := by
    dsimp [c] at hmul ⊢
    nlinarith [sq_pos_of_pos hε]
  exact lt_of_lt_of_le htarget hlower

/-- A convenient paper-shaped version of the previous theorem.  It isolates the sole remaining
probabilistic obligation in Proposition 2.4: proving, via Lemma 1.5 and zero-respecting support,
that the unfinished-output event has probability greater than one half. -/
theorem proposition24_of_progress_event {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε)
    (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (A : BernoulliRun T R K (liftedOracle B P))
    (hprogress : 1 / 2 < roundProb p (unfinishedOutputEvent P A)) :
    ε ^ 2 < stationarityRisk p L.gradPhi A := by
  exact proposition24_expectation_of_unfinished_probability C B P L p ε
    (le_of_lt hp) hp1 hε hγq hratio A hprogress


/-! ### v14 proof phase IV: zero-respecting support bridge for Proposition 2.4 -/

/-- The last (one-based coordinate `T`) index of a nonempty chain. -/
def lastIndexOfPos {T : ℕ} (hT : 0 < T) : Fin T :=
  ⟨T - 1, by omega⟩

/-- If the terminal pair coordinate has never appeared in an oracle response, a pair-zero-respecting
output has zero terminal primal coordinate.  This is the support implication used in the paper's
proof of Proposition 2.4. -/
theorem output_terminal_zero_of_unrevealed {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (A : BernoulliRun T R K O) (w : RoundWorld R)
    (hunrev : lastIndexOfPos hT ∉ revealedAll (A.trace w)) :
    (A.trace w).output (lastIndexOfPos hT) = 0 := by
  by_contra hne
  have hsupp : lastIndexOfPos hT ∈ supp (A.trace w).output := by
    simpa [supp] using hne
  have hrevealed : lastIndexOfPos hT ∈ revealedAll (A.trace w) :=
    (A.zero_respecting w).2 hsupp
  exact hunrev hrevealed

/-- Zero terminal support is enough to keep `prog_1` strictly below `T`, after the paper's
`βγ` scaling.  This is the deterministic support bridge between "pair coordinate `T` is
unrevealed" and the unfinished-chain hypothesis consumed by the terminal-gradient lemma. -/
theorem unfinished_prog_of_terminal_unrevealed {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (P : LiftParameters) (A : BernoulliRun T R K O) (w : RoundWorld R)
    (hunrev : lastIndexOfPos hT ∉ revealedAll (A.trace w)) :
    prog 1 ((P.β * P.γ) • (A.trace w).output) < T := by
  let u : Vec T := (P.β * P.γ) • (A.trace w).output
  have hlast : (A.trace w).output (lastIndexOfPos hT) = 0 :=
    output_terminal_zero_of_unrevealed hT A w hunrev
  have hzero : ∀ i : Fin T, T - 1 < i.1 + 1 → u i = 0 := by
    intro i hi
    have hival : i.1 = T - 1 := by
      have hib : i.1 < T := i.2
      omega
    have hieq : i = lastIndexOfPos hT := by
      apply Fin.ext
      simpa [lastIndexOfPos] using hival
    subst i
    simp [u, hlast]
  have hprog0 : prog 0 u ≤ T - 1 :=
    prog_zero_le_of_zero_above u (T - 1) hzero
  have hprog1 : prog 1 u ≤ prog 0 u :=
    prog_antitone_threshold u (by norm_num : (0 : ℝ) ≤ 1)
  have hle : prog 1 u ≤ T - 1 := le_trans hprog1 hprog0
  dsimp [u] at hle ⊢
  omega

/-- Event that the terminal pair coordinate has not been revealed by the end of the run. -/
def terminalUnrevealedEvent {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (A : BernoulliRun T R K O) : Set (RoundWorld R) :=
  {w | lastIndexOfPos hT ∉ revealedAll (A.trace w)}

/-- Monotonicity of the finite product-Bernoulli probability. -/
theorem roundProb_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R : ℕ} {E F : Set (RoundWorld R)} (hEF : E ⊆ F) :
    roundProb p E ≤ roundProb p F := by
  classical
  unfold roundProb roundExpect
  apply Finset.sum_le_sum
  intro w hw
  have hweight : 0 ≤ roundWeight p w := roundWeight_nonneg p hp0 hp1 w
  by_cases hE : w ∈ E
  · have hF : w ∈ F := hEF hE
    simp [hE, hF]
  · by_cases hF : w ∈ F
    · simp [hE, hF, hweight]
    · simp [hE, hF]

/-- The terminal-unrevealed event is contained in the unfinished-output event used by the
expectation half of Proposition 2.4. -/
theorem terminalUnrevealed_subset_unfinishedOutput {T R K : ℕ}
    {O : StochasticOracle T Bool} (hT : 0 < T) (P : LiftParameters)
    (A : BernoulliRun T R K O) :
    terminalUnrevealedEvent hT A ⊆ unfinishedOutputEvent P A := by
  intro w hw
  exact unfinished_prog_of_terminal_unrevealed hT P A w hw

/-- Probability form of the support bridge: if Lemma 1.5 gives probability greater than one half
for the terminal coordinate to remain unrevealed, then the unfinished-output event also has
probability greater than one half. -/
theorem unfinished_probability_of_terminal_unrevealed {T R K : ℕ}
    {O : StochasticOracle T Bool} (hT : 0 < T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : LiftParameters) (A : BernoulliRun T R K O)
    (hprob : 1 / 2 < roundProb p (terminalUnrevealedEvent hT A)) :
    1 / 2 < roundProb p (unfinishedOutputEvent P A) := by
  exact lt_of_lt_of_le hprob
    (roundProb_mono p hp0 hp1 (terminalUnrevealed_subset_unfinishedOutput hT P A))

/-- Proposition 2.4 with the zero-respecting support bridge discharged.  After this theorem,
the sole remaining probabilistic input is exactly the conclusion of Lemma 1.5: terminal pair
coordinate `T` remains unrevealed with probability greater than one half. -/
theorem proposition24_of_terminal_unrevealed_probability {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε)
    (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (A : BernoulliRun T R K (liftedOracle B P))
    (hprob : 1 / 2 < roundProb p (terminalUnrevealedEvent C.dim_pos A)) :
    ε ^ 2 < stationarityRisk p L.gradPhi A := by
  apply proposition24_expectation_of_unfinished_probability C B P L p ε
    (le_of_lt hp) hp1 hε hγq hratio A
  exact unfinished_probability_of_terminal_unrevealed C.dim_pos p (le_of_lt hp) hp1 P A hprob


/-! ## v15 proof phase V: the probabilistic progress lemma

This section closes the finite Bernoulli probability calculation behind paper Lemma 1.5.
The proof is deliberately elementary: for `p < 1/2`, the one-round reveal bound forces a
zero reveal on the `Z=false` branch, hence the total progress is pointwise dominated by the
number of Bernoulli successes.  A finite-product Markov bound then gives probability at most
`1/4` of accumulating `T` successes under `R ≤ T/(4p)`.  For `p ≥ 1/2`, the round budget itself
is already strictly below `T`, so the result is deterministic. -/

/-- One-coordinate Bernoulli mass used to factor the finite product world. -/
def bernoulliMass (p : ℝ) (z : Bool) : ℝ := if z then p else 1 - p

/-- The product weights on `RoundWorld R` have total mass one. -/
theorem roundWeight_total (p : ℝ) (R : ℕ) :
    (∑ w : RoundWorld R, roundWeight p w) = 1 := by
  classical
  calc
    (∑ w : RoundWorld R, roundWeight p w)
        = ∑ w : RoundWorld R, ∏ t : Fin R, bernoulliMass p (w t) := by
            rfl
    _ = ∏ t : Fin R, ∑ z : Bool, bernoulliMass p z := by
          symm
          exact Fintype.prod_sum (fun (_t : Fin R) z => bernoulliMass p z)
    _ = 1 := by simp [bernoulliMass]

/-- The full round world has probability one. -/
theorem roundProb_univ (p : ℝ) (R : ℕ) :
    roundProb p (Set.univ : Set (RoundWorld R)) = 1 := by
  classical
  unfold roundProb roundExpect
  simpa using roundWeight_total p R

/-- Complement rule for the explicit finite product probability. -/
theorem roundProb_compl (p : ℝ) {R : ℕ} (A : Set (RoundWorld R)) :
    roundProb p Aᶜ = 1 - roundProb p A := by
  classical
  have hpartition : roundProb p Aᶜ + roundProb p A =
      roundProb p (Set.univ : Set (RoundWorld R)) := by
    unfold roundProb roundExpect
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hA : w ∈ A <;> simp [hA]
  rw [roundProb_univ] at hpartition
  linarith

/-- A product of coordinate factors can be summed by `Fintype.prod_sum`; the extra factor at
coordinate `t` extracts the Bernoulli marginal. -/
theorem roundExpect_bernoulliZ (p : ℝ) {R : ℕ} (t : Fin R) :
    roundExpect p (fun w => bernoulliZ (w t)) = p := by
  classical
  let f : Fin R → Bool → ℝ := fun s z =>
    bernoulliMass p z * (if s = t then bernoulliZ z else 1)
  have hprod : ∀ w : RoundWorld R,
      (∏ s : Fin R, f s (w s)) = roundWeight p w * bernoulliZ (w t) := by
    intro w
    dsimp [f]
    rw [Finset.prod_mul_distrib]
    simp [roundWeight, bernoulliMass]
  unfold roundExpect
  calc
    (∑ w : RoundWorld R, roundWeight p w * bernoulliZ (w t))
        = ∑ w : RoundWorld R, ∏ s : Fin R, f s (w s) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact (hprod w).symm
    _ = ∏ s : Fin R, ∑ z : Bool, f s z := by
          symm
          exact Fintype.prod_sum f
    _ = p := by
      dsimp [f]
      simp [bernoulliMass, bernoulliZ]

/-- Real-valued number of Bernoulli successes in a round world. -/
def roundSuccessCount {R : ℕ} (w : RoundWorld R) : ℝ :=
  ∑ t : Fin R, bernoulliZ (w t)

/-- The expected number of successes in `R` independent Bernoulli rounds is `R p`. -/
theorem roundExpect_successCount (p : ℝ) (R : ℕ) :
    roundExpect p (fun w : RoundWorld R => roundSuccessCount w) = (R : ℝ) * p := by
  classical
  unfold roundExpect roundSuccessCount
  calc
    (∑ w : RoundWorld R,
        roundWeight p w * ∑ t : Fin R, bernoulliZ (w t))
        = ∑ w : RoundWorld R, ∑ t : Fin R,
            roundWeight p w * bernoulliZ (w t) := by
              apply Finset.sum_congr rfl
              intro w hw
              rw [Finset.mul_sum]
    _ = ∑ t : Fin R, ∑ w : RoundWorld R,
          roundWeight p w * bernoulliZ (w t) := by
            rw [Finset.sum_comm]
    _ = ∑ t : Fin R, p := by
          apply Finset.sum_congr rfl
          intro t ht
          simpa [roundExpect] using roundExpect_bernoulliZ (p := p) t
    _ = (R : ℝ) * p := by simp

/-- Replacing a coordinate by its current value does nothing. -/
theorem setRoundSeed_current {R : ℕ} (w : RoundWorld R) (t : Fin R) :
    setRoundSeed w t (w t) = w := by
  funext s
  by_cases hst : s = t
  · subst s
    simp [setRoundSeed]
  · simp [setRoundSeed, hst]

/-- In the nontrivial regime `p < 1/2`, the one-round reveal-probability condition forces a
zero increment whenever the Bernoulli seed is `false`.  Thus every progress increment is
pointwise dominated by the Bernoulli success indicator. -/
theorem progress_increment_le_seed_of_lt_half {R : ℕ} (p : ℝ)
    (inc : Fin R → RoundWorld R → ℕ)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p)
    (hp_half : p < 1 / 2) :
    ∀ t w, (inc t w : ℝ) ≤ bernoulliZ (w t) := by
  intro t w
  cases hwt : w t with
  | true =>
      rcases h01 t w with hzero | hone
      · simp [hzero, bernoulliZ, hwt]
      · simp [hone, bernoulliZ, hwt]
  | false =>
      have hset : setRoundSeed w t false = w := by
        rw [← hwt]
        exact setRoundSeed_current w t
      rcases h01 t w with hzero | hone
      · simp [hzero, bernoulliZ, hwt]
      · exfalso
        have hcond := hreveal t w
        have hfalse : inc t (setRoundSeed w t false) = 1 := by
          simpa [hset] using hone
        unfold oneRoundRevealProb at hcond
        rw [if_pos hfalse] at hcond
        by_cases htrue : inc t (setRoundSeed w t true) = 1
        · rw [if_pos htrue] at hcond
          linarith
        · rw [if_neg htrue] at hcond
          linarith

/-- In the small-`p` regime, total progress is pointwise dominated by the number of Bernoulli
successes. -/
theorem progress_sum_le_successCount_of_lt_half {R : ℕ} (p : ℝ)
    (inc : Fin R → RoundWorld R → ℕ)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p)
    (hp_half : p < 1 / 2) (w : RoundWorld R) :
    (∑ t : Fin R, (inc t w : ℝ)) ≤ roundSuccessCount w := by
  unfold roundSuccessCount
  exact Finset.sum_le_sum fun t ht =>
    progress_increment_le_seed_of_lt_half p inc h01 hreveal hp_half t w

/-- Markov bound for the progress event in the small-`p` regime. -/
theorem progress_bad_probability_le_quarter_of_lt_half
    (R T : ℕ) (p : ℝ) (inc : Fin R → RoundWorld R → ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hp_half : p < 1 / 2)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p)
    (hT : 8 ≤ T) (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    roundProb p {w | T ≤ ∑ t : Fin R, inc t w} ≤ 1 / 4 := by
  classical
  let Bad : Set (RoundWorld R) := {w | T ≤ ∑ t : Fin R, inc t w}
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 8) hT)
  have hpoint : ∀ w : RoundWorld R,
      (T : ℝ) * (if w ∈ Bad then 1 else 0) ≤ roundSuccessCount w := by
    intro w
    by_cases hbad : w ∈ Bad
    · have hsum := progress_sum_le_successCount_of_lt_half p inc h01 hreveal hp_half w
      have hcast : (T : ℝ) ≤ ∑ t : Fin R, (inc t w : ℝ) := by
        exact_mod_cast hbad
      simp [hbad]
      exact le_trans hcast hsum
    · have hnonneg : 0 ≤ roundSuccessCount w := by
        unfold roundSuccessCount
        apply Finset.sum_nonneg
        intro t ht
        cases h : w t <;> simp [bernoulliZ, h]
      simpa [hbad] using hnonneg
  have hweighted : (T : ℝ) * roundProb p Bad ≤
      roundExpect p (fun w : RoundWorld R => roundSuccessCount w) := by
    unfold roundProb roundExpect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    have hwgt : 0 ≤ roundWeight p w := roundWeight_nonneg p (le_of_lt hp) hp1 w
    have hmul := mul_le_mul_of_nonneg_left (hpoint w) hwgt
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hRp : (R : ℝ) * p ≤ (T : ℝ) / 4 := by
    have hden : 0 < 4 * p := mul_pos (by norm_num) hp
    have hm := (le_div_iff₀ hden).1 hR
    nlinarith
  rw [roundExpect_successCount] at hweighted
  change roundProb p {w | T ≤ ∑ t : Fin R, inc t w} ≤ 1 / 4
  change roundProb p Bad ≤ 1 / 4
  nlinarith

/-- Paper Lemma 1.5 in the finite Bernoulli model used by this artifact.  The proof handles
`p=0`, `p≥1/2`, and `0<p<1/2` separately; the latter uses the Markov argument above. -/
theorem lemma15_progress_bound : ProgressBoundStatement := by
  intro R T p inc hp0 hp1 h01 _hadapt hreveal hT hR
  by_cases hpz : p = 0
  · subst p
    have hRzero_real : (R : ℝ) ≤ 0 := by simpa using hR
    have hRzero : R = 0 := by
      have : R ≤ 0 := by exact_mod_cast hRzero_real
      exact Nat.eq_zero_of_le_zero this
    subst R
    have hgood : {w : RoundWorld 0 | (∑ t : Fin 0, inc t w) < T} = Set.univ := by
      ext w
      simp
      omega
    rw [hgood, roundProb_univ]
    norm_num
  · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    by_cases hhalf : (1 / 2 : ℝ) ≤ p
    · have hden : 0 < 4 * p := mul_pos (by norm_num) hp
      have hmul := (le_div_iff₀ hden).1 hR
      have hTpos : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 8) hT)
      have hRTreal : (R : ℝ) < T := by
        nlinarith
      have hRT : R < T := by exact_mod_cast hRTreal
      have hgood : {w : RoundWorld R | (∑ t : Fin R, inc t w) < T} = Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        have hsumR : (∑ t : Fin R, inc t w) ≤ R := by
          calc
            (∑ t : Fin R, inc t w) ≤ ∑ _t : Fin R, 1 := by
              apply Finset.sum_le_sum
              intro t ht
              rcases h01 t w with h0 | h1 <;> omega
            _ = R := by simp
        exact lt_of_le_of_lt hsumR hRT
      rw [hgood, roundProb_univ]
      norm_num
    · have hp_half : p < 1 / 2 := lt_of_not_ge hhalf
      let Bad : Set (RoundWorld R) := {w | T ≤ ∑ t : Fin R, inc t w}
      have hbad : roundProb p Bad ≤ 1 / 4 := by
        exact progress_bad_probability_le_quarter_of_lt_half R T p inc hp hp1 hp_half
          h01 hreveal hT hR
      have hcomp : {w : RoundWorld R | (∑ t : Fin R, inc t w) < T} = Badᶜ := by
        ext w
        simp [Bad, not_le]
      rw [hcomp, roundProb_compl]
      linarith

/-! ### Progress-process bridge for Proposition 2.4

The next structure isolates exactly what the oracle/support induction must provide: an adapted
0/1 progress process satisfying the one-round reveal bound and whose failure to accumulate `T`
increments implies that the terminal coordinate has not been revealed.  Once such a process is
constructed from the lifted zero-chain, Lemma 1.5 and the v14 support/expectation theorems close
Proposition 2.4 automatically. -/

structure RunProgressWitness {T R K : ℕ} {O : StochasticOracle T Bool}
    (hTpos : 0 < T) (p : ℝ) (A : BernoulliRun T R K O) where
  inc : Fin R → RoundWorld R → ℕ
  zero_one : ∀ t w, inc t w = 0 ∨ inc t w = 1
  adapted : ProgressAdapted inc
  reveal_prob : ∀ t w, oneRoundRevealProb p inc t w ≤ p
  unfinished_implies_terminal_unrevealed : ∀ w,
    (∑ t : Fin R, inc t w) < T →
      w ∈ terminalUnrevealedEvent hTpos A

/-- Lemma 1.5 plus a run-progress witness yields the terminal-unrevealed probability required by
Proposition 2.4. -/
theorem terminal_unrevealed_probability_of_runProgress {T R K : ℕ}
    {O : StochasticOracle T Bool} (hTpos : 0 < T) (hT : 8 ≤ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : BernoulliRun T R K O) (W : RunProgressWitness hTpos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    1 / 2 < roundProb p (terminalUnrevealedEvent hTpos A) := by
  have hprogress :
      1 / 2 < roundProb p {w | (∑ t : Fin R, W.inc t w) < T} :=
    lemma15_progress_bound R T p W.inc hp0 hp1 W.zero_one W.adapted W.reveal_prob hT hR
  exact lt_of_lt_of_le hprogress
    (roundProb_mono p hp0 hp1 W.unfinished_implies_terminal_unrevealed)

/-- Full Proposition 2.4 once the standard progress process associated with the lifted zero-chain
has been supplied.  No stationarity or expectation argument remains outside Lean. -/
theorem proposition24_of_runProgress {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε)
    (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (liftedOracle B P))
    (W : RunProgressWitness C.dim_pos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    ε ^ 2 < stationarityRisk p L.gradPhi A := by
  apply proposition24_of_terminal_unrevealed_probability C B P L p ε hp hp1 hε hγq hratio A
  exact terminal_unrevealed_probability_of_runProgress C.dim_pos hT p (le_of_lt hp) hp1 A W hR

/-! ### Additional deterministic analytic consequences of Lemma 2.1

These are direct, certificate-free consequences of the imported zero-chain gradient Lipschitz
bound and the quadratic lift algebra.  They are the monotonicity inequalities used in the paper's
strong-concavity argument for Lemma 2.3. -/

/-- The zero-chain gradient contribution to the dual gradient difference is bounded by
`ℓ₀ h ‖y-y'‖²`. -/
theorem lift_chain_inner_bound {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : LiftParameters) (y y' : Vec T) :
    @inner ℝ (Vec T) _
        (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) (y - y')
      ≤ ℓ₀ * P.h * ‖y - y'‖ ^ 2 := by
  let b : Vec T := y - y'
  have hgrad := C.grad_lipschitz (P.β • y) (P.β • y')
  have hβpos : 0 < P.β := div_pos P.h_pos P.q_pos
  have hq0 : 0 ≤ P.q := le_of_lt P.q_pos
  have hinner := real_inner_le_norm
    (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) b
  have hnormdiff : ‖P.β • y - P.β • y'‖ = P.β * ‖b‖ := by
    rw [← smul_sub]
    simp [b, norm_smul, Real.norm_eq_abs, abs_of_pos hβpos]
  have hgrad' : ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ ≤
      ℓ₀ * P.β * ‖b‖ := by
    rw [hnormdiff] at hgrad
    simpa [mul_assoc] using hgrad
  have hnormq : ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ =
      P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos P.q_pos]
  rw [hnormq] at hinner
  have hmul := mul_le_mul_of_nonneg_left hgrad' hq0
  have hnorm0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hprod := mul_le_mul_of_nonneg_right hmul hnorm0
  have hqh : P.q * P.β = P.h := P.q_mul_beta
  dsimp [b] at hinner hprod ⊢
  calc
    @inner ℝ (Vec T) _
        (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) (y - y')
        ≤ P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ * ‖y - y'‖ := hinner
    _ ≤ P.q * (ℓ₀ * P.β * ‖y - y'‖) * ‖y - y'‖ := hprod
    _ = ℓ₀ * P.h * ‖y - y'‖ ^ 2 := by rw [← hqh]; ring

/-- The reverse Cauchy estimate for the chain term.  Together with the upper estimate above it
gives the two-sided dual monotonicity bounds used to bracket the actual strong-concavity modulus. -/
theorem lift_chain_inner_lower_bound {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : LiftParameters) (y y' : Vec T) :
    -(ℓ₀ * P.h * ‖y - y'‖ ^ 2) ≤
      @inner ℝ (Vec T) _
        (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) (y - y') := by
  let b : Vec T := y - y'
  have hgrad := C.grad_lipschitz (P.β • y) (P.β • y')
  have hβpos : 0 < P.β := div_pos P.h_pos P.q_pos
  have hq0 : 0 ≤ P.q := le_of_lt P.q_pos
  have habs := abs_real_inner_le_norm
    (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) b
  have hneg :
      -(‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ * ‖b‖) ≤
        @inner ℝ (Vec T) _
          (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) b := by
    have habs' := neg_le_of_abs_le habs
    simpa [mul_comm] using habs'
  have hnormdiff : ‖P.β • y - P.β • y'‖ = P.β * ‖b‖ := by
    rw [← smul_sub]
    simp [b, norm_smul, Real.norm_eq_abs, abs_of_pos hβpos]
  have hgrad' : ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ ≤
      ℓ₀ * P.β * ‖b‖ := by
    rw [hnormdiff] at hgrad
    simpa [mul_assoc] using hgrad
  have hnormq : ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ =
      P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos P.q_pos]
  have hmul := mul_le_mul_of_nonneg_left hgrad' hq0
  have hnorm0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hprod := mul_le_mul_of_nonneg_right hmul hnorm0
  have hqh : P.q * P.β = P.h := P.q_mul_beta
  rw [hnormq] at hneg
  dsimp [b] at hneg hprod ⊢
  have hupper :
      P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ * ‖y - y'‖ ≤
        ℓ₀ * P.h * ‖y - y'‖ ^ 2 := by
    calc
      P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖ * ‖y - y'‖
          ≤ P.q * (ℓ₀ * P.β * ‖y - y'‖) * ‖y - y'‖ := hprod
      _ = ℓ₀ * P.h * ‖y - y'‖ ^ 2 := by rw [← hqh]; ring
  exact le_trans (neg_le_neg hupper) hneg

/-- The lifted dual gradient is `μ`-strongly antimonotone.  This is the differential core of the
paper's strong-concavity proof. -/
theorem lift_gradY_strong_antimonotone {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y y' : Vec T) :
    @inner ℝ (Vec T) _
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x)))
      (y - y')
      ≤ -P.μ * ‖y - y'‖ ^ 2 := by
  have hchain := lift_chain_inner_bound C P y y'
  have hquad :
      @inner ℝ (Vec T) _ (P.ν • (y - y')) (y - y') =
        P.ν * ‖y - y'‖ ^ 2 := by
    simpa [pow_two] using real_inner_smul_self_left (y - y') P.ν
  have hν : P.ν = P.μ + ℓ₀ * P.h := rfl
  have hvec :
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x))) =
      P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')) -
        P.ν • (y - y') := by
    module
  rw [hvec, inner_sub_left, hquad]
  rw [hν]
  nlinarith

/-- Reverse dual-gradient monotonicity bound from the paper: the effective uniform strong-concavity
modulus cannot exceed `ν + ℓ₀ h`.  This is the analytic inequality used in Lemma 2.3(i). -/
theorem lift_gradY_reverse_bound {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y y' : Vec T) :
    -(P.ν + ℓ₀ * P.h) * ‖y - y'‖ ^ 2 ≤
      @inner ℝ (Vec T) _
        ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
         (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x)))
        (y - y') := by
  have hchain := lift_chain_inner_lower_bound C P y y'
  have hquad :
      @inner ℝ (Vec T) _ (P.ν • (y - y')) (y - y') =
        P.ν * ‖y - y'‖ ^ 2 := by
    simpa [pow_two] using real_inner_smul_self_left (y - y') P.ν
  have hvec :
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x))) =
      P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')) -
        P.ν • (y - y') := by
    module
  rw [hvec, inner_sub_left, hquad]
  nlinarith


/-! ## v16 proof phase VI: bounded-variance assembly

This section continues the end-to-end bounded-variance proof.  It proves the exact noise budget
induced by equation (18), transfers Lemma 3.1 through the quadratic lift to the actual oracle,
and specialises Proposition 2.4 to the bounded-variance parameter choice.  These are actual proof
terms; no new axioms are introduced. -/

/-- In the noiseless branch of equation (18), `p = 1`. -/
theorem bv_p_eq_one_of_sigma_zero (P : BVParameters) (hσ : P.σ = 0) : P.p = 1 := by
  rw [P.p_def]
  simp [hσ]

/-- In the genuinely stochastic branch, the reveal probability is the minimum in equation (18). -/
theorem bv_p_eq_min_of_sigma_ne_zero (P : BVParameters) (hσ : P.σ ≠ 0) :
    P.p = min 1 (P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2) := by
  rw [P.p_def]
  simp [hσ]

/-- The Bernoulli masking chosen in equation (18) makes the lifted variance term fit inside the
prescribed variance budget `σ²`. -/
theorem bv_noise_budget (P : BVParameters) :
    P.q ^ 2 * g₀ ^ 2 * (1 - P.p) / P.p ≤ P.σ ^ 2 := by
  by_cases hσ : P.σ = 0
  · have hp1 : P.p = 1 := bv_p_eq_one_of_sigma_zero P hσ
    rw [hσ, hp1]
    norm_num
  · have hpdef := bv_p_eq_min_of_sigma_ne_zero P hσ
    let a : ℝ := P.q ^ 2 * g₀ ^ 2
    have hq : 0 < P.q := by
      rw [P.q_def]
      exact div_pos (mul_pos (by norm_num) P.ε_pos) P.γ_pos
    have hg : 0 < g₀ := by norm_num [g₀]
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hs2 : 0 < P.σ ^ 2 := sq_pos_of_ne_zero hσ
    by_cases hlarge : 1 ≤ a / P.σ ^ 2
    · have hp1 : P.p = 1 := by
        rw [hpdef, min_eq_left hlarge]
      rw [hp1]
      simp
      positivity
    · have hsmall : a / P.σ ^ 2 ≤ 1 := le_of_not_ge hlarge
      have hp : P.p = a / P.σ ^ 2 := by
        rw [hpdef, min_eq_right hsmall]
      rw [hp]
      have ha0 : a ≠ 0 := ne_of_gt ha
      have hs0 : P.σ ^ 2 ≠ 0 := ne_of_gt hs2
      have heq : a * (1 - a / P.σ ^ 2) / (a / P.σ ^ 2) = P.σ ^ 2 - a := by
        field_simp [ha0, hs0]
      change a * (1 - a / P.σ ^ 2) / (a / P.σ ^ 2) ≤ P.σ ^ 2
      rw [heq]
      exact sub_le_self _ (le_of_lt ha)

/-- The concrete lifted BV oracle therefore has variance at most the prescribed `σ²`. -/
theorem bvConstructedOracle_boundedVariance {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P)
    (H : BVBaseOracleCertificate T C P.p) :
    OracleBoundedVariance (bvConstructedPopulation W) (bernoulliLaw P.p)
      (bvConstructedOracle W) P.σ := by
  intro x y
  have hbase : BaseVarianceHypothesis C W.B P.p g₀ := bvWitness_baseVariance W H
  have htransfer := lifted_variance_transfer C W.B W.LP P.p g₀ hbase x y
  have hbudget := bv_noise_budget P
  have hq : W.LP.q = P.q := W.lift_q
  have htransfer' :
      bernoulliExpectReal P.p (fun Z =>
        ‖liftedGx W.LP x y Z - (W.LP.ν * W.LP.γ) • (y - W.LP.γ • x)‖ ^ 2 +
        ‖liftedGy W.B W.LP x y Z -
          (W.LP.q • C.gradF (W.LP.β • y) - W.LP.ν • (y - W.LP.γ • x))‖ ^ 2) ≤
        P.q ^ 2 * g₀ ^ 2 * (1 - P.p) / P.p := by
    simpa [hq] using htransfer
  change bernoulliExpectReal P.p (fun Z =>
      ‖(bvConstructedOracle W).Gx x y Z - (bvConstructedPopulation W).gradX x y‖ ^ 2 +
      ‖(bvConstructedOracle W).Gy x y Z - (bvConstructedPopulation W).gradY x y‖ ^ 2) ≤ P.σ ^ 2
  exact le_trans htransfer' hbudget

/-- Equation (17) gives `γ q = 2 ε`. -/
theorem bv_gamma_mul_q (P : BVParameters) : P.γ * P.q = 2 * P.ε := by
  rw [P.q_def]
  field_simp [ne_of_gt P.γ_pos]

/-- A bounded-variance construction witness inherits the paper identity `γ q = 2 ε`. -/
theorem bvWitness_gamma_mul_q {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P) :
    W.LP.γ * W.LP.q = 2 * P.ε := by
  rw [W.lift_gamma, W.lift_q]
  exact bv_gamma_mul_q P

/-- A bounded-variance construction witness also inherits equation (19), `ℓ₀ h / ν = 1/5`. -/
theorem bvWitness_transfer_ratio {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P) :
    ℓ₀ * W.LP.h / W.LP.ν = 1 / 5 := by
  have h := LiftParameters.transfer_ratio_bv P.μ P.μ_pos
  simpa [LiftParameters.ν, W.lift_h, W.lift_mu, BVParameters.h] using h

/-- Proposition 2.4 specialised to the exact bounded-variance parameter choice.  All numerical
hypotheses `γq=2ε` and `ℓ₀h/ν≤1/5` are discharged from equations (17)--(19). -/
theorem proposition24_bv_of_runProgress {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (RW : RunProgressWitness C.dim_pos P.p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    P.ε ^ 2 < stationarityRisk P.p (bvConstructedPopulation W).gradPhi A := by
  have hp : 0 < P.p := bv_p_pos P
  have hp1 : P.p ≤ 1 := bv_p_le_one P
  apply proposition24_of_runProgress C W.B W.LP W.lift_properties P.p P.ε
    hp hp1 P.ε_pos (bvWitness_gamma_mul_q W) ?_ hT A RW hR
  rw [bvWitness_transfer_ratio W]

/-- Consequently, any BV run that attains the target risk must use more than `T/(4p)` rounds,
provided the standard progress witness has been constructed. -/
theorem bv_round_lower_bound_of_runProgress {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (RW : RunProgressWitness C.dim_pos P.p A)
    (hrisk : stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2) :
    (T : ℝ) / (4 * P.p) < R := by
  by_contra hnot
  have hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p) := le_of_not_gt hnot
  have hbad := proposition24_bv_of_runProgress C P W hT A RW hR
  linarith

/-- The round lower bound immediately transfers to returned-gradient complexity on every valid
batch trace. -/
theorem bv_gradient_lower_bound_of_runProgress {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (RW : RunProgressWitness C.dim_pos P.p A)
    (hrisk : stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2)
    (hbatch : ∀ w, ValidBatchSizes (A.trace w)) :
    ∀ w, (T : ℝ) / (4 * P.p) < returnedGradientCount (A.trace w) := by
  intro w
  have hround := bv_round_lower_bound_of_runProgress C P W hT A RW hrisk
  have hcount : R ≤ returnedGradientCount (A.trace w) :=
    (gradientCountAccounting T R K (A.trace w) (hbatch w)).1
  have hcast : (R : ℝ) ≤ returnedGradientCount (A.trace w) := by exact_mod_cast hcount
  exact lt_of_lt_of_le hround hcast

/-! ### Support algebra for the remaining run-progress induction

The following facts are the deterministic support calculus needed to construct the canonical
`RunProgressWitness` from the explicit BV lifted oracle.  They reduce the remaining induction to
round bookkeeping rather than analytic estimates. -/

/-- Scalar multiplication cannot create a new nonzero coordinate. -/
theorem prog_zero_smul_le {T : ℕ} (c : ℝ) (u : Vec T) :
    prog 0 (c • u) ≤ prog 0 u := by
  apply prog_zero_le_of_zero_above
  intro i hi
  have hu : u i = 0 := coord_eq_zero_of_prog_lt u i hi
  simp [hu]

/-- Addition cannot create support beyond the maximum support of the summands. -/
theorem prog_zero_add_le_max {T : ℕ} (u v : Vec T) :
    prog 0 (u + v) ≤ max (prog 0 u) (prog 0 v) := by
  apply prog_zero_le_of_zero_above
  intro i hi
  have huProg : prog 0 u < i.1 + 1 := lt_of_le_of_lt (Nat.le_max_left _ _) hi
  have hvProg : prog 0 v < i.1 + 1 := lt_of_le_of_lt (Nat.le_max_right _ _) hi
  have hu := coord_eq_zero_of_prog_lt u i huProg
  have hv := coord_eq_zero_of_prog_lt v i hvProg
  simp [hu, hv]

/-- Subtraction obeys the same support bound. -/
theorem prog_zero_sub_le_max {T : ℕ} (u v : Vec T) :
    prog 0 (u - v) ≤ max (prog 0 u) (prog 0 v) := by
  rw [sub_eq_add_neg]
  have h := prog_zero_add_le_max u (-v)
  have hneg : prog 0 (-v) ≤ prog 0 v := by
    simpa using prog_zero_smul_le (-1 : ℝ) v
  exact le_trans h (max_le_max_left _ hneg)

/-- Any positive-threshold progress is bounded by ordinary support progress. -/
theorem prog_threshold_le_zero {T : ℕ} (a : ℝ) (ha : 0 ≤ a) (u : Vec T) :
    prog a u ≤ prog 0 u :=
  prog_antitone_threshold u ha

/-- The deterministic primal block of the quadratic lift cannot reveal a coordinate outside the
support of the current query pair. -/
theorem liftedGx_prog_le_pairProg {T : ℕ} (P : LiftParameters) (x y : Vec T) (Z : Bool) :
    prog 0 (liftedGx P x y Z) ≤ pairProg x y := by
  unfold liftedGx pairProg
  have hsmul := prog_zero_smul_le (P.ν * P.γ) (y - P.γ • x)
  have hsub := prog_zero_sub_le_max y (P.γ • x)
  have hx := prog_zero_smul_le P.γ x
  calc
    prog 0 ((P.ν * P.γ) • (y - P.γ • x)) ≤ prog 0 (y - P.γ • x) := hsmul
    _ ≤ max (prog 0 y) (prog 0 (P.γ • x)) := hsub
    _ ≤ max (prog 0 y) (prog 0 x) := max_le_max_left _ hx
    _ = max (prog 0 x) (prog 0 y) := by omega

/-- On the `Z=false` branch, the explicit BV base oracle cannot advance beyond the support of its
input. -/
theorem bvBaseOracle_false_prog_le_zero {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) :
    prog 0 (bvBaseOracle C p u false) ≤ prog 0 u := by
  exact le_trans (bvBaseOracle_prog_false_le C p u)
    (prog_threshold_le_zero (1 / 4) (by norm_num) u)

/-- On the `Z=true` branch, the explicit BV base oracle advances support by at most one. -/
theorem bvBaseOracle_true_prog_le_succ_zero {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (u : Vec T) :
    prog 0 (bvBaseOracle C p u true) ≤ prog 0 u + 1 := by
  have h := bvBaseOracle_prog_le_succ C p u true
  have hq := prog_threshold_le_zero (1 / 4) (by norm_num) u
  omega



/-- The deterministic coupling term in the lifted dual block stays inside the support of the query
pair. -/
theorem lift_dual_coupling_prog_le_pairProg {T : ℕ} (P : LiftParameters) (x y : Vec T) :
    prog 0 (P.ν • (y - P.γ • x)) ≤ pairProg x y := by
  have hsmul := prog_zero_smul_le P.ν (y - P.γ • x)
  have hsub := prog_zero_sub_le_max y (P.γ • x)
  have hx := prog_zero_smul_le P.γ x
  calc
    prog 0 (P.ν • (y - P.γ • x)) ≤ prog 0 (y - P.γ • x) := hsmul
    _ ≤ max (prog 0 y) (prog 0 (P.γ • x)) := hsub
    _ ≤ max (prog 0 y) (prog 0 x) := max_le_max_left _ hx
    _ = pairProg x y := by simp [pairProg, max_comm]

/-- For the exact BV construction, a false Bernoulli seed creates no new pair coordinate. -/
theorem bvConstructed_response_false_pairProg_le {T : ℕ}
    {C : ExplicitZeroChainCertificate T} {P : BVParameters}
    (W : BVConstructionWitness C P) (x y : Vec T) :
    pairProg (liftedGx W.LP x y false) (liftedGy W.B W.LP x y false) ≤
      pairProg x y := by
  have hx : prog 0 (liftedGx W.LP x y false) ≤ pairProg x y :=
    liftedGx_prog_le_pairProg W.LP x y false
  have hbase0 : prog 0 (W.B.g (W.LP.β • y) false) ≤ prog 0 y := by
    rw [W.base_oracle_def]
    exact le_trans (bvBaseOracle_false_prog_le_zero C P.p (W.LP.β • y))
      (prog_zero_smul_le W.LP.β y)
  have hbase : prog 0 (W.LP.q • W.B.g (W.LP.β • y) false) ≤ prog 0 y :=
    le_trans (prog_zero_smul_le W.LP.q (W.B.g (W.LP.β • y) false)) hbase0
  have hdet : prog 0 (W.LP.ν • (y - W.LP.γ • x)) ≤ pairProg x y :=
    lift_dual_coupling_prog_le_pairProg W.LP x y
  have hy0 := prog_zero_sub_le_max
    (W.LP.q • W.B.g (W.LP.β • y) false)
    (W.LP.ν • (y - W.LP.γ • x))
  have hy : prog 0 (liftedGy W.B W.LP x y false) ≤ pairProg x y := by
    unfold liftedGy
    exact le_trans hy0 (max_le (le_trans hbase (Nat.le_max_right _ _)) hdet)
  exact max_le hx hy

/-- For the exact BV construction, a true Bernoulli seed can create at most one new pair
coordinate. -/
theorem bvConstructed_response_true_pairProg_le_succ {T : ℕ}
    {C : ExplicitZeroChainCertificate T} {P : BVParameters}
    (W : BVConstructionWitness C P) (x y : Vec T) :
    pairProg (liftedGx W.LP x y true) (liftedGy W.B W.LP x y true) ≤
      pairProg x y + 1 := by
  have hx0 : prog 0 (liftedGx W.LP x y true) ≤ pairProg x y :=
    liftedGx_prog_le_pairProg W.LP x y true
  have hx : prog 0 (liftedGx W.LP x y true) ≤ pairProg x y + 1 :=
    le_trans hx0 (Nat.le_add_right _ _)
  have hbase0 : prog 0 (W.B.g (W.LP.β • y) true) ≤ prog 0 y + 1 := by
    rw [W.base_oracle_def]
    have h := bvBaseOracle_true_prog_le_succ_zero C P.p (W.LP.β • y)
    have hs := prog_zero_smul_le W.LP.β y
    omega
  have hbase : prog 0 (W.LP.q • W.B.g (W.LP.β • y) true) ≤ pairProg x y + 1 := by
    have hs := prog_zero_smul_le W.LP.q (W.B.g (W.LP.β • y) true)
    have hy : prog 0 y ≤ pairProg x y := Nat.le_max_right _ _
    omega
  have hdet0 : prog 0 (W.LP.ν • (y - W.LP.γ • x)) ≤ pairProg x y :=
    lift_dual_coupling_prog_le_pairProg W.LP x y
  have hdet : prog 0 (W.LP.ν • (y - W.LP.γ • x)) ≤ pairProg x y + 1 :=
    le_trans hdet0 (Nat.le_add_right _ _)
  have hy0 := prog_zero_sub_le_max
    (W.LP.q • W.B.g (W.LP.β • y) true)
    (W.LP.ν • (y - W.LP.γ • x))
  have hy : prog 0 (liftedGy W.B W.LP x y true) ≤ pairProg x y + 1 := by
    unfold liftedGy
    exact le_trans hy0 (max_le hbase hdet)
  exact max_le hx hy

/-- Any active coordinate lies below the pair progress. -/
theorem index_succ_le_pairProg_of_mem_psupp {T : ℕ} {x y : Vec T} {i : Fin T}
    (hi : i ∈ psupp x y) : i.1 + 1 ≤ pairProg x y := by
  rcases hi with hxi | hyi
  · have hpos : (0 : ℝ) < |x i| := abs_pos.mpr hxi
    have hib : i.1 + 1 ≤ T := Nat.succ_le_iff.mpr i.2
    have hp : i.1 + 1 ≤ prog 0 x := by
      unfold prog
      exact Nat.le_findGreatest hib ⟨i, rfl, hpos⟩
    exact le_trans hp (Nat.le_max_left _ _)
  · have hpos : (0 : ℝ) < |y i| := abs_pos.mpr hyi
    have hib : i.1 + 1 ≤ T := Nat.succ_le_iff.mpr i.2
    have hp : i.1 + 1 ≤ prog 0 y := by
      unfold prog
      exact Nat.le_findGreatest hib ⟨i, rfl, hpos⟩
    exact le_trans hp (Nat.le_max_right _ _)

/-- If every prior response has pair progress at most `m`, every zero-respecting query at the
next round also has pair progress at most `m`. -/
theorem zeroRespecting_query_pairProg_le {T R K : ℕ}
    (tr : InteractionTrace T R K) (hzr : PairZeroRespectingTrace tr)
    (t : Fin R) (m : ℕ)
    (hprior : ∀ s : Fin R, s.1 < t.1 → ∀ k : Fin K, ∀ r : Vec T × Vec T,
      tr.response s k = some r → pairProg r.1 r.2 ≤ m)
    (k : Fin K) (q : Vec T × Vec T) (hq : tr.query t k = some q) :
    pairProg q.1 q.2 ≤ m := by
  have hsub := hzr.1 t k q hq
  have hx : prog 0 q.1 ≤ m := by
    apply prog_zero_le_of_zero_above
    intro i hi
    by_contra hne
    have himem : i ∈ psupp q.1 q.2 := Or.inl hne
    rcases hsub himem with ⟨s, hst, ks, r, hrs, hir⟩
    have hidx := index_succ_le_pairProg_of_mem_psupp hir
    have hrb := hprior s hst ks r hrs
    omega
  have hy : prog 0 q.2 ≤ m := by
    apply prog_zero_le_of_zero_above
    intro i hi
    by_contra hne
    have himem : i ∈ psupp q.1 q.2 := Or.inr hne
    rcases hsub himem with ⟨s, hst, ks, r, hrs, hir⟩
    have hidx := index_succ_le_pairProg_of_mem_psupp hir
    have hrb := hprior s hst ks r hrs
    omega
  exact max_le hx hy

/-- The seed-success increment is adapted and has one-round reveal probability exactly `p`. -/
def seedSuccessIncrement {R : ℕ} (t : Fin R) (w : RoundWorld R) : ℕ :=
  if w t then 1 else 0

 theorem seedSuccessIncrement_zero_one {R : ℕ} :
    ∀ (t : Fin R) (w : RoundWorld R),
      seedSuccessIncrement t w = 0 ∨ seedSuccessIncrement t w = 1 := by
  intro t w
  unfold seedSuccessIncrement
  cases h : w t <;> simp [h]

 theorem seedSuccessIncrement_adapted {R : ℕ} :
    ProgressAdapted (seedSuccessIncrement (R := R)) := by
  intro w w' t hprefix
  unfold seedSuccessIncrement
  rw [hprefix t (Nat.le_refl _)]

 theorem seedSuccessIncrement_reveal_prob {R : ℕ} (p : ℝ) :
    ∀ t w, oneRoundRevealProb p (seedSuccessIncrement (R := R)) t w = p := by
  intro t w
  unfold oneRoundRevealProb seedSuccessIncrement setRoundSeed
  simp



/-! ### Canonical progress witness for the explicit BV construction -/

/-- Prefix count written over `Finset.range`, convenient for induction on the round number. -/
def roundSuccessPrefixR {R : ℕ} (w : RoundWorld R) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n,
    if h : j < R then seedSuccessIncrement ⟨j, h⟩ w else 0

/-- Adding one valid round adds exactly its Bernoulli success indicator. -/
theorem roundSuccessPrefixR_succ {R : ℕ} (w : RoundWorld R) (n : ℕ) (hn : n < R) :
    roundSuccessPrefixR w (n + 1) =
      roundSuccessPrefixR w n + seedSuccessIncrement ⟨n, hn⟩ w := by
  unfold roundSuccessPrefixR
  rw [Finset.sum_range_succ]
  simp [hn]

/-- The full prefix is the sum of the seed-success increments over `Fin R`. -/
theorem roundSuccessPrefixR_total {R : ℕ} (w : RoundWorld R) :
    roundSuccessPrefixR w R = ∑ t : Fin R, seedSuccessIncrement t w := by
  unfold roundSuccessPrefixR
  simpa using
    (Finset.sum_fin_eq_sum_range (fun t : Fin R => seedSuccessIncrement t w)).symm

/-- Every response produced before prefix `n` has pair progress at most the number of successful
Bernoulli seeds in that prefix.  This is the round-by-round support induction hidden in the paper's
phrase "the chain reveals sequentially". -/
theorem bv_response_pairProg_le_successPrefix {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (w : RoundWorld R) :
    ∀ n : ℕ, n ≤ R →
      ∀ s : Fin R, s.1 < n → ∀ k : Fin K, ∀ r : Vec T × Vec T,
        (A.trace w).response s k = some r →
          pairProg r.1 r.2 ≤ roundSuccessPrefixR w n := by
  intro n
  induction n with
  | zero =>
      intro hn s hs
      omega
  | succ n ih =>
      intro hn s hs k r hrs
      have hnr : n < R := by omega
      have hprefix := roundSuccessPrefixR_succ w n hnr
      by_cases hsn : s.1 < n
      · have hprev := ih (Nat.le_of_lt hnr) s hsn k r hrs
        have hinc0 : 0 ≤ seedSuccessIncrement ⟨n, hnr⟩ w := Nat.zero_le _
        omega
      · have hseqval : s.1 = n := by omega
        have hseq : s = (⟨n, hnr⟩ : Fin R) := Fin.ext hseqval
        subst s
        let t : Fin R := ⟨n, hnr⟩
        have hprior : ∀ s' : Fin R, s'.1 < t.1 → ∀ k' : Fin K,
            ∀ r' : Vec T × Vec T, (A.trace w).response s' k' = some r' →
              pairProg r'.1 r'.2 ≤ roundSuccessPrefixR w n := by
          intro s' hs' k' r' hrs'
          exact ih (Nat.le_of_lt hnr) s' hs' k' r' hrs'
        cases hq : (A.trace w).query t k with
        | none =>
            have hc := A.response_consistent w t k
            rw [hq] at hc
            rw [hrs] at hc
            simp at hc
        | some q =>
            have hqprog := zeroRespecting_query_pairProg_le
              (A.trace w) (A.zero_respecting w) t (roundSuccessPrefixR w n)
              hprior k q hq
            have hc := A.response_consistent w t k
            rw [hq] at hc
            rw [hrs] at hc
            have hrpair : r =
                ((bvConstructedOracle W).Gx q.1 q.2 (w t),
                 (bvConstructedOracle W).Gy q.1 q.2 (w t)) := by
              exact Option.some.inj hc
            rw [hrpair]
            simp only [Prod.fst, Prod.snd]
            cases hz : w t with
            | false =>
                have hresp := bvConstructed_response_false_pairProg_le W q.1 q.2
                have hprefix' : roundSuccessPrefixR w (n + 1) = roundSuccessPrefixR w n := by
                  simpa [t, seedSuccessIncrement, hz] using hprefix
                calc
                  pairProg ((bvConstructedOracle W).Gx q.1 q.2 false)
                      ((bvConstructedOracle W).Gy q.1 q.2 false)
                      ≤ pairProg q.1 q.2 := hresp
                  _ ≤ roundSuccessPrefixR w n := hqprog
                  _ = roundSuccessPrefixR w (n + 1) := hprefix'.symm
            | true =>
                have hresp := bvConstructed_response_true_pairProg_le_succ W q.1 q.2
                have hprefix' :
                    roundSuccessPrefixR w (n + 1) = roundSuccessPrefixR w n + 1 := by
                  simpa [t, seedSuccessIncrement, hz] using hprefix
                have hstep : pairProg q.1 q.2 + 1 ≤ roundSuccessPrefixR w n + 1 :=
                  Nat.add_le_add_right hqprog 1
                calc
                  pairProg ((bvConstructedOracle W).Gx q.1 q.2 true)
                      ((bvConstructedOracle W).Gy q.1 q.2 true)
                      ≤ pairProg q.1 q.2 + 1 := hresp
                  _ ≤ roundSuccessPrefixR w n + 1 := hstep
                  _ = roundSuccessPrefixR w (n + 1) := hprefix'.symm

/-- If fewer than `T` Bernoulli successes occur, the terminal coordinate cannot have appeared in
any response of a BV zero-respecting run. -/
theorem bv_successes_lt_T_implies_terminal_unrevealed {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (w : RoundWorld R)
    (hsucc : (∑ t : Fin R, seedSuccessIncrement t w) < T) :
    w ∈ terminalUnrevealedEvent C.dim_pos A := by
  intro hrev
  rcases hrev with ⟨s, k, r, hrs, hmem⟩
  have hrb := bv_response_pairProg_le_successPrefix C P W A w R (Nat.le_refl R)
    s s.2 k r hrs
  rw [roundSuccessPrefixR_total] at hrb
  have hidx := index_succ_le_pairProg_of_mem_psupp hmem
  have hlast : (lastIndexOfPos C.dim_pos).1 + 1 = T := by
    simp [lastIndexOfPos]
    omega
  rw [hlast] at hidx
  omega

/-- The seed-success process is the canonical `RunProgressWitness` for the explicit BV oracle. -/
def bvCanonicalRunProgressWitness {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (A : BernoulliRun T R K (bvConstructedOracle W)) :
    RunProgressWitness C.dim_pos P.p A where
  inc := seedSuccessIncrement
  zero_one := seedSuccessIncrement_zero_one
  adapted := seedSuccessIncrement_adapted
  reveal_prob := by
    intro t w
    rw [seedSuccessIncrement_reveal_prob]
  unfinished_implies_terminal_unrevealed := by
    intro w hsum
    exact bv_successes_lt_T_implies_terminal_unrevealed C P W A w hsum

/-- Proposition 2.4 is now closed end-to-end for the explicit BV construction: no external
progress witness remains. -/
theorem proposition24_bv {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    P.ε ^ 2 < stationarityRisk P.p (bvConstructedPopulation W).gradPhi A := by
  exact proposition24_bv_of_runProgress C P W hT A
    (bvCanonicalRunProgressWitness C P W A) hR

/-- Equivalently, every successful BV run needs more than `T/(4p)` rounds. -/
theorem bv_round_lower_bound {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (hrisk : stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2) :
    (T : ℝ) / (4 * P.p) < R := by
  exact bv_round_lower_bound_of_runProgress C P W hT A
    (bvCanonicalRunProgressWitness C P W A) hrisk



/-! ## v17 proof phase VII: exact BV scaling and Theorem 3.3 rate assembly

This section closes the remaining *rate algebra* between Lemma 3.2 and Theorem 3.3.
It does not manufacture the analytic Lemma-2.3 certificate or the actual-condition-number
certificate; rather, once a genuine `Lemma32Conclusion` is available, the paper's
`T/p -> LΔ ε⁻² max{1, κσ²/ε²}` conversion and the returned-gradient consequence are
proved by Lean.
-/

/-- Positivity of the BV signal scale `q`. -/
theorem bv_q_pos (P : BVParameters) : 0 < P.q := by
  rw [P.q_def]
  exact div_pos (mul_pos (by norm_num) P.ε_pos) P.γ_pos

/-- Positivity of the BV choice `h = μ/(4ℓ₀)`. -/
theorem bv_h_pos (P : BVParameters) : 0 < P.h := by
  rw [BVParameters.h]
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  exact div_pos P.μ_pos (mul_pos (by norm_num) hℓ)

/-- The reciprocal of the stochastic masking ratio is exactly the expression used in
Lemma 3.2(v). -/
theorem bv_recip_noise_ratio (P : BVParameters) (hσ : P.σ ≠ 0) :
    1 / (P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2) =
      P.κ * P.σ ^ 2 / (16 * g₀ ^ 2 * P.ε ^ 2) := by
  rw [P.q_sq]
  have hκ : P.κ ≠ 0 := by
    rw [P.κ_def]
    exact div_ne_zero (ne_of_gt P.L_pos) (ne_of_gt P.μ_pos)
  have hε : P.ε ≠ 0 := ne_of_gt P.ε_pos
  have hg : g₀ ≠ 0 := by norm_num [g₀]
  field_simp [hκ, hσ, hε, hg]
  ring

/-- Equation (18) implies the exact `1/p` identity stated in Lemma 3.2(v), including the
noiseless branch. -/
theorem bv_inv_p_scaling_exact (P : BVParameters) :
    BVInvPScalingExact P.p P.κ P.σ P.ε := by
  by_cases hσ : P.σ = 0
  · exact Or.inl ⟨hσ, bv_p_eq_one_of_sigma_zero P hσ⟩
  · right
    refine ⟨hσ, ?_⟩
    have hp := bv_p_eq_min_of_sigma_ne_zero P hσ
    let a : ℝ := P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2
    have ha : 0 < a := by
      dsimp [a]
      have hq : 0 < P.q := bv_q_pos P
      have hg : 0 < g₀ := by norm_num [g₀]
      exact div_pos (mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos hg))
        (sq_pos_of_ne_zero hσ)
    have hrecip : 1 / a = P.κ * P.σ ^ 2 / (16 * g₀ ^ 2 * P.ε ^ 2) := by
      dsimp [a]
      exact bv_recip_noise_ratio P hσ
    rw [hp]
    change 1 / min 1 a = _
    by_cases ha1 : 1 ≤ a
    · rw [min_eq_left ha1]
      have hle : P.κ * P.σ ^ 2 / (16 * g₀ ^ 2 * P.ε ^ 2) ≤ 1 := by
        rw [← hrecip]
        exact (div_le_iff₀ ha).2 (by simpa using ha1)
      rw [max_eq_left hle]
      norm_num
    · have hale : a ≤ 1 := le_of_not_ge ha1
      rw [min_eq_right hale]
      have hge : 1 ≤ P.κ * P.σ ^ 2 / (16 * g₀ ^ 2 * P.ε ^ 2) := by
        rw [← hrecip]
        exact (le_div_iff₀ ha).2 (by simpa using hale)
      rw [max_eq_right hge]
      exact hrecip

/-- The exact `1/p` formula controls the theorem-rate factor with the paper's universal
constant `1/(16 g₀²)`. -/
theorem bv_inv_p_rate_factor_lower (P : BVParameters)
    (hexact : BVInvPScalingExact P.p P.κ P.σ P.ε) :
    (1 / (16 * g₀ ^ 2)) * max 1 (P.κ * P.σ ^ 2 / P.ε ^ 2) ≤ 1 / P.p := by
  rcases hexact with hzero | hnoise
  · rcases hzero with ⟨hσ, hp⟩
    rw [hσ, hp]
    norm_num [g₀]
  · rcases hnoise with ⟨_hσ, hinv⟩
    rw [hinv]
    let x : ℝ := P.κ * P.σ ^ 2 / P.ε ^ 2
    have hratio :
        (1 / (16 * g₀ ^ 2)) * x =
          P.κ * P.σ ^ 2 / (16 * g₀ ^ 2 * P.ε ^ 2) := by
      dsimp [x]
      ring
    by_cases hx : x ≤ 1
    · rw [max_eq_left hx]
      simp only [mul_one]
      calc
        1 / (16 * g₀ ^ 2) ≤ 1 := by norm_num [g₀]
        _ ≤ max 1 (P.κ * P.σ ^ 2 / (16 * g₀ ^ 2 * P.ε ^ 2)) :=
          le_max_left _ _
    · have hx1 : 1 ≤ x := le_of_not_ge hx
      rw [max_eq_right hx1]
      rw [hratio]
      exact le_max_right _ _

/-- The canonical BV progress witness also gives the returned-gradient lower bound, with no
external progress certificate left. -/
theorem bv_gradient_lower_bound {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (hrisk : stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2)
    (hbatch : ∀ w, ValidBatchSizes (A.trace w)) :
    ∀ w, (T : ℝ) / (4 * P.p) < returnedGradientCount (A.trace w) := by
  intro w
  have hround := bv_round_lower_bound C P W hT A hrisk
  have hcount : R ≤ returnedGradientCount (A.trace w) :=
    (gradientCountAccounting T R K (A.trace w) (hbatch w)).1
  have hcast : (R : ℝ) ≤ returnedGradientCount (A.trace w) := by
    exact_mod_cast hcount
  exact lt_of_lt_of_le hround hcast

/-- Lemma 3.2 plus the now-closed Proposition 2.4 imply the Theorem-3.3 *round-rate* lower
bound with an explicit universal constant.  This is the exact final rate-assembly step of the
bounded-variance proof. -/
theorem bv_rate_round_lower_bound_of_lemma32 {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P) (c₁ cκLo cκHi : ℝ)
    (D : Lemma32Conclusion C P W c₁ cκLo cκHi)
    (hc₁ : 0 ≤ c₁) (hΔ : 0 ≤ P.Δ)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (hrisk : stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2) :
    ((c₁ / 4) * (1 / (16 * g₀ ^ 2))) *
        bvRate P.L P.Δ P.ε P.κ P.σ ≤ (R : ℝ) := by
  have hround_lt := bv_round_lower_bound C P W D.T_ge_eight A hrisk
  have hround : (T : ℝ) / (4 * P.p) ≤ (R : ℝ) := le_of_lt hround_lt
  have hinv := bv_inv_p_rate_factor_lower P D.inv_p_exact
  have hbase : 0 ≤ P.L * P.Δ / P.ε ^ 2 := by
    exact div_nonneg (mul_nonneg (le_of_lt P.L_pos) hΔ) (sq_nonneg P.ε)
  have hrate :
      (1 / (16 * g₀ ^ 2)) * bvRate P.L P.Δ P.ε P.κ P.σ ≤
        (P.L * P.Δ / P.ε ^ 2) * (1 / P.p) := by
    unfold bvRate
    calc
      (1 / (16 * g₀ ^ 2)) *
          ((P.L * P.Δ / P.ε ^ 2) * max 1 (P.κ * P.σ ^ 2 / P.ε ^ 2)) =
          (P.L * P.Δ / P.ε ^ 2) *
            ((1 / (16 * g₀ ^ 2)) * max 1 (P.κ * P.σ ^ 2 / P.ε ^ 2)) := by
              ring
      _ ≤ (P.L * P.Δ / P.ε ^ 2) * (1 / P.p) :=
        mul_le_mul_of_nonneg_left hinv hbase
  have hcquarter : 0 ≤ c₁ / 4 := div_nonneg hc₁ (by norm_num)
  have hrate' := mul_le_mul_of_nonneg_left hrate hcquarter
  have hp : 0 < P.p := D.p_pos
  have hfac : 0 ≤ 1 / (4 * P.p) := by positivity
  have hchain := mul_le_mul_of_nonneg_right D.chain_length hfac
  calc
    ((c₁ / 4) * (1 / (16 * g₀ ^ 2))) * bvRate P.L P.Δ P.ε P.κ P.σ =
        (c₁ / 4) * ((1 / (16 * g₀ ^ 2)) * bvRate P.L P.Δ P.ε P.κ P.σ) := by
          ring
    _ ≤ (c₁ / 4) * ((P.L * P.Δ / P.ε ^ 2) * (1 / P.p)) := hrate'
    _ = (c₁ * (P.L * P.Δ / P.ε ^ 2)) * (1 / (4 * P.p)) := by
      ring
    _ ≤ (T : ℝ) * (1 / (4 * P.p)) := hchain
    _ = (T : ℝ) / (4 * P.p) := by ring
    _ ≤ (R : ℝ) := hround

/-- The same universal-rate lower bound holds for the actual number of returned gradients
whenever the paper's `1 ≤ K_t ≤ K` protocol is respected. -/
theorem bv_rate_gradient_lower_bound_of_lemma32 {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P) (c₁ cκLo cκHi : ℝ)
    (D : Lemma32Conclusion C P W c₁ cκLo cκHi)
    (hc₁ : 0 ≤ c₁) (hΔ : 0 ≤ P.Δ)
    (A : BernoulliRun T R K (bvConstructedOracle W))
    (hrisk : stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2)
    (hbatch : ∀ w, ValidBatchSizes (A.trace w)) :
    ∀ w,
      ((c₁ / 4) * (1 / (16 * g₀ ^ 2))) *
          bvRate P.L P.Δ P.ε P.κ P.σ ≤
        (returnedGradientCount (A.trace w) : ℝ) := by
  intro w
  have hround := bv_rate_round_lower_bound_of_lemma32 C P W c₁ cκLo cκHi D hc₁ hΔ A hrisk
  have hcount : R ≤ returnedGradientCount (A.trace w) :=
    (gradientCountAccounting T R K (A.trace w) (hbatch w)).1
  have hcast : (R : ℝ) ≤ returnedGradientCount (A.trace w) := by
    exact_mod_cast hcount
  exact le_trans hround hcast



/-- The lift witness has the same `ν` as the bounded-variance parameter block. -/
theorem bvWitness_nu_eq {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P) : W.LP.ν = P.ν := by
  rw [LiftParameters.ν, W.lift_mu, W.lift_h]
  simpa [BVParameters.h, BVParameters.ν] using LiftParameters.nu_bv P.μ

/-- The lift witness has the same `α=q²/h` as the bounded-variance parameter block. -/
theorem bvWitness_alpha_eq {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : BVParameters} (W : BVConstructionWitness C P) : W.LP.α = P.α := by
  rw [LiftParameters.α, BVParameters.α, W.lift_q, W.lift_h]

/-- Assembly lemma for Lemma 3.2.  All stochastic conclusions are discharged internally from
Lemma 3.1 and the v16 variance transfer; only the genuinely analytic/numerical pieces that still
belong to Lemma 3.2 are supplied as hypotheses. -/
def lemma32Conclusion_of_core {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : BVParameters) (W : BVConstructionWitness C P)
    (c₁ cκLo cκHi : ℝ) (hκ : 8 ≤ P.κ)
    (hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1)
    (hT : 8 ≤ T)
    (hchain : c₁ * (P.L * P.Δ / P.ε ^ 2) ≤ T)
    (Acond : ActualConditionNumberCertificate (bvConstructedPopulation W))
    (hcond : cκLo * P.κ ≤ Acond.Mlo / Acond.muHi ∧
      Acond.Mhi / Acond.muLo ≤ cκHi * P.κ) :
    Lemma32Conclusion C P W c₁ cκLo cκHi := by
  have Hbase : BVBaseOracleCertificate T C P.p :=
    lemma31_bvBaseOracle_certificate C P.p (bv_p_pos P) (bv_p_le_one P)
  have hsmoothP := bv_lift_smooth_constant_le_half P hκ
  have hsmooth : W.LP.ν * (1 + W.LP.γ ^ 2) + ℓ₀ * W.LP.h ≤ P.L := by
    calc
      W.LP.ν * (1 + W.LP.γ ^ 2) + ℓ₀ * W.LP.h =
          P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h := by
            rw [bvWitness_nu_eq W, W.lift_gamma, W.lift_h]
      _ ≤ P.L / 2 := hsmoothP
      _ ≤ P.L := by linarith [P.L_pos]
  have hgapW :
      W.LP.α * Δ₀ * T + W.LP.q ^ 2 * g₀ ^ 2 / (2 * W.LP.μ) ≤ P.Δ := by
    rw [bvWitness_alpha_eq W, W.lift_q, W.lift_mu]
    exact hgap
  exact
    { base_certificate := Hbase
      p_pos := bv_p_pos P
      p_le_one := bv_p_le_one P
      ncsc := by
        have hncsc := populationFromLift_inNCSCClass_of_bounds C W.B W.LP W.lift_properties
          P.L P.Δ hsmooth hgapW
        simpa only [bvConstructedPopulation, W.lift_mu] using hncsc
      unbiased := bvConstructedOracle_unbiased W Hbase
      bounded_variance := bvConstructedOracle_boundedVariance W Hbase
      chain_floor := hfloor
      T_ge_eight := hT
      chain_length := hchain
      inv_p_exact := bv_inv_p_scaling_exact P
      actual := Acond
      actual_condition_number := hcond }

/-! ## v18 proof phase VIII: BV floor bookkeeping and Theorem 3.3 assembly

The bounded-variance rate and progress arguments are already closed in v17.  This phase adds
reusable floor-interval consequences and proves that a genuine Lemma-3.2 theorem immediately
implies the full Theorem-3.3 statement, including returned-gradient complexity.  No analytic
certificate is postulated here: the only hypothesis of the final assembly theorem is exactly
`Lemma32Statement` itself.
-/

/-- If a natural chain length is the floor witness for a real scale at least `16`, then in
particular it is at least `8`.  This is the elementary floor step used in Lemma 3.2. -/
theorem floor_interval_ge_eight {T : ℕ} {A : ℝ}
    (hfloor : (T : ℝ) ≤ A ∧ A < (T : ℝ) + 1) (hA : 16 ≤ A) : 8 ≤ T := by
  have h15 : (15 : ℝ) < (T : ℝ) := by linarith [hfloor.2, hA]
  have h15nat : 15 < T := by exact_mod_cast h15
  omega

/-- The same floor interval gives the standard `T ≥ A/2` estimate once `A ≥ 2`. -/
theorem floor_interval_ge_half {T : ℕ} {A : ℝ}
    (hfloor : (T : ℝ) ≤ A ∧ A < (T : ℝ) + 1) (hA : 2 ≤ A) :
    A / 2 ≤ (T : ℝ) := by
  linarith [hfloor.2, hA]

/-- Positivity of the universal rate constant used when Lemma 3.2 is converted into
Theorem 3.3. -/
theorem bv_theorem_rate_constant_pos {c₁ : ℝ} (hc₁ : 0 < c₁) :
    0 < (c₁ / 4) * (1 / (16 * g₀ ^ 2)) := by
  have hg : 0 < g₀ := by norm_num [g₀]
  positivity

/-- Canonical external-parameter record used to instantiate Lemma 3.2 inside Theorem 3.3. -/
noncomputable def canonicalBVParameters
    (L μ Δ σ ε : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε)
    (_hκ : 8 ≤ L / μ) : BVParameters := by
  let κ : ℝ := L / μ
  let γ : ℝ := Real.sqrt (κ / 4)
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact div_pos hL hμ
  have hγarg : 0 ≤ κ / 4 := by positivity
  have hγpos : 0 < γ := by
    dsimp [γ]
    exact Real.sqrt_pos.2 (by positivity)
  let q : ℝ := 2 * ε / γ
  let p : ℝ := if σ = 0 then 1 else min 1 (q ^ 2 * g₀ ^ 2 / σ ^ 2)
  exact
    { L := L
      μ := μ
      ε := ε
      σ := σ
      Δ := Δ
      κ := κ
      γ := γ
      q := q
      p := p
      L_pos := hL
      μ_pos := hμ
      ε_pos := hε
      κ_def := rfl
      γ_sq := by
        dsimp [γ]
        exact Real.sq_sqrt hγarg
      γ_pos := hγpos
      q_def := rfl
      p_def := rfl }

/-- The canonical parameter record has exactly the external data of Theorem 3.3. -/
theorem canonicalBVParameters_match
    (L μ Δ σ ε : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε)
    (hκ : 8 ≤ L / μ) :
    BVParameterMatch (canonicalBVParameters L μ Δ σ ε hL hμ hε hκ)
      L μ Δ σ ε := by
  simp [BVParameterMatch, canonicalBVParameters]

/-- Proof-theoretic assembly of the bounded-variance main theorem from Lemma 3.2.

All oracle/progress/rate steps used here are already actual Lean theorems (`Lemma 3.1`, the
canonical BV progress witness, Proposition 2.4, and the v17 rate conversion).  Consequently the
only remaining mathematical premise is exactly the paper's Lemma-3.2 statement. -/
theorem theorem33_of_lemma32 (h32 : Lemma32Statement) : Theorem33Statement := by
  rcases h32 with ⟨c₀, c₁, cκLo, cκHi, hc₀, hc₁, hcκLo, hcκHi, hlemma32⟩
  let c : ℝ := (c₁ / 4) * (1 / (16 * g₀ ^ 2))
  have hc : 0 < c := by
    dsimp [c]
    exact bv_theorem_rate_constant_pos hc₁
  refine ⟨c, c₀, hc, hc₀, ?_⟩
  intro K hK L μ Δ σ ε hL hμ hε hσ hΔ hκ hsmall
  let P : BVParameters := canonicalBVParameters L μ Δ σ ε hL hμ hε hκ
  have hPκ : 8 ≤ P.κ := by
    simpa [P, canonicalBVParameters] using hκ
  have hPsmall : P.ε ^ 2 ≤ c₀ * P.L * P.Δ := by
    simpa [P, canonicalBVParameters] using hsmall
  rcases hlemma32 P hPκ hPsmall with ⟨T, C, W, hD⟩
  rcases hD with ⟨D⟩
  refine ⟨P, T, C, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalBVParameters_match L μ Δ σ ε hL hμ hε hκ
  · exact ⟨D.base_certificate⟩
  · simpa [P, canonicalBVParameters] using D.ncsc
  · simpa [P, canonicalBVParameters] using D.unbiased
  · simpa [P, canonicalBVParameters] using D.bounded_variance
  · simpa [P, canonicalBVParameters] using D.inv_p_exact
  · intro R A hbatch hrisk
    have hriskP :
        stationarityRisk P.p (bvConstructedPopulation W).gradPhi A ≤ P.ε ^ 2 := by
      simpa [P, canonicalBVParameters] using hrisk
    have hround := bv_rate_round_lower_bound_of_lemma32
      C P W c₁ cκLo cκHi D (le_of_lt hc₁) hΔ A hriskP
    have hgrads := bv_rate_gradient_lower_bound_of_lemma32
      C P W c₁ cκLo cκHi D (le_of_lt hc₁) hΔ A hriskP hbatch
    constructor
    · simpa [c, P, canonicalBVParameters] using hround
    · intro w
      simpa [c, P, canonicalBVParameters] using hgrads w


/-! ## v20 proof phase X: deterministic lift inequalities

This phase attacks the deterministic analytic core of Lemma 2.3 directly.  It proves the
scaled descent inequality for the chain term, the exact quadratic expansion of the lift, and
combines them into the paper's `μ`-strong concavity inequality for `f_T(x,·)`.  These are actual
proof terms derived from the imported Lemma-2.1 smoothness certificate; no new analytic axiom is
introduced here. -/

/-- Equation (7) also gives the second scaling identity `α β² = h`. -/
theorem lift_alpha_mul_beta_sq (P : LiftParameters) :
    P.α * P.β ^ 2 = P.h := by
  calc
    P.α * P.β ^ 2 = (P.α * P.β) * P.β := by ring
    _ = P.q * P.β := by rw [P.alpha_mul_beta]
    _ = P.h := P.q_mul_beta

/-- Exact square expansion for the quadratic coupling around the current dual point. -/
theorem lift_quadratic_norm_expansion {T : ℕ} (P : LiftParameters)
    (x y y' : Vec T) :
    ‖y' - P.γ • x‖ ^ 2 =
      ‖y - P.γ • x‖ ^ 2 +
        2 * @inner ℝ (Vec T) _ (y - P.γ • x) (y' - y) +
        ‖y' - y‖ ^ 2 := by
  have hvec : y' - P.γ • x = (y - P.γ • x) + (y' - y) := by
    module
  rw [hvec, norm_add_sq_real]

/-- Lemma 2.1's smooth upper inequality, after the lift scaling, becomes exactly the chain
part of the strong-concavity estimate used in Lemma 2.3(i). -/
theorem lift_chain_smooth_upper_scaled {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (y y' : Vec T) :
    P.α * explicitFT T C.dim_pos (P.β • y') ≤
      P.α * explicitFT T C.dim_pos (P.β • y) +
        P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
        (ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2 := by
  have hα0 : 0 ≤ P.α := by
    rw [LiftParameters.α]
    exact div_nonneg (sq_nonneg P.q) (le_of_lt P.h_pos)
  have hβpos : 0 < P.β := by
    exact div_pos P.h_pos P.q_pos
  have hs := explicitFT_smooth_upper C (P.β • y) (P.β • y')
  have hm := mul_le_mul_of_nonneg_left hs hα0
  have hdiff : P.β • y' - P.β • y = P.β • (y' - y) := by
    module
  have hinner :
      @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (P.β • y' - P.β • y) =
        P.β * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) := by
    rw [hdiff, real_inner_smul_right]
  have hnorm :
      ‖P.β • y' - P.β • y‖ ^ 2 = P.β ^ 2 * ‖y' - y‖ ^ 2 := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hβpos]
    ring
  rw [hinner, hnorm] at hm
  calc
    P.α * explicitFT T C.dim_pos (P.β • y')
        ≤ P.α * (explicitFT T C.dim_pos (P.β • y) +
          P.β * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
          ℓ₀ / 2 * (P.β ^ 2 * ‖y' - y‖ ^ 2)) := hm
    _ = P.α * explicitFT T C.dim_pos (P.β • y) +
          (P.α * P.β) * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
          ℓ₀ / 2 * (P.α * P.β ^ 2) * ‖y' - y‖ ^ 2 := by ring
    _ = P.α * explicitFT T C.dim_pos (P.β • y) +
          P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
          (ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2 := by
      rw [P.alpha_mul_beta, lift_alpha_mul_beta_sq]
      ring

/-- Paper Lemma 2.3(i), deterministic core: for every fixed primal point, the lifted dual
objective is `μ`-strongly concave.  This is derived directly from the imported chain smoothness
inequality and the quadratic block, rather than supplied as a certificate field. -/
theorem liftedF_mu_strong_concavity {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) :
    LiftStrongConcavity C P P.μ := by
  intro x y y'
  have hchain := lift_chain_smooth_upper_scaled C P y y'
  have hquad := lift_quadratic_norm_expansion P x y y'
  have hgradinner :
      @inner ℝ (Vec T) _
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) =
      P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
        P.ν * @inner ℝ (Vec T) _ (y - P.γ • x) (y' - y) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  have hsub := sub_le_sub_right hchain (P.ν / 2 * ‖y' - P.γ • x‖ ^ 2)
  unfold liftedF
  calc
    P.α * explicitFT T C.dim_pos (P.β • y') -
          P.ν / 2 * ‖y' - P.γ • x‖ ^ 2
        ≤ (P.α * explicitFT T C.dim_pos (P.β • y) +
            P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
            (ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2) -
          P.ν / 2 * ‖y' - P.γ • x‖ ^ 2 := hsub
    _ = P.α * explicitFT T C.dim_pos (P.β • y) -
          P.ν / 2 * ‖y - P.γ • x‖ ^ 2 +
          @inner ℝ (Vec T) _
            (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
          P.μ / 2 * ‖y' - y‖ ^ 2 := by
      rw [hquad, hgradinner]
      simp only [LiftParameters.ν]
      ring

/-- The strong-concavity inequality specialised at `(x,y)=(0,0)`.  This is the starting point
of the paper's primal-gap estimate (12). -/
theorem liftedF_origin_quadratic_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (y : Vec T) :
    liftedF C P 0 y ≤
      P.α * explicitFT T C.dim_pos 0 +
        P.q * @inner ℝ (Vec T) _ (C.gradF 0) y -
        P.μ / 2 * ‖y‖ ^ 2 := by
  have h := liftedF_mu_strong_concavity C P (0 : Vec T) (0 : Vec T) y
  have hgrad :
      P.q • C.gradF (P.β • (0 : Vec T)) -
          P.ν • ((0 : Vec T) - P.γ • (0 : Vec T)) =
        P.q • C.gradF 0 := by
    simp
  have hdiff : y - (0 : Vec T) = y := by
    simp
  rw [hgrad, hdiff, real_inner_smul_left] at h
  simpa [liftedF] using h

/-- On the diagonal `y = γx` the quadratic penalty vanishes.  This is the lower comparison used
in the primal-gap proof of Lemma 2.3(ii). -/
theorem liftedF_diagonal_value {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    liftedF C P x (P.γ • x) =
      P.α * explicitFT T C.dim_pos ((P.β * P.γ) • x) := by
  simp [liftedF, smul_smul]



/-! ## v21 proof phase XII: closing more of the deterministic Lemma-2.3 core

This phase keeps the paper statements unchanged and derives three pieces that were still only
certificate fields in v20: the upper bracket on every strong-concavity modulus, the completed
origin quadratic bound used in the primal-gap estimate, and the coercive tail estimate needed for
existence of the dual maximizer.  The final theorem below packages the whole paper equation (12)
once a maximizer representation of the value function has been supplied. -/

/-- The lift scaling coefficient `α=q²/h` is nonnegative. -/
theorem lift_alpha_nonneg (P : LiftParameters) : 0 ≤ P.α := by
  rw [LiftParameters.α]
  exact div_nonneg (sq_nonneg P.q) (le_of_lt P.h_pos)

/-- Any gradient-form strong-concavity inequality implies strong antimonotonicity of the
corresponding dual gradient.  This is the standard two-inequality argument, now made explicit so
that the upper bracket on the actual strong-concavity modulus does not remain a certificate
assumption. -/
theorem liftStrongConcavity_antimonotone {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (m : ℝ)
    (hm : LiftStrongConcavity C P m) (x y y' : Vec T) :
    @inner ℝ (Vec T) _
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x)))
      (y - y') ≤ -m * ‖y - y'‖ ^ 2 := by
  have h1 := hm x y y'
  have h2 := hm x y' y
  have hdiff : y' - y = -(y - y') := by
    module
  rw [hdiff] at h1
  simp only [inner_neg_right, norm_neg] at h1
  rw [inner_sub_left]
  nlinarith

/-- The zero vector has progress zero at threshold `0`. -/
theorem prog_zero_zero {T : ℕ} : prog 0 (0 : Vec T) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply prog_zero_le_of_zero_above
  intro i _hi
  simp

/-- At any positive threshold the zero vector still has zero progress. -/
theorem prog_pos_threshold_zero {T : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    prog a (0 : Vec T) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact le_trans (prog_antitone_threshold (0 : Vec T) ha) (by
    rw [prog_zero_zero])

/-- Paper Lemma 2.3(i), second half: every uniform strong-concavity modulus of the lifted dual
objective is at most `ν + ℓ₀ h`.  Together with `liftedF_mu_strong_concavity`, this supplies the
paper's bracket `μ ≤ μ_act ≤ ν+ℓ₀h` without assuming attainment of a largest modulus. -/
theorem lift_strong_modulus_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (m : ℝ)
    (hm : LiftStrongConcavity C P m) :
    m ≤ P.ν + ℓ₀ * P.h := by
  have hprog0 : prog 1 (0 : Vec T) = 0 :=
    prog_pos_threshold_zero (T := T) (a := (1 : ℝ)) (by norm_num)
  have hprog : prog 1 (0 : Vec T) < T := by
    rw [hprog0]
    exact C.dim_pos
  have hnorm : 1 < ‖C.gradF 0‖ := C.terminal_gradient 0 hprog
  have hnormpos : 0 < ‖C.gradF 0‖ := lt_trans (by norm_num) hnorm
  have hsqpos : 0 < ‖C.gradF 0‖ ^ 2 := sq_pos_of_pos hnormpos
  have ha := liftStrongConcavity_antimonotone C P m hm
    (0 : Vec T) (C.gradF 0) (0 : Vec T)
  have hr := lift_gradY_reverse_bound C P
    (0 : Vec T) (C.gradF 0) (0 : Vec T)
  simp only [sub_zero] at ha hr
  nlinarith

/-- Completion of the square in the origin estimate: uniformly over the dual variable,
`f_T(0,y)` is at most the paper's origin term
`αF_T(0)+q²g₀²/(2μ)`. -/
theorem liftedF_origin_uniform_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (y : Vec T) :
    liftedF C P 0 y ≤
      P.α * explicitFT T C.dim_pos 0 + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
  have h0 := liftedF_origin_quadratic_upper C P y
  have hinner0 := real_inner_le_norm (C.gradF 0) y
  have hinner :
      @inner ℝ (Vec T) _ (C.gradF 0) y ≤ g₀ * ‖y‖ := by
    exact le_trans hinner0
      (mul_le_mul_of_nonneg_right C.origin_grad_bound (norm_nonneg y))
  have hq :
      P.q * @inner ℝ (Vec T) _ (C.gradF 0) y ≤ P.q * (g₀ * ‖y‖) :=
    mul_le_mul_of_nonneg_left hinner (le_of_lt P.q_pos)
  have hden : 0 < 2 * P.μ := mul_pos (by norm_num) P.μ_pos
  have hyoung :
      P.q * (g₀ * ‖y‖) - P.μ / 2 * ‖y‖ ^ 2 ≤
        P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (P.μ * ‖y‖ - P.q * g₀)]
  calc
    liftedF C P 0 y
        ≤ P.α * explicitFT T C.dim_pos 0 +
            P.q * @inner ℝ (Vec T) _ (C.gradF 0) y -
            P.μ / 2 * ‖y‖ ^ 2 := h0
    _ ≤ P.α * explicitFT T C.dim_pos 0 +
          P.q * (g₀ * ‖y‖) - P.μ / 2 * ‖y‖ ^ 2 := by
      linarith
    _ ≤ P.α * explicitFT T C.dim_pos 0 +
          P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
      linarith

/-- Strong concavity at the dual origin gives the quadratic tail estimate used to localise a
global maximizer to a compact ball. -/
theorem liftedF_fixed_x_quadratic_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    liftedF C P x y ≤ liftedF C P x 0 +
      @inner ℝ (Vec T) _
        (P.q • C.gradF 0 + (P.ν * P.γ) • x) y -
      P.μ / 2 * ‖y‖ ^ 2 := by
  have h := liftedF_mu_strong_concavity C P x (0 : Vec T) y
  have hgrad :
      P.q • C.gradF (P.β • (0 : Vec T)) -
          P.ν • ((0 : Vec T) - P.γ • x) =
        P.q • C.gradF 0 + (P.ν * P.γ) • x := by
    simp [smul_smul]
  rw [hgrad] at h
  simpa using h

/-- Norm form of the preceding coercive estimate. -/
theorem liftedF_fixed_x_radial_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    liftedF C P x y ≤ liftedF C P x 0 +
      ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ * ‖y‖ -
      P.μ / 2 * ‖y‖ ^ 2 := by
  have h := liftedF_fixed_x_quadratic_upper C P x y
  have hi := real_inner_le_norm
    (P.q • C.gradF 0 + (P.ν * P.γ) • x) y
  linarith

/-- Quantitative coercivity: beyond radius `2‖g_x(0)‖/μ`, the lifted objective is already
strictly below its value at the dual origin.  This is the exact compact-localisation fact needed
for the next argmax-existence phase. -/
theorem liftedF_lt_origin_of_norm_gt {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T)
    (hy : 2 * ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ / P.μ < ‖y‖) :
    liftedF C P x y < liftedF C P x 0 := by
  have h := liftedF_fixed_x_radial_upper C P x y
  have hmul := (div_lt_iff₀ P.μ_pos).1 hy
  have hA : 0 ≤ ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ := norm_nonneg _
  have hr : 0 ≤ ‖y‖ := norm_nonneg _
  have hrpos : 0 < ‖y‖ := by
    by_contra hnot
    have hrzero : ‖y‖ = 0 := le_antisymm (le_of_not_gt hnot) hr
    rw [hrzero] at hmul
    norm_num at hmul
    have hAneg : ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ < 0 := by
      linarith
    exact (not_lt_of_ge hA) hAneg
  have hhalf :
      ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ < ‖y‖ * P.μ / 2 := by
    linarith
  have hprod :
      ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ * ‖y‖ <
        P.μ / 2 * ‖y‖ ^ 2 := by
    calc
      ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ * ‖y‖
          < (‖y‖ * P.μ / 2) * ‖y‖ :=
            mul_lt_mul_of_pos_right hhalf hrpos
      _ = P.μ / 2 * ‖y‖ ^ 2 := by ring
  have hneg :
      ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖ * ‖y‖ -
        P.μ / 2 * ‖y‖ ^ 2 < 0 :=
    sub_neg.mpr hprod
  linarith

/-- Paper equation (12), with the only remaining semantic input isolated: `Phi` must be the
value function represented by some global maximizer `yStar`.  Thus, after argmax existence is
constructed, the primal-gap certificate is now automatic rather than a separate analytic gap. -/
theorem lift_primal_gap_of_maximizer_data {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters)
    (Phi : Vec T → ℝ) (yStar : Vec T → Vec T)
    (hPhi : ∀ x, Phi x = liftedF C P x (yStar x))
    (hmax : ∀ x y, liftedF C P x y ≤ liftedF C P x (yStar x)) :
    Phi 0 - sInf (Set.range Phi) ≤
      P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
  have hα0 : 0 ≤ P.α := lift_alpha_nonneg P
  have hPhi0 :
      Phi 0 ≤ P.α * explicitFT T C.dim_pos 0 +
        P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
    rw [hPhi 0]
    exact liftedF_origin_uniform_upper C P (yStar 0)
  have hFlow : ∀ u : Vec T,
      sInf (Set.range (explicitFT T C.dim_pos)) ≤ explicitFT T C.dim_pos u := by
    intro u
    exact csInf_le C.bddBelow ⟨u, rfl⟩
  have hPhiLower : ∀ x : Vec T,
      P.α * sInf (Set.range (explicitFT T C.dim_pos)) ≤ Phi x := by
    intro x
    have hinf := mul_le_mul_of_nonneg_left
      (hFlow ((P.β * P.γ) • x)) hα0
    have hdiag := liftedF_diagonal_value C P x
    have hmx := hmax x (P.γ • x)
    rw [hPhi x]
    rw [hdiag] at hmx
    exact le_trans hinf hmx
  have hInfPhi :
      P.α * sInf (Set.range (explicitFT T C.dim_pos)) ≤ sInf (Set.range Phi) := by
    apply le_csInf
    · exact ⟨Phi 0, Set.mem_range_self 0⟩
    · exact Set.forall_mem_range.2 hPhiLower
  have hgapScaled :
      P.α * (explicitFT T C.dim_pos 0 -
        sInf (Set.range (explicitFT T C.dim_pos))) ≤
        P.α * (Δ₀ * T) :=
    mul_le_mul_of_nonneg_left C.gap_bound hα0
  calc
    Phi 0 - sInf (Set.range Phi)
        ≤ (P.α * explicitFT T C.dim_pos 0 +
            P.q ^ 2 * g₀ ^ 2 / (2 * P.μ)) -
          P.α * sInf (Set.range (explicitFT T C.dim_pos)) :=
      sub_le_sub hPhi0 hInfPhi
    _ = P.α * (explicitFT T C.dim_pos 0 -
          sInf (Set.range (explicitFT T C.dim_pos))) +
        P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by ring
    _ ≤ P.α * (Δ₀ * T) + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
      exact add_le_add_right hgapScaled _
    _ = P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by ring


/-! ## v22 proof phase XIII: global dual argmax and the actual primal gap

The paper's proof of Lemma 2.3(ii) uses coercivity of the strongly-concave dual
objective to conclude that a global maximizer exists.  v21 established the
quantitative coercive tail estimate.  This phase now carries out the missing
finite-dimensional compactness argument, chooses a canonical maximizer, and
feeds it into the already-proved gap lemma.  No new analytic assumption is
introduced. -/

/-- The imported single-level chain is continuous because it has a Euclidean
gradient at every point. -/
theorem explicitFT_continuous {T : ℕ}
    (C : ExplicitZeroChainCertificate T) :
    Continuous (explicitFT T C.dim_pos) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (C.grad_is_gradient u).continuousAt

/-- For every fixed primal point, the lifted objective is continuous in the
dual variable.  This is the continuity input for the compact-ball extreme
value theorem. -/
theorem liftedF_continuous_in_y {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    Continuous (fun y : Vec T => liftedF C P x y) := by
  have hF : Continuous (explicitFT T C.dim_pos) := explicitFT_continuous C
  have hscale : Continuous (fun y : Vec T => P.β • y) :=
    continuous_const.smul continuous_id
  have hchain : Continuous (fun y : Vec T =>
      P.α * explicitFT T C.dim_pos (P.β • y)) :=
    continuous_const.mul (hF.comp hscale)
  have haff : Continuous (fun y : Vec T => y - P.γ • x) :=
    continuous_id.sub continuous_const
  have hquad : Continuous (fun y : Vec T =>
      P.ν / 2 * ‖y - P.γ • x‖ ^ 2) :=
    continuous_const.mul (haff.norm.pow 2)
  simpa [liftedF] using hchain.sub hquad

/-- The lifted dual objective attains a global maximum at every primal point.
The proof localises to the closed ball of radius
`2 ‖q∇F_T(0)+(νγ)x‖/μ + 1`, applies the extreme value theorem there, and uses
v21's coercive tail estimate to rule out every point outside the ball. -/
theorem liftedF_exists_global_maximizer {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    ∃ yStar : Vec T, ∀ y : Vec T,
      liftedF C P x y ≤ liftedF C P x yStar := by
  let A : ℝ := ‖P.q • C.gradF 0 + (P.ν * P.γ) • x‖
  let R : ℝ := 2 * A / P.μ + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact norm_nonneg _
  have hratio : 0 ≤ 2 * A / P.μ :=
    div_nonneg (mul_nonneg (by norm_num) hA) (le_of_lt P.μ_pos)
  have hRpos : 0 < R := by
    dsimp [R]
    linarith
  let s : Set (Vec T) := Metric.closedBall 0 R
  have hscompact : IsCompact s := by
    simpa [s] using (isCompact_closedBall (0 : Vec T) R)
  have hzero : (0 : Vec T) ∈ s := by
    dsimp [s]
    rw [Metric.mem_closedBall]
    simpa using (le_of_lt hRpos)
  have hsne : s.Nonempty := ⟨0, hzero⟩
  have hcont : ContinuousOn (fun y : Vec T => liftedF C P x y) s :=
    (liftedF_continuous_in_y C P x).continuousOn
  obtain ⟨yStar, hyStar, hmaxOn⟩ :=
    hscompact.exists_isMaxOn hsne hcont
  refine ⟨yStar, ?_⟩
  intro y
  by_cases hy : y ∈ s
  · exact hmaxOn hy
  · have hynorm : R < ‖y‖ := by
      dsimp [s] at hy
      simp only [Metric.mem_closedBall, dist_zero_right] at hy
      exact lt_of_not_ge hy
    have hthreshold : 2 * A / P.μ < ‖y‖ := by
      dsimp [R] at hynorm
      linarith
    have htail : liftedF C P x y < liftedF C P x 0 := by
      apply liftedF_lt_origin_of_norm_gt C P x y
      simpa [A] using hthreshold
    have h0max : liftedF C P x 0 ≤ liftedF C P x yStar :=
      hmaxOn hzero
    exact le_trans (le_of_lt htail) h0max

/-- A canonical choice of the global dual maximizer supplied by the preceding
existence theorem.  Uniqueness will be proved separately from strong concavity;
the definition itself requires only existence. -/
noncomputable def canonicalLiftYStar {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) : Vec T :=
  Classical.choose (liftedF_exists_global_maximizer C P x)

/-- The canonical choice is indeed a global maximizer. -/
theorem canonicalLiftYStar_maximizer {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    liftedF C P x y ≤ liftedF C P x (canonicalLiftYStar C P x) := by
  exact (Classical.choose_spec (liftedF_exists_global_maximizer C P x)) y

/-- The value function associated with the canonical dual maximizer. -/
noncomputable def canonicalLiftPhi {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) : ℝ :=
  liftedF C P x (canonicalLiftYStar C P x)

/-- Definitional representation of the canonical value function. -/
theorem canonicalLiftPhi_def {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    canonicalLiftPhi C P x = liftedF C P x (canonicalLiftYStar C P x) := rfl

/-- The canonical value function dominates the lifted objective at every dual
point, i.e. it is exactly the paper's `max_y f_T(x,y)` value. -/
theorem canonicalLiftPhi_is_value {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    liftedF C P x y ≤ canonicalLiftPhi C P x := by
  exact canonicalLiftYStar_maximizer C P x y

/-- Paper equation (12), now with no remaining maximizer-existence hypothesis:
the canonical lifted value function satisfies the required initial-gap bound. -/
theorem canonicalLiftPhi_primal_gap {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) :
    canonicalLiftPhi C P 0 - sInf (Set.range (canonicalLiftPhi C P)) ≤
      P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) := by
  exact lift_primal_gap_of_maximizer_data C P
    (canonicalLiftPhi C P) (canonicalLiftYStar C P)
    (fun _ => rfl)
    (fun x y => canonicalLiftYStar_maximizer C P x y)


/-! ## v23 proof phase XIV: dual first-order condition and uniqueness

The compactness argument of v22 gives existence of a global dual maximizer.  This phase proves
its first-order condition without importing any additional differentiability theorem: the reverse
descent inequality from Lemma 2.1 gives a quadratic lower model for the lifted dual objective, and
a short ascent step would improve the value unless the displayed dual-gradient vector vanished.
Strong concavity then makes the maximizer unique.  The final scaled fixed-point identity is the
exact algebraic relation used in the paper's envelope/stationarity-transfer argument.
-/

/-- The parameter `ν = μ + ℓ₀ h` is strictly positive. -/
theorem lift_nu_pos (P : LiftParameters) : 0 < P.ν := by
  rw [LiftParameters.ν]
  have hl0 : 0 < ℓ₀ := by norm_num [ℓ₀]
  exact add_pos P.μ_pos (mul_pos hl0 P.h_pos)

/-- The two-sided curvature constant `ν + ℓ₀ h` used in the reverse dual descent estimate is
strictly positive. -/
theorem lift_dual_curvature_pos (P : LiftParameters) : 0 < P.ν + ℓ₀ * P.h := by
  have hnu := lift_nu_pos P
  have hl0 : 0 < ℓ₀ := by norm_num [ℓ₀]
  nlinarith [P.h_pos]

/-- Lemma 2.1's smooth lower inequality after the lift scaling.  This is the reverse companion of
`lift_chain_smooth_upper_scaled`. -/
theorem lift_chain_smooth_lower_scaled {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (y y' : Vec T) :
    P.α * explicitFT T C.dim_pos (P.β • y) +
        P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
        (ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2 ≤
      P.α * explicitFT T C.dim_pos (P.β • y') := by
  have hα0 : 0 ≤ P.α := lift_alpha_nonneg P
  have hβpos : 0 < P.β := div_pos P.h_pos P.q_pos
  have hs := explicitFT_smooth_lower C (P.β • y) (P.β • y')
  have hm := mul_le_mul_of_nonneg_left hs hα0
  have hdiff : P.β • y' - P.β • y = P.β • (y' - y) := by
    module
  have hinner :
      @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (P.β • y' - P.β • y) =
        P.β * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) := by
    rw [hdiff, real_inner_smul_right]
  have hnorm :
      ‖P.β • y' - P.β • y‖ ^ 2 = P.β ^ 2 * ‖y' - y‖ ^ 2 := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hβpos]
    ring
  rw [hinner, hnorm] at hm
  calc
    P.α * explicitFT T C.dim_pos (P.β • y) +
          P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
          (ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2
        = P.α * (explicitFT T C.dim_pos (P.β • y) +
            P.β * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
            ℓ₀ / 2 * (P.β ^ 2 * ‖y' - y‖ ^ 2)) := by
          rw [← P.alpha_mul_beta, ← lift_alpha_mul_beta_sq]
          ring
    _ ≤ P.α * explicitFT T C.dim_pos (P.β • y') := hm

/-- Reverse quadratic model for the lifted dual objective.  Together with the strong-concavity
upper model, this gives the exact two-sided first-order control used in the paper. -/
theorem liftedF_dual_quadratic_lower {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y y' : Vec T) :
    liftedF C P x y +
        @inner ℝ (Vec T) _
          (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
        (P.ν + ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2 ≤
      liftedF C P x y' := by
  have hchain := lift_chain_smooth_lower_scaled C P y y'
  have hquad := lift_quadratic_norm_expansion P x y y'
  have hgradinner :
      @inner ℝ (Vec T) _
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) =
      P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
        P.ν * @inner ℝ (Vec T) _ (y - P.γ • x) (y' - y) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  unfold liftedF
  calc
    P.α * explicitFT T C.dim_pos (P.β • y) -
          P.ν / 2 * ‖y - P.γ • x‖ ^ 2 +
          @inner ℝ (Vec T) _
            (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
          (P.ν + ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2
        = (P.α * explicitFT T C.dim_pos (P.β • y) +
            P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
            (ℓ₀ * P.h) / 2 * ‖y' - y‖ ^ 2) -
          P.ν / 2 * ‖y' - P.γ • x‖ ^ 2 := by
            rw [hquad, hgradinner]
            ring
    _ ≤ P.α * explicitFT T C.dim_pos (P.β • y') -
          P.ν / 2 * ‖y' - P.γ • x‖ ^ 2 :=
      sub_le_sub_right hchain _

/-- The displayed dual-gradient vector vanishes at the canonical global maximizer.  This is proved
from the reverse quadratic model and global maximality, so no additional Fermat-rule import is
needed. -/
theorem canonicalLiftYStar_dual_stationary {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    P.q • C.gradF (P.β • canonicalLiftYStar C P x) -
        P.ν • (canonicalLiftYStar C P x - P.γ • x) = 0 := by
  let ys : Vec T := canonicalLiftYStar C P x
  let g : Vec T :=
    P.q • C.gradF (P.β • ys) - P.ν • (ys - P.γ • x)
  let L : ℝ := P.ν + ℓ₀ * P.h
  let t : ℝ := 1 / L
  have hL : 0 < L := by
    simpa [L] using lift_dual_curvature_pos P
  have ht : 0 < t := by
    dsimp [t]
    exact one_div_pos.mpr hL
  let ytrial : Vec T := ys + t • g
  have hdiff : ytrial - ys = t • g := by
    dsimp [ytrial]
    module
  have hlo := liftedF_dual_quadratic_lower C P x ys ytrial
  have hmax : liftedF C P x ytrial ≤ liftedF C P x ys := by
    dsimp [ys]
    exact canonicalLiftYStar_maximizer C P x ytrial
  have hinner :
      @inner ℝ (Vec T) _ g (ytrial - ys) = t * (‖g‖ * ‖g‖) := by
    rw [hdiff]
    exact real_inner_smul_self_right g t
  have hnorm : ‖ytrial - ys‖ ^ 2 = t ^ 2 * ‖g‖ ^ 2 := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring
  have hmodel_nonpos :
      @inner ℝ (Vec T) _ g (ytrial - ys) -
          L / 2 * ‖ytrial - ys‖ ^ 2 ≤ 0 := by
    have hlo' :
        liftedF C P x ys +
            @inner ℝ (Vec T) _ g (ytrial - ys) -
            L / 2 * ‖ytrial - ys‖ ^ 2 ≤
          liftedF C P x ytrial := by
      simpa [g, L] using hlo
    linarith
  have hquad_nonpos :
      t * ‖g‖ ^ 2 - L / 2 * (t ^ 2 * ‖g‖ ^ 2) ≤ 0 := by
    rw [hinner, hnorm] at hmodel_nonpos
    simpa [pow_two] using hmodel_nonpos
  have hcoef : t - L / 2 * t ^ 2 = 1 / (2 * L) := by
    dsimp [t]
    field_simp [ne_of_gt hL]
    ring
  have hcoefpos : 0 < 1 / (2 * L) := by
    positivity
  have hsq : ‖g‖ ^ 2 = 0 := by
    have hrewrite :
        t * ‖g‖ ^ 2 - L / 2 * (t ^ 2 * ‖g‖ ^ 2) =
          (t - L / 2 * t ^ 2) * ‖g‖ ^ 2 := by ring
    rw [hrewrite, hcoef] at hquad_nonpos
    have hsnonneg : 0 ≤ ‖g‖ ^ 2 := sq_nonneg _
    nlinarith
  have hg : g = 0 := by
    apply norm_eq_zero.mp
    have hnormnonneg : 0 ≤ ‖g‖ := norm_nonneg _
    nlinarith
  simpa [g, ys] using hg

/-- The canonical maximizer is unique.  Once the dual first-order vector vanishes, the strict
quadratic term in the `μ`-strong-concavity inequality forces every equal-value point to coincide
with the canonical maximizer. -/
theorem canonicalLiftYStar_unique {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T)
    (heq : liftedF C P x y = liftedF C P x (canonicalLiftYStar C P x)) :
    y = canonicalLiftYStar C P x := by
  let ys : Vec T := canonicalLiftYStar C P x
  have hsc := liftedF_mu_strong_concavity C P x ys y
  have hstat :
      P.q • C.gradF (P.β • ys) - P.ν • (ys - P.γ • x) = 0 := by
    simpa only [ys] using canonicalLiftYStar_dual_stationary C P x
  rw [hstat] at hsc
  simp at hsc
  have hsc' :
      liftedF C P x ys ≤
        liftedF C P x ys - P.μ / 2 * ‖y - ys‖ ^ 2 := by
    rw [heq] at hsc
    simpa only [ys] using hsc
  have hsqys : ‖y - ys‖ ^ 2 = 0 := by
    have hμ : 0 < P.μ := P.μ_pos
    nlinarith [hsc', sq_nonneg ‖y - ys‖]
  have hsq : ‖y - canonicalLiftYStar C P x‖ ^ 2 = 0 := by
    simpa only [ys] using hsqys
  have hnorm : ‖y - canonicalLiftYStar C P x‖ = 0 := by
    have hn : 0 ≤ ‖y - canonicalLiftYStar C P x‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Equality with the value function characterises the unique dual maximizer. -/
theorem liftedF_eq_canonicalLiftPhi_iff {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    liftedF C P x y = canonicalLiftPhi C P x ↔
      y = canonicalLiftYStar C P x := by
  constructor
  · intro h
    apply canonicalLiftYStar_unique C P x y
    simpa [canonicalLiftPhi] using h
  · intro h
    subst y
    rfl

/-- Scaled optimality relation from the paper.  Writing `z*=β y*(x)` and
`w=(βγ)x`, this is exactly `z* - w = (h/ν) ∇F_T(z*)`. -/
theorem canonicalLiftYStar_scaled_fixed_point {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    P.β • canonicalLiftYStar C P x - (P.β * P.γ) • x =
      (P.h / P.ν) • C.gradF (P.β • canonicalLiftYStar C P x) := by
  have hstat := canonicalLiftYStar_dual_stationary C P x
  have hnu : P.ν ≠ 0 := ne_of_gt (lift_nu_pos P)
  have hqb : P.q * P.β = P.h := P.q_mul_beta
  ext i
  have hi := congrArg (fun v : Vec T => v i) hstat
  simp at hi ⊢
  have hi' :
      P.ν * (canonicalLiftYStar C P x i - P.γ * x i) =
        P.q * C.gradF (P.β • canonicalLiftYStar C P x) i := by
    linarith
  have hβq : P.β * P.q = P.h := by
    nlinarith [hqb]
  field_simp [hnu]
  calc
    (P.β * canonicalLiftYStar C P x i - P.β * P.γ * x i) * P.ν
        = P.β * (P.ν * (canonicalLiftYStar C P x i - P.γ * x i)) := by ring
    _ = P.β * (P.q * C.gradF (P.β • canonicalLiftYStar C P x) i) := by rw [hi']
    _ = P.h * C.gradF (P.β • canonicalLiftYStar C P x) i := by rw [← mul_assoc, hβq]



/-! ## v24 proof phase XV: actual lift gradients and joint smoothness

This phase closes the two deterministic pieces of Lemma 2.3 that sit between the explicit lift
and the envelope argument.  First, the displayed partial gradients are derived as genuine
Mathlib `HasGradientAt` statements from the imported chain gradient and the quadratic block.
Second, the paper's joint smoothness estimate (11) is proved directly in the product Euclidean
norm.  No new analytic assumption is introduced.
-/

/-- Squaring the paper's product norm recovers the sum of the squared block norms. -/
theorem pairNorm_sq_eq {T : ℕ} (a b : Vec T) :
    pairNorm a b ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  unfold pairNorm pairNormSq
  rw [pow_two, Real.mul_self_sqrt]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The product norm is nonnegative. -/
theorem pairNorm_nonneg {T : ℕ} (a b : Vec T) : 0 ≤ pairNorm a b := by
  unfold pairNorm
  exact Real.sqrt_nonneg _

/-- Each block norm is bounded by the product norm. -/
theorem norm_le_pairNorm_left {T : ℕ} (a b : Vec T) : ‖a‖ ≤ pairNorm a b := by
  have hs := pairNorm_sq_eq a b
  have hp := pairNorm_nonneg a b
  have ha := norm_nonneg a
  have hb2 : 0 ≤ ‖b‖ ^ 2 := sq_nonneg _
  nlinarith

/-- Symmetric block bound. -/
theorem norm_le_pairNorm_right {T : ℕ} (a b : Vec T) : ‖b‖ ≤ pairNorm a b := by
  have hs := pairNorm_sq_eq a b
  have hp := pairNorm_nonneg a b
  have hb := norm_nonneg b
  have ha2 : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  nlinarith

/-- Triangle inequality for the explicit product norm used throughout the paper. -/
theorem pairNorm_triangle {T : ℕ} (a b c d : Vec T) :
    pairNorm (a + c) (b + d) ≤ pairNorm a b + pairNorm c d := by
  let p := pairNorm a b
  let q := pairNorm c d
  have hp : 0 ≤ p := by simpa [p] using pairNorm_nonneg a b
  have hq : 0 ≤ q := by simpa [q] using pairNorm_nonneg c d
  have hp2 : p ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simpa [p] using pairNorm_sq_eq a b
  have hq2 : q ^ 2 = ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
    simpa [q] using pairNorm_sq_eq c d
  have hac := norm_add_le a c
  have hbd := norm_add_le b d
  have hac2 : ‖a + c‖ ^ 2 ≤ (‖a‖ + ‖c‖) ^ 2 := by
    have h0 : 0 ≤ ‖a + c‖ := norm_nonneg _
    have h1 : 0 ≤ ‖a‖ + ‖c‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have hbd2 : ‖b + d‖ ^ 2 ≤ (‖b‖ + ‖d‖) ^ 2 := by
    have h0 : 0 ≤ ‖b + d‖ := norm_nonneg _
    have h1 : 0 ≤ ‖b‖ + ‖d‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have hcauchy_sq :
      (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖) ^ 2 ≤
        (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖)]
  have hcauchy : ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ ≤ p * q := by
    have hcross : 0 ≤ ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ := by positivity
    have hpq : 0 ≤ p * q := mul_nonneg hp hq
    rw [← hp2, ← hq2] at hcauchy_sq
    nlinarith [sq_nonneg (p * q - (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖))]
  have hsq :
      pairNorm (a + c) (b + d) ^ 2 ≤ (p + q) ^ 2 := by
    rw [pairNorm_sq_eq]
    calc
      ‖a + c‖ ^ 2 + ‖b + d‖ ^ 2
          ≤ (‖a‖ + ‖c‖) ^ 2 + (‖b‖ + ‖d‖) ^ 2 := add_le_add hac2 hbd2
      _ ≤ (p + q) ^ 2 := by
        nlinarith [hp2, hq2, hcauchy]
  have hl : 0 ≤ pairNorm (a + c) (b + d) := pairNorm_nonneg _ _
  have hr : 0 ≤ p + q := add_nonneg hp hq
  nlinarith

/-- The pure quadratic coupling has product-gradient Lipschitz constant
`ν(1+γ²)`. -/
theorem lift_quadratic_pair_bound {T : ℕ} (P : LiftParameters) (dx dy : Vec T) :
    pairNorm
        ((P.ν * P.γ) • (dy - P.γ • dx))
        ((-P.ν) • (dy - P.γ • dx)) ≤
      P.ν * (1 + P.γ ^ 2) * pairNorm dx dy := by
  let r : Vec T := dy - P.γ • dx
  have hnu : 0 < P.ν := lift_nu_pos P
  have hγ : 0 < P.γ := P.γ_pos
  have hr : ‖r‖ ≤ ‖dy‖ + P.γ * ‖dx‖ := by
    dsimp [r]
    calc
      ‖dy - P.γ • dx‖ ≤ ‖dy‖ + ‖P.γ • dx‖ := norm_sub_le _ _
      _ = ‖dy‖ + P.γ * ‖dx‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hr2 : ‖r‖ ^ 2 ≤ (1 + P.γ ^ 2) * pairNorm dx dy ^ 2 := by
    have hrsq : ‖r‖ ^ 2 ≤ (‖dy‖ + P.γ * ‖dx‖) ^ 2 := by
      have h0 := norm_nonneg r
      have h1 : 0 ≤ ‖dy‖ + P.γ * ‖dx‖ := by positivity
      nlinarith
    have hp := pairNorm_sq_eq dx dy
    calc
      ‖r‖ ^ 2 ≤ (‖dy‖ + P.γ * ‖dx‖) ^ 2 := hrsq
      _ ≤ (1 + P.γ ^ 2) * (‖dx‖ ^ 2 + ‖dy‖ ^ 2) := by
        nlinarith [sq_nonneg (‖dx‖ - P.γ * ‖dy‖)]
      _ = (1 + P.γ ^ 2) * pairNorm dx dy ^ 2 := by rw [hp]
  have hout :
      pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) ^ 2 =
        P.ν ^ 2 * (1 + P.γ ^ 2) * ‖r‖ ^ 2 := by
    rw [pairNorm_sq_eq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (mul_pos hnu hγ), abs_neg, abs_of_pos hnu]
    ring
  have htarget :
      pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) ^ 2 ≤
        (P.ν * (1 + P.γ ^ 2) * pairNorm dx dy) ^ 2 := by
    rw [hout]
    have hfac : 0 ≤ P.ν ^ 2 * (1 + P.γ ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hr2 hfac
    nlinarith [sq_nonneg P.γ]
  have hl : 0 ≤ pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) := pairNorm_nonneg _ _
  have hγfac : 0 ≤ 1 + P.γ ^ 2 := by nlinarith [sq_nonneg P.γ]
  have hright : 0 ≤ P.ν * (1 + P.γ ^ 2) * pairNorm dx dy :=
    mul_nonneg (mul_nonneg (le_of_lt hnu) hγfac) (pairNorm_nonneg dx dy)
  simpa [r] using (by nlinarith :
    pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) ≤
      P.ν * (1 + P.γ ^ 2) * pairNorm dx dy)

/-- The chain contribution to the lifted dual gradient is `ℓ₀ h`-Lipschitz in the product norm. -/
theorem lift_chain_pair_bound {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (dx y y' : Vec T) :
    pairNorm 0 (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) ≤
      (ℓ₀ * P.h) * pairNorm dx (y - y') := by
  have hq : 0 < P.q := P.q_pos
  have hβ : 0 < P.β := div_pos P.h_pos P.q_pos
  have hl0 : 0 ≤ ℓ₀ := by norm_num [ℓ₀]
  have hgrad := C.grad_lipschitz (P.β • y) (P.β • y')
  have harg : ‖P.β • y - P.β • y'‖ = P.β * ‖y - y'‖ := by
    have hv : P.β • y - P.β • y' = P.β • (y - y') := by module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  rw [harg] at hgrad
  have hchain :
      ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ ≤
        (ℓ₀ * P.h) * ‖y - y'‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    calc
      P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖
          ≤ P.q * (ℓ₀ * (P.β * ‖y - y'‖)) :=
            mul_le_mul_of_nonneg_left hgrad (le_of_lt hq)
      _ = (ℓ₀ * P.h) * ‖y - y'‖ := by
        rw [← P.q_mul_beta]
        ring
  have hzero :
      pairNorm (0 : Vec T) (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) =
        ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ := by
    have hs := pairNorm_sq_eq (0 : Vec T)
      (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')))
    have hp := pairNorm_nonneg (0 : Vec T)
      (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')))
    have hn := norm_nonneg (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')))
    simp at hs
    nlinarith
  rw [hzero]
  calc
    ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖
        ≤ (ℓ₀ * P.h) * ‖y - y'‖ := hchain
    _ ≤ (ℓ₀ * P.h) * pairNorm dx (y - y') := by
      exact mul_le_mul_of_nonneg_left (norm_le_pairNorm_right dx (y - y'))
        (mul_nonneg hl0 (le_of_lt P.h_pos))

/-- Paper equation (11): the displayed lifted gradient is jointly Lipschitz with constant
`ν(1+γ²)+ℓ₀h`. -/
theorem liftedF_joint_smoothness {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) :
    ∀ x y x' y',
      pairNorm
        ((P.ν * P.γ) • (y - P.γ • x) - (P.ν * P.γ) • (y' - P.γ • x'))
        ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
         (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x'))) ≤
        (P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h) * pairNorm (x - x') (y - y') := by
  intro x y x' y'
  let dx : Vec T := x - x'
  let dy : Vec T := y - y'
  let r : Vec T := dy - P.γ • dx
  let dg : Vec T := C.gradF (P.β • y) - C.gradF (P.β • y')
  have hx :
      (P.ν * P.γ) • (y - P.γ • x) - (P.ν * P.γ) • (y' - P.γ • x') =
        (P.ν * P.γ) • r := by
    dsimp [r, dx, dy]
    module
  have hy :
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
          (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x')) =
        (-P.ν) • r + P.q • dg := by
    dsimp [r, dx, dy, dg]
    module
  rw [hx, hy]
  calc
    pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r + P.q • dg)
        ≤ pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) + pairNorm 0 (P.q • dg) := by
          simpa using pairNorm_triangle
            ((P.ν * P.γ) • r) ((-P.ν) • r) (0 : Vec T) (P.q • dg)
    _ ≤ P.ν * (1 + P.γ ^ 2) * pairNorm dx dy +
          (ℓ₀ * P.h) * pairNorm dx dy := by
      apply add_le_add
      · simpa [r] using lift_quadratic_pair_bound P dx dy
      · simpa [dg, dy] using lift_chain_pair_bound C P dx y y'
    _ = (P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h) * pairNorm dx dy := by ring
    _ = (P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h) *
          pairNorm (x - x') (y - y') := by rfl

/-- Actual primal partial gradient of the lifted objective. -/
theorem liftedF_gradX_formula {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    IsEuclideanGradientAt (fun x' => liftedF C P x' y)
      ((P.ν * P.γ) • (y - P.γ • x)) x := by
  change HasGradientAt (fun x' => liftedF C P x' y)
    ((P.ν * P.γ) • (y - P.γ • x)) x
  rw [hasGradientAt_iff_hasFDerivAt]
  have haff0 :
      HasFDerivAt (fun x' : Vec T => y - P.γ • x')
        ((0 : Vec T →L[ℝ] Vec T) - P.γ • (1 : Vec T →L[ℝ] Vec T)) x :=
    (hasFDerivAt_const (𝕜 := ℝ) y x).sub
      ((hasFDerivAt_id x).const_smul P.γ)
  have haff :
      HasFDerivAt (fun x' : Vec T => y - P.γ • x')
        ((-P.γ) • (1 : Vec T →L[ℝ] Vec T)) x := by
    convert haff0 using 1
    · ext z
      simp
  have hsq := haff.norm_sq
  have hquad := hsq.const_smul (-P.ν / 2)
  have hconst := hasFDerivAt_const (𝕜 := ℝ)
    (P.α * explicitFT T C.dim_pos (P.β • y)) x
  have hsum := hconst.add hquad
  have hD :
      (0 : Vec T →L[ℝ] ℝ) +
          (-P.ν / 2) •
            (2 • (innerSL ℝ (y - P.γ • x)).comp
              ((-P.γ) • (1 : Vec T →L[ℝ] Vec T))) =
        InnerProductSpace.toDual ℝ (Vec T) ((P.ν * P.γ) • (y - P.γ • x)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hD] at hsum
  have hfun :
      (fun x' : Vec T => liftedF C P x' y) =
        (fun x' : Vec T =>
          P.α * explicitFT T C.dim_pos (P.β • y) +
            (-P.ν / 2) • ‖y - P.γ • x'‖ ^ 2) := by
    funext x'
    simp [liftedF, smul_eq_mul]
    ring
  rw [hfun]
  exact hsum

/-- Actual dual partial gradient of the lifted objective. -/
theorem liftedF_gradY_formula {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x y : Vec T) :
    IsEuclideanGradientAt (fun y' => liftedF C P x y')
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) y := by
  change HasGradientAt (fun y' => liftedF C P x y')
    (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) y
  rw [hasGradientAt_iff_hasFDerivAt]
  have hbase : HasGradientAt (explicitFT T C.dim_pos)
      (C.gradF (P.β • y)) (P.β • y) := by
    exact C.grad_is_gradient (P.β • y)
  have hlin :
      HasFDerivAt (fun y' : Vec T => P.β • y')
        (P.β • (1 : Vec T →L[ℝ] Vec T)) y := by
    simpa using (hasFDerivAt_id y).const_smul P.β
  have hchain0 := hbase.hasFDerivAt.comp y hlin
  have hchain := hchain0.const_smul P.α
  have hchainD :
      P.α • ((InnerProductSpace.toDual ℝ (Vec T) (C.gradF (P.β • y))).comp
        (P.β • (1 : Vec T →L[ℝ] Vec T))) =
        InnerProductSpace.toDual ℝ (Vec T) (P.q • C.gradF (P.β • y)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, P.alpha_mul_beta]
  rw [hchainD] at hchain
  have haff0 := (hasFDerivAt_id y).sub
    (hasFDerivAt_const (𝕜 := ℝ) (P.γ • x) y)
  have haff :
      HasFDerivAt (fun y' : Vec T => y' - P.γ • x)
        (1 : Vec T →L[ℝ] Vec T) y := by
    simpa using haff0
  have hsq := haff.norm_sq
  have hquad := hsq.const_smul (-P.ν / 2)
  have hquadD :
      (-P.ν / 2) •
          (2 • (innerSL ℝ (y - P.γ • x)).comp
            (1 : Vec T →L[ℝ] Vec T)) =
        InnerProductSpace.toDual ℝ (Vec T) ((-P.ν) • (y - P.γ • x)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hquadD] at hquad
  have hsum := hchain.add hquad
  have hsumD :
      InnerProductSpace.toDual ℝ (Vec T) (P.q • C.gradF (P.β • y)) +
          InnerProductSpace.toDual ℝ (Vec T) ((-P.ν) • (y - P.γ • x)) =
        InnerProductSpace.toDual ℝ (Vec T)
          (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) := by
    ext z
    simpa [sub_eq_add_neg, real_inner_smul_left, add_comm]
  rw [hsumD] at hsum
  have hfun :
      (fun y' : Vec T => liftedF C P x y') =
        (fun y' : Vec T =>
          P.α • explicitFT T C.dim_pos (P.β • y') +
            (-P.ν / 2) • ‖y' - P.γ • x‖ ^ 2) := by
    funext y'
    simp [liftedF, smul_eq_mul]
    ring
  rw [hfun]
  exact hsum


/-! ## v25 proof phase XVI: argmax stability and the stationarity-transfer candidate

This phase isolates the quantitative part of the envelope argument that does not yet require
Fréchet differentiation of the value function.  Strong concavity gives a global Lipschitz estimate
for the canonical maximizer.  The dual first-order condition then identifies the natural envelope
gradient candidate and proves the exact norm comparison underlying paper equation (15).

The only remaining step before this candidate can fill `gradPhi_spec` is the Danskin/envelope
differentiability proof for `canonicalLiftPhi`.
-/

/-- The canonical dual maximizer is globally Lipschitz.  This is the quantitative estimate used
in the paper's direct envelope argument:

`‖y*(x)-y*(x')‖ ≤ (νγ/μ) ‖x-x'‖`.
-/
theorem canonicalLiftYStar_lipschitz {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x x' : Vec T) :
    ‖canonicalLiftYStar C P x - canonicalLiftYStar C P x'‖ ≤
      (P.ν * P.γ / P.μ) * ‖x - x'‖ := by
  let y : Vec T := canonicalLiftYStar C P x
  let y' : Vec T := canonicalLiftYStar C P x'
  let d : Vec T := y - y'
  let dx : Vec T := x - x'
  have hy :
      P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x) = 0 := by
    simpa only [y] using canonicalLiftYStar_dual_stationary C P x
  have hy' :
      P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x') = 0 := by
    simpa only [y'] using canonicalLiftYStar_dual_stationary C P x'
  have hcross :
      P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x) =
        (P.ν * P.γ) • dx := by
    calc
      P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x) =
          (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x')) +
            (P.ν * P.γ) • (x - x') := by
              module
      _ = (P.ν * P.γ) • (x - x') := by rw [hy']; simp
      _ = (P.ν * P.γ) • dx := by rfl
  have hanti := liftStrongConcavity_antimonotone C P P.μ
    (liftedF_mu_strong_concavity C P) x y y'
  have hgradDiff :
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
        (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x)) =
          -((P.ν * P.γ) • dx) := by
    rw [hy, hcross]
    module
  rw [hgradDiff] at hanti
  have hinner :
      @inner ℝ (Vec T) _ dx d ≤ ‖dx‖ * ‖d‖ :=
    real_inner_le_norm dx d
  have hk : 0 < P.ν * P.γ := mul_pos (lift_nu_pos P) P.γ_pos
  have hmuquad :
      P.μ * ‖d‖ ^ 2 ≤ (P.ν * P.γ) *
        @inner ℝ (Vec T) _ dx d := by
    rw [inner_neg_left, real_inner_smul_left] at hanti
    nlinarith
  have hmain :
      P.μ * ‖d‖ ^ 2 ≤ (P.ν * P.γ) * (‖dx‖ * ‖d‖) := by
    exact le_trans hmuquad
      (mul_le_mul_of_nonneg_left hinner (le_of_lt hk))
  by_cases hd0 : ‖d‖ = 0
  · have hcoef : 0 ≤ P.ν * P.γ / P.μ :=
      le_of_lt (div_pos hk P.μ_pos)
    have hleft :
        ‖canonicalLiftYStar C P x - canonicalLiftYStar C P x'‖ = 0 := by
      simpa only [d, y, y'] using hd0
    rw [hleft]
    exact mul_nonneg hcoef (norm_nonneg _)
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd0)
    have hcancel : P.μ * ‖d‖ ≤ (P.ν * P.γ) * ‖dx‖ := by
      nlinarith
    have hcancel' : ‖d‖ * P.μ ≤ (P.ν * P.γ) * ‖dx‖ := by
      nlinarith [hcancel]
    have hdiv : ‖d‖ ≤ ((P.ν * P.γ) * ‖dx‖) / P.μ :=
      (le_div_iff₀ P.μ_pos).2 hcancel'
    simpa [d, dx, y, y', div_mul_eq_mul_div, mul_assoc] using hdiv

/-- The natural envelope-gradient candidate obtained by differentiating the lift only in the
primal variable at the canonical maximizer. -/
noncomputable def canonicalLiftGradPhi {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) : Vec T :=
  (P.ν * P.γ) • (canonicalLiftYStar C P x - P.γ • x)

/-- The dual first-order condition rewrites the envelope-gradient candidate exactly as
`γ q ∇F_T(z*)`. -/
theorem canonicalLiftGradPhi_eq_scaled_chain {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    canonicalLiftGradPhi C P x =
      (P.γ * P.q) • C.gradF (P.β • canonicalLiftYStar C P x) := by
  have hstat := canonicalLiftYStar_dual_stationary C P x
  have hqeq :
      P.q • C.gradF (P.β • canonicalLiftYStar C P x) =
        P.ν • (canonicalLiftYStar C P x - P.γ • x) :=
    sub_eq_zero.mp hstat
  unfold canonicalLiftGradPhi
  calc
    (P.ν * P.γ) • (canonicalLiftYStar C P x - P.γ • x) =
        P.γ • (P.ν • (canonicalLiftYStar C P x - P.γ • x)) := by
          module
    _ = P.γ • (P.q • C.gradF (P.β • canonicalLiftYStar C P x)) := by rw [← hqeq]
    _ = (P.γ * P.q) • C.gradF (P.β • canonicalLiftYStar C P x) := by
      module

/-- Fixed-point comparison between the chain gradient at the primal point
`w=(βγ)x` and at the dual maximizer `z*=βy*(x)`.  This is the quantitative core
of paper equation (15). -/
theorem canonicalLift_chain_gradient_comparison {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    ‖C.gradF ((P.β * P.γ) • x)‖ ≤
      (1 + ℓ₀ * P.h / P.ν) *
        ‖C.gradF (P.β • canonicalLiftYStar C P x)‖ := by
  let z : Vec T := P.β • canonicalLiftYStar C P x
  let w : Vec T := (P.β * P.γ) • x
  let gz : Vec T := C.gradF z
  let gw : Vec T := C.gradF w
  have hfp := canonicalLiftYStar_scaled_fixed_point C P x
  have hzw : z - w = (P.h / P.ν) • gz := by
    simpa only [z, w, gz] using hfp
  have hwz : w - z = -(P.h / P.ν) • gz := by
    calc
      w - z = -(z - w) := by module
      _ = -((P.h / P.ν) • gz) := by rw [hzw]
      _ = -(P.h / P.ν) • gz := by module
  have hratio : 0 < P.h / P.ν := div_pos P.h_pos (lift_nu_pos P)
  have hnormdiff : ‖w - z‖ = (P.h / P.ν) * ‖gz‖ := by
    rw [hwz, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hratio]
  have hlip : ‖gw - gz‖ ≤ ℓ₀ * ‖w - z‖ := by
    simpa only [gw, gz] using C.grad_lipschitz w z
  have htri : ‖gw‖ ≤ ‖gw - gz‖ + ‖gz‖ := by
    calc
      ‖gw‖ = ‖(gw - gz) + gz‖ := by
        congr 1
        module
      _ ≤ ‖gw - gz‖ + ‖gz‖ := norm_add_le _ _
  calc
    ‖C.gradF ((P.β * P.γ) • x)‖ = ‖gw‖ := by rfl
    _ ≤ ‖gw - gz‖ + ‖gz‖ := htri
    _ ≤ ℓ₀ * ‖w - z‖ + ‖gz‖ := add_le_add_right hlip _
    _ = (1 + ℓ₀ * P.h / P.ν) * ‖gz‖ := by
      rw [hnormdiff]
      ring
    _ = (1 + ℓ₀ * P.h / P.ν) *
          ‖C.gradF (P.β • canonicalLiftYStar C P x)‖ := by rfl

/-- Paper equation (15) for the explicit envelope-gradient candidate.  Once
`canonicalLiftPhi_grad` proves that this candidate is the actual gradient of the value function,
this theorem fills `LiftPropertiesCertificate.stationarity_transfer` without any additional
analytic assumption. -/
theorem canonicalLift_stationarity_transfer_candidate {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) *
      ‖C.gradF ((P.β * P.γ) • x)‖ ≤ ‖canonicalLiftGradPhi C P x‖ := by
  have hcomp := canonicalLift_chain_gradient_comparison C P x
  have hnu : 0 < P.ν := lift_nu_pos P
  have hden : 0 < 1 + ℓ₀ * P.h / P.ν := by
    have hl0 : 0 ≤ ℓ₀ := by norm_num [ℓ₀]
    have hfrac : 0 ≤ ℓ₀ * P.h / P.ν :=
      div_nonneg (mul_nonneg hl0 (le_of_lt P.h_pos)) (le_of_lt hnu)
    linarith
  have hγq : 0 < P.γ * P.q := mul_pos P.γ_pos P.q_pos
  have hnorm :
      ‖canonicalLiftGradPhi C P x‖ =
        (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar C P x)‖ := by
    rw [canonicalLiftGradPhi_eq_scaled_chain C P x, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγq]
  rw [hnorm]
  have hscaled := mul_le_mul_of_nonneg_left hcomp (le_of_lt hγq)
  have hdiv :
      ((P.γ * P.q) * ‖C.gradF ((P.β * P.γ) • x)‖) /
          (1 + ℓ₀ * P.h / P.ν) ≤
        (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar C P x)‖ := by
    apply (div_le_iff₀ hden).2
    calc
      (P.γ * P.q) * ‖C.gradF ((P.β * P.γ) • x)‖
          ≤ (P.γ * P.q) *
              ((1 + ℓ₀ * P.h / P.ν) *
                ‖C.gradF (P.β • canonicalLiftYStar C P x)‖) := hscaled
      _ = (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar C P x)‖ *
            (1 + ℓ₀ * P.h / P.ν) := by ring
  simpa [div_mul_eq_mul_div, mul_assoc] using hdiv


/-! ## v26 proof phase XVII: envelope differentiability

The v25 phase identified the natural value-function gradient and proved the quantitative
stationarity comparison.  This phase closes the remaining Danskin/envelope bridge directly from
the special quadratic dependence of `liftedF` on the primal variable and the global Lipschitz
stability of the canonical dual maximizer.  No abstract envelope theorem is imported.
-/

/-- Exact primal increment of the quadratic lift with the dual point held fixed.  This is the
finite-dimensional Taylor formula underlying the direct envelope argument. -/
theorem liftedF_primal_increment_exact {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters)
    (x x' y : Vec T) :
    liftedF C P x' y - liftedF C P x y =
      @inner ℝ (Vec T) _
        ((P.ν * P.γ) • (y - P.γ • x)) (x' - x) -
      (P.ν * P.γ ^ 2 / 2) * ‖x' - x‖ ^ 2 := by
  have hvec :
      y - P.γ • x' =
        (y - P.γ • x) + (-P.γ) • (x' - x) := by
    module
  have hnorm :
      ‖y - P.γ • x'‖ ^ 2 =
        ‖y - P.γ • x‖ ^ 2 -
          2 * P.γ * @inner ℝ (Vec T) _ (y - P.γ • x) (x' - x) +
          P.γ ^ 2 * ‖x' - x‖ ^ 2 := by
    rw [hvec, norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos P.γ_pos]
    ring
  unfold liftedF
  rw [hnorm, real_inner_smul_left]
  ring

/-- Lower envelope estimate: freezing the old maximizer gives the lower quadratic model for the
value-function increment. -/
theorem canonicalLiftPhi_remainder_lower {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters)
    (x x' : Vec T) :
    -(P.ν * P.γ ^ 2 / 2) * ‖x' - x‖ ^ 2 ≤
      canonicalLiftPhi C P x' - canonicalLiftPhi C P x -
        @inner ℝ (Vec T) _ (canonicalLiftGradPhi C P x) (x' - x) := by
  let y : Vec T := canonicalLiftYStar C P x
  have hmax : liftedF C P x' y ≤ canonicalLiftPhi C P x' :=
    canonicalLiftPhi_is_value C P x' y
  have hinc := liftedF_primal_increment_exact C P x x' y
  have hphix : canonicalLiftPhi C P x = liftedF C P x y := by
    rfl
  have hgrad :
      canonicalLiftGradPhi C P x =
        (P.ν * P.γ) • (y - P.γ • x) := by
    rfl
  rw [hphix, hgrad]
  nlinarith

/-- Upper envelope estimate: evaluate the old primal point at the new maximizer and control the
resulting gradient mismatch by the Lipschitz stability of `y*`. -/
theorem canonicalLiftPhi_remainder_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters)
    (x x' : Vec T) :
    canonicalLiftPhi C P x' - canonicalLiftPhi C P x -
        @inner ℝ (Vec T) _ (canonicalLiftGradPhi C P x) (x' - x) ≤
      ((P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖x' - x‖ ^ 2 := by
  let y : Vec T := canonicalLiftYStar C P x
  let y' : Vec T := canonicalLiftYStar C P x'
  let d : Vec T := x' - x
  have hvalue : liftedF C P x y' ≤ canonicalLiftPhi C P x :=
    canonicalLiftPhi_is_value C P x y'
  have hinc := liftedF_primal_increment_exact C P x x' y'
  have hphix' : canonicalLiftPhi C P x' = liftedF C P x' y' := by
    rfl
  have hgrad :
      canonicalLiftGradPhi C P x =
        (P.ν * P.γ) • (y - P.γ • x) := by
    rfl
  have hdiffgrad :
      (P.ν * P.γ) • (y' - P.γ • x) -
          (P.ν * P.γ) • (y - P.γ • x) =
        (P.ν * P.γ) • (y' - y) := by
    module
  have hinnerdiff :
      @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - P.γ • x)) d -
          @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y - P.γ • x)) d =
        @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - y)) d := by
    rw [← inner_sub_left, hdiffgrad]
  have hylip :
      ‖y' - y‖ ≤ (P.ν * P.γ / P.μ) * ‖d‖ := by
    simpa only [y, y', d] using canonicalLiftYStar_lipschitz C P x' x
  have hkpos : 0 < P.ν * P.γ := mul_pos (lift_nu_pos P) P.γ_pos
  have hinner0 :
      @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - y)) d ≤
        ‖(P.ν * P.γ) • (y' - y)‖ * ‖d‖ :=
    real_inner_le_norm _ _
  have hprod :
      (P.ν * P.γ) * ‖y' - y‖ * ‖d‖ ≤
        ((P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖d‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hylip (le_of_lt hkpos)
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg d)
    simpa [pow_two, mul_assoc] using h2
  have hinner :
      @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - y)) d ≤
        ((P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖d‖ ^ 2 := by
    calc
      @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - y)) d
          ≤ ‖(P.ν * P.γ) • (y' - y)‖ * ‖d‖ := hinner0
      _ = (P.ν * P.γ) * ‖y' - y‖ * ‖d‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hkpos]
      _ ≤ ((P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖d‖ ^ 2 := hprod
  rw [hphix', hgrad]
  have hinc' := hinc
  rw [show x' - x = d by rfl] at hinc'
  have hc0 : 0 ≤ P.ν * P.γ ^ 2 / 2 := by
    exact div_nonneg
      (mul_nonneg (le_of_lt (lift_nu_pos P)) (sq_nonneg P.γ)) (by norm_num)
  have hc : 0 ≤ (P.ν * P.γ ^ 2 / 2) * ‖d‖ ^ 2 :=
    mul_nonneg hc0 (sq_nonneg ‖d‖)
  change
    liftedF C P x' y' - canonicalLiftPhi C P x -
        @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y - P.γ • x)) d ≤
      ((P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖d‖ ^ 2
  calc
    liftedF C P x' y' - canonicalLiftPhi C P x -
          @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y - P.γ • x)) d
        ≤ (liftedF C P x' y' - liftedF C P x y') -
          @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y - P.γ • x)) d := by
            linarith
    _ = (@inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - P.γ • x)) d -
          (P.ν * P.γ ^ 2 / 2) * ‖d‖ ^ 2) -
          @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y - P.γ • x)) d := by
            rw [hinc']
    _ ≤ @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - P.γ • x)) d -
          @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y - P.γ • x)) d := by
            linarith
    _ = @inner ℝ (Vec T) _ ((P.ν * P.γ) • (y' - y)) d := hinnerdiff
    _ ≤ ((P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖d‖ ^ 2 := hinner

/-- The value-function Taylor remainder is quadratically small.  This is the precise estimate
needed by the Fréchet-gradient criterion. -/
theorem canonicalLiftPhi_remainder_norm_bound {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters)
    (x x' : Vec T) :
    ‖canonicalLiftPhi C P x' - canonicalLiftPhi C P x -
        @inner ℝ (Vec T) _ (canonicalLiftGradPhi C P x) (x' - x)‖ ≤
      (P.ν * P.γ ^ 2 / 2 +
        (P.ν * P.γ) * (P.ν * P.γ / P.μ)) * ‖x' - x‖ ^ 2 := by
  have hlo := canonicalLiftPhi_remainder_lower C P x x'
  have hup := canonicalLiftPhi_remainder_upper C P x x'
  have hnu0 : 0 ≤ P.ν := le_of_lt (lift_nu_pos P)
  have hgamma0 : 0 ≤ P.γ := le_of_lt P.γ_pos
  have hmu0 : 0 ≤ P.μ := le_of_lt P.μ_pos
  have hc : 0 ≤ P.ν * P.γ ^ 2 / 2 := by
    exact div_nonneg (mul_nonneg hnu0 (sq_nonneg P.γ)) (by norm_num)
  have hkg : 0 ≤ P.ν * P.γ := mul_nonneg hnu0 hgamma0
  have hratio : 0 ≤ P.ν * P.γ / P.μ := div_nonneg hkg hmu0
  have hk : 0 ≤ (P.ν * P.γ) * (P.ν * P.γ / P.μ) :=
    mul_nonneg hkg hratio
  have hn : 0 ≤ ‖x' - x‖ ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Direct Danskin/envelope theorem for the explicit lifted value function.  The proof uses the
quadratic remainder estimate above rather than importing an abstract envelope theorem. -/
theorem canonicalLiftPhi_grad {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    IsEuclideanGradientAt (canonicalLiftPhi C P) (canonicalLiftGradPhi C P x) x := by
  change HasGradientAt (canonicalLiftPhi C P) (canonicalLiftGradPhi C P x) x
  rw [hasGradientAt_iff_tendsto]
  let K : ℝ := P.ν * P.γ ^ 2 / 2 +
    (P.ν * P.γ) * (P.ν * P.γ / P.μ)
  have hnu0 : 0 ≤ P.ν := le_of_lt (lift_nu_pos P)
  have hgamma0 : 0 ≤ P.γ := le_of_lt P.γ_pos
  have hmu0 : 0 ≤ P.μ := le_of_lt P.μ_pos
  have hc0 : 0 ≤ P.ν * P.γ ^ 2 / 2 := by
    exact div_nonneg (mul_nonneg hnu0 (sq_nonneg P.γ)) (by norm_num)
  have hkg : 0 ≤ P.ν * P.γ := mul_nonneg hnu0 hgamma0
  have hratio : 0 ≤ P.ν * P.γ / P.μ := div_nonneg hkg hmu0
  have hk0 : 0 ≤ (P.ν * P.γ) * (P.ν * P.γ / P.μ) :=
    mul_nonneg hkg hratio
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hc0 hk0
  have hnormt :
      Filter.Tendsto (fun x' : Vec T => ‖x' - x‖) (nhds x) (nhds 0) := by
    have hc : ContinuousAt (fun x' : Vec T => ‖x' - x‖) x :=
      (continuousAt_id.sub continuousAt_const).norm
    simpa only [ContinuousAt, sub_self, norm_zero] using hc
  have hKt :
      Filter.Tendsto (fun x' : Vec T => K * ‖x' - x‖) (nhds x) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hnormt)
  apply squeeze_zero
  · intro x'
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · intro x'
    have hrem := canonicalLiftPhi_remainder_norm_bound C P x x'
    change
      ‖x' - x‖⁻¹ *
          ‖canonicalLiftPhi C P x' - canonicalLiftPhi C P x -
            @inner ℝ (Vec T) _ (canonicalLiftGradPhi C P x) (x' - x)‖ ≤
        K * ‖x' - x‖
    by_cases hd : ‖x' - x‖ = 0
    · simp [hd]
    · have hdpos : 0 < ‖x' - x‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      have hmul := mul_le_mul_of_nonneg_left hrem
        (inv_nonneg.mpr (norm_nonneg (x' - x)))
      calc
        ‖x' - x‖⁻¹ *
            ‖canonicalLiftPhi C P x' - canonicalLiftPhi C P x -
              @inner ℝ (Vec T) _ (canonicalLiftGradPhi C P x) (x' - x)‖
            ≤ ‖x' - x‖⁻¹ * (K * ‖x' - x‖ ^ 2) := by
              simpa [K] using hmul
        _ = K * ‖x' - x‖ := by
          field_simp [hd]
          ring
  · exact hKt

/-- Equation (15) for the actual gradient of the value function. -/
theorem canonicalLift_stationarity_transfer {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x : Vec T) :
    P.γ * P.q / (1 + ℓ₀ * P.h / P.ν) *
      ‖C.gradF ((P.β * P.γ) • x)‖ ≤ ‖canonicalLiftGradPhi C P x‖ :=
  canonicalLift_stationarity_transfer_candidate C P x


/-! ## v27 proof phase XVIII: stochastic lift-transfer closure

The deterministic analytic core of Lemma 2.3 is kernel-built through v26.2.  This phase repairs
and proves the two remaining stochastic transfer interfaces needed by the Bernoulli specialization:

* the same-seed averaged-smooth transfer is stated under the natural probability assumptions
  `0 < p ≤ 1` and the paper's nonnegative root constant `s₀`;
* the zero-chain transfer is formulated almost surely, exactly as Definition 1.4, rather than
  pointwise on null seeds.

No new analytic input is introduced.
-/

/-- Monotonicity of the explicit two-point Bernoulli expectation. -/
theorem bernoulliExpectReal_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X Y : Bool → ℝ) (hXY : ∀ z, X z ≤ Y z) :
    bernoulliExpectReal p X ≤ bernoulliExpectReal p Y := by
  unfold bernoulliExpectReal
  have hfalse : 0 ≤ 1 - p := by linarith
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hXY true) hp0)
    (mul_le_mul_of_nonneg_left (hXY false) hfalse)

/-- Nonnegative functions have nonnegative Bernoulli expectation. -/
theorem bernoulliExpectReal_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Bool → ℝ) (hX : ∀ z, 0 ≤ X z) :
    0 ≤ bernoulliExpectReal p X := by
  unfold bernoulliExpectReal
  have hfalse : 0 ≤ 1 - p := by linarith
  exact add_nonneg (mul_nonneg hp0 (hX true)) (mul_nonneg hfalse (hX false))

/-- Two-point Cauchy--Schwarz: the square of a Bernoulli mean is at most its second moment. -/
theorem bernoulliExpectReal_sq_le_second_moment (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Bool → ℝ) :
    (bernoulliExpectReal p X) ^ 2 ≤ bernoulliExpectReal p (fun z => X z ^ 2) := by
  have hfalse : 0 ≤ 1 - p := by linarith
  have hw : 0 ≤ p * (1 - p) := mul_nonneg hp0 hfalse
  have hs : 0 ≤ (X true - X false) ^ 2 := sq_nonneg _
  have hrem : 0 ≤ p * (1 - p) * (X true - X false) ^ 2 := mul_nonneg hw hs
  unfold bernoulliExpectReal
  calc
    (p * X true + (1 - p) * X false) ^ 2 =
        p * X true ^ 2 + (1 - p) * X false ^ 2 -
          p * (1 - p) * (X true - X false) ^ 2 := by ring
    _ ≤ p * X true ^ 2 + (1 - p) * X false ^ 2 := by linarith

/-- If a nonnegative Bernoulli random variable has second moment at most `S²`, then its mean is
at most the nonnegative root bound `S`. -/
theorem bernoulliExpectReal_le_of_second_moment_le_sq
    (p S : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hS : 0 ≤ S)
    (X : Bool → ℝ) (hX : ∀ z, 0 ≤ X z)
    (h2 : bernoulliExpectReal p (fun z => X z ^ 2) ≤ S ^ 2) :
    bernoulliExpectReal p X ≤ S := by
  have hm0 := bernoulliExpectReal_nonneg p hp0 hp1 X hX
  have hm2 := bernoulliExpectReal_sq_le_second_moment p hp0 hp1 X
  nlinarith

/-- Pointwise same-seed difference bound for the lifted stochastic oracle.  The quadratic block
contributes `ν(1+γ²)` and the stochastic base difference enters only through the dual block. -/
theorem liftedOracle_pair_difference_bound {T : ℕ}
    (B : BaseOracle T) (P : LiftParameters)
    (x y x' y' : Vec T) (Z : Bool) :
    pairNorm
      (liftedGx P x y Z - liftedGx P x' y' Z)
      (liftedGy B P x y Z - liftedGy B P x' y' Z) ≤
      P.ν * (1 + P.γ ^ 2) * pairNorm (x - x') (y - y') +
        P.q * ‖B.g (P.β • y) Z - B.g (P.β • y') Z‖ := by
  let dx : Vec T := x - x'
  let dy : Vec T := y - y'
  let r : Vec T := dy - P.γ • dx
  let db : Vec T := B.g (P.β • y) Z - B.g (P.β • y') Z
  have hx :
      liftedGx P x y Z - liftedGx P x' y' Z = (P.ν * P.γ) • r := by
    dsimp [liftedGx, r, dx, dy]
    module
  have hy :
      liftedGy B P x y Z - liftedGy B P x' y' Z =
        (-P.ν) • r + P.q • db := by
    dsimp [liftedGy, r, dx, dy, db]
    module
  have hbase : pairNorm (0 : Vec T) (P.q • db) = P.q * ‖db‖ := by
    have hzero : pairNorm (0 : Vec T) (P.q • db) = ‖P.q • db‖ := by
      have hs := pairNorm_sq_eq (0 : Vec T) (P.q • db)
      have hp := pairNorm_nonneg (0 : Vec T) (P.q • db)
      have hn := norm_nonneg (P.q • db)
      simp at hs
      nlinarith
    rw [hzero, norm_smul, Real.norm_eq_abs, abs_of_pos P.q_pos]
  rw [hx, hy]
  calc
    pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r + P.q • db)
        ≤ pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) +
            pairNorm (0 : Vec T) (P.q • db) := by
          simpa using pairNorm_triangle
            ((P.ν * P.γ) • r) ((-P.ν) • r) (0 : Vec T) (P.q • db)
    _ ≤ P.ν * (1 + P.γ ^ 2) * pairNorm dx dy + pairNorm (0 : Vec T) (P.q • db) := by
          exact add_le_add_right (lift_quadratic_pair_bound P dx dy) _
    _ = P.ν * (1 + P.γ ^ 2) * pairNorm dx dy + P.q * ‖db‖ := by rw [hbase]
    _ = P.ν * (1 + P.γ ^ 2) * pairNorm (x - x') (y - y') +
          P.q * ‖B.g (P.β • y) Z - B.g (P.β • y') Z‖ := by rfl

/-- Seed-generic version of the preceding pointwise estimate. -/
theorem genericLiftedOracle_pair_difference_bound {T : ℕ} {Seed : Type}
    (B : GenericBaseOracle T Seed) (P : LiftParameters)
    (x y x' y' : Vec T) (ξ : Seed) :
    pairNorm
      (genericLiftedGx P x y ξ - genericLiftedGx P x' y' ξ)
      (genericLiftedGy B P x y ξ - genericLiftedGy B P x' y' ξ) ≤
      P.ν * (1 + P.γ ^ 2) * pairNorm (x - x') (y - y') +
        P.q * ‖B.g (P.β • y) ξ - B.g (P.β • y') ξ‖ := by
  let dx : Vec T := x - x'
  let dy : Vec T := y - y'
  let r : Vec T := dy - P.γ • dx
  let db : Vec T := B.g (P.β • y) ξ - B.g (P.β • y') ξ
  have hx :
      genericLiftedGx P x y ξ - genericLiftedGx P x' y' ξ =
        (P.ν * P.γ) • r := by
    dsimp [genericLiftedGx, r, dx, dy]
    module
  have hy :
      genericLiftedGy B P x y ξ - genericLiftedGy B P x' y' ξ =
        (-P.ν) • r + P.q • db := by
    dsimp [genericLiftedGy, r, dx, dy, db]
    module
  have hbase : pairNorm (0 : Vec T) (P.q • db) = P.q * ‖db‖ := by
    have hzero : pairNorm (0 : Vec T) (P.q • db) = ‖P.q • db‖ := by
      have hs := pairNorm_sq_eq (0 : Vec T) (P.q • db)
      have hp := pairNorm_nonneg (0 : Vec T) (P.q • db)
      have hn := norm_nonneg (P.q • db)
      simp at hs
      nlinarith
    rw [hzero, norm_smul, Real.norm_eq_abs, abs_of_pos P.q_pos]
  rw [hx, hy]
  calc
    pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r + P.q • db)
        ≤ pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) +
            pairNorm (0 : Vec T) (P.q • db) := by
          simpa using pairNorm_triangle
            ((P.ν * P.γ) • r) ((-P.ν) • r) (0 : Vec T) (P.q • db)
    _ ≤ P.ν * (1 + P.γ ^ 2) * pairNorm dx dy +
          pairNorm (0 : Vec T) (P.q • db) := by
          exact add_le_add_right (lift_quadratic_pair_bound P dx dy) _
    _ = P.ν * (1 + P.γ ^ 2) * pairNorm dx dy + P.q * ‖db‖ := by rw [hbase]
    _ = P.ν * (1 + P.γ ^ 2) * pairNorm (x - x') (y - y') +
          P.q * ‖B.g (P.β • y) ξ - B.g (P.β • y') ξ‖ := by rfl

/-- Paper Lemma 2.3(iv) for an arbitrary coherent probability law. -/
theorem generic_lifted_averaged_smooth_transfer {T : ℕ} {Seed : Type}
    (E : Law Seed) (H : LawAxioms E) (B : GenericBaseOracle T Seed)
    (P : LiftParameters) (p s₀ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hs₀ : 0 ≤ s₀)
    (havg : GenericBaseAveragedSmoothHypothesis E B p s₀) :
    ∀ x y x' y', E.expectReal (fun ξ =>
      ‖genericLiftedGx P x y ξ - genericLiftedGx P x' y' ξ‖ ^ 2 +
      ‖genericLiftedGy B P x y ξ - genericLiftedGy B P x' y' ξ‖ ^ 2) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * s₀ / Real.sqrt p) ^ 2 *
        (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  intro x y x' y'
  let dx : Vec T := x - x'
  let dy : Vec T := y - y'
  let R : ℝ := pairNorm dx dy
  let A : ℝ := P.ν * (1 + P.γ ^ 2)
  let Bc : ℝ := P.h * s₀ / Real.sqrt p
  let X : Seed → ℝ := fun ξ => ‖B.g (P.β • y) ξ - B.g (P.β • y') ξ‖
  let N : Seed → ℝ := fun ξ =>
    pairNorm (genericLiftedGx P x y ξ - genericLiftedGx P x' y' ξ)
      (genericLiftedGy B P x y ξ - genericLiftedGy B P x' y' ξ)
  have hp0 : 0 ≤ p := le_of_lt hp
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrt_ne : Real.sqrt p ≠ 0 := ne_of_gt hsqrt
  have hβ : 0 < P.β := div_pos P.h_pos P.q_pos
  have hR : 0 ≤ R := by simpa [R] using pairNorm_nonneg dx dy
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (le_of_lt (lift_nu_pos P)) (by nlinarith [sq_nonneg P.γ])
  have hBc : 0 ≤ Bc := by
    dsimp [Bc]
    exact div_nonneg (mul_nonneg (le_of_lt P.h_pos) hs₀) (le_of_lt hsqrt)
  have hX0 : ∀ ξ, 0 ≤ X ξ := fun ξ => norm_nonneg _
  have hpoint : ∀ ξ, N ξ ≤ A * R + P.q * X ξ := by
    intro ξ
    simpa [N, A, R, X, dx, dy] using
      genericLiftedOracle_pair_difference_bound B P x y x' y' ξ
  have hpointSq : ∀ ξ, N ξ ^ 2 ≤ (A * R + P.q * X ξ) ^ 2 := by
    intro ξ
    have hn : 0 ≤ N ξ := pairNorm_nonneg _ _
    have hrhs : 0 ≤ A * R + P.q * X ξ :=
      add_nonneg (mul_nonneg hA hR) (mul_nonneg (le_of_lt P.q_pos) (hX0 ξ))
    nlinarith [hpoint ξ]
  have hEN : E.expectReal (fun ξ => N ξ ^ 2) ≤
      E.expectReal (fun ξ => (A * R + P.q * X ξ) ^ 2) :=
    H.expect_mono _ _ hpointSq
  have harg : ‖P.β • y - P.β • y'‖ = P.β * ‖dy‖ := by
    have hv : P.β • y - P.β • y' = P.β • dy := by dsimp [dy]; module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  have hbase := havg (P.β • y) (P.β • y')
  rw [harg] at hbase
  let S : ℝ := (s₀ / Real.sqrt p) * (P.β * ‖dy‖)
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hSsq : s₀ ^ 2 / p * (P.β * ‖dy‖) ^ 2 = S ^ 2 := by
    dsimp [S]
    rw [← Real.sq_sqrt hp0]
    field_simp [hsqrt_ne]
    ring
  have hEX2 : E.expectReal (fun ξ => X ξ ^ 2) ≤ S ^ 2 := by
    dsimp [X]
    rw [← hSsq]
    exact hbase
  have hEXnonneg : 0 ≤ E.expectReal X := H.expect_nonneg X hX0
  have hEXsq := H.sq_expect_le_expect_sq X
  have hEX : E.expectReal X ≤ S := by nlinarith
  have hdyR : ‖dy‖ ≤ R := by simpa [R] using norm_le_pairNorm_right dx dy
  have hqS_eq : P.q * S = Bc * ‖dy‖ := by
    dsimp [S, Bc]
    rw [← P.q_mul_beta]
    field_simp [hsqrt_ne]
    ring
  have hqEX : P.q * E.expectReal X ≤ Bc * R := by
    have h1 := mul_le_mul_of_nonneg_left hEX (le_of_lt P.q_pos)
    rw [hqS_eq] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hdyR hBc)
  have hq2EX2 : P.q ^ 2 * E.expectReal (fun ξ => X ξ ^ 2) ≤ (Bc * R) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hEX2 (sq_nonneg P.q)
    have hqS_le : P.q * S ≤ Bc * R := by
      rw [hqS_eq]
      exact mul_le_mul_of_nonneg_left hdyR hBc
    have hqS_nonneg : 0 ≤ P.q * S := mul_nonneg (le_of_lt P.q_pos) hS
    have hBcR_nonneg : 0 ≤ Bc * R := mul_nonneg hBc hR
    calc
      P.q ^ 2 * E.expectReal (fun ξ => X ξ ^ 2) ≤ P.q ^ 2 * S ^ 2 := h1
      _ = (P.q * S) ^ 2 := by ring
      _ ≤ (Bc * R) ^ 2 := by nlinarith
  have hexpand : E.expectReal (fun ξ => (A * R + P.q * X ξ) ^ 2) =
      (A * R) ^ 2 + 2 * (A * R) * (P.q * E.expectReal X) +
        P.q ^ 2 * E.expectReal (fun ξ => X ξ ^ 2) := by
    have hfun : (fun ξ => (A * R + P.q * X ξ) ^ 2) =
        (fun ξ => (A * R) ^ 2 + (2 * (A * R) * P.q) * X ξ +
          P.q ^ 2 * X ξ ^ 2) := by funext ξ; ring
    rw [hfun, H.expect_add, H.expect_add, H.expect_const,
      H.expect_smul, H.expect_smul]
    ring
  have hroot : E.expectReal (fun ξ => (A * R + P.q * X ξ) ^ 2) ≤
      ((A + Bc) * R) ^ 2 := by
    rw [hexpand]
    have hcross : 2 * (A * R) * (P.q * E.expectReal X) ≤
        2 * (A * R) * (Bc * R) :=
      mul_le_mul_of_nonneg_left hqEX (mul_nonneg (by norm_num) (mul_nonneg hA hR))
    calc
      (A * R) ^ 2 + 2 * (A * R) * (P.q * E.expectReal X) +
          P.q ^ 2 * E.expectReal (fun ξ => X ξ ^ 2)
        ≤ (A * R) ^ 2 + 2 * (A * R) * (Bc * R) + (Bc * R) ^ 2 :=
          add_le_add (add_le_add_left hcross _) hq2EX2
      _ = ((A + Bc) * R) ^ 2 := by ring
  have hsum : E.expectReal (fun ξ =>
      ‖genericLiftedGx P x y ξ - genericLiftedGx P x' y' ξ‖ ^ 2 +
      ‖genericLiftedGy B P x y ξ - genericLiftedGy B P x' y' ξ‖ ^ 2) =
      E.expectReal (fun ξ => N ξ ^ 2) := by
    congr 1
    funext ξ
    exact (pairNorm_sq_eq _ _).symm
  rw [hsum]
  calc
    E.expectReal (fun ξ => N ξ ^ 2)
        ≤ E.expectReal (fun ξ => (A * R + P.q * X ξ) ^ 2) := hEN
    _ ≤ ((A + Bc) * R) ^ 2 := hroot
    _ = (P.ν * (1 + P.γ ^ 2) + P.h * s₀ / Real.sqrt p) ^ 2 *
          (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
      dsimp [A, Bc, R, dx, dy]
      rw [mul_pow, pairNorm_sq_eq]

/-- Paper Lemma 2.3(iv), in the Bernoulli specialization used in Sections 3--4. -/
theorem lifted_averaged_smooth_transfer {T : ℕ}
    (B : BaseOracle T) (P : LiftParameters) (p s₀ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hs₀ : 0 ≤ s₀)
    (havg : BaseAveragedSmoothHypothesis B p s₀) :
    ∀ x y x' y',
      bernoulliExpectReal p (fun Z =>
        ‖liftedGx P x y Z - liftedGx P x' y' Z‖ ^ 2 +
        ‖liftedGy B P x y Z - liftedGy B P x' y' Z‖ ^ 2) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * s₀ / Real.sqrt p) ^ 2 *
        (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  intro x y x' y'
  let dx : Vec T := x - x'
  let dy : Vec T := y - y'
  let R : ℝ := pairNorm dx dy
  let A : ℝ := P.ν * (1 + P.γ ^ 2)
  let Bc : ℝ := P.h * s₀ / Real.sqrt p
  let X : Bool → ℝ := fun Z => ‖B.g (P.β • y) Z - B.g (P.β • y') Z‖
  let N : Bool → ℝ := fun Z =>
    pairNorm (liftedGx P x y Z - liftedGx P x' y' Z)
      (liftedGy B P x y Z - liftedGy B P x' y' Z)
  have hp0 : 0 ≤ p := le_of_lt hp
  have hpm : 0 ≤ 1 - p := by linarith
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsqrt_ne : Real.sqrt p ≠ 0 := ne_of_gt hsqrt
  have hβ : 0 < P.β := div_pos P.h_pos P.q_pos
  have hR : 0 ≤ R := by simpa [R] using pairNorm_nonneg dx dy
  have hA : 0 ≤ A := by
    dsimp [A]
    have hnu : 0 ≤ P.ν := le_of_lt (lift_nu_pos P)
    have hg : 0 ≤ 1 + P.γ ^ 2 := by nlinarith [sq_nonneg P.γ]
    exact mul_nonneg hnu hg
  have hBc : 0 ≤ Bc := by
    dsimp [Bc]
    exact div_nonneg (mul_nonneg (le_of_lt P.h_pos) hs₀) (le_of_lt hsqrt)
  have hX0 : ∀ Z, 0 ≤ X Z := by
    intro Z
    exact norm_nonneg _
  have hpoint : ∀ Z, N Z ≤ A * R + P.q * X Z := by
    intro Z
    simpa [N, A, R, X, dx, dy] using
      liftedOracle_pair_difference_bound B P x y x' y' Z
  have hpointSq : ∀ Z, N Z ^ 2 ≤ (A * R + P.q * X Z) ^ 2 := by
    intro Z
    have hn : 0 ≤ N Z := by
      dsimp [N]
      exact pairNorm_nonneg _ _
    have hrhs : 0 ≤ A * R + P.q * X Z := by
      exact add_nonneg (mul_nonneg hA hR)
        (mul_nonneg (le_of_lt P.q_pos) (hX0 Z))
    nlinarith [hpoint Z]
  have hEN : bernoulliExpectReal p (fun Z => N Z ^ 2) ≤
      bernoulliExpectReal p (fun Z => (A * R + P.q * X Z) ^ 2) :=
    bernoulliExpectReal_mono p hp0 hp1 _ _ hpointSq
  have harg : ‖P.β • y - P.β • y'‖ = P.β * ‖dy‖ := by
    have hv : P.β • y - P.β • y' = P.β • dy := by
      dsimp [dy]
      module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  have hbase := havg (P.β • y) (P.β • y')
  rw [harg] at hbase
  let S : ℝ := (s₀ / Real.sqrt p) * (P.β * ‖dy‖)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg (div_nonneg hs₀ (le_of_lt hsqrt))
      (mul_nonneg (le_of_lt hβ) (norm_nonneg _))
  have hSsq :
      s₀ ^ 2 / p * (P.β * ‖dy‖) ^ 2 = S ^ 2 := by
    dsimp [S]
    have hsqp : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp0
    rw [← hsqp]
    field_simp [hsqrt_ne]
    ring
  have hEX2 : bernoulliExpectReal p (fun Z => X Z ^ 2) ≤ S ^ 2 := by
    dsimp [X]
    rw [← hSsq]
    exact hbase
  have hEX : bernoulliExpectReal p X ≤ S :=
    bernoulliExpectReal_le_of_second_moment_le_sq p S hp0 hp1 hS X hX0 hEX2
  have hdyR : ‖dy‖ ≤ R := by
    simpa [R] using norm_le_pairNorm_right dx dy
  have hqS_eq : P.q * S = Bc * ‖dy‖ := by
    dsimp [S, Bc]
    rw [← P.q_mul_beta]
    field_simp [hsqrt_ne]
    ring
  have hqEX : P.q * bernoulliExpectReal p X ≤ Bc * R := by
    have h1 := mul_le_mul_of_nonneg_left hEX (le_of_lt P.q_pos)
    rw [hqS_eq] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hdyR hBc)
  have hq2EX2 : P.q ^ 2 * bernoulliExpectReal p (fun Z => X Z ^ 2) ≤
      (Bc * R) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hEX2 (sq_nonneg P.q)
    have hqS_nonneg : 0 ≤ P.q * S := mul_nonneg (le_of_lt P.q_pos) hS
    have hBR_nonneg : 0 ≤ Bc * R := mul_nonneg hBc hR
    have hqS_le : P.q * S ≤ Bc * R := by
      rw [hqS_eq]
      exact mul_le_mul_of_nonneg_left hdyR hBc
    have hsq : (P.q * S) ^ 2 ≤ (Bc * R) ^ 2 := by nlinarith
    calc
      P.q ^ 2 * bernoulliExpectReal p (fun Z => X Z ^ 2)
          ≤ P.q ^ 2 * S ^ 2 := h1
      _ = (P.q * S) ^ 2 := by ring
      _ ≤ (Bc * R) ^ 2 := hsq
  have hcross :
      2 * (A * R) * (P.q * bernoulliExpectReal p X) ≤
        2 * (A * R) * (Bc * R) := by
    exact mul_le_mul_of_nonneg_left hqEX
      (mul_nonneg (by norm_num) (mul_nonneg hA hR))
  have hexpand :
      bernoulliExpectReal p (fun Z => (A * R + P.q * X Z) ^ 2) =
        (A * R) ^ 2 +
          2 * (A * R) * (P.q * bernoulliExpectReal p X) +
          P.q ^ 2 * bernoulliExpectReal p (fun Z => X Z ^ 2) := by
    unfold bernoulliExpectReal
    ring
  have hroot :
      bernoulliExpectReal p (fun Z => (A * R + P.q * X Z) ^ 2) ≤
        ((A + Bc) * R) ^ 2 := by
    rw [hexpand]
    calc
      (A * R) ^ 2 + 2 * (A * R) * (P.q * bernoulliExpectReal p X) +
          P.q ^ 2 * bernoulliExpectReal p (fun Z => X Z ^ 2)
          ≤ (A * R) ^ 2 + 2 * (A * R) * (Bc * R) + (Bc * R) ^ 2 := by
            exact add_le_add (add_le_add_left hcross _) hq2EX2
      _ = ((A + Bc) * R) ^ 2 := by ring
  have hsum_to_pair :
      bernoulliExpectReal p (fun Z =>
        ‖liftedGx P x y Z - liftedGx P x' y' Z‖ ^ 2 +
        ‖liftedGy B P x y Z - liftedGy B P x' y' Z‖ ^ 2) =
      bernoulliExpectReal p (fun Z => N Z ^ 2) := by
    congr 1
    funext Z
    dsimp [N]
    exact (pairNorm_sq_eq _ _).symm
  rw [hsum_to_pair]
  calc
    bernoulliExpectReal p (fun Z => N Z ^ 2)
        ≤ bernoulliExpectReal p (fun Z => (A * R + P.q * X Z) ^ 2) := hEN
    _ ≤ ((A + Bc) * R) ^ 2 := hroot
    _ = (P.ν * (1 + P.γ ^ 2) + P.h * s₀ / Real.sqrt p) ^ 2 *
          (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
      dsimp [A, Bc, R, dx, dy]
      rw [mul_pow, pairNorm_sq_eq]

/-- Nonnegativity of Bernoulli event probabilities under `0 ≤ p ≤ 1`. -/
theorem bernoulliProb_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Bool → Prop) : 0 ≤ bernoulliProb p A := by
  classical
  unfold bernoulliProb
  have hf : 0 ≤ 1 - p := by linarith
  have ht : 0 ≤ (if A true then (1 : ℝ) else 0) := by split <;> norm_num
  have hff : 0 ≤ (if A false then (1 : ℝ) else 0) := by split <;> norm_num
  exact add_nonneg (mul_nonneg hp0 ht) (mul_nonneg hf hff)

/-- Monotonicity of the explicit Bernoulli event probability. -/
theorem bernoulliProb_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Bool → Prop) (hAB : ∀ z, A z → B z) :
    bernoulliProb p A ≤ bernoulliProb p B := by
  classical
  unfold bernoulliProb
  have hf : 0 ≤ 1 - p := by linarith
  have ht : (if A true then (1 : ℝ) else 0) ≤ (if B true then (1 : ℝ) else 0) := by
    by_cases hA : A true
    · have hB := hAB true hA
      simp [hA, hB]
    · by_cases hB : B true <;> simp [hA, hB]
  have hff : (if A false then (1 : ℝ) else 0) ≤ (if B false then (1 : ℝ) else 0) := by
    by_cases hA : A false
    · have hB := hAB false hA
      simp [hA, hB]
    · by_cases hB : B false <;> simp [hA, hB]
  exact add_le_add
    (mul_le_mul_of_nonneg_left ht hp0)
    (mul_le_mul_of_nonneg_left hff hf)

/-- Union bound for the explicit two-point Bernoulli law. -/
theorem bernoulliProb_union_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Bool → Prop) :
    bernoulliProb p (fun z => A z ∨ B z) ≤ bernoulliProb p A + bernoulliProb p B := by
  classical
  unfold bernoulliProb
  by_cases hAt : A true <;>
    by_cases hBt : B true <;>
    by_cases hAf : A false <;>
    by_cases hBf : B false <;>
    simp [hAt, hBt, hAf, hBf] <;> linarith

/-- Threshold progress of the scaled dual query is bounded by the current pair support. -/
theorem prog_quarter_scaled_y_le_pairProg {T : ℕ}
    (P : LiftParameters) (x y : Vec T) :
    prog (1 / 4) (P.β • y) ≤ pairProg x y := by
  calc
    prog (1 / 4) (P.β • y) ≤ prog 0 (P.β • y) :=
      prog_threshold_le_zero (1 / 4) (by norm_num) (P.β • y)
    _ ≤ prog 0 y := prog_zero_smul_le P.β y
    _ ≤ pairProg x y := by simp [pairProg]

/-- Every lifted response is supported below the maximum of the current query-pair support and
that of the stochastic base response. -/
theorem lifted_response_pairProg_le_max_base {T : ℕ}
    (B : BaseOracle T) (P : LiftParameters) (x y : Vec T) (Z : Bool) :
    pairProg (liftedGx P x y Z) (liftedGy B P x y Z) ≤
      max (pairProg x y) (prog 0 (B.g (P.β • y) Z)) := by
  let qprog := pairProg x y
  let bprog := prog 0 (B.g (P.β • y) Z)
  have hx0 : prog 0 (liftedGx P x y Z) ≤ qprog := by
    simpa [qprog] using liftedGx_prog_le_pairProg P x y Z
  have hx : prog 0 (liftedGx P x y Z) ≤ max qprog bprog :=
    le_trans hx0 (Nat.le_max_left _ _)
  have hb : prog 0 (P.q • B.g (P.β • y) Z) ≤ bprog := by
    simpa [bprog] using prog_zero_smul_le P.q (B.g (P.β • y) Z)
  have hd : prog 0 (P.ν • (y - P.γ • x)) ≤ qprog := by
    simpa [qprog] using lift_dual_coupling_prog_le_pairProg P x y
  have hy0 := prog_zero_sub_le_max
    (P.q • B.g (P.β • y) Z) (P.ν • (y - P.γ • x))
  have hy : prog 0 (liftedGy B P x y Z) ≤ max qprog bprog := by
    unfold liftedGy
    have hmax :
        max (prog 0 (P.q • B.g (P.β • y) Z))
          (prog 0 (P.ν • (y - P.γ • x))) ≤ max bprog qprog :=
      max_le_max hb hd
    have h := le_trans hy0 hmax
    simpa [max_comm] using h
  unfold pairProg
  exact max_le hx hy

/-- A farther-than-one lifted reveal forces a farther-than-one reveal in the base zero-chain. -/
theorem lifted_far_reveal_implies_base_far {T : ℕ}
    (B : BaseOracle T) (P : LiftParameters) (Z : Bool) :
    (∃ x y, pairProg (liftedGx P x y Z) (liftedGy B P x y Z) > pairProg x y + 1) →
    ∃ u, prog 0 (B.g u Z) > prog (1 / 4) u + 1 := by
  rintro ⟨x, y, hout⟩
  let u : Vec T := P.β • y
  have hbound := lifted_response_pairProg_le_max_base B P x y Z
  have hfront := prog_quarter_scaled_y_le_pairProg P x y
  have hbgt : pairProg x y + 1 < prog 0 (B.g (P.β • y) Z) := by
    by_contra hnot
    have hb_le : prog 0 (B.g (P.β • y) Z) ≤ pairProg x y + 1 := Nat.le_of_not_gt hnot
    have hmax_le :
        max (pairProg x y) (prog 0 (B.g (P.β • y) Z)) ≤ pairProg x y + 1 :=
      max_le (Nat.le_succ _) hb_le
    omega
  refine ⟨u, ?_⟩
  dsimp [u]
  omega

/-- An exact one-pair lifted reveal is caused either by the base frontier event itself or by the
base far-reveal null event. -/
theorem lifted_exact_reveal_implies_base_exact_or_far {T : ℕ}
    (B : BaseOracle T) (P : LiftParameters) (Z : Bool) :
    (∃ x y, pairProg (liftedGx P x y Z) (liftedGy B P x y Z) = pairProg x y + 1) →
      (∃ u, prog 0 (B.g u Z) = prog (1 / 4) u + 1) ∨
      (∃ u, prog 0 (B.g u Z) > prog (1 / 4) u + 1) := by
  rintro ⟨x, y, hout⟩
  let u : Vec T := P.β • y
  have hbound := lifted_response_pairProg_le_max_base B P x y Z
  have hfront := prog_quarter_scaled_y_le_pairProg P x y
  have hbase : pairProg x y + 1 ≤ prog 0 (B.g u Z) := by
    dsimp [u]
    omega
  by_cases heq : prog 0 (B.g u Z) = prog (1 / 4) u + 1
  · exact Or.inl ⟨u, heq⟩
  · right
    refine ⟨u, ?_⟩
    have hfrontu : prog (1 / 4) u ≤ pairProg x y := by
      simpa [u] using hfront
    have hge : prog (1 / 4) u + 1 ≤ prog 0 (B.g u Z) :=
      le_trans (Nat.succ_le_succ hfrontu) hbase
    exact lt_of_le_of_ne hge (Ne.symm heq)

/-- Paper Lemma 2.3(vi), in the Bernoulli specialization. -/
theorem lifted_zero_chain_transfer {T : ℕ}
    (B : BaseOracle T) (P : LiftParameters) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hchain : ProbabilityPZeroChain (bernoulliLaw p) B.g p) :
    LiftCanRevealAtMostOnePair B P p := by
  rcases hchain with ⟨hexact, hfar⟩
  let LE : Bool → Prop := fun Z => ∃ x y,
    pairProg (liftedGx P x y Z) (liftedGy B P x y Z) = pairProg x y + 1
  let LF : Bool → Prop := fun Z => ∃ x y,
    pairProg (liftedGx P x y Z) (liftedGy B P x y Z) > pairProg x y + 1
  let BE : Bool → Prop := fun Z => ∃ u,
    prog 0 (B.g u Z) = prog (1 / 4) u + 1
  let BF : Bool → Prop := fun Z => ∃ u,
    prog 0 (B.g u Z) > prog (1 / 4) u + 1
  have hLE : ∀ Z, LE Z → BE Z ∨ BF Z := by
    intro Z hZ
    exact lifted_exact_reveal_implies_base_exact_or_far B P Z hZ
  have hLF : ∀ Z, LF Z → BF Z := by
    intro Z hZ
    exact lifted_far_reveal_implies_base_far B P Z hZ
  have hexact' : bernoulliProb p BE ≤ p := by
    simpa [ProbabilityPZeroChain, bernoulliLaw, LE, LF, BE, BF] using hexact
  have hfar' : bernoulliProb p BF = 0 := by
    simpa [ProbabilityPZeroChain, bernoulliLaw, LE, LF, BE, BF] using hfar
  constructor
  · calc
      bernoulliProb p LE ≤ bernoulliProb p (fun Z => BE Z ∨ BF Z) :=
        bernoulliProb_mono p hp0 hp1 LE (fun Z => BE Z ∨ BF Z) hLE
      _ ≤ bernoulliProb p BE + bernoulliProb p BF :=
        bernoulliProb_union_le p hp0 hp1 BE BF
      _ = bernoulliProb p BE := by rw [hfar']; ring
      _ ≤ p := hexact'
  · apply le_antisymm
    · calc
        bernoulliProb p LF ≤ bernoulliProb p BF :=
          bernoulliProb_mono p hp0 hp1 LF BF hLF
        _ = 0 := hfar'
    · exact bernoulliProb_nonneg p hp0 hp1 LF

/-- Generic-seed support bound underlying Lemma 2.3(vi). -/
theorem generic_lifted_response_pairProg_le_max_base {T : ℕ} {Seed : Type}
    (B : GenericBaseOracle T Seed) (P : LiftParameters) (x y : Vec T) (ξ : Seed) :
    pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) ≤
      max (pairProg x y) (prog 0 (B.g (P.β • y) ξ)) := by
  have hx0 : prog 0 (genericLiftedGx P x y ξ) ≤ pairProg x y := by
    simpa [genericLiftedGx, liftedGx] using liftedGx_prog_le_pairProg P x y false
  have hx : prog 0 (genericLiftedGx P x y ξ) ≤
      max (pairProg x y) (prog 0 (B.g (P.β • y) ξ)) :=
    le_trans hx0 (Nat.le_max_left _ _)
  have hb : prog 0 (P.q • B.g (P.β • y) ξ) ≤ prog 0 (B.g (P.β • y) ξ) :=
    prog_zero_smul_le P.q _
  have hd : prog 0 (P.ν • (y - P.γ • x)) ≤ pairProg x y :=
    lift_dual_coupling_prog_le_pairProg P x y
  have hy0 := prog_zero_sub_le_max
    (P.q • B.g (P.β • y) ξ) (P.ν • (y - P.γ • x))
  have hy : prog 0 (genericLiftedGy B P x y ξ) ≤
      max (pairProg x y) (prog 0 (B.g (P.β • y) ξ)) := by
    unfold genericLiftedGy
    exact le_trans hy0 (by simpa [max_comm] using max_le_max hb hd)
  exact max_le hx hy

theorem generic_lifted_far_reveal_implies_base_far {T : ℕ} {Seed : Type}
    (B : GenericBaseOracle T Seed) (P : LiftParameters) (ξ : Seed) :
    (∃ x y, pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) >
      pairProg x y + 1) →
    ∃ u, prog 0 (B.g u ξ) > prog (1 / 4) u + 1 := by
  rintro ⟨x, y, hout⟩
  let u : Vec T := P.β • y
  have hbound := generic_lifted_response_pairProg_le_max_base B P x y ξ
  have hfront := prog_quarter_scaled_y_le_pairProg P x y
  have hbgt : pairProg x y + 1 < prog 0 (B.g (P.β • y) ξ) := by
    by_contra hnot
    have hb_le : prog 0 (B.g (P.β • y) ξ) ≤ pairProg x y + 1 := Nat.le_of_not_gt hnot
    have hmax_le : max (pairProg x y) (prog 0 (B.g (P.β • y) ξ)) ≤
        pairProg x y + 1 := max_le (Nat.le_succ _) hb_le
    omega
  refine ⟨u, ?_⟩
  dsimp [u]
  omega

theorem generic_lifted_exact_reveal_implies_base_exact_or_far {T : ℕ} {Seed : Type}
    (B : GenericBaseOracle T Seed) (P : LiftParameters) (ξ : Seed) :
    (∃ x y, pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) =
      pairProg x y + 1) →
      (∃ u, prog 0 (B.g u ξ) = prog (1 / 4) u + 1) ∨
      (∃ u, prog 0 (B.g u ξ) > prog (1 / 4) u + 1) := by
  rintro ⟨x, y, hout⟩
  let u : Vec T := P.β • y
  have hbound := generic_lifted_response_pairProg_le_max_base B P x y ξ
  have hfront := prog_quarter_scaled_y_le_pairProg P x y
  have hbase : pairProg x y + 1 ≤ prog 0 (B.g u ξ) := by dsimp [u]; omega
  by_cases heq : prog 0 (B.g u ξ) = prog (1 / 4) u + 1
  · exact Or.inl ⟨u, heq⟩
  · right
    refine ⟨u, ?_⟩
    have hfrontu : prog (1 / 4) u ≤ pairProg x y := by simpa [u] using hfront
    have hge : prog (1 / 4) u + 1 ≤ prog 0 (B.g u ξ) :=
      le_trans (Nat.succ_le_succ hfrontu) hbase
    exact lt_of_le_of_ne hge (Ne.symm heq)

/-- Generic probability-`p` zero-chain transfer. -/
theorem generic_lifted_zero_chain_transfer {T : ℕ} {Seed : Type}
    (E : Law Seed) (H : LawAxioms E) (B : GenericBaseOracle T Seed)
    (P : LiftParameters) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hchain : ProbabilityPZeroChain E B.g p) :
    GenericLiftCanRevealAtMostOnePair E B P p := by
  rcases hchain with ⟨hexact, hfar⟩
  let LE : Set Seed := {ξ | ∃ x y,
    pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) =
      pairProg x y + 1}
  let LF : Set Seed := {ξ | ∃ x y,
    pairProg (genericLiftedGx P x y ξ) (genericLiftedGy B P x y ξ) >
      pairProg x y + 1}
  let BE : Set Seed := {ξ | ∃ u, prog 0 (B.g u ξ) = prog (1 / 4) u + 1}
  let BF : Set Seed := {ξ | ∃ u, prog 0 (B.g u ξ) > prog (1 / 4) u + 1}
  have hLE : LE ⊆ BE ∪ BF := by
    intro ξ hξ
    exact generic_lifted_exact_reveal_implies_base_exact_or_far B P ξ hξ
  have hLF : LF ⊆ BF := by
    intro ξ hξ
    exact generic_lifted_far_reveal_implies_base_far B P ξ hξ
  have hexact' : E.probability BE ≤ p := by
    simpa [ProbabilityPZeroChain, BE, BF] using hexact
  have hfar' : E.probability BF = 0 := by
    simpa [ProbabilityPZeroChain, BE, BF] using hfar
  constructor
  · change E.probability LE ≤ p
    calc
      E.probability LE ≤ E.probability (BE ∪ BF) := H.probability_mono hLE
      _ ≤ E.probability BE + E.probability BF := H.probability_union_le BE BF
      _ = E.probability BE := by rw [hfar']; ring
      _ ≤ p := hexact'
  · change E.probability LF = 0
    apply le_antisymm
    · exact le_trans (H.probability_mono hLF) (le_of_eq hfar')
    · exact H.probability_nonneg LF


/-! ## v28 proof phase XIX: canonical assembly of paper Lemma 2.3

Versions v20--v27.2 proved the deterministic and Bernoulli stochastic fields of the lift
certificate separately.  This phase closes the packaging gap: the Bernoulli
`LiftPropertiesCertificate` now uses the same non-attainment formulation of the strong-concavity
modulus as the authoritative generic-seed interface, and the theorem below assembles every field
from the already-proved concrete lemmas.

No new analytic assumption is introduced here.  In particular, `mu_strong_concavity` is supplied
by the explicit `μ`-strong-concavity proof and `strong_modulus_upper` by the reverse-gradient
argument, so no existence of a largest strong-concavity modulus is assumed.
-/

/-- Canonical Bernoulli Lemma-2.3 certificate for the explicit quadratic lift.  Every field is
now discharged by a theorem proved in the preceding phases: actual partial gradients, existence
and uniqueness of the dual maximizer, the direct envelope gradient, strong concavity and its
upper modulus bracket, joint smoothness, the primal gap, variance and averaged-smooth transfer,
stationarity transfer, and the probability-`p` zero-chain transfer. -/
noncomputable def canonicalLiftPropertiesCertificate {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters) :
    LiftPropertiesCertificate T C B P where
  Phi := canonicalLiftPhi C P
  gradPhi := canonicalLiftGradPhi C P
  yStar := canonicalLiftYStar C P
  gradX_formula := by
    intro x y
    exact liftedF_gradX_formula C P x y
  gradY_formula := by
    intro x y
    exact liftedF_gradY_formula C P x y
  maximizer := by
    intro x y
    exact canonicalLiftYStar_maximizer C P x y
  maximizer_unique := by
    intro x y heq
    exact canonicalLiftYStar_unique C P x y heq
  Phi_def := by
    intro x
    exact canonicalLiftPhi_def C P x
  gradPhi_spec := by
    intro x
    exact canonicalLiftPhi_grad C P x
  mu_strong_concavity := liftedF_mu_strong_concavity C P
  strong_modulus_upper := by
    intro m hm
    exact lift_strong_modulus_upper C P m hm
  joint_smoothness := liftedF_joint_smoothness C P
  primal_gap := canonicalLiftPhi_primal_gap C P
  variance_transfer := by
    intro p v₀ hvar x y
    exact lifted_variance_transfer C B P p v₀ hvar x y
  averaged_smooth_transfer := by
    intro p s₀ hp hp1 hs₀ havg x y x' y'
    exact lifted_averaged_smooth_transfer B P p s₀ hp hp1 hs₀ havg x y x' y'
  stationarity_transfer := by
    intro x
    exact canonicalLift_stationarity_transfer C P x
  zero_chain_transfer := by
    intro p hp0 hp1 hchain
    exact lifted_zero_chain_transfer B P p hp0 hp1 hchain

/-- Existence form of the preceding constructor, useful when a downstream theorem only asks for
some Lemma-2.3 certificate. -/
theorem canonicalLiftPropertiesCertificate_nonempty {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters) :
    Nonempty (LiftPropertiesCertificate T C B P) :=
  ⟨canonicalLiftPropertiesCertificate C B P⟩

/-- Canonical arbitrary-seed form of paper Lemma 2.3.  The probability-law
coherence is explicit; no additional analytic axiom is used. -/
noncomputable def canonicalGenericLiftPropertiesCertificate {T : ℕ} {Seed : Type}
    (C : ExplicitZeroChainCertificate T) (E : Law Seed) (H : LawAxioms E)
    (B : GenericBaseOracle T Seed) (P : LiftParameters)
    (hbase : GenericBaseUnbiased C E B) :
    GenericLiftPropertiesCertificate T C E B P where
  base_unbiased := hbase
  Phi := canonicalLiftPhi C P
  gradPhi := canonicalLiftGradPhi C P
  yStar := canonicalLiftYStar C P
  gradX_formula := fun x y => liftedF_gradX_formula C P x y
  gradY_formula := fun x y => liftedF_gradY_formula C P x y
  maximizer := fun x y => canonicalLiftYStar_maximizer C P x y
  maximizer_unique := fun x y heq => canonicalLiftYStar_unique C P x y heq
  Phi_def := fun x => canonicalLiftPhi_def C P x
  gradPhi_spec := fun x => canonicalLiftPhi_grad C P x
  mu_strong_concavity := liftedF_mu_strong_concavity C P
  strong_modulus_upper := fun m hm => lift_strong_modulus_upper C P m hm
  joint_smoothness := liftedF_joint_smoothness C P
  primal_gap := canonicalLiftPhi_primal_gap C P
  variance_transfer := by
    intro p v₀ hvar x y
    exact generic_lifted_variance_transfer C E H B P p v₀ hvar x y
  averaged_smooth_transfer := by
    intro p s₀ hp hp1 hs₀ havg x y x' y'
    exact generic_lifted_averaged_smooth_transfer E H B P p s₀ hp hp1 hs₀ havg
      x y x' y'
  stationarity_transfer := fun x => canonicalLift_stationarity_transfer C P x
  zero_chain_transfer := by
    intro p hp0 hp1 hchain
    exact generic_lifted_zero_chain_transfer E H B P p hp0 hp1 hchain

theorem canonicalLemma23 : Lemma23Statement := by
  intro T Seed C E B P H hbase
  exact ⟨canonicalGenericLiftPropertiesCertificate C E H B P hbase⟩


/-! ## v29 proof phase XX: canonical BV/AS construction witnesses

Version v28 closed the Bernoulli form of paper Lemma 2.3 by constructing a concrete
`LiftPropertiesCertificate`.  The Section-3 and Section-4 witness structures still carried such a
certificate as an externally supplied field, however.  This phase removes that packaging gap at
the construction level: for every explicit zero-chain certificate and every legal BV/AS parameter
record we build the exact lift parameters, the exact base oracle, and the corresponding canonical
Lemma-2.3 certificate internally.

No theorem statement is weakened.  In particular, `BVConstructionWitness` and
`ASConstructionWitness` are left unchanged so all earlier theorems remain source-compatible; the
new definitions simply provide their distinguished canonical inhabitants.
-/

/-- The Section-3 parameter record determines the lift parameters in equations (7) and (17). -/
noncomputable def canonicalBVLiftParameters (P : BVParameters) : LiftParameters where
  μ := P.μ
  h := P.h
  q := P.q
  γ := P.γ
  μ_pos := P.μ_pos
  h_pos := bv_h_pos P
  q_pos := bv_q_pos P
  γ_pos := P.γ_pos

/-- Positivity of the averaged-smooth signal scale `q`. -/
theorem as_q_pos (P : ASParameters) : 0 < P.q := by
  rw [P.q_def]
  exact div_pos (mul_pos (by norm_num) P.ε_pos) P.γ_pos

/-- Positivity of the Section-4 choice
`h = min { μ/(4ℓ₀), Lbar*sqrt(p)/(4s₀) }`. -/
theorem as_h_pos (P : ASParameters) : 0 < P.h := by
  rw [ASParameters.h]
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  have hsqrt : 0 < Real.sqrt P.p := Real.sqrt_pos.2 P.p_pos
  have hleft : 0 < P.μ / (4 * ℓ₀) :=
    div_pos P.μ_pos (mul_pos (by norm_num) hℓ)
  have hright : 0 < P.Lbar * Real.sqrt P.p / (4 * P.s₀) :=
    div_pos (mul_pos P.Lbar_pos hsqrt) (mul_pos (by norm_num) P.s₀_pos)
  exact lt_min hleft hright

/-- The Section-4 parameter record determines the lift parameters in equations (7), (25), and
(26). -/
noncomputable def canonicalASLiftParameters (P : ASParameters) : LiftParameters where
  μ := P.μ
  h := P.h
  q := P.q
  γ := P.γ
  μ_pos := P.μ_pos
  h_pos := as_h_pos P
  q_pos := as_q_pos P
  γ_pos := P.γ_pos

/-- Equation (16) packaged as the `BaseOracle` used by the quadratic lift. -/
def canonicalBVBaseOracle {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : BVParameters) : BaseOracle T where
  g := bvBaseOracle C P.p

/-- Equation (21) packaged as the `BaseOracle` used by the quadratic lift. -/
noncomputable def canonicalASBaseOracle {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : ASParameters) : BaseOracle T where
  g := asBaseOracle C P.p

/-- Canonical Section-3 construction witness.  Its `lift_properties` field is the v28
end-to-end Lemma-2.3 certificate, so no analytic lift certificate is supplied by a caller. -/
noncomputable def canonicalBVConstructionWitness {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) :
    BVConstructionWitness C P where
  LP := canonicalBVLiftParameters P
  lift_mu := rfl
  lift_h := rfl
  lift_q := rfl
  lift_gamma := rfl
  B := canonicalBVBaseOracle C P
  base_oracle_def := by
    intro u Z
    rfl
  lift_properties :=
    canonicalLiftPropertiesCertificate C (canonicalBVBaseOracle C P)
      (canonicalBVLiftParameters P)

/-- Canonical Section-4 construction witness.  As above, the lift certificate is generated
internally from the explicit chain and the exact smooth-gated base oracle. -/
noncomputable def canonicalASConstructionWitness {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters) :
    ASConstructionWitness C P where
  LP := canonicalASLiftParameters P
  lift_mu := rfl
  lift_h := rfl
  lift_q := rfl
  lift_gamma := rfl
  B := canonicalASBaseOracle C P
  base_oracle_def := by
    intro u Z
    rfl
  lift_properties :=
    canonicalLiftPropertiesCertificate C (canonicalASBaseOracle C P)
      (canonicalASLiftParameters P)

/-- For the canonical BV witness, the concrete population objective can be named without carrying
an additional witness argument. -/
noncomputable def canonicalBVPopulation {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) : PopulationObjective T :=
  bvConstructedPopulation (canonicalBVConstructionWitness C P)

/-- The corresponding exact bounded-variance oracle. -/
def canonicalBVOracle {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) : StochasticOracle T Bool :=
  bvConstructedOracle (canonicalBVConstructionWitness C P)

/-- Canonical Section-4 population objective. -/
noncomputable def canonicalASPopulation {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters) : PopulationObjective T :=
  asConstructedPopulation (canonicalASConstructionWitness C P)

/-- The corresponding exact averaged-smooth oracle. -/
noncomputable def canonicalASOracle {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters) : StochasticOracle T Bool :=
  asConstructedOracle (canonicalASConstructionWitness C P)

/-- Canonical-witness form of the existing Lemma-3.2 assembly lemma.  Compared with
`lemma32Conclusion_of_core`, callers no longer provide a `BVConstructionWitness` and hence no
longer provide a Lemma-2.3 certificate.  The remaining hypotheses are exactly the still-open
Lemma-3.2 numerical gap/floor/chain estimates and the actual-condition-number bracket. -/
noncomputable def canonicalLemma32Conclusion_of_core {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (c₁ cκLo cκHi : ℝ) (hκ : 8 ≤ P.κ)
    (hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1)
    (hT : 8 ≤ T)
    (hchain : c₁ * (P.L * P.Δ / P.ε ^ 2) ≤ T)
    (Acond : ActualConditionNumberCertificate
      (bvConstructedPopulation (canonicalBVConstructionWitness C P)))
    (hcond : cκLo * P.κ ≤ Acond.Mlo / Acond.muHi ∧
      Acond.Mhi / Acond.muLo ≤ cκHi * P.κ) :
    Lemma32Conclusion C P (canonicalBVConstructionWitness C P)
      c₁ cκLo cκHi :=
  lemma32Conclusion_of_core C P (canonicalBVConstructionWitness C P)
    c₁ cκLo cκHi hκ hgap hfloor hT hchain Acond hcond

/-- Existence form of the canonical BV witness. -/
theorem canonicalBVConstructionWitness_nonempty {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) :
    Nonempty (BVConstructionWitness C P) :=
  ⟨canonicalBVConstructionWitness C P⟩

/-- Existence form of the canonical AS witness. -/
theorem canonicalASConstructionWitness_nonempty {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters) :
    Nonempty (ASConstructionWitness C P) :=
  ⟨canonicalASConstructionWitness C P⟩


/-! ## v30 proof phase XXI: BV condition-number and numerical closure

The v29 canonical constructor removed the remaining Lemma-2.3 packaging hypothesis.  This phase
closes the other reusable parts of paper Lemma 3.2: the actual condition-number bracket and all
numerical consequences of the floor interval.  After this phase, the only genuinely discrete
input needed to instantiate Lemma 3.2 is the existence of a natural `T` satisfying the displayed
floor interval for `P.chainScale` (together with the imported Lemma-2.1 chain certificate at that
`T`).
-/

/-- On the product Euclidean norm, adjoining a zero block does not change the norm. -/
theorem pairNorm_zero_right_eq_norm {T : ℕ} (u : Vec T) :
    pairNorm u 0 = ‖u‖ := by
  have hs := pairNorm_sq_eq u (0 : Vec T)
  have hp := pairNorm_nonneg u (0 : Vec T)
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  simp at hs
  nlinarith

/-- The symmetric zero-left version. -/
theorem pairNorm_zero_left_eq_norm {T : ℕ} (u : Vec T) :
    pairNorm 0 u = ‖u‖ := by
  have hs := pairNorm_sq_eq (0 : Vec T) u
  have hp := pairNorm_nonneg (0 : Vec T) u
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  simp at hs
  nlinarith

/-- Any joint-smoothness constant of a quadratic lift is at least `ν γ²`.

We vary only the primal variable, using the nonzero chain gradient at the origin as a witness.
The first block of the lifted gradient already changes by exactly `ν γ²` times that direction, so
no information about the chain Hessian is required. -/
theorem populationFromLift_jointSmooth_lower_primal {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (M : ℝ)
    (hM : JointSmooth (populationFromLift C B P L) M) :
    P.ν * P.γ ^ 2 ≤ M := by
  let u : Vec T := C.gradF 0
  have hprog0 : prog 1 (0 : Vec T) = 0 :=
    prog_pos_threshold_zero (T := T) (a := (1 : ℝ)) (by norm_num)
  have hprog : prog 1 (0 : Vec T) < T := by
    rw [hprog0]
    exact C.dim_pos
  have hunorm : 1 < ‖u‖ := by
    dsimp [u]
    exact C.terminal_gradient 0 hprog
  have hunormpos : 0 < ‖u‖ := lt_trans (by norm_num) hunorm
  have hs := hM (0 : Vec T) (0 : Vec T) u (0 : Vec T)
  have hfirst := norm_le_pairNorm_left
    ((populationFromLift C B P L).gradX 0 0 -
      (populationFromLift C B P L).gradX u 0)
    ((populationFromLift C B P L).gradY 0 0 -
      (populationFromLift C B P L).gradY u 0)
  have hbound :
      ‖(populationFromLift C B P L).gradX 0 0 -
          (populationFromLift C B P L).gradX u 0‖ ≤
        M * pairNorm ((0 : Vec T) - u) ((0 : Vec T) - 0) :=
    le_trans hfirst hs
  have hx :
      (populationFromLift C B P L).gradX 0 0 -
          (populationFromLift C B P L).gradX u 0 =
        (P.ν * P.γ ^ 2) • u := by
    change
      (P.ν * P.γ) • ((0 : Vec T) - P.γ • (0 : Vec T)) -
          (P.ν * P.γ) • ((0 : Vec T) - P.γ • u) =
        (P.ν * P.γ ^ 2) • u
    module
  have hden : pairNorm ((0 : Vec T) - u) ((0 : Vec T) - 0) = ‖u‖ := by
    simp [pairNorm_zero_right_eq_norm]
  rw [hx, hden, norm_smul, Real.norm_eq_abs] at hbound
  have hν : 0 < P.ν := lift_nu_pos P
  have hcoef : 0 < P.ν * P.γ ^ 2 := mul_pos hν (sq_pos_of_pos P.γ_pos)
  rw [abs_of_pos hcoef] at hbound
  exact (mul_le_mul_right hunormpos).mp hbound

/-- Strong concavity of the concrete population objective has exactly the same gradient-form
meaning as `LiftStrongConcavity`, hence the v28 upper-modulus theorem transfers to the population
interface. -/
theorem populationFromLift_strong_modulus_upper {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P) (m : ℝ)
    (hm : StronglyConcaveY (populationFromLift C B P L) m) :
    m ≤ P.ν + ℓ₀ * P.h := by
  have hlift : LiftStrongConcavity C P m := by
    intro x y y'
    have h := hm x y y'
    change liftedF C P x y' ≤ liftedF C P x y +
      @inner ℝ (Vec T) _
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
      m / 2 * ‖y' - y‖ ^ 2 at h
    exact h
  exact L.strong_modulus_upper m hlift

/-- For the bounded-variance parameter choice, the upper dual-curvature bracket is exactly
`3 μ / 2`. -/
theorem bv_dual_curvature_identity (P : BVParameters) :
    P.ν + ℓ₀ * P.h = 3 * P.μ / 2 := by
  rw [BVParameters.ν, BVParameters.h]
  norm_num [ℓ₀]
  ring

/-- The primal-only gradient variation already forces every valid joint-smoothness constant of
the canonical BV hard instance to be at least `L/4`. -/
theorem canonicalBV_jointSmooth_lower {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) (M : ℝ)
    (hM : JointSmooth (canonicalBVPopulation C P) M) :
    P.L / 4 ≤ M := by
  let W := canonicalBVConstructionWitness C P
  have hM' : JointSmooth (populationFromLift C W.B W.LP W.lift_properties) M := by
    simpa [canonicalBVPopulation, bvConstructedPopulation, W] using hM
  have hbase := populationFromLift_jointSmooth_lower_primal
    C W.B W.LP W.lift_properties M hM'
  have hbase' : P.ν * P.γ ^ 2 ≤ M := by
    rw [bvWitness_nu_eq W, W.lift_gamma] at hbase
    exact hbase
  have hνmu : P.μ ≤ P.ν := by
    rw [BVParameters.ν]
    nlinarith [P.μ_pos]
  have hγsq : 0 ≤ P.γ ^ 2 := sq_nonneg P.γ
  have hmul : P.μ * P.γ ^ 2 ≤ P.ν * P.γ ^ 2 :=
    mul_le_mul_of_nonneg_right hνmu hγsq
  have hμγ : P.μ * P.γ ^ 2 = P.L / 4 := by
    rw [P.γ_sq, P.κ_def]
    field_simp [ne_of_gt P.μ_pos]
    ring
  rw [hμγ] at hmul
  exact le_trans hmul hbase'

/-- A concrete actual-condition-number certificate for the canonical BV hard instance.
We use the paper brackets `L/4 ≤ M_act ≤ L/2` and `μ ≤ μ_act ≤ 3μ/2`. -/
noncomputable def canonicalBVActualConditionNumberCertificate {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) (hκ : 8 ≤ P.κ) :
    ActualConditionNumberCertificate (canonicalBVPopulation C P) := by
  let W := canonicalBVConstructionWitness C P
  refine
    { Mlo := P.L / 4
      Mhi := P.L / 2
      muLo := P.μ
      muHi := P.ν + ℓ₀ * P.h
      Mlo_pos := div_pos P.L_pos (by norm_num)
      Mhi_pos := div_pos P.L_pos (by norm_num)
      muLo_pos := P.μ_pos
      muHi_pos := by
        rw [bv_dual_curvature_identity P]
        nlinarith [P.μ_pos]
      smooth_upper := ?_
      smooth_lower := ?_
      strong_lower := ?_
      strong_upper := ?_ }
  · have hs := bv_lift_smooth_constant_le_half P hκ
    have hs' : W.LP.ν * (1 + W.LP.γ ^ 2) + ℓ₀ * W.LP.h ≤ P.L / 2 := by
      rw [bvWitness_nu_eq W, W.lift_gamma, W.lift_h]
      exact hs
    have hout := populationFromLift_jointSmooth_of_bound
      C W.B W.LP W.lift_properties (P.L / 2) hs'
    simpa [canonicalBVPopulation, bvConstructedPopulation, W] using hout
  · intro M _hM0 hM
    exact canonicalBV_jointSmooth_lower C P M hM
  · have hstrong := populationFromLift_stronglyConcaveY C W.B W.LP W.lift_properties
    have hstrong' : StronglyConcaveY (populationFromLift C W.B W.LP W.lift_properties) P.μ := by
      simpa [W.lift_mu] using hstrong
    simpa [canonicalBVPopulation, bvConstructedPopulation, W] using hstrong'
  · intro m hm
    have hm' : StronglyConcaveY (populationFromLift C W.B W.LP W.lift_properties) m := by
      simpa [canonicalBVPopulation, bvConstructedPopulation, W] using hm
    have hu := populationFromLift_strong_modulus_upper
      C W.B W.LP W.lift_properties m hm'
    rw [bvWitness_nu_eq W, W.lift_h] at hu
    exact hu

/-- Universal condition-number constants used below. -/
def bvKappaLowerConstant : ℝ := 1 / 8

def bvKappaUpperConstant : ℝ := 1

/-- Exact ratio identities for the four BV condition-number brackets. -/
theorem canonicalBV_condition_ratios (P : BVParameters) :
    (P.L / 4) / (P.ν + ℓ₀ * P.h) = P.κ / 6 ∧
      (P.L / 2) / P.μ = P.κ / 2 := by
  have hμ0 : P.μ ≠ 0 := ne_of_gt P.μ_pos
  rw [bv_dual_curvature_identity P]
  constructor
  · rw [P.κ_def]
    field_simp [hμ0] <;> (try ring) <;> simp
  · rw [P.κ_def]
    field_simp [hμ0] <;> (try ring) <;> simp

/-- The canonical actual-condition certificate is `Θ(κ)` with explicit universal constants. -/
theorem canonicalBVActualConditionNumber_scaling {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters) (hκ : 8 ≤ P.κ) :
    let A := canonicalBVActualConditionNumberCertificate C P hκ
    bvKappaLowerConstant * P.κ ≤ A.Mlo / A.muHi ∧
      A.Mhi / A.muLo ≤ bvKappaUpperConstant * P.κ := by
  have hr := canonicalBV_condition_ratios P
  have hκpos : 0 < P.κ := by
    rw [P.κ_def]
    exact div_pos P.L_pos P.μ_pos
  dsimp [canonicalBVActualConditionNumberCertificate, bvKappaLowerConstant,
    bvKappaUpperConstant]
  rw [hr.1, hr.2]
  constructor <;> nlinarith

/-- Universal small-accuracy constant for the explicit BV Lemma-3.2 closure.  It is chosen so
that the same hypothesis simultaneously makes the origin term at most `Δ/2` and the real chain
scale at least `16`. -/
def bvLemma32C0 : ℝ := 1 / (4096 * Δ₀ * ℓ₀)

/-- Universal chain-length constant obtained from `T ≥ chainScale/2`. -/
def bvLemma32C1 : ℝ := 1 / (512 * Δ₀ * ℓ₀)

theorem bvLemma32C0_pos : 0 < bvLemma32C0 := by
  norm_num [bvLemma32C0, Δ₀, ℓ₀]

theorem bvLemma32C1_pos : 0 < bvLemma32C1 := by
  norm_num [bvLemma32C1, Δ₀, ℓ₀]

/-- The small-accuracy hypothesis forces a strictly positive gap budget. -/
theorem bv_delta_pos_of_small (P : BVParameters)
    (hsmall : P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ) :
    0 < P.Δ := by
  have heps : 0 < P.ε ^ 2 := sq_pos_of_pos P.ε_pos
  have hrhs : 0 < (bvLemma32C0 * P.L) * P.Δ := by
    have := lt_of_lt_of_le heps hsmall
    simpa [mul_assoc] using this
  have hcoef : 0 < bvLemma32C0 * P.L := mul_pos bvLemma32C0_pos P.L_pos
  by_contra hnot
  have hΔ : P.Δ ≤ 0 := le_of_not_gt hnot
  have hnonpos : (bvLemma32C0 * P.L) * P.Δ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hcoef) hΔ
  linarith

/-- Under the Lemma-3.2 small-accuracy condition, the real precursor of the chain length is at
least `16`. -/
theorem bv_chainScale_ge_sixteen (P : BVParameters)
    (hsmall : P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ) :
    16 ≤ P.chainScale := by
  have hε2 : 0 < P.ε ^ 2 := sq_pos_of_pos P.ε_pos
  have hD : 0 < (4096 * Δ₀ * ℓ₀ : ℝ) := by norm_num [Δ₀, ℓ₀]
  have hsmallDiv : P.ε ^ 2 ≤ (P.L * P.Δ) / (4096 * Δ₀ * ℓ₀) := by
    calc
      P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ := hsmall
      _ = (P.L * P.Δ) / (4096 * Δ₀ * ℓ₀) := by
        rw [bvLemma32C0]
        ring
  have hscale :
      4096 * Δ₀ * ℓ₀ * P.ε ^ 2 ≤ P.L * P.Δ := by
    have hs := (le_div_iff₀ hD).1 hsmallDiv
    simpa [mul_comm] using hs
  rw [bv_chainScale_identity P]
  have hden : 0 < 256 * Δ₀ * ℓ₀ * P.ε ^ 2 := by
    have hc : 0 < (256 * Δ₀ * ℓ₀ : ℝ) := by norm_num [Δ₀, ℓ₀]
    positivity
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The origin correction in equation (12) is at most `Δ/2` under the same universal smallness
condition. -/
theorem bv_origin_term_le_half_delta (P : BVParameters)
    (hsmall : P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ) :
    P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ / 2 := by
  rw [bv_origin_term_identity P]
  have hD : 0 < (4096 * Δ₀ * ℓ₀ : ℝ) := by norm_num [Δ₀, ℓ₀]
  have hsmallDiv : P.ε ^ 2 ≤ (P.L * P.Δ) / (4096 * Δ₀ * ℓ₀) := by
    calc
      P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ := hsmall
      _ = (P.L * P.Δ) / (4096 * Δ₀ * ℓ₀) := by
        rw [bvLemma32C0]
        ring
  have hscale :
      4096 * Δ₀ * ℓ₀ * P.ε ^ 2 ≤ P.L * P.Δ := by
    have hs := (le_div_iff₀ hD).1 hsmallDiv
    simpa [mul_comm] using hs
  have hconst : (16 * g₀ ^ 2 : ℝ) ≤ 4096 * Δ₀ * ℓ₀ := by
    norm_num [g₀, Δ₀, ℓ₀]
  have htarget : 16 * g₀ ^ 2 * P.ε ^ 2 ≤ P.L * P.Δ :=
    le_trans (mul_le_mul_of_nonneg_right hconst (sq_nonneg P.ε)) hscale
  apply (div_le_iff₀ P.L_pos).2
  nlinarith

/-- Once `T` satisfies the floor interval, the chain term in equation (12) is at most `Δ/4`. -/
theorem bv_chain_gap_term_le_quarter {T : ℕ} (P : BVParameters)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1) :
    P.α * Δ₀ * T ≤ P.Δ / 4 := by
  have hα : 0 < P.α := by
    rw [BVParameters.α]
    exact div_pos (sq_pos_of_pos (bv_q_pos P)) (bv_h_pos P)
  have hΔ0 : 0 < Δ₀ := by norm_num [Δ₀]
  have hm := mul_le_mul_of_nonneg_left hfloor.1
    (mul_nonneg (le_of_lt hα) (le_of_lt hΔ0))
  have hscale : P.α * Δ₀ * P.chainScale = P.Δ / 4 := by
    rw [BVParameters.chainScale]
    field_simp [ne_of_gt hα]
    ring
  rw [hscale] at hm
  exact hm

/-- All numerical conclusions of Lemma 3.2 follow automatically from the floor interval and the
single small-accuracy hypothesis. -/
theorem canonicalBV_numerical_closure {T : ℕ} (P : BVParameters)
    (hsmall : P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1) :
    (P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ) ∧
    8 ≤ T ∧
    bvLemma32C1 * (P.L * P.Δ / P.ε ^ 2) ≤ T := by
  have hΔ : 0 < P.Δ := bv_delta_pos_of_small P hsmall
  have hA16 : 16 ≤ P.chainScale := bv_chainScale_ge_sixteen P hsmall
  have hT8 : 8 ≤ T := floor_interval_ge_eight hfloor hA16
  have hhalf : P.chainScale / 2 ≤ (T : ℝ) :=
    floor_interval_ge_half hfloor (by linarith [hA16])
  have hchainTerm := bv_chain_gap_term_le_quarter P hfloor
  have horigin := bv_origin_term_le_half_delta P hsmall
  have hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ := by
    linarith
  have hrateEq :
      bvLemma32C1 * (P.L * P.Δ / P.ε ^ 2) = P.chainScale / 2 := by
    rw [bvLemma32C1, bv_chainScale_identity P]
    have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
    field_simp [hε0]
    ring
  have hchainReal :
      bvLemma32C1 * (P.L * P.Δ / P.ε ^ 2) ≤ (T : ℝ) := by
    rw [hrateEq]
    exact hhalf
  have hchainNat : bvLemma32C1 * (P.L * P.Δ / P.ε ^ 2) ≤ T := hchainReal
  exact ⟨hgap, hT8, hchainNat⟩

/-- Canonical Lemma-3.2 assembly after v30: once a natural chain length satisfying the exact floor
interval has been selected, the gap, chain-length, and actual-condition-number obligations are all
discharged internally. -/
noncomputable def canonicalLemma32Conclusion_of_floor {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (hκ : 8 ≤ P.κ)
    (hsmall : P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1) :
    Lemma32Conclusion C P (canonicalBVConstructionWitness C P)
      bvLemma32C1 bvKappaLowerConstant bvKappaUpperConstant := by
  have hnum := canonicalBV_numerical_closure P hsmall hfloor
  let Acond := canonicalBVActualConditionNumberCertificate C P hκ
  have hcond := canonicalBVActualConditionNumber_scaling C P hκ
  exact canonicalLemma32Conclusion_of_core C P
    bvLemma32C1 bvKappaLowerConstant bvKappaUpperConstant hκ
    hnum.1 hfloor hnum.2.1 hnum.2.2 Acond hcond



/-! ## v31 proof phase XXII: exact floor witness and end-to-end Theorem 3.3

The v30 numerical closure reduced paper Lemma 3.2 to one discrete bookkeeping step: choose the
natural chain length to be the natural-valued floor of `P.chainScale`.  Mathlib's floor theorem
then gives the exact interval required by the paper.  Since the v30 small-accuracy estimate already
shows `P.chainScale ≥ 16`, this floor is at least eight and hence is large enough to instantiate the
sole imported analytic input, Lemma 2.1.  Combining that imported explicit-chain certificate with
the canonical v29 construction and the v30 numerical/condition-number closure proves the full
`Lemma32Statement`, and the previously verified theorem `theorem33_of_lemma32` then yields the
paper's bounded-variance main theorem end to end.
-/

/-- The exact natural chain length in paper equation (18). -/
def canonicalBVChainLength (P : BVParameters) : ℕ :=
  ⌊P.chainScale⌋₊

/-- Mathlib's natural floor gives precisely the interval used in paper Lemma 3.2. -/
theorem canonicalBVChainLength_floor (P : BVParameters)
    (hscale : 0 ≤ P.chainScale) :
    (canonicalBVChainLength P : ℝ) ≤ P.chainScale ∧
      P.chainScale < (canonicalBVChainLength P : ℝ) + 1 := by
  constructor
  · simpa [canonicalBVChainLength] using (Nat.floor_le hscale)
  · simpa [canonicalBVChainLength] using (Nat.lt_floor_add_one P.chainScale)

/-- The small-accuracy hypothesis makes the canonical floor length at least eight. -/
theorem canonicalBVChainLength_ge_eight (P : BVParameters)
    (hsmall : P.ε ^ 2 ≤ bvLemma32C0 * P.L * P.Δ) :
    8 ≤ canonicalBVChainLength P := by
  have hA16 : 16 ≤ P.chainScale := bv_chainScale_ge_sixteen P hsmall
  have hA0 : 0 ≤ P.chainScale := by linarith
  have hfloor := canonicalBVChainLength_floor P hA0
  exact floor_interval_ge_eight hfloor hA16

/-- Fully instantiated paper Lemma 3.2.  No construction, lift, numerical, floor, or
condition-number certificate is supplied by the caller.  The only imported ingredient used here
is the paper's explicitly cited single-level Lemma 2.1 certificate. -/
theorem canonicalLemma32 : Lemma32Statement := by
  refine ⟨bvLemma32C0, bvLemma32C1,
    bvKappaLowerConstant, bvKappaUpperConstant,
    bvLemma32C0_pos, bvLemma32C1_pos, ?_, ?_, ?_⟩
  · norm_num [bvKappaLowerConstant]
  · norm_num [bvKappaUpperConstant]
  · intro P hκ hsmall
    let T : ℕ := canonicalBVChainLength P
    have hA16 : 16 ≤ P.chainScale := bv_chainScale_ge_sixteen P hsmall
    have hA0 : 0 ≤ P.chainScale := by linarith
    have hfloor :
        (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1 := by
      dsimp [T]
      exact canonicalBVChainLength_floor P hA0
    have hT8 : 8 ≤ T := floor_interval_ge_eight hfloor hA16
    have hT2 : 2 ≤ T := by omega
    rcases importedLemma21Certificate T hT2 with ⟨C⟩
    refine ⟨T, C, canonicalBVConstructionWitness C P, ?_⟩
    exact ⟨canonicalLemma32Conclusion_of_floor C P hκ hsmall hfloor⟩

/-- End-to-end bounded-variance main theorem (paper Theorem 3.3). -/
theorem canonicalTheorem33 : Theorem33Statement :=
  theorem33_of_lemma32 canonicalLemma32




end PaperExact

end NCSCPureStochasticLB


/-! ## v32 proof phase XXIII: averaged-smooth structural assembly

The bounded-variance theorem is end-to-end in v31.  This phase starts the analogous closure of
Section 4.  It proves the exact `p` semantics and variance budget for the AS parameter block,
transfers a full Lemma-4.1 base certificate through the already-proved quadratic lift, proves the
population and averaged-smooth upper bounds needed by Lemma 4.3, and packages all of those facts
into a reusable `Lemma43Conclusion` constructor.  The remaining AS obligations are thereby
isolated to the smooth-gate/base equation (23), the floor/rate arithmetic, and the actual averaged
condition-number lower bracket.
-/

namespace NCSCPureStochasticLB

namespace PaperExact

/-- Positivity of the reveal probability chosen in paper equation (25). -/
theorem as_p_pos (P : ASParameters) : 0 < P.p := by
  rw [P.p_def]
  by_cases hσ : P.σ = 0
  · simp [hσ]
  · simp only [hσ, if_false]
    apply lt_min (by norm_num)
    have hq : 0 < P.q := as_q_pos P
    have hg : 0 < g₀ := by norm_num [g₀]
    have hnum : 0 < P.q ^ 2 * g₀ ^ 2 := by positivity
    have hden : 0 < P.σ ^ 2 := sq_pos_of_ne_zero hσ
    exact div_pos hnum hden

/-- Equation (25) always chooses `p ≤ 1`. -/
theorem as_p_le_one (P : ASParameters) : P.p ≤ 1 := by
  rw [P.p_def]
  by_cases hσ : P.σ = 0
  · simp [hσ]
  · simp only [hσ, if_false]
    exact min_le_left _ _

/-- Noiseless branch of equation (25). -/
theorem as_p_eq_one_of_sigma_zero (P : ASParameters) (hσ : P.σ = 0) : P.p = 1 := by
  rw [P.p_def]
  simp [hσ]

/-- Genuinely stochastic branch of equation (25). -/
theorem as_p_eq_min_of_sigma_ne_zero (P : ASParameters) (hσ : P.σ ≠ 0) :
    P.p = min 1 (P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2) := by
  rw [P.p_def]
  simp [hσ]

/-- The exact equation-(27) scaling of the AS masking probability. -/
theorem as_p_scaling_exact (P : ASParameters) :
    ASPScalingExact P.p P.κ P.σ P.ε := by
  by_cases hσ : P.σ = 0
  · exact Or.inl ⟨hσ, as_p_eq_one_of_sigma_zero P hσ⟩
  · right
    refine ⟨hσ, ?_⟩
    rw [as_p_eq_min_of_sigma_ne_zero P hσ, P.q_sq]
    have hκ : P.κ ≠ 0 := by
      rw [P.κ_def]
      exact div_ne_zero (ne_of_gt P.Lbar_pos) (ne_of_gt P.μ_pos)
    have hσ2 : P.σ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_ne_zero hσ)
    congr 1
    field_simp [hκ, hσ2]
    ring

/-- Equation (25) makes the lifted Bernoulli variance fit the prescribed budget `σ²`. -/
theorem as_noise_budget (P : ASParameters) :
    P.q ^ 2 * g₀ ^ 2 * (1 - P.p) / P.p ≤ P.σ ^ 2 := by
  by_cases hσ : P.σ = 0
  · have hp1 : P.p = 1 := as_p_eq_one_of_sigma_zero P hσ
    rw [hσ, hp1]
    norm_num
  · have hpdef := as_p_eq_min_of_sigma_ne_zero P hσ
    let a : ℝ := P.q ^ 2 * g₀ ^ 2
    have hq : 0 < P.q := as_q_pos P
    have hg : 0 < g₀ := by norm_num [g₀]
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hs2 : 0 < P.σ ^ 2 := sq_pos_of_ne_zero hσ
    by_cases hlarge : 1 ≤ a / P.σ ^ 2
    · have hp1 : P.p = 1 := by
        rw [hpdef, min_eq_left hlarge]
      rw [hp1]
      simp
      positivity
    · have hsmall : a / P.σ ^ 2 ≤ 1 := le_of_not_ge hlarge
      have hp : P.p = a / P.σ ^ 2 := by
        rw [hpdef, min_eq_right hsmall]
      rw [hp]
      have ha0 : a ≠ 0 := ne_of_gt ha
      have hs0 : P.σ ^ 2 ≠ 0 := ne_of_gt hs2
      have heq : a * (1 - a / P.σ ^ 2) / (a / P.σ ^ 2) = P.σ ^ 2 - a := by
        field_simp [ha0, hs0]
      change a * (1 - a / P.σ ^ 2) / (a / P.σ ^ 2) ≤ P.σ ^ 2
      rw [heq]
      exact sub_le_self _ (le_of_lt ha)

/-- The lift witness has the same `ν` as the AS parameter block. -/
theorem asWitness_nu_eq {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) : W.LP.ν = P.ν := by
  rw [LiftParameters.ν, W.lift_mu, W.lift_h, ASParameters.ν]

/-- The lift witness has the same `α=q²/h` as the AS parameter block. -/
theorem asWitness_alpha_eq {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) : W.LP.α = P.α := by
  rw [LiftParameters.α, ASParameters.α, W.lift_q, W.lift_h]

/-- A full Lemma-4.1 certificate supplies the base unbiasedness hypothesis needed by Lemma 2.3. -/
theorem asWitness_baseUnbiased {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) {mΓ : ℝ}
    {Gate : SmoothGateCertificate mΓ}
    (H : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate) :
    BaseUnbiased C W.B P.p := by
  intro u
  have h := H.unbiased u
  simpa only [W.base_oracle_def] using h

/-- A full Lemma-4.1 certificate supplies the base variance hypothesis. -/
theorem asWitness_baseVariance {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) {mΓ : ℝ}
    {Gate : SmoothGateCertificate mΓ}
    (H : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate) :
    BaseVarianceHypothesis C W.B P.p g₀ := by
  intro u
  have h := H.variance u
  simpa only [W.base_oracle_def] using h

/-- A full Lemma-4.1 certificate supplies the same-seed base smoothness hypothesis. -/
theorem asWitness_baseAveragedSmooth {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) {mΓ : ℝ}
    {Gate : SmoothGateCertificate mΓ}
    (H : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate) :
    BaseAveragedSmoothHypothesis W.B P.p P.s₀ := by
  intro u v
  have h := H.averaged_smooth u v
  simpa only [W.base_oracle_def] using h

/-- The AS population joint-gradient constant is already at most `Lbar/2` under `κ ≥ 8`. -/
theorem as_lift_joint_smooth_constant_le_half (P : ASParameters) (hκ : 8 ≤ P.κ) :
    P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h ≤ P.Lbar / 2 := by
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  have hh := as_h_le_mu_branch P
  have hden : 0 < 4 * ℓ₀ := mul_pos (by norm_num) hℓ
  have hmul := (le_div_iff₀ hden).1 hh
  have hℓh : ℓ₀ * P.h ≤ P.μ / 4 := by
    nlinarith [hmul]
  have hν : P.ν ≤ 5 * P.μ / 4 := by
    rw [ASParameters.ν]
    nlinarith
  have hfac : 0 ≤ 1 + P.γ ^ 2 := by nlinarith [sq_nonneg P.γ]
  have hνfac := mul_le_mul_of_nonneg_right hν hfac
  have hκ' : 8 ≤ P.Lbar / P.μ := by simpa [P.κ_def] using hκ
  have hLmu : 8 * P.μ ≤ P.Lbar := (le_div_iff₀ P.μ_pos).1 hκ'
  have hexact :
      (5 * P.μ / 4) * (1 + P.γ ^ 2) + P.μ / 4 =
        3 * P.μ / 2 + 5 * P.Lbar / 16 := by
    rw [P.γ_sq, P.κ_def]
    field_simp [ne_of_gt P.μ_pos]
    ring
  calc
    P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h
        ≤ (5 * P.μ / 4) * (1 + P.γ ^ 2) + P.μ / 4 :=
          add_le_add hνfac hℓh
    _ = 3 * P.μ / 2 + 5 * P.Lbar / 16 := hexact
    _ ≤ P.Lbar / 2 := by nlinarith

/-- The stochastic branch of the AS `h` choice contributes at most `Lbar/4` to the root
same-seed smoothness constant. -/
theorem as_lift_noise_root_le_quarter (P : ASParameters) :
    P.h * P.s₀ / Real.sqrt P.p ≤ P.Lbar / 4 := by
  have hsqrt : 0 < Real.sqrt P.p := Real.sqrt_pos.2 P.p_pos
  have hs0 : 0 < P.s₀ := P.s₀_pos
  have hh := as_h_le_smooth_branch P
  have hm := mul_le_mul_of_nonneg_right hh (le_of_lt hs0)
  have hcancel :
      (P.Lbar * Real.sqrt P.p / (4 * P.s₀)) * P.s₀ =
        P.Lbar * Real.sqrt P.p / 4 := by
    field_simp [ne_of_gt hs0]
    ring
  rw [hcancel] at hm
  apply (div_le_iff₀ hsqrt).2
  nlinarith

/-- The root constant supplied by Lemma 2.3(iv) is below the target `Lbar`. -/
theorem as_lift_averaged_root_le_Lbar (P : ASParameters) (hκ : 8 ≤ P.κ) :
    P.ν * (1 + P.γ ^ 2) + P.h * P.s₀ / Real.sqrt P.p ≤ P.Lbar := by
  have hhalf := as_lift_joint_smooth_constant_le_half P hκ
  have hquarter := as_lift_noise_root_le_quarter P
  have hℓh_nonneg : 0 ≤ ℓ₀ * P.h := by
    exact mul_nonneg (by norm_num [ℓ₀]) (le_of_lt (as_h_pos P))
  have hjoint : P.ν * (1 + P.γ ^ 2) ≤ P.Lbar / 2 := by
    calc
      P.ν * (1 + P.γ ^ 2)
          ≤ P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h := le_add_of_nonneg_right hℓh_nonneg
      _ ≤ P.Lbar / 2 := hhalf
  calc
    P.ν * (1 + P.γ ^ 2) + P.h * P.s₀ / Real.sqrt P.p
        ≤ P.Lbar / 2 + P.Lbar / 4 := add_le_add hjoint hquarter
    _ ≤ P.Lbar := by nlinarith [P.Lbar_pos]

/-- The concrete AS lifted oracle is unbiased whenever Lemma 4.1 is available. -/
theorem asConstructedOracle_unbiased {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) {mΓ : ℝ}
    {Gate : SmoothGateCertificate mΓ}
    (H : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate) :
    OracleUnbiased (asConstructedPopulation W) (bernoulliLaw P.p)
      (asConstructedOracle W) := by
  exact liftedOracle_unbiased C W.B W.LP W.lift_properties P.p
    (asWitness_baseUnbiased W H)

/-- The concrete AS lifted oracle has variance at most the prescribed `σ²`. -/
theorem asConstructedOracle_boundedVariance {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) {mΓ : ℝ}
    {Gate : SmoothGateCertificate mΓ}
    (H : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate) :
    OracleBoundedVariance (asConstructedPopulation W) (bernoulliLaw P.p)
      (asConstructedOracle W) P.σ := by
  intro x y
  have hbase : BaseVarianceHypothesis C W.B P.p g₀ := asWitness_baseVariance W H
  have htransfer := lifted_variance_transfer C W.B W.LP P.p g₀ hbase x y
  have hbudget := as_noise_budget P
  have hq : W.LP.q = P.q := W.lift_q
  have htransfer' :
      bernoulliExpectReal P.p (fun Z =>
        ‖liftedGx W.LP x y Z - (W.LP.ν * W.LP.γ) • (y - W.LP.γ • x)‖ ^ 2 +
        ‖liftedGy W.B W.LP x y Z -
          (W.LP.q • C.gradF (W.LP.β • y) - W.LP.ν • (y - W.LP.γ • x))‖ ^ 2) ≤
        P.q ^ 2 * g₀ ^ 2 * (1 - P.p) / P.p := by
    simpa [hq] using htransfer
  change bernoulliExpectReal P.p (fun Z =>
      ‖(asConstructedOracle W).Gx x y Z - (asConstructedPopulation W).gradX x y‖ ^ 2 +
      ‖(asConstructedOracle W).Gy x y Z - (asConstructedPopulation W).gradY x y‖ ^ 2) ≤ P.σ ^ 2
  exact le_trans htransfer' hbudget

/-- The concrete AS lifted oracle is `Lbar`-averaged-smooth whenever Lemma 4.1 is available. -/
theorem asConstructedOracle_averagedSmooth {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) {mΓ : ℝ}
    {Gate : SmoothGateCertificate mΓ}
    (H : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate)
    (hκ : 8 ≤ P.κ) :
    OracleAveragedSmooth (bernoulliLaw P.p) (asConstructedOracle W) P.Lbar := by
  intro x y x' y'
  have hbase : BaseAveragedSmoothHypothesis W.B P.p P.s₀ :=
    asWitness_baseAveragedSmooth W H
  have ht := lifted_averaged_smooth_transfer W.B W.LP P.p P.s₀
    H.p_pos H.p_le_one (le_of_lt P.s₀_pos) hbase x y x' y'
  have hrootP := as_lift_averaged_root_le_Lbar P hκ
  have hrootW :
      W.LP.ν * (1 + W.LP.γ ^ 2) + W.LP.h * P.s₀ / Real.sqrt P.p ≤ P.Lbar := by
    rw [asWitness_nu_eq W, W.lift_gamma, W.lift_h]
    exact hrootP
  have hroot_nonneg :
      0 ≤ W.LP.ν * (1 + W.LP.γ ^ 2) + W.LP.h * P.s₀ / Real.sqrt P.p := by
    have hν : 0 ≤ W.LP.ν := le_of_lt (lift_nu_pos W.LP)
    have hfac : 0 ≤ 1 + W.LP.γ ^ 2 := by nlinarith [sq_nonneg W.LP.γ]
    have hsqrt : 0 < Real.sqrt P.p := Real.sqrt_pos.2 H.p_pos
    exact add_nonneg (mul_nonneg hν hfac)
      (div_nonneg (mul_nonneg (le_of_lt W.LP.h_pos) (le_of_lt P.s₀_pos)) (le_of_lt hsqrt))
  have hsq :
      (W.LP.ν * (1 + W.LP.γ ^ 2) + W.LP.h * P.s₀ / Real.sqrt P.p) ^ 2 ≤
        P.Lbar ^ 2 := by
    nlinarith [P.Lbar_pos]
  have hnorm : 0 ≤ ‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2 := by positivity
  have hscale := mul_le_mul_of_nonneg_right hsq hnorm
  change bernoulliExpectReal P.p (fun Z =>
      ‖liftedGx W.LP x y Z - liftedGx W.LP x' y' Z‖ ^ 2 +
      ‖liftedGy W.B W.LP x y Z - liftedGy W.B W.LP x' y' Z‖ ^ 2) ≤
    P.Lbar ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  exact le_trans ht hscale

/-- AS analogue of the v18/v30 core assembler: once Lemma 4.1, the displayed gap/floor/rate
arithmetic, and the actual averaged-condition certificate are available, every field of paper
Lemma 4.3 follows from the canonical lift. -/
def lemma43Conclusion_of_core {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : ASParameters) (W : ASConstructionWitness C P)
    (mΓ : ℝ) (Gate : SmoothGateCertificate mΓ)
    (c₂ cκLo cκHi : ℝ) (hκ : 8 ≤ P.κ)
    (Hbase : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate)
    (hs0 : P.s₀ = universalS0 mΓ)
    (hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1)
    (hT : 8 ≤ T)
    (heq29 : c₂ * (P.Lbar * P.Δ / P.ε ^ 2) *
      min 1 (P.κ * Real.sqrt P.p) ≤ T)
    (heq30 : c₂ * (P.Lbar * P.Δ / P.ε ^ 2) *
      min (1 / P.p) (P.κ / Real.sqrt P.p) ≤ (T : ℝ) / P.p)
    (Acond : ActualAveragedConditionNumberCertificate (asConstructedPopulation W)
      (bernoulliLaw P.p) (asConstructedOracle W))
    (hcond : cκLo * P.κ ≤ Acond.LbarLo / Acond.muHi ∧
      Acond.LbarHi / Acond.muLo ≤ cκHi * P.κ) :
    Lemma43Conclusion C P W mΓ Gate c₂ cκLo cκHi := by
  have hsmoothP := as_lift_joint_smooth_constant_le_half P hκ
  have hsmooth : W.LP.ν * (1 + W.LP.γ ^ 2) + ℓ₀ * W.LP.h ≤ P.Lbar := by
    calc
      W.LP.ν * (1 + W.LP.γ ^ 2) + ℓ₀ * W.LP.h =
          P.ν * (1 + P.γ ^ 2) + ℓ₀ * P.h := by
            rw [asWitness_nu_eq W, W.lift_gamma, W.lift_h]
      _ ≤ P.Lbar / 2 := hsmoothP
      _ ≤ P.Lbar := by linarith [P.Lbar_pos]
  have hgapW :
      W.LP.α * Δ₀ * T + W.LP.q ^ 2 * g₀ ^ 2 / (2 * W.LP.μ) ≤ P.Δ := by
    rw [asWitness_alpha_eq W, W.lift_q, W.lift_mu]
    exact hgap
  have hncsc := populationFromLift_inNCSCClass_of_bounds C W.B W.LP W.lift_properties
    P.Lbar P.Δ hsmooth hgapW
  have hstrong := populationFromLift_stronglyConcaveY C W.B W.LP W.lift_properties
  have hinit := populationFromLift_initialGap_of_bound C W.B W.LP W.lift_properties P.Δ hgapW
  exact
    { base_certificate := Hbase
      p_pos := Hbase.p_pos
      p_le_one := Hbase.p_le_one
      fixed_s0 := hs0
      ncsc := by simpa [asConstructedPopulation, W.lift_mu] using hncsc
      strong_concavity := by simpa [asConstructedPopulation, W.lift_mu] using hstrong
      unbiased := asConstructedOracle_unbiased W Hbase
      variance := asConstructedOracle_boundedVariance W Hbase
      averaged_smooth := asConstructedOracle_averagedSmooth W Hbase hκ
      initial_gap := by simpa [asConstructedPopulation] using hinit
      chain_floor := hfloor
      T_ge_eight := hT
      eq29 := heq29
      eq30 := heq30
      p_scaling := as_p_scaling_exact P
      actual := Acond
      actual_condition_number := hcond }


/-! ## v33 proof phase XXIV: local analytic core of the smooth-gated estimate (23)

This phase proves the dimension-free Lipschitz facts that are specific to the smooth gate.  The
key point is that `ThetaGate` inherits an `mΓ²` Lipschitz constant from the inner coordinatewise
step and the outer step, while the stochastic mask remains supported on at most the single
`1/2`-frontier coordinate.  These are the analytic ingredients needed for the final two-active-
coordinate argument in equation (23).
-/

/-- Coordinatewise Lipschitz estimate for the gated tail. -/
theorem gatedTail_coord_diff_le {T : ℕ} {mΓ : ℝ}
    (Gate : SmoothGateCertificate mΓ) (u v : Vec T) (i j : Fin T) :
    ‖(gatedTail u i - gatedTail v i) j‖ ≤ mΓ * ‖(u - v) j‖ := by
  by_cases hij : i.1 ≤ j.1
  · have hΓ := Gate.gamma_lipschitz |u j| |v j|
    have habs : abs (|u j| - |v j|) ≤ |u j - v j| :=
      abs_abs_sub_abs_le_abs_sub (u j) (v j)
    have hmul := mul_le_mul_of_nonneg_left habs Gate.mΓ_nonneg
    have h := le_trans hΓ hmul
    simpa [gatedTail, hij, Real.norm_eq_abs] using h
  · have hrhs : 0 ≤ mΓ * ‖(u - v) j‖ :=
      mul_nonneg Gate.mΓ_nonneg (norm_nonneg _)
    simpa [gatedTail, hij] using hrhs

/-- The coordinatewise inner smooth step is `mΓ`-Lipschitz in the Euclidean norm. -/
theorem gatedTail_lipschitz {T : ℕ} {mΓ : ℝ}
    (Gate : SmoothGateCertificate mΓ) (u v : Vec T) (i : Fin T) :
    ‖gatedTail u i - gatedTail v i‖ ≤ mΓ * ‖u - v‖ := by
  have hcoord : ∀ j : Fin T,
      ‖(gatedTail u i - gatedTail v i) j‖ ^ 2 ≤
        mΓ ^ 2 * ‖(u - v) j‖ ^ 2 := by
    intro j
    have h := gatedTail_coord_diff_le Gate u v i j
    have hleft : 0 ≤ ‖(gatedTail u i - gatedTail v i) j‖ := norm_nonneg _
    have hright : 0 ≤ mΓ * ‖(u - v) j‖ :=
      mul_nonneg Gate.mΓ_nonneg (norm_nonneg _)
    nlinarith
  have hsum :
      (∑ j : Fin T, ‖(gatedTail u i - gatedTail v i) j‖ ^ 2) ≤
        mΓ ^ 2 * ∑ j : Fin T, ‖(u - v) j‖ ^ 2 := by
    calc
      (∑ j : Fin T, ‖(gatedTail u i - gatedTail v i) j‖ ^ 2)
          ≤ ∑ j : Fin T, mΓ ^ 2 * ‖(u - v) j‖ ^ 2 := by
            exact Finset.sum_le_sum fun j _ => hcoord j
      _ = mΓ ^ 2 * ∑ j : Fin T, ‖(u - v) j‖ ^ 2 := by
            rw [Finset.mul_sum]
  have hsq :
      ‖gatedTail u i - gatedTail v i‖ ^ 2 ≤
        (mΓ * ‖u - v‖) ^ 2 := by
    rw [@PiLp.norm_sq_eq_of_L2, mul_pow, @PiLp.norm_sq_eq_of_L2]
    exact hsum
  have hleft : 0 ≤ ‖gatedTail u i - gatedTail v i‖ := norm_nonneg _
  have hright : 0 ≤ mΓ * ‖u - v‖ :=
    mul_nonneg Gate.mΓ_nonneg (norm_nonneg _)
  nlinarith

/-- The paper's gate `Theta_i` is globally `mΓ²`-Lipschitz. -/
theorem thetaGate_lipschitz {T : ℕ} {mΓ : ℝ}
    (Gate : SmoothGateCertificate mΓ) (u v : Vec T) (i : Fin T) :
    |ThetaGate u i - ThetaGate v i| ≤ mΓ ^ 2 * ‖u - v‖ := by
  have hΓ := Gate.gamma_lipschitz
    (1 - ‖gatedTail u i‖) (1 - ‖gatedTail v i‖)
  have harg :
      |(1 - ‖gatedTail u i‖) - (1 - ‖gatedTail v i‖)| =
        |‖gatedTail u i‖ - ‖gatedTail v i‖| := by
    calc
      |(1 - ‖gatedTail u i‖) - (1 - ‖gatedTail v i‖)| =
          |-(‖gatedTail u i‖ - ‖gatedTail v i‖)| := by congr 1 <;> ring
      _ = |‖gatedTail u i‖ - ‖gatedTail v i‖| := abs_neg _
  have hnorm :
      |‖gatedTail u i‖ - ‖gatedTail v i‖| ≤
        ‖gatedTail u i - gatedTail v i‖ :=
    abs_norm_sub_norm_le _ _
  have htail := gatedTail_lipschitz Gate u v i
  calc
    |ThetaGate u i - ThetaGate v i|
        ≤ mΓ * |(1 - ‖gatedTail u i‖) - (1 - ‖gatedTail v i‖)| := by
          simpa [ThetaGate] using hΓ
    _ = mΓ * |‖gatedTail u i‖ - ‖gatedTail v i‖| := by rw [harg]
    _ ≤ mΓ * ‖gatedTail u i - gatedTail v i‖ :=
          mul_le_mul_of_nonneg_left hnorm Gate.mΓ_nonneg
    _ ≤ mΓ * (mΓ * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left htail Gate.mΓ_nonneg
    _ = mΓ ^ 2 * ‖u - v‖ := by ring

/-- Deterministic mask multiplying the centered Bernoulli scalar in equation (21). -/
noncomputable def asMaskVector {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (u : Vec T) : Vec T :=
  fun i => (C.gradF u) i * ThetaGate u i

/-- The stochastic error is exactly one centered scalar times the deterministic mask. -/
theorem asBaseOracle_error_eq_center_smul_mask {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (u : Vec T) (Z : Bool) :
    asBaseOracle C p u Z - C.gradF u =
      (bernoulliZ Z / p - 1) • asMaskVector C u := by
  ext i
  simp [asBaseOracle, asMaskVector]
  ring

/-- When the half-frontier is inside the chain, the deterministic mask is a single-coordinate
vector. -/
theorem asMaskVector_eq_single {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (u : Vec T) (hfront : prog (1 / 2) u < T) :
    asMaskVector C u =
      EuclideanSpace.single (halfFrontierIndex u hfront)
        ((C.gradF u) (halfFrontierIndex u hfront) *
          ThetaGate u (halfFrontierIndex u hfront)) := by
  ext i
  by_cases hij : i = halfFrontierIndex u hfront
  · subst i
    simp [asMaskVector, EuclideanSpace.single_apply]
  · have hneval : i.1 ≠ (halfFrontierIndex u hfront).1 := by
      intro hval
      apply hij
      exact Fin.ext hval
    rcases lt_or_gt_of_ne hneval with hlt | hgt
    · have hle0 : i.1 + 1 ≤ (halfFrontierIndex u hfront).1 :=
        Nat.succ_le_iff.mpr hlt
      have hle : i.1 + 1 ≤ prog (1 / 2) u := by
        simpa [halfFrontierIndex] using hle0
      have htheta := thetaGate_eq_zero_at_or_before_half Gate u i hle
      simp [asMaskVector, htheta, EuclideanSpace.single_apply, hij]
    · have hfar : prog (1 / 2) u + 1 < i.1 + 1 := by
        simpa [halfFrontierIndex] using Nat.succ_lt_succ hgt
      have hgzero := gradF_zero_beyond_half_frontier C u i hfar
      simp [asMaskVector, hgzero, EuclideanSpace.single_apply, hij]

/-- If the half-frontier has reached the chain end, the deterministic mask is zero. -/
theorem asMaskVector_eq_zero_of_half_frontier_full {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (u : Vec T) (hfront : ¬ prog (1 / 2) u < T) :
    asMaskVector C u = 0 := by
  have hprog_le : prog (1 / 2) u ≤ T := by
    unfold prog
    exact Nat.findGreatest_le T
  have hprog : prog (1 / 2) u = T := by omega
  ext i
  have hiT : i.1 + 1 ≤ T := Nat.succ_le_iff.mpr i.2
  have hi : i.1 + 1 ≤ prog (1 / 2) u := by omega
  have htheta := thetaGate_eq_zero_at_or_before_half Gate u i hi
  simp [asMaskVector, htheta]

/-- Coordinatewise difference bound for the deterministic masks. -/
theorem asMaskVector_coord_diff_abs_le {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (u v : Vec T) (i : Fin T) :
    |(asMaskVector C u - asMaskVector C v) i| ≤
      g₀ * mΓ ^ 2 * ‖u - v‖ + |(C.gradF u - C.gradF v) i| := by
  have htheta := thetaGate_lipschitz Gate u v i
  have hgu := C.grad_coord_bound u i
  have htv := thetaGate_range Gate v i
  have htva : |ThetaGate v i| ≤ 1 := by
    rw [abs_of_nonneg htv.1]
    exact htv.2
  have hg0 : 0 ≤ g₀ := by norm_num [g₀]
  have hm2 : 0 ≤ mΓ ^ 2 := sq_nonneg mΓ
  have hdist : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hfirst :
      |(C.gradF u) i| * |ThetaGate u i - ThetaGate v i| ≤
        g₀ * (mΓ ^ 2 * ‖u - v‖) := by
    exact mul_le_mul hgu htheta (abs_nonneg _) hg0
  have hsecond :
      |(C.gradF u) i - (C.gradF v) i| * |ThetaGate v i| ≤
        |(C.gradF u) i - (C.gradF v) i| := by
    calc
      |(C.gradF u) i - (C.gradF v) i| * |ThetaGate v i|
          ≤ |(C.gradF u) i - (C.gradF v) i| * 1 :=
            mul_le_mul_of_nonneg_left htva (abs_nonneg _)
      _ = |(C.gradF u) i - (C.gradF v) i| := by ring
  have hdecomp :
      (asMaskVector C u - asMaskVector C v) i =
        (C.gradF u) i * (ThetaGate u i - ThetaGate v i) +
          ((C.gradF u) i - (C.gradF v) i) * ThetaGate v i := by
    simp [asMaskVector]
    ring
  rw [hdecomp]
  calc
    |(C.gradF u) i * (ThetaGate u i - ThetaGate v i) +
        ((C.gradF u) i - (C.gradF v) i) * ThetaGate v i|
        ≤ |(C.gradF u) i * (ThetaGate u i - ThetaGate v i)| +
            |((C.gradF u) i - (C.gradF v) i) * ThetaGate v i| :=
          abs_add _ _
    _ = |(C.gradF u) i| * |ThetaGate u i - ThetaGate v i| +
          |(C.gradF u) i - (C.gradF v) i| * |ThetaGate v i| := by
          rw [abs_mul, abs_mul]
    _ ≤ g₀ * (mΓ ^ 2 * ‖u - v‖) +
          |(C.gradF u) i - (C.gradF v) i| := add_le_add hfirst hsecond
    _ = g₀ * mΓ ^ 2 * ‖u - v‖ + |(C.gradF u - C.gradF v) i| := by
          simp
          ring

/-- Squared coordinate form used in the final two-active-coordinate estimate. -/
theorem asMaskVector_coord_diff_sq_le {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (u v : Vec T) (i : Fin T) :
    ((asMaskVector C u - asMaskVector C v) i) ^ 2 ≤
      2 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
        2 * ((C.gradF u - C.gradF v) i) ^ 2 := by
  let A : ℝ := g₀ * mΓ ^ 2 * ‖u - v‖
  let B : ℝ := |(C.gradF u - C.gradF v) i|
  have hAB : |(asMaskVector C u - asMaskVector C v) i| ≤ A + B := by
    simpa [A, B] using asMaskVector_coord_diff_abs_le C Gate u v i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by norm_num [g₀]) (sq_nonneg mΓ)) (norm_nonneg _)
  have hB : 0 ≤ B := by exact abs_nonneg _
  have hsq1 : |(asMaskVector C u - asMaskVector C v) i| ^ 2 ≤ (A + B) ^ 2 := by
    have hmul := mul_self_le_mul_self
      (abs_nonneg ((asMaskVector C u - asMaskVector C v) i)) hAB
    simpa [pow_two] using hmul
  have hsq2 : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A - B)]
  calc
    ((asMaskVector C u - asMaskVector C v) i) ^ 2 =
        |(asMaskVector C u - asMaskVector C v) i| ^ 2 := by rw [sq_abs]
    _ ≤ (A + B) ^ 2 := hsq1
    _ ≤ 2 * A ^ 2 + 2 * B ^ 2 := hsq2
    _ = 2 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
          2 * ((C.gradF u - C.gradF v) i) ^ 2 := by
          dsimp [A, B]
          rw [sq_abs]
          ring


/-! ## v34 proof phase XXV: global two-frontier mask control and Bernoulli cancellation

The v33.1 coordinate estimate is lifted to the full Euclidean norm.  The key structural fact is
that every deterministic AS mask is either zero or a single half-frontier coordinate, so the
difference of two masks has at most two active coordinates.  We also isolate the exact Bernoulli
second-moment identity that removes the mixed term in equation (23). -/

/-- One coordinate contributes at most the full squared Euclidean norm. -/
theorem vec_coord_sq_le_norm_sq {T : ℕ} (w : Vec T) (i : Fin T) :
    (w i) ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [@PiLp.norm_sq_eq_of_L2]
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- Two distinct coordinates contribute at most the full squared Euclidean norm. -/
theorem vec_two_coord_sq_le_norm_sq {T : ℕ} (w : Vec T) (i j : Fin T)
    (hij : i ≠ j) :
    (w i) ^ 2 + (w j) ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [@PiLp.norm_sq_eq_of_L2]
  have h := Finset.sum_le_univ_sum_of_nonneg
    (s := ({i, j} : Finset (Fin T))) (fun k => sq_nonneg ‖w k‖)
  simpa [hij, Real.norm_eq_abs, sq_abs] using h

/-- Global two-active-coordinate bound for the deterministic masks. -/
theorem asMaskVector_diff_norm_sq_le {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (u v : Vec T) :
    ‖asMaskVector C u - asMaskVector C v‖ ^ 2 ≤
      4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
        2 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
  let M : Vec T := asMaskVector C u - asMaskVector C v
  let G : Vec T := C.gradF u - C.gradF v
  let A : ℝ := g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hcoord : ∀ i : Fin T, (M i) ^ 2 ≤ 2 * A + 2 * (G i) ^ 2 := by
    intro i
    have h := asMaskVector_coord_diff_sq_le C Gate u v i
    simpa [M, G, A, mul_assoc] using h
  by_cases hu : prog (1 / 2) u < T
  · by_cases hv : prog (1 / 2) v < T
    · let iu : Fin T := halfFrontierIndex u hu
      let iv : Fin T := halfFrontierIndex v hv
      have hmu := asMaskVector_eq_single C Gate u hu
      have hmv := asMaskVector_eq_single C Gate v hv
      by_cases huv : iu = iv
      · have hidx : halfFrontierIndex u hu = halfFrontierIndex v hv := by
          simpa [iu, iv] using huv
        have hnorm : ‖M‖ ^ 2 = (M iu) ^ 2 := by
          dsimp [M, iu, iv]
          rw [hmu, hmv, norm_sub_sq_real,
            EuclideanSpace.norm_single, EuclideanSpace.norm_single,
            EuclideanSpace.inner_single_left]
          simp [EuclideanSpace.single_apply, hidx, Real.norm_eq_abs]
          simp only [mul_pow, sq_abs]
          ring
        have hc := hcoord iu
        have hg := vec_coord_sq_le_norm_sq G iu
        rw [hnorm]
        calc
          (M iu) ^ 2 ≤ 2 * A + 2 * (G iu) ^ 2 := hc
          _ ≤ 4 * A + 2 * ‖G‖ ^ 2 := by nlinarith [hA, hg]
          _ = 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
                2 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
                dsimp [A, G]
                ring
      · have hidx : halfFrontierIndex u hu ≠ halfFrontierIndex v hv := by
          simpa [iu, iv] using huv
        have hnorm : ‖M‖ ^ 2 = (M iu) ^ 2 + (M iv) ^ 2 := by
          dsimp [M, iu, iv]
          rw [hmu, hmv, norm_sub_sq_real,
            EuclideanSpace.norm_single, EuclideanSpace.norm_single,
            EuclideanSpace.inner_single_left]
          simp [EuclideanSpace.single_apply, hidx, Ne.symm hidx,
            Real.norm_eq_abs]
          simp only [mul_pow, sq_abs]
        have hcu := hcoord iu
        have hcv := hcoord iv
        have hg := vec_two_coord_sq_le_norm_sq G iu iv huv
        rw [hnorm]
        calc
          (M iu) ^ 2 + (M iv) ^ 2
              ≤ 4 * A + 2 * ((G iu) ^ 2 + (G iv) ^ 2) := by
                nlinarith [hcu, hcv]
          _ ≤ 4 * A + 2 * ‖G‖ ^ 2 := by nlinarith [hg]
          _ = 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
                2 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
                dsimp [A, G]
                ring
    · let iu : Fin T := halfFrontierIndex u hu
      have hmu := asMaskVector_eq_single C Gate u hu
      have hmv := asMaskVector_eq_zero_of_half_frontier_full C Gate v hv
      have hnorm : ‖M‖ ^ 2 = (M iu) ^ 2 := by
        dsimp [M, iu]
        rw [hmu, hmv, sub_zero, EuclideanSpace.norm_single, Real.norm_eq_abs]
        simp [EuclideanSpace.single_apply, sq_abs]
      have hc := hcoord iu
      have hg := vec_coord_sq_le_norm_sq G iu
      rw [hnorm]
      calc
        (M iu) ^ 2 ≤ 2 * A + 2 * (G iu) ^ 2 := hc
        _ ≤ 4 * A + 2 * ‖G‖ ^ 2 := by nlinarith [hA, hg]
        _ = 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
              2 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
              dsimp [A, G]
              ring
  · by_cases hv : prog (1 / 2) v < T
    · let iv : Fin T := halfFrontierIndex v hv
      have hmu := asMaskVector_eq_zero_of_half_frontier_full C Gate u hu
      have hmv := asMaskVector_eq_single C Gate v hv
      have hnorm : ‖M‖ ^ 2 = (M iv) ^ 2 := by
        dsimp [M, iv]
        rw [hmu, hmv, zero_sub, norm_neg,
          EuclideanSpace.norm_single, Real.norm_eq_abs]
        simp [EuclideanSpace.single_apply, sq_abs]
      have hc := hcoord iv
      have hg := vec_coord_sq_le_norm_sq G iv
      rw [hnorm]
      calc
        (M iv) ^ 2 ≤ 2 * A + 2 * (G iv) ^ 2 := hc
        _ ≤ 4 * A + 2 * ‖G‖ ^ 2 := by nlinarith [hA, hg]
        _ = 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
              2 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
              dsimp [A, G]
              ring
    · have hmu := asMaskVector_eq_zero_of_half_frontier_full C Gate u hu
      have hmv := asMaskVector_eq_zero_of_half_frontier_full C Gate v hv
      rw [hmu, hmv, sub_self, norm_zero]
      have hfirst :
          0 ≤ 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 := by
        positivity
      have hsecond :
          0 ≤ 2 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
        positivity
      nlinarith

/-- Same-seed oracle difference splits into the population gradient difference and one centered
Bernoulli scalar multiplying the mask difference. -/
theorem asBaseOracle_diff_decomp {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ)
    (u v : Vec T) (Z : Bool) :
    asBaseOracle C p u Z - asBaseOracle C p v Z =
      (C.gradF u - C.gradF v) +
        (bernoulliZ Z / p - 1) • (asMaskVector C u - asMaskVector C v) := by
  have hu := asBaseOracle_error_eq_center_smul_mask C p u Z
  have hv := asBaseOracle_error_eq_center_smul_mask C p v Z
  have hu' : asBaseOracle C p u Z =
      (bernoulliZ Z / p - 1) • asMaskVector C u + C.gradF u :=
    (sub_eq_iff_eq_add).mp hu
  have hv' : asBaseOracle C p v Z =
      (bernoulliZ Z / p - 1) • asMaskVector C v + C.gradF v :=
    (sub_eq_iff_eq_add).mp hv
  rw [hu', hv']
  module

/-- Pointwise square expansion before averaging over the Bernoulli seed. -/
theorem asBaseOracle_diff_norm_sq_expansion {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ)
    (u v : Vec T) (Z : Bool) :
    ‖asBaseOracle C p u Z - asBaseOracle C p v Z‖ ^ 2 =
      ‖C.gradF u - C.gradF v‖ ^ 2 +
        2 * (bernoulliZ Z / p - 1) *
          @inner ℝ (Vec T) _ (C.gradF u - C.gradF v)
            (asMaskVector C u - asMaskVector C v) +
        (bernoulliZ Z / p - 1) ^ 2 *
          ‖asMaskVector C u - asMaskVector C v‖ ^ 2 := by
  rw [asBaseOracle_diff_decomp C p u v Z, norm_add_sq_real,
    real_inner_smul_right, norm_smul, Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]
  ring

/-- Exact Bernoulli cancellation: the mixed term vanishes and the centered second moment is
`(1-p)/p`. -/
theorem asBaseOracle_diff_second_moment_identity {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (hp : p ≠ 0)
    (u v : Vec T) :
    bernoulliExpectReal p
      (fun Z => ‖asBaseOracle C p u Z - asBaseOracle C p v Z‖ ^ 2) =
      ‖C.gradF u - C.gradF v‖ ^ 2 +
        ((1 - p) / p) * ‖asMaskVector C u - asMaskVector C v‖ ^ 2 := by
  unfold bernoulliExpectReal
  dsimp
  rw [asBaseOracle_diff_norm_sq_expansion C p u v true,
    asBaseOracle_diff_norm_sq_expansion C p u v false]
  simp [bernoulliZ]
  field_simp [hp]
  ring


/-! ## v35 proof phase XXVI: close equation (23) and Lemma 4.1

The v34.4 two-frontier estimate and exact Bernoulli second-moment identity reduce the remaining
same-seed estimate to scalar bookkeeping.  Multiplying by the positive Bernoulli parameter `p`
removes all divisions.  The two coefficients `p` and `1-p` are then bounded by one, the mask
estimate contributes two additional copies of the population-gradient difference, and the
`ℓ₀`-Lipschitz property of the explicit chain supplies the final third copy.  This is exactly the
paper's conservative constant `s₀² = 4 g₀² mΓ⁴ + 3 ℓ₀²` in equation (24).
-/

/-- Paper equation (23): the smooth-gated Bernoulli oracle is averaged-smooth with root constant
`universalS0 mΓ / sqrt p`. -/
theorem asBaseOracle_averaged_smooth {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (u v : Vec T) :
    bernoulliExpectReal p
      (fun Z => ‖asBaseOracle C p u Z - asBaseOracle C p v Z‖ ^ 2) ≤
      (universalS0 mΓ) ^ 2 / p * ‖u - v‖ ^ 2 := by
  rw [asBaseOracle_diff_second_moment_identity C p (ne_of_gt hp0) u v]
  rw [universalS0_sq]
  have hp_nonneg : 0 ≤ p := le_of_lt hp0
  have h1mp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hG_nonneg : 0 ≤ ‖C.gradF u - C.gradF v‖ ^ 2 := sq_nonneg _
  have hM_nonneg : 0 ≤ ‖asMaskVector C u - asMaskVector C v‖ ^ 2 := sq_nonneg _
  have hpG_nonneg :
      0 ≤ p * ‖C.gradF u - C.gradF v‖ ^ 2 :=
    mul_nonneg hp_nonneg hG_nonneg
  have hpM_nonneg :
      0 ≤ p * ‖asMaskVector C u - asMaskVector C v‖ ^ 2 :=
    mul_nonneg hp_nonneg hM_nonneg
  have hG_weight :
      p * ‖C.gradF u - C.gradF v‖ ^ 2 ≤ ‖C.gradF u - C.gradF v‖ ^ 2 := by
    have hgap :
        0 ≤ (1 - p) * ‖C.gradF u - C.gradF v‖ ^ 2 :=
      mul_nonneg h1mp_nonneg hG_nonneg
    nlinarith
  have hM_weight :
      (1 - p) * ‖asMaskVector C u - asMaskVector C v‖ ^ 2 ≤
        ‖asMaskVector C u - asMaskVector C v‖ ^ 2 := by
    nlinarith
  have hmask := asMaskVector_diff_norm_sq_le C Gate u v
  have hgrad := C.grad_lipschitz u v
  have hgrad_sq :
      ‖C.gradF u - C.gradF v‖ ^ 2 ≤ ℓ₀ ^ 2 * ‖u - v‖ ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg (C.gradF u - C.gradF v)) hgrad
    calc
      ‖C.gradF u - C.gradF v‖ ^ 2 =
          ‖C.gradF u - C.gradF v‖ * ‖C.gradF u - C.gradF v‖ := by ring
      _ ≤ (ℓ₀ * ‖u - v‖) * (ℓ₀ * ‖u - v‖) := hs
      _ = ℓ₀ ^ 2 * ‖u - v‖ ^ 2 := by ring
  have hrhs :
      (4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2) / p * ‖u - v‖ ^ 2 =
        ((4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2) * ‖u - v‖ ^ 2) / p := by
    field_simp [ne_of_gt hp0] <;> ring
  rw [hrhs]
  apply (le_div_iff₀ hp0).2
  have hleft :
      (‖C.gradF u - C.gradF v‖ ^ 2 +
          (1 - p) / p * ‖asMaskVector C u - asMaskVector C v‖ ^ 2) * p =
        p * ‖C.gradF u - C.gradF v‖ ^ 2 +
          (1 - p) * ‖asMaskVector C u - asMaskVector C v‖ ^ 2 := by
    field_simp [ne_of_gt hp0] <;> ring
  rw [hleft]
  calc
    p * ‖C.gradF u - C.gradF v‖ ^ 2 +
        (1 - p) * ‖asMaskVector C u - asMaskVector C v‖ ^ 2
        ≤ ‖C.gradF u - C.gradF v‖ ^ 2 +
            ‖asMaskVector C u - asMaskVector C v‖ ^ 2 :=
          add_le_add hG_weight hM_weight
    _ ≤ 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
          3 * ‖C.gradF u - C.gradF v‖ ^ 2 := by
          linarith
    _ ≤ 4 * g₀ ^ 2 * mΓ ^ 4 * ‖u - v‖ ^ 2 +
          3 * (ℓ₀ ^ 2 * ‖u - v‖ ^ 2) := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_left hgrad_sq (by norm_num : (0 : ℝ) ≤ 3)) _
    _ = (4 * g₀ ^ 2 * mΓ ^ 4 + 3 * ℓ₀ ^ 2) * ‖u - v‖ ^ 2 := by
          ring

/-- Full Lemma 4.1 certificate.  After v34.4, equation (23) is no longer an external
hypothesis: it is generated from the gate certificate and the explicit zero-chain certificate. -/
theorem lemma41_full_certificate {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ASBaseOracleCertificate T C p mΓ (universalS0 mΓ) Gate := by
  apply lemma41_certificate_of_averaged_smooth C Gate p hp0 hp1
  intro u v
  exact asBaseOracle_averaged_smooth C Gate p hp0 hp1 u v

/-- Canonical Section-4 form of Lemma 4.1 for an `ASParameters` block whose fixed `s₀` is the
paper's universal value. -/
theorem canonicalASBaseOracleCertificate {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (P : ASParameters) (hs0 : P.s₀ = universalS0 mΓ) :
    ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate := by
  have H := lemma41_full_certificate C Gate P.p P.p_pos (as_p_le_one P)
  simpa [hs0] using H

/-- The universal constant in equation (24) is strictly positive, independently of `mΓ`. -/
theorem universalS0_pos (mΓ : ℝ) : 0 < universalS0 mΓ := by
  unfold universalS0
  apply Real.sqrt_pos.2
  have hmain : 0 < 3 * ℓ₀ ^ 2 := by norm_num [ℓ₀]
  have hgate : 0 ≤ 4 * g₀ ^ 2 * mΓ ^ 4 := by positivity
  nlinarith


/-! ## v36 proof phase XXVII: AS arithmetic and actual averaged condition number

The full smooth-gated Lemma 4.1 certificate is now internal (v35.1).  This phase turns the
remaining condition-number part of Lemma 4.3 into a concrete theorem and records the exact
Section-4 arithmetic identities used by the later floor/rate closure.  The lower averaged-smooth
bracket is proved directly from the deterministic primal block of the lifted oracle; no Jensen or
attainment assumption is used.
-/

/-- Any same-seed averaged-smooth constant for the lifted Bernoulli oracle is at least
`ν γ²`.  We vary only the primal variable.  The primal oracle block is deterministic in the seed,
so its squared change survives the Bernoulli expectation unchanged. -/
theorem liftedOracle_averagedSmooth_lower_primal {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (p L : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hL0 : 0 ≤ L)
    (havg : OracleAveragedSmooth (bernoulliLaw p) (liftedOracle B P) L) :
    P.ν * P.γ ^ 2 ≤ L := by
  let u : Vec T := C.gradF 0
  have hprog0 : prog 1 (0 : Vec T) = 0 :=
    prog_pos_threshold_zero (T := T) (a := (1 : ℝ)) (by norm_num)
  have hprog : prog 1 (0 : Vec T) < T := by
    rw [hprog0]
    exact C.dim_pos
  have hunorm : 1 < ‖u‖ := by
    dsimp [u]
    exact C.terminal_gradient 0 hprog
  have hunormpos : 0 < ‖u‖ := lt_trans (by norm_num) hunorm
  have hcoef : 0 < P.ν * P.γ ^ 2 :=
    mul_pos (lift_nu_pos P) (sq_pos_of_pos P.γ_pos)
  have hx : ∀ Z : Bool,
      liftedGx P 0 0 Z - liftedGx P u 0 Z = (P.ν * P.γ ^ 2) • u := by
    intro Z
    unfold liftedGx
    module
  have hs := havg (0 : Vec T) (0 : Vec T) u (0 : Vec T)
  let A : ℝ := ‖(P.ν * P.γ ^ 2) • u‖ ^ 2
  let Bt : ℝ :=
    ‖liftedGy B P 0 0 true - liftedGy B P u 0 true‖ ^ 2
  let Bf : ℝ :=
    ‖liftedGy B P 0 0 false - liftedGy B P u 0 false‖ ^ 2
  have hs' : p * (A + Bt) + (1 - p) * (A + Bf) ≤ L ^ 2 * ‖u‖ ^ 2 := by
    simpa [OracleAveragedSmooth, bernoulliLaw, bernoulliExpectReal,
      liftedOracle, A, Bt, Bf, hx] using hs
  have h1p : 0 ≤ 1 - p := by linarith
  have hnoise : 0 ≤ p * Bt + (1 - p) * Bf :=
    add_nonneg (mul_nonneg hp0 (sq_nonneg _)) (mul_nonneg h1p (sq_nonneg _))
  have hsum : p * (A + Bt) + (1 - p) * (A + Bf) =
      A + (p * Bt + (1 - p) * Bf) := by ring
  rw [hsum] at hs'
  have hA : A ≤ L ^ 2 * ‖u‖ ^ 2 :=
    le_trans (le_add_of_nonneg_right hnoise) hs'
  have hAform : A = (P.ν * P.γ ^ 2) ^ 2 * ‖u‖ ^ 2 := by
    dsimp [A]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoef]
    ring
  rw [hAform] at hA
  have hnormsq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos hunormpos
  have hsq : (P.ν * P.γ ^ 2) ^ 2 ≤ L ^ 2 := by
    exact (mul_le_mul_right hnormsq).mp hA
  by_contra hnot
  have hgt : L < P.ν * P.γ ^ 2 := lt_of_not_ge hnot
  have hsumpos : 0 < P.ν * P.γ ^ 2 + L := add_pos_of_pos_of_nonneg hcoef hL0
  have hprod : 0 < (P.ν * P.γ ^ 2 - L) * (P.ν * P.γ ^ 2 + L) :=
    mul_pos (sub_pos.mpr hgt) hsumpos
  have hid :
      (P.ν * P.γ ^ 2 - L) * (P.ν * P.γ ^ 2 + L) =
        (P.ν * P.γ ^ 2) ^ 2 - L ^ 2 := by ring
  rw [hid] at hprod
  linarith

/-- For the canonical AS construction, every valid averaged-smooth constant is at least
`Lbar/4`.  This is the averaged-smooth analogue of the BV primal-only joint-smoothness lower
bracket. -/
theorem canonicalAS_averagedSmooth_lower {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters) (L : ℝ)
    (hL0 : 0 ≤ L)
    (havg : OracleAveragedSmooth (bernoulliLaw P.p) (canonicalASOracle C P) L) :
    P.Lbar / 4 ≤ L := by
  let W := canonicalASConstructionWitness C P
  have havg' : OracleAveragedSmooth (bernoulliLaw P.p) (liftedOracle W.B W.LP) L := by
    simpa [canonicalASOracle, asConstructedOracle, W] using havg
  have hbase := liftedOracle_averagedSmooth_lower_primal
    C W.B W.LP P.p L (le_of_lt P.p_pos) (as_p_le_one P) hL0 havg'
  have hbase' : P.ν * P.γ ^ 2 ≤ L := by
    rw [asWitness_nu_eq W, W.lift_gamma] at hbase
    exact hbase
  have hνmu : P.μ ≤ P.ν := by
    rw [ASParameters.ν]
    have hh : 0 ≤ P.h := le_of_lt (as_h_pos P)
    have hℓ : 0 ≤ ℓ₀ := by norm_num [ℓ₀]
    nlinarith [mul_nonneg hℓ hh]
  have hγsq : 0 ≤ P.γ ^ 2 := sq_nonneg P.γ
  have hmul : P.μ * P.γ ^ 2 ≤ P.ν * P.γ ^ 2 :=
    mul_le_mul_of_nonneg_right hνmu hγsq
  have hμγ : P.μ * P.γ ^ 2 = P.Lbar / 4 := by
    rw [P.γ_sq, P.κ_def]
    field_simp [ne_of_gt P.μ_pos]
    ring
  rw [hμγ] at hmul
  exact le_trans hmul hbase'

/-- The upper strong-concavity bracket of the AS lift is at most `3μ/2`. -/
theorem as_dual_curvature_upper (P : ASParameters) :
    P.ν + ℓ₀ * P.h ≤ 3 * P.μ / 2 := by
  have hh := as_h_le_mu_branch P
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  have hden : 0 < 4 * ℓ₀ := mul_pos (by norm_num) hℓ
  have hscaled := (le_div_iff₀ hden).1 hh
  have hℓh : ℓ₀ * P.h ≤ P.μ / 4 := by
    nlinarith [hscaled]
  rw [ASParameters.ν]
  nlinarith

/-- The AS upper strong-concavity bracket is strictly positive. -/
theorem as_dual_curvature_pos (P : ASParameters) :
    0 < P.ν + ℓ₀ * P.h := by
  rw [ASParameters.ν]
  have hh : 0 < P.h := as_h_pos P
  have hℓ : 0 < ℓ₀ := by norm_num [ℓ₀]
  nlinarith [mul_pos hℓ hh, P.μ_pos]

/-- Concrete actual averaged-condition-number certificate for the canonical AS hard instance.
The brackets are `Lbar/4 ≤ Lbar_act ≤ Lbar` and
`μ ≤ μ_act ≤ ν+ℓ₀h ≤ 3μ/2`. -/
noncomputable def canonicalASActualConditionNumberCertificate {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (Gate : SmoothGateCertificate mΓ) (hs0 : P.s₀ = universalS0 mΓ)
    (hκ : 8 ≤ P.κ) :
    ActualAveragedConditionNumberCertificate (canonicalASPopulation C P)
      (bernoulliLaw P.p) (canonicalASOracle C P) := by
  let W := canonicalASConstructionWitness C P
  have Hbase : ASBaseOracleCertificate T C P.p mΓ P.s₀ Gate :=
    canonicalASBaseOracleCertificate C Gate P hs0
  refine
    { LbarLo := P.Lbar / 4
      LbarHi := P.Lbar
      muLo := P.μ
      muHi := P.ν + ℓ₀ * P.h
      LbarLo_pos := div_pos P.Lbar_pos (by norm_num)
      LbarHi_pos := P.Lbar_pos
      muLo_pos := P.μ_pos
      muHi_pos := as_dual_curvature_pos P
      averaged_smooth_upper := ?_
      averaged_smooth_lower := ?_
      strong_lower := ?_
      strong_upper := ?_ }
  · have hout := asConstructedOracle_averagedSmooth W Hbase hκ
    simpa [canonicalASPopulation, canonicalASOracle, W] using hout
  · intro L hL0 hL
    exact canonicalAS_averagedSmooth_lower C P L hL0 hL
  · have hstrong := populationFromLift_stronglyConcaveY C W.B W.LP W.lift_properties
    have hstrong' : StronglyConcaveY
        (populationFromLift C W.B W.LP W.lift_properties) P.μ := by
      simpa [W.lift_mu] using hstrong
    simpa [canonicalASPopulation, asConstructedPopulation, W] using hstrong'
  · intro m hm
    have hm' : StronglyConcaveY
        (populationFromLift C W.B W.LP W.lift_properties) m := by
      simpa [canonicalASPopulation, asConstructedPopulation, W] using hm
    have hu := populationFromLift_strong_modulus_upper
      C W.B W.LP W.lift_properties m hm'
    rw [asWitness_nu_eq W, W.lift_h] at hu
    exact hu

/-- Universal condition-number constants for the AS construction. -/
def asKappaLowerConstant : ℝ := 1 / 8

def asKappaUpperConstant : ℝ := 1

theorem asKappaLowerConstant_pos : 0 < asKappaLowerConstant := by
  norm_num [asKappaLowerConstant]

theorem asKappaUpperConstant_pos : 0 < asKappaUpperConstant := by
  norm_num [asKappaUpperConstant]

/-- The canonical actual averaged condition number is `Θ(κ)`. -/
theorem canonicalASActualConditionNumber_scaling {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (Gate : SmoothGateCertificate mΓ) (hs0 : P.s₀ = universalS0 mΓ)
    (hκ : 8 ≤ P.κ) :
    let A := canonicalASActualConditionNumberCertificate C P Gate hs0 hκ
    asKappaLowerConstant * P.κ ≤ A.LbarLo / A.muHi ∧
      A.LbarHi / A.muLo ≤ asKappaUpperConstant * P.κ := by
  have hκpos : 0 < P.κ := by
    rw [P.κ_def]
    exact div_pos P.Lbar_pos P.μ_pos
  have hmuhi := as_dual_curvature_upper P
  have hmupos := as_dual_curvature_pos P
  have hκμ : P.κ * P.μ = P.Lbar := by
    rw [P.κ_def]
    field_simp [ne_of_gt P.μ_pos]
  dsimp [canonicalASActualConditionNumberCertificate,
    asKappaLowerConstant, asKappaUpperConstant]
  constructor
  · apply (le_div_iff₀ hmupos).2
    have hcoef : 0 ≤ (1 / 8 : ℝ) * P.κ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmuhi hcoef
    calc
      (1 / 8 : ℝ) * P.κ * (P.ν + ℓ₀ * P.h)
          ≤ (1 / 8 : ℝ) * P.κ * (3 * P.μ / 2) := by
            simpa [mul_assoc] using hmul
      _ = 3 * P.Lbar / 16 := by rw [← hκμ]; ring
      _ ≤ P.Lbar / 4 := by nlinarith [P.Lbar_pos]
  · simpa [P.κ_def]

/-- Section-4 origin correction, identical in scale to the bounded-variance case. -/
theorem as_origin_term_identity (P : ASParameters) :
    P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) = 8 * g₀ ^ 2 * P.ε ^ 2 / P.Lbar := by
  rw [P.q_sq, P.κ_def]
  have hL0 : P.Lbar ≠ 0 := ne_of_gt P.Lbar_pos
  have hμ0 : P.μ ≠ 0 := ne_of_gt P.μ_pos
  field_simp [hL0, hμ0]
  ring

/-- Exact real precursor of the AS chain length before resolving the two branches of `h`. -/
theorem as_chainScale_identity (P : ASParameters) :
    P.chainScale = P.Δ * P.h * P.κ / (64 * Δ₀ * P.ε ^ 2) := by
  rw [ASParameters.chainScale, ASParameters.α, P.q_sq]
  have hh0 : P.h ≠ 0 := ne_of_gt (as_h_pos P)
  have hκ0 : P.κ ≠ 0 := by
    rw [P.κ_def]
    exact ne_of_gt (div_pos P.Lbar_pos P.μ_pos)
  have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
  field_simp [hh0, hκ0, hε0]
  ring

/-- As in the BV branch, the floor relation alone makes the chain part of the primal gap at most
`Δ/4`. -/
theorem as_chain_gap_term_le_quarter {T : ℕ} (P : ASParameters)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1) :
    P.α * Δ₀ * T ≤ P.Δ / 4 := by
  have hα : 0 < P.α := by
    rw [ASParameters.α]
    exact div_pos (sq_pos_of_pos (as_q_pos P)) (as_h_pos P)
  have hΔ0 : 0 < Δ₀ := by norm_num [Δ₀]
  have hm := mul_le_mul_of_nonneg_left hfloor.1
    (mul_nonneg (le_of_lt hα) (le_of_lt hΔ0))
  have hscale : P.α * Δ₀ * P.chainScale = P.Δ / 4 := by
    rw [ASParameters.chainScale]
    field_simp [ne_of_gt hα]
    ring
  rw [hscale] at hm
  exact hm


/-! ## v37 proof phase XXVIII: AS numerical closure, floor witness, and per-parameter Lemma 4.3

The v36 phase closed the actual averaged-condition-number bracket and reduced the remaining
arithmetic in Lemma 4.3 to the two smallness assumptions in paper equation (28).  This phase fixes
explicit universal constants, proves that the real chain precursor is at least `16`, derives the
paper bounds (29)--(30), chooses the exact natural floor, and assembles a complete
`Lemma43Conclusion` for every fixed smooth-gate certificate.  The only item not discharged here is
the standalone analytic existence of a `SmoothGateCertificate` for the explicit bump-defined
`GammaGate`; no new axiom is introduced for that fact.

A small statement correction is made above: Lemma 4.3 now explicitly assumes `0 ≤ σ`.  This is
implicit in the paper because `σ` is a standard-deviation/variance-budget parameter and is already
an explicit hypothesis of Theorem 4.4.  Without this sign condition the second inequality in (28)
would be vacuous for negative `σ`, so the formal statement would be strictly stronger than the
paper and in fact false.
-/

/-- Universal `c₀` for Lemma 4.3.  The three branches respectively guarantee: the
strong-concavity branch of the chain scale is at least `16`, the `p=1` averaged-smooth branch is at
least `16`, and the origin correction is at most `Δ/2`. -/
def asLemma43C0 (s₀ : ℝ) : ℝ :=
  min (1 / (4096 * Δ₀ * ℓ₀))
    (min (1 / (512 * Δ₀ * s₀)) (1 / (16 * g₀ ^ 2)))

/-- Universal `c₁` for the genuinely stochastic `p<1` branch in equation (28). -/
def asLemma43C1 (s₀ : ℝ) : ℝ :=
  g₀ / (1024 * Δ₀ * s₀)

/-- Universal rate constant used in both equations (29) and (30). -/
def asLemma43C2 (s₀ : ℝ) : ℝ :=
  min (1 / (512 * Δ₀ * ℓ₀)) (1 / (512 * Δ₀ * s₀))

theorem asLemma43C0_pos {s₀ : ℝ} (hs₀ : 0 < s₀) : 0 < asLemma43C0 s₀ := by
  rw [asLemma43C0]
  apply lt_min
  · norm_num [Δ₀, ℓ₀]
  · apply lt_min
    · have hden : 0 < 512 * Δ₀ * s₀ := by
        norm_num [Δ₀]
        positivity
      positivity
    · norm_num [g₀]

theorem asLemma43C1_pos {s₀ : ℝ} (hs₀ : 0 < s₀) : 0 < asLemma43C1 s₀ := by
  rw [asLemma43C1]
  have hg : 0 < g₀ := by norm_num [g₀]
  have hden : 0 < 1024 * Δ₀ * s₀ := by
    norm_num [Δ₀]
    positivity
  exact div_pos hg hden

theorem asLemma43C2_pos {s₀ : ℝ} (hs₀ : 0 < s₀) : 0 < asLemma43C2 s₀ := by
  rw [asLemma43C2]
  apply lt_min
  · norm_num [Δ₀, ℓ₀]
  · have hden : 0 < 512 * Δ₀ * s₀ := by
      norm_num [Δ₀]
      positivity
    positivity

theorem asLemma43C0_le_mu (s₀ : ℝ) :
    asLemma43C0 s₀ ≤ 1 / (4096 * Δ₀ * ℓ₀) := by
  exact min_le_left _ _

theorem asLemma43C0_le_smooth (s₀ : ℝ) :
    asLemma43C0 s₀ ≤ 1 / (512 * Δ₀ * s₀) := by
  calc
    asLemma43C0 s₀ ≤ min (1 / (512 * Δ₀ * s₀)) (1 / (16 * g₀ ^ 2)) :=
      min_le_right _ _
    _ ≤ 1 / (512 * Δ₀ * s₀) := min_le_left _ _

theorem asLemma43C0_le_origin (s₀ : ℝ) :
    asLemma43C0 s₀ ≤ 1 / (16 * g₀ ^ 2) := by
  calc
    asLemma43C0 s₀ ≤ min (1 / (512 * Δ₀ * s₀)) (1 / (16 * g₀ ^ 2)) :=
      min_le_right _ _
    _ ≤ 1 / (16 * g₀ ^ 2) := min_le_right _ _

theorem asLemma43C2_le_mu (s₀ : ℝ) :
    asLemma43C2 s₀ ≤ 1 / (512 * Δ₀ * ℓ₀) := by
  exact min_le_left _ _

theorem asLemma43C2_le_smooth (s₀ : ℝ) :
    asLemma43C2 s₀ ≤ 1 / (512 * Δ₀ * s₀) := by
  exact min_le_right _ _

/-- The first equation-(28) smallness assumption forces a strictly positive gap budget. -/
theorem as_delta_pos_of_small (P : ASParameters)
    (hsmall : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ) :
    0 < P.Δ := by
  have hc0 : 0 < asLemma43C0 P.s₀ := asLemma43C0_pos P.s₀_pos
  have heps : 0 < P.ε ^ 2 := sq_pos_of_pos P.ε_pos
  have hrhs : 0 < (asLemma43C0 P.s₀ * P.Lbar) * P.Δ := by
    have h := lt_of_lt_of_le heps hsmall
    simpa [mul_assoc] using h
  have hcoef : 0 < asLemma43C0 P.s₀ * P.Lbar := mul_pos hc0 P.Lbar_pos
  by_contra hnot
  have hΔ : P.Δ ≤ 0 := le_of_not_gt hnot
  have hnonpos : (asLemma43C0 P.s₀ * P.Lbar) * P.Δ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hcoef) hΔ
  linarith

/-- The first smallness assumption simultaneously implies the three scalar inequalities used in
Lemma 4.3. -/
theorem as_small_accuracy_scales (P : ASParameters)
    (hsmall : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ) :
    (4096 * Δ₀ * ℓ₀) * P.ε ^ 2 ≤ P.Lbar * P.Δ ∧
      (512 * Δ₀ * P.s₀) * P.ε ^ 2 ≤ P.Lbar * P.Δ ∧
      (16 * g₀ ^ 2) * P.ε ^ 2 ≤ P.Lbar * P.Δ := by
  have hΔ : 0 < P.Δ := as_delta_pos_of_small P hsmall
  have hLD : 0 ≤ P.Lbar * P.Δ := mul_nonneg (le_of_lt P.Lbar_pos) (le_of_lt hΔ)
  have aux : ∀ (c D : ℝ),
      asLemma43C0 P.s₀ ≤ c → 0 < D → c = 1 / D →
      D * P.ε ^ 2 ≤ P.Lbar * P.Δ := by
    intro c D hc hD hcD
    have hm := mul_le_mul_of_nonneg_right hc hLD
    have he : P.ε ^ 2 ≤ c * (P.Lbar * P.Δ) := by
      calc
        P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ := hsmall
        _ = asLemma43C0 P.s₀ * (P.Lbar * P.Δ) := by ring
        _ ≤ c * (P.Lbar * P.Δ) := hm
    have he' : P.ε ^ 2 ≤ (P.Lbar * P.Δ) / D := by
      rw [hcD] at he
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using he
    simpa [mul_comm] using (le_div_iff₀ hD).1 he'
  constructor
  · apply aux (1 / (4096 * Δ₀ * ℓ₀)) (4096 * Δ₀ * ℓ₀)
    · exact asLemma43C0_le_mu P.s₀
    · norm_num [Δ₀, ℓ₀]
    · rfl
  · constructor
    · apply aux (1 / (512 * Δ₀ * P.s₀)) (512 * Δ₀ * P.s₀)
      · exact asLemma43C0_le_smooth P.s₀
      · exact mul_pos (mul_pos (by norm_num) (by norm_num [Δ₀])) P.s₀_pos
      · rfl
    · apply aux (1 / (16 * g₀ ^ 2)) (16 * g₀ ^ 2)
      · exact asLemma43C0_le_origin P.s₀
      · norm_num [g₀]
      · rfl

/-- The origin term in equation (12) is at most `Δ/2` in the AS construction. -/
theorem as_origin_term_le_half_delta (P : ASParameters)
    (hsmall : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ) :
    P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ / 2 := by
  rw [as_origin_term_identity P]
  have hs := (as_small_accuracy_scales P hsmall).2.2
  apply (div_le_iff₀ P.Lbar_pos).2
  nlinarith

/-- Exact first branch of the real chain precursor `B` in the proof of Lemma 4.3. -/
theorem as_chainScale_eq_mu_branch (P : ASParameters)
    (hbranch : P.μ / (4 * ℓ₀) ≤ P.Lbar * Real.sqrt P.p / (4 * P.s₀)) :
    P.chainScale = P.Lbar * P.Δ / (256 * Δ₀ * ℓ₀ * P.ε ^ 2) := by
  rw [as_chainScale_identity P, ASParameters.h, min_eq_left hbranch]
  have hμκ : P.μ * P.κ = P.Lbar := by
    rw [P.κ_def]
    field_simp [ne_of_gt P.μ_pos] <;> ring
  calc
    P.Δ * (P.μ / (4 * ℓ₀)) * P.κ / (64 * Δ₀ * P.ε ^ 2) =
        P.Δ * (P.μ * P.κ) / (256 * Δ₀ * ℓ₀ * P.ε ^ 2) := by
          norm_num [Δ₀, ℓ₀] <;> ring
    _ = P.Lbar * P.Δ / (256 * Δ₀ * ℓ₀ * P.ε ^ 2) := by
          rw [hμκ]
          ring

/-- Exact second branch of the real chain precursor `B`. -/
theorem as_chainScale_eq_smooth_branch (P : ASParameters)
    (hbranch : P.Lbar * Real.sqrt P.p / (4 * P.s₀) ≤ P.μ / (4 * ℓ₀)) :
    P.chainScale =
      P.Lbar * P.Δ * P.κ * Real.sqrt P.p /
        (256 * Δ₀ * P.s₀ * P.ε ^ 2) := by
  rw [as_chainScale_identity P, ASParameters.h, min_eq_right hbranch]
  have hs0 : P.s₀ ≠ 0 := ne_of_gt P.s₀_pos
  have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
  field_simp [hs0, hε0]
  ring

/-- Since `γ²=κ/4` and `γ>0`, the canonical scaling has `sqrt κ = 2γ`. -/
theorem as_sqrt_kappa_eq_two_gamma (P : ASParameters) :
    Real.sqrt P.κ = 2 * P.γ := by
  have hκpos : 0 < P.κ := by
    rw [P.κ_def]
    exact div_pos P.Lbar_pos P.μ_pos
  have hsqrt_sq : (Real.sqrt P.κ) ^ 2 = P.κ :=
    Real.sq_sqrt (le_of_lt hκpos)
  have hgamma_sq : (2 * P.γ) ^ 2 = P.κ := by
    nlinarith [P.γ_sq]
  have hsqrt_nonneg : 0 ≤ Real.sqrt P.κ := Real.sqrt_nonneg _
  have hgamma_nonneg : 0 ≤ 2 * P.γ := by nlinarith [P.γ_pos]
  nlinarith

/-- A convenient exact form of the `q=4ε/sqrt κ` scaling. -/
theorem as_kappa_mul_q_eq_four_eps_sqrt (P : ASParameters) :
    P.κ * P.q = 4 * P.ε * Real.sqrt P.κ := by
  have hκeq : P.κ = 4 * P.γ ^ 2 := by
    nlinarith [P.γ_sq]
  have hγ0 : P.γ ≠ 0 := ne_of_gt P.γ_pos
  rw [P.q_def, as_sqrt_kappa_eq_two_gamma P, hκeq]
  field_simp [hγ0] <;> ring

/-- In the stochastic branch `p<1`, the exact equation-(25) square-root relation is
`sqrt p = q g₀ / σ`. -/
theorem as_sqrt_p_eq_qg_div_sigma (P : ASParameters)
    (hσ0 : 0 ≤ P.σ) (hp1 : P.p < 1) :
    Real.sqrt P.p = P.q * g₀ / P.σ := by
  have hσne : P.σ ≠ 0 := by
    intro hσ
    have hp := as_p_eq_one_of_sigma_zero P hσ
    linarith
  have hσpos : 0 < P.σ := lt_of_le_of_ne hσ0 (Ne.symm hσne)
  have hratio_le : P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2 ≤ 1 := by
    by_contra hnot
    have hge : 1 ≤ P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2 := le_of_not_ge hnot
    have hpone : P.p = 1 := by
      rw [as_p_eq_min_of_sigma_ne_zero P hσne, min_eq_left hge]
    linarith
  have hp : P.p = P.q ^ 2 * g₀ ^ 2 / P.σ ^ 2 := by
    rw [as_p_eq_min_of_sigma_ne_zero P hσne, min_eq_right hratio_le]
  have hsqrt_sq : (Real.sqrt P.p) ^ 2 = P.p := Real.sq_sqrt (le_of_lt P.p_pos)
  have hratio_sq : (P.q * g₀ / P.σ) ^ 2 = P.p := by
    rw [hp]
    field_simp [hσne]
    ring
  have hratio_pos : 0 < P.q * g₀ / P.σ := by
    have hg : 0 < g₀ := by norm_num [g₀]
    exact div_pos (mul_pos (as_q_pos P) hg) hσpos
  have hprod :
      (Real.sqrt P.p - P.q * g₀ / P.σ) *
          (Real.sqrt P.p + P.q * g₀ / P.σ) = 0 := by
    calc
      (Real.sqrt P.p - P.q * g₀ / P.σ) *
          (Real.sqrt P.p + P.q * g₀ / P.σ) =
          (Real.sqrt P.p) ^ 2 - (P.q * g₀ / P.σ) ^ 2 := by ring
      _ = 0 := by rw [hsqrt_sq, hratio_sq]; ring
  have hsumpos : 0 < Real.sqrt P.p + P.q * g₀ / P.σ :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hratio_pos
  have hdiff : Real.sqrt P.p - P.q * g₀ / P.σ = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hsumpos)
  linarith

/-- Smooth-branch chain scale after substituting the exact stochastic `p<1` relation. -/
theorem as_chainScale_eq_smooth_stochastic (P : ASParameters)
    (hσ0 : 0 ≤ P.σ) (hp1 : P.p < 1)
    (hbranch : P.Lbar * Real.sqrt P.p / (4 * P.s₀) ≤ P.μ / (4 * ℓ₀)) :
    P.chainScale =
      g₀ * P.Lbar * P.Δ * Real.sqrt P.κ /
        (64 * Δ₀ * P.s₀ * P.ε * P.σ) := by
  rw [as_chainScale_eq_smooth_branch P hbranch,
    as_sqrt_p_eq_qg_div_sigma P hσ0 hp1]
  have hkq := as_kappa_mul_q_eq_four_eps_sqrt P
  have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
  have hs0 : P.s₀ ≠ 0 := ne_of_gt P.s₀_pos
  have hσne : P.σ ≠ 0 := by
    intro hσ
    have hp := as_p_eq_one_of_sigma_zero P hσ
    linarith
  have hσpos : 0 < P.σ := lt_of_le_of_ne hσ0 (Ne.symm hσne)
  calc
    P.Lbar * P.Δ * P.κ * (P.q * g₀ / P.σ) /
          (256 * Δ₀ * P.s₀ * P.ε ^ 2) =
        P.Lbar * P.Δ * (P.κ * P.q) * g₀ /
          (256 * Δ₀ * P.s₀ * P.ε ^ 2 * P.σ) := by
            field_simp [hε0, hs0, hσne] <;> ring
    _ = P.Lbar * P.Δ * (4 * P.ε * Real.sqrt P.κ) * g₀ /
          (256 * Δ₀ * P.s₀ * P.ε ^ 2 * P.σ) := by rw [hkq]
    _ = g₀ * P.Lbar * P.Δ * Real.sqrt P.κ /
          (64 * Δ₀ * P.s₀ * P.ε * P.σ) := by
            have hD1 : 256 * Δ₀ * P.s₀ * P.ε ^ 2 * P.σ ≠ 0 := by
              exact ne_of_gt (mul_pos
                (mul_pos
                  (mul_pos
                    (mul_pos (by norm_num) (by norm_num [Δ₀])) P.s₀_pos)
                  (sq_pos_of_pos P.ε_pos))
                hσpos)
            have hD2 : 64 * Δ₀ * P.s₀ * P.ε * P.σ ≠ 0 := by
              exact ne_of_gt (mul_pos
                (mul_pos
                  (mul_pos
                    (mul_pos (by norm_num) (by norm_num [Δ₀])) P.s₀_pos)
                  P.ε_pos)
                hσpos)
            apply (div_eq_div_iff hD1 hD2).2
            ring

/-- The two equation-(28) hypotheses make the real precursor `B` at least `16`. -/
theorem as_chainScale_ge_sixteen (P : ASParameters)
    (hσ0 : 0 ≤ P.σ) (hκ : 8 ≤ P.κ)
    (hsmall0 : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ)
    (hsmall1 : P.ε * P.σ ≤
      asLemma43C1 P.s₀ * P.Lbar * P.Δ * Real.sqrt P.κ) :
    16 ≤ P.chainScale := by
  have hΔ : 0 < P.Δ := as_delta_pos_of_small P hsmall0
  have hLD : 0 ≤ P.Lbar * P.Δ := mul_nonneg (le_of_lt P.Lbar_pos) (le_of_lt hΔ)
  have hscales := as_small_accuracy_scales P hsmall0
  by_cases hb : P.μ / (4 * ℓ₀) ≤ P.Lbar * Real.sqrt P.p / (4 * P.s₀)
  · rw [as_chainScale_eq_mu_branch P hb]
    have hden : 0 < 256 * Δ₀ * ℓ₀ * P.ε ^ 2 := by
      exact mul_pos
        (mul_pos (mul_pos (by norm_num) (by norm_num [Δ₀])) (by norm_num [ℓ₀]))
        (sq_pos_of_pos P.ε_pos)
    apply (le_div_iff₀ hden).2
    calc
      16 * (256 * Δ₀ * ℓ₀ * P.ε ^ 2) =
          (4096 * Δ₀ * ℓ₀) * P.ε ^ 2 := by ring
      _ ≤ P.Lbar * P.Δ := hscales.1
  · have hb' : P.Lbar * Real.sqrt P.p / (4 * P.s₀) ≤ P.μ / (4 * ℓ₀) :=
      le_of_not_ge hb
    by_cases hpone : P.p = 1
    · rw [as_chainScale_eq_smooth_branch P hb', hpone]
      norm_num
      have hden : 0 < 256 * Δ₀ * P.s₀ * P.ε ^ 2 := by
        exact mul_pos
          (mul_pos (mul_pos (by norm_num) (by norm_num [Δ₀])) P.s₀_pos)
          (sq_pos_of_pos P.ε_pos)
      apply (le_div_iff₀ hden).2
      calc
        16 * (256 * Δ₀ * P.s₀ * P.ε ^ 2) =
            8 * ((512 * Δ₀ * P.s₀) * P.ε ^ 2) := by ring
        _ ≤ 8 * (P.Lbar * P.Δ) :=
          mul_le_mul_of_nonneg_left hscales.2.1 (by norm_num)
        _ ≤ P.κ * (P.Lbar * P.Δ) :=
          mul_le_mul_of_nonneg_right hκ hLD
        _ = P.Lbar * P.Δ * P.κ := by ring
    · have hp1 : P.p < 1 := lt_of_le_of_ne (as_p_le_one P) hpone
      rw [as_chainScale_eq_smooth_stochastic P hσ0 hp1 hb']
      have hσpos : 0 < P.σ := by
        have hσne : P.σ ≠ 0 := by
          intro hσ
          have hp := as_p_eq_one_of_sigma_zero P hσ
          linarith
        exact lt_of_le_of_ne hσ0 (Ne.symm hσne)
      have hden : 0 < 64 * Δ₀ * P.s₀ * P.ε * P.σ := by
        exact mul_pos
          (mul_pos
            (mul_pos (mul_pos (by norm_num) (by norm_num [Δ₀])) P.s₀_pos)
            P.ε_pos)
          hσpos
      apply (le_div_iff₀ hden).2
      have hfac : 0 < 1024 * Δ₀ * P.s₀ := by
        exact mul_pos (mul_pos (by norm_num) (by norm_num [Δ₀])) P.s₀_pos
      have hm := mul_le_mul_of_nonneg_left hsmall1 (le_of_lt hfac)
      calc
        16 * (64 * Δ₀ * P.s₀ * P.ε * P.σ) =
            (1024 * Δ₀ * P.s₀) * (P.ε * P.σ) := by ring
        _ ≤ (1024 * Δ₀ * P.s₀) *
              (asLemma43C1 P.s₀ * P.Lbar * P.Δ * Real.sqrt P.κ) := hm
        _ = g₀ * P.Lbar * P.Δ * Real.sqrt P.κ := by
          rw [asLemma43C1]
          field_simp [ne_of_gt hfac]

/-- Equation (29) follows from the exact floor interval and the two branches defining `h`. -/
theorem as_eq29_of_floor {T : ℕ} (P : ASParameters)
    (hΔ : 0 ≤ P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1)
    (hscale16 : 16 ≤ P.chainScale) :
    asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
      min 1 (P.κ * Real.sqrt P.p) ≤ T := by
  have hhalf : P.chainScale / 2 ≤ (T : ℝ) :=
    floor_interval_ge_half hfloor (by linarith [hscale16])
  have hbase : 0 ≤ P.Lbar * P.Δ / P.ε ^ 2 := by
    exact div_nonneg (mul_nonneg (le_of_lt P.Lbar_pos) hΔ) (sq_nonneg P.ε)
  have hc2 : 0 ≤ asLemma43C2 P.s₀ := le_of_lt (asLemma43C2_pos P.s₀_pos)
  have ht : 0 ≤ P.κ * Real.sqrt P.p := by
    have hκ0 : 0 ≤ P.κ := by
      rw [P.κ_def]
      exact le_of_lt (div_pos P.Lbar_pos P.μ_pos)
    exact mul_nonneg hκ0 (Real.sqrt_nonneg _)
  by_cases hb : P.μ / (4 * ℓ₀) ≤ P.Lbar * Real.sqrt P.p / (4 * P.s₀)
  · have hmin := min_le_left (1 : ℝ) (P.κ * Real.sqrt P.p)
    have hcoef : 0 ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) :=
      mul_nonneg hc2 hbase
    have hc := asLemma43C2_le_mu P.s₀
    have hmul := mul_le_mul_of_nonneg_right hc hbase
    have heq :
        (1 / (512 * Δ₀ * ℓ₀)) * (P.Lbar * P.Δ / P.ε ^ 2) =
          P.chainScale / 2 := by
      rw [as_chainScale_eq_mu_branch P hb]
      have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
      field_simp [hε0]
      ring
    calc
      asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
          min 1 (P.κ * Real.sqrt P.p)
          ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hmin hcoef
      _ = asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) := by ring
      _ ≤ (1 / (512 * Δ₀ * ℓ₀)) * (P.Lbar * P.Δ / P.ε ^ 2) := hmul
      _ = P.chainScale / 2 := heq
      _ ≤ (T : ℝ) := hhalf
  · have hb' : P.Lbar * Real.sqrt P.p / (4 * P.s₀) ≤ P.μ / (4 * ℓ₀) :=
      le_of_not_ge hb
    have hmin := min_le_right (1 : ℝ) (P.κ * Real.sqrt P.p)
    have hcoef : 0 ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) :=
      mul_nonneg hc2 hbase
    have hc := asLemma43C2_le_smooth P.s₀
    have hmul := mul_le_mul_of_nonneg_right hc hbase
    have hmul2 := mul_le_mul_of_nonneg_right hmul ht
    have heq :
        (1 / (512 * Δ₀ * P.s₀)) * (P.Lbar * P.Δ / P.ε ^ 2) *
            (P.κ * Real.sqrt P.p) = P.chainScale / 2 := by
      rw [as_chainScale_eq_smooth_branch P hb']
      have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
      have hs0 : P.s₀ ≠ 0 := ne_of_gt P.s₀_pos
      field_simp [hε0, hs0]
      ring
    calc
      asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
          min 1 (P.κ * Real.sqrt P.p)
          ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
              (P.κ * Real.sqrt P.p) := mul_le_mul_of_nonneg_left hmin hcoef
      _ ≤ (1 / (512 * Δ₀ * P.s₀)) * (P.Lbar * P.Δ / P.ε ^ 2) *
              (P.κ * Real.sqrt P.p) := hmul2
      _ = P.chainScale / 2 := heq
      _ ≤ (T : ℝ) := hhalf

/-- Equation (30) is the corresponding floor bound after dividing by the positive reveal
probability. -/
theorem as_eq30_of_floor {T : ℕ} (P : ASParameters)
    (hΔ : 0 ≤ P.Δ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1)
    (hscale16 : 16 ≤ P.chainScale) :
    asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
      min (1 / P.p) (P.κ / Real.sqrt P.p) ≤ (T : ℝ) / P.p := by
  have hhalf : P.chainScale / 2 ≤ (T : ℝ) :=
    floor_interval_ge_half hfloor (by linarith [hscale16])
  have hhalfdiv : P.chainScale / (2 * P.p) ≤ (T : ℝ) / P.p := by
    have hp0' : 0 < P.p := as_p_pos P
    have hfac : 0 ≤ 1 / P.p := by positivity
    have hm := mul_le_mul_of_nonneg_right hhalf hfac
    calc
      P.chainScale / (2 * P.p) = (P.chainScale / 2) * (1 / P.p) := by
        field_simp [ne_of_gt hp0']
      _ ≤ (T : ℝ) * (1 / P.p) := hm
      _ = (T : ℝ) / P.p := by ring
  have hbase : 0 ≤ P.Lbar * P.Δ / P.ε ^ 2 := by
    exact div_nonneg (mul_nonneg (le_of_lt P.Lbar_pos) hΔ) (sq_nonneg P.ε)
  have hc2 : 0 ≤ asLemma43C2 P.s₀ := le_of_lt (asLemma43C2_pos P.s₀_pos)
  have hp0 : 0 < P.p := as_p_pos P
  have hsqrt : 0 < Real.sqrt P.p := Real.sqrt_pos.2 hp0
  by_cases hb : P.μ / (4 * ℓ₀) ≤ P.Lbar * Real.sqrt P.p / (4 * P.s₀)
  · have hmin := min_le_left (1 / P.p) (P.κ / Real.sqrt P.p)
    have hcoef : 0 ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) :=
      mul_nonneg hc2 hbase
    have hc := asLemma43C2_le_mu P.s₀
    have hmul := mul_le_mul_of_nonneg_right hc hbase
    have h1p : 0 ≤ 1 / P.p := by positivity
    have hmul2 := mul_le_mul_of_nonneg_right hmul h1p
    have heq :
        (1 / (512 * Δ₀ * ℓ₀)) * (P.Lbar * P.Δ / P.ε ^ 2) * (1 / P.p) =
          P.chainScale / (2 * P.p) := by
      rw [as_chainScale_eq_mu_branch P hb]
      have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
      have hpne : P.p ≠ 0 := ne_of_gt hp0
      field_simp [hε0, hpne]
      ring
    calc
      asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
          min (1 / P.p) (P.κ / Real.sqrt P.p)
          ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) * (1 / P.p) :=
            mul_le_mul_of_nonneg_left hmin hcoef
      _ ≤ (1 / (512 * Δ₀ * ℓ₀)) * (P.Lbar * P.Δ / P.ε ^ 2) * (1 / P.p) := hmul2
      _ = P.chainScale / (2 * P.p) := heq
      _ ≤ (T : ℝ) / P.p := hhalfdiv
  · have hb' : P.Lbar * Real.sqrt P.p / (4 * P.s₀) ≤ P.μ / (4 * ℓ₀) :=
      le_of_not_ge hb
    have hmin := min_le_right (1 / P.p) (P.κ / Real.sqrt P.p)
    have hcoef : 0 ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) :=
      mul_nonneg hc2 hbase
    have hc := asLemma43C2_le_smooth P.s₀
    have hmul := mul_le_mul_of_nonneg_right hc hbase
    have hkr : 0 ≤ P.κ / Real.sqrt P.p := by
      have hκ0 : 0 ≤ P.κ := by
        rw [P.κ_def]
        exact le_of_lt (div_pos P.Lbar_pos P.μ_pos)
      exact div_nonneg hκ0 (le_of_lt hsqrt)
    have hmul2 := mul_le_mul_of_nonneg_right hmul hkr
    have hsqrt_div_p : Real.sqrt P.p / P.p = 1 / Real.sqrt P.p := by
      have hpne : P.p ≠ 0 := ne_of_gt hp0
      have hsqrtn : Real.sqrt P.p ≠ 0 := ne_of_gt hsqrt
      apply (div_eq_iff hpne).2
      field_simp [hsqrtn]
    have hkrel :
        (P.κ * Real.sqrt P.p) / P.p = P.κ / Real.sqrt P.p := by
      calc
        (P.κ * Real.sqrt P.p) / P.p = P.κ * (Real.sqrt P.p / P.p) := by ring
        _ = P.κ * (1 / Real.sqrt P.p) := by rw [hsqrt_div_p]
        _ = P.κ / Real.sqrt P.p := by ring
    have heq :
        (1 / (512 * Δ₀ * P.s₀)) * (P.Lbar * P.Δ / P.ε ^ 2) *
            (P.κ / Real.sqrt P.p) = P.chainScale / (2 * P.p) := by
      rw [← hkrel, as_chainScale_eq_smooth_branch P hb']
      have hε0 : P.ε ≠ 0 := ne_of_gt P.ε_pos
      have hs0 : P.s₀ ≠ 0 := ne_of_gt P.s₀_pos
      have hpne : P.p ≠ 0 := ne_of_gt hp0
      field_simp [hε0, hs0, hpne]
      ring
    calc
      asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
          min (1 / P.p) (P.κ / Real.sqrt P.p)
          ≤ asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
              (P.κ / Real.sqrt P.p) := mul_le_mul_of_nonneg_left hmin hcoef
      _ ≤ (1 / (512 * Δ₀ * P.s₀)) * (P.Lbar * P.Δ / P.ε ^ 2) *
              (P.κ / Real.sqrt P.p) := hmul2
      _ = P.chainScale / (2 * P.p) := heq
      _ ≤ (T : ℝ) / P.p := hhalfdiv

/-- All numerical conclusions of Lemma 4.3 from the exact floor interval and equation (28). -/
theorem canonicalAS_numerical_closure {T : ℕ} (P : ASParameters)
    (hσ0 : 0 ≤ P.σ) (hκ : 8 ≤ P.κ)
    (hsmall0 : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ)
    (hsmall1 : P.ε * P.σ ≤
      asLemma43C1 P.s₀ * P.Lbar * P.Δ * Real.sqrt P.κ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1) :
    (P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ) ∧
      8 ≤ T ∧
      asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
        min 1 (P.κ * Real.sqrt P.p) ≤ T ∧
      asLemma43C2 P.s₀ * (P.Lbar * P.Δ / P.ε ^ 2) *
        min (1 / P.p) (P.κ / Real.sqrt P.p) ≤ (T : ℝ) / P.p := by
  have hΔ : 0 < P.Δ := as_delta_pos_of_small P hsmall0
  have hA16 := as_chainScale_ge_sixteen P hσ0 hκ hsmall0 hsmall1
  have hT8 := floor_interval_ge_eight hfloor hA16
  have hchain := as_chain_gap_term_le_quarter P hfloor
  have horigin := as_origin_term_le_half_delta P hsmall0
  have hgap : P.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ := by
    linarith
  have heq29 := as_eq29_of_floor P (le_of_lt hΔ) hfloor hA16
  have heq30 := as_eq30_of_floor P (le_of_lt hΔ) hfloor hA16
  exact ⟨hgap, hT8, heq29, heq30⟩

/-- Canonical Lemma-4.3 conclusion once the floor length is fixed. -/
noncomputable def canonicalLemma43Conclusion_of_floor {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (Gate : SmoothGateCertificate mΓ) (hs0 : P.s₀ = universalS0 mΓ)
    (hσ0 : 0 ≤ P.σ) (hκ : 8 ≤ P.κ)
    (hsmall0 : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ)
    (hsmall1 : P.ε * P.σ ≤
      asLemma43C1 P.s₀ * P.Lbar * P.Δ * Real.sqrt P.κ)
    (hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1) :
    Lemma43Conclusion C P (canonicalASConstructionWitness C P) mΓ Gate
      (asLemma43C2 P.s₀) asKappaLowerConstant asKappaUpperConstant := by
  have hnum := canonicalAS_numerical_closure P hσ0 hκ hsmall0 hsmall1 hfloor
  have Hbase := canonicalASBaseOracleCertificate C Gate P hs0
  let Acond := canonicalASActualConditionNumberCertificate C P Gate hs0 hκ
  have hcond := canonicalASActualConditionNumber_scaling C P Gate hs0 hκ
  exact lemma43Conclusion_of_core C P (canonicalASConstructionWitness C P)
    mΓ Gate (asLemma43C2 P.s₀) asKappaLowerConstant asKappaUpperConstant hκ
    Hbase hs0 hnum.1 hfloor hnum.2.1 hnum.2.2.1 hnum.2.2.2 Acond hcond

/-- The exact natural floor length in paper equation (26). -/
def canonicalASChainLength (P : ASParameters) : ℕ :=
  ⌊P.chainScale⌋₊

theorem canonicalASChainLength_floor (P : ASParameters)
    (hscale : 0 ≤ P.chainScale) :
    (canonicalASChainLength P : ℝ) ≤ P.chainScale ∧
      P.chainScale < (canonicalASChainLength P : ℝ) + 1 := by
  constructor
  · simpa [canonicalASChainLength] using (Nat.floor_le hscale)
  · simpa [canonicalASChainLength] using (Nat.lt_floor_add_one P.chainScale)

/-- Fully instantiated per-parameter form of Lemma 4.3, conditional only on the fixed universal
smooth-gate certificate. -/
theorem canonicalLemma43_for_parameters {mΓ : ℝ}
    (Gate : SmoothGateCertificate mΓ) (P : ASParameters)
    (hs0 : P.s₀ = universalS0 mΓ)
    (hσ0 : 0 ≤ P.σ) (hκ : 8 ≤ P.κ)
    (hsmall0 : P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ)
    (hsmall1 : P.ε * P.σ ≤
      asLemma43C1 P.s₀ * P.Lbar * P.Δ * Real.sqrt P.κ) :
    ∃ (T : ℕ) (C : ExplicitZeroChainCertificate T)
      (W : ASConstructionWitness C P),
      Nonempty (Lemma43Conclusion C P W mΓ Gate
        (asLemma43C2 P.s₀) asKappaLowerConstant asKappaUpperConstant) := by
  let T : ℕ := canonicalASChainLength P
  have hA16 := as_chainScale_ge_sixteen P hσ0 hκ hsmall0 hsmall1
  have hA0 : 0 ≤ P.chainScale := by linarith
  have hfloor : (T : ℝ) ≤ P.chainScale ∧ P.chainScale < (T : ℝ) + 1 := by
    dsimp [T]
    exact canonicalASChainLength_floor P hA0
  have hT8 := floor_interval_ge_eight hfloor hA16
  have hT2 : 2 ≤ T := by omega
  rcases importedLemma21Certificate T hT2 with ⟨C⟩
  refine ⟨T, C, canonicalASConstructionWitness C P, ?_⟩
  exact ⟨canonicalLemma43Conclusion_of_floor C P Gate hs0 hσ0 hκ
    hsmall0 hsmall1 hfloor⟩


end PaperExact

end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

/-! ## v38 proof phase XXIX: analytic construction of the universal smooth gate

This phase discharges the last standalone analytic input in Lemma 4.3.  The compactly supported
bump `LambdaGate` is identified with mathlib's smooth `expNegInvGlue` composed with the quadratic
window `100 (s-1/4) (1/2-s)`.  This gives continuity and interval integrability for free.  The
normalizing denominator is then shown strictly positive, and the normalized primitive `GammaGate`
is proved to be a `[0,1]`-valued globally Lipschitz step.  Finally these scalar facts are lifted to
the exact `ThetaGate` sandwich in equation (20).
-/

/-- The quadratic window appearing in the compactly supported bump. -/
def gateWindow (s : ℝ) : ℝ :=
  100 * (s - 1 / 4) * (1 / 2 - s)

/-- `LambdaGate` is exactly mathlib's standard smooth glued exponential applied to the quadratic
window.  This avoids any boundary-by-boundary continuity argument at `1/4` and `1/2`. -/
theorem lambdaGate_eq_expNegInvGlue (s : ℝ) :
    LambdaGate s = expNegInvGlue (gateWindow s) := by
  unfold LambdaGate gateWindow expNegInvGlue
  by_cases h : 1 / 4 < s ∧ s < 1 / 2
  · have hx : 0 < 100 * (s - 1 / 4) * (1 / 2 - s) := by
      have h100 : (0 : ℝ) < 100 := by norm_num
      exact mul_pos (mul_pos h100 (sub_pos.mpr h.1)) (sub_pos.mpr h.2)
    rw [if_pos h, if_neg (not_le.mpr hx)]
    congr 1
    simp [div_eq_mul_inv]
  · have hout : s ≤ 1 / 4 ∨ 1 / 2 ≤ s := by
      by_cases hs : s ≤ 1 / 4
      · exact Or.inl hs
      · right
        by_contra hhi
        exact h ⟨lt_of_not_ge hs, lt_of_not_ge hhi⟩
    have hx : 100 * (s - 1 / 4) * (1 / 2 - s) ≤ 0 := by
      rcases hout with hs | hs
      · have h1 : s - 1 / 4 ≤ 0 := sub_nonpos.mpr hs
        have h2 : 0 ≤ 1 / 2 - s := by linarith
        have hprod : (s - 1 / 4) * (1 / 2 - s) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h1 h2
        nlinarith
      · have h1 : 0 ≤ s - 1 / 4 := by linarith
        have h2 : 1 / 2 - s ≤ 0 := sub_nonpos.mpr hs
        have hprod : (s - 1 / 4) * (1 / 2 - s) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h1 h2
        nlinarith
    rw [if_neg h, if_pos hx]

/-- The paper bump is continuous on the whole line. -/
theorem lambdaGate_continuous : Continuous LambdaGate := by
  have hglue : Continuous expNegInvGlue := (@expNegInvGlue.contDiff 0).continuous
  have hwin : Continuous gateWindow := by
    unfold gateWindow
    fun_prop
  have heq : LambdaGate = fun s => expNegInvGlue (gateWindow s) := by
    funext s
    exact lambdaGate_eq_expNegInvGlue s
  rw [heq]
  exact hglue.comp hwin

/-- The paper bump is interval-integrable on every finite real interval. -/
theorem lambdaGate_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable LambdaGate MeasureTheory.volume a b :=
  lambdaGate_continuous.intervalIntegrable a b

/-- The bump is globally nonnegative. -/
theorem lambdaGate_nonneg (s : ℝ) : 0 ≤ LambdaGate s := by
  rw [lambdaGate_eq_expNegInvGlue]
  exact expNegInvGlue.nonneg _

/-- The bump is bounded by one. -/
theorem lambdaGate_le_one (s : ℝ) : LambdaGate s ≤ 1 := by
  rw [lambdaGate_eq_expNegInvGlue]
  by_cases hx : gateWindow s ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    norm_num
  · have hxpos : 0 < gateWindow s := lt_of_not_ge hx
    simp only [expNegInvGlue, if_neg (not_le.mpr hxpos)]
    rw [Real.exp_le_one_iff]
    have hinv : 0 ≤ (gateWindow s)⁻¹ := inv_nonneg.mpr hxpos.le
    linarith

/-- The bump vanishes to the left of its support. -/
theorem lambdaGate_zero_of_le_quarter {s : ℝ} (hs : s ≤ 1 / 4) :
    LambdaGate s = 0 := by
  unfold LambdaGate
  rw [if_neg (by
    intro hmem
    exact (not_lt_of_ge hs) hmem.1)]

/-- The bump vanishes to the right of its support. -/
theorem lambdaGate_zero_of_half_le {s : ℝ} (hs : 1 / 2 ≤ s) :
    LambdaGate s = 0 := by
  unfold LambdaGate
  rw [if_neg (by
    intro hmem
    exact (not_lt_of_ge hs) hmem.2)]

/-- The bump is strictly positive in the open transition interval. -/
theorem lambdaGate_pos_of_mem_Ioo {s : ℝ}
    (hs : s ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    0 < LambdaGate s := by
  have hs' : (1 / 4 : ℝ) < s ∧ s < (1 / 2 : ℝ) := by
    simpa only [Set.mem_Ioo] using hs
  unfold LambdaGate
  rw [if_pos hs']
  exact Real.exp_pos _

/-- Normalizing integral in the definition of `GammaGate`. -/
noncomputable def gateDenom : ℝ :=
  ∫ s in (1 / 4 : ℝ)..(1 / 2 : ℝ), LambdaGate s

/-- The normalizing integral is strictly positive. -/
theorem gateDenom_pos : 0 < gateDenom := by
  unfold gateDenom
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact lambdaGate_intervalIntegrable _ _
  · intro x hx
    exact lambdaGate_pos_of_mem_Ioo hx
  · norm_num

/-- The universal Lipschitz constant selected for the normalized primitive. -/
noncomputable def explicitMGamma : ℝ := gateDenom⁻¹

theorem explicitMGamma_pos : 0 < explicitMGamma := by
  unfold explicitMGamma
  exact inv_pos.mpr gateDenom_pos

/-- Rewriting `GammaGate` through the named positive normalizer. -/
theorem gammaGate_eq_normalized (t : ℝ) :
    GammaGate t = (∫ s in (1 / 4 : ℝ)..t, LambdaGate s) / gateDenom := by
  rfl

/-- The normalized primitive is zero on `(-∞,1/4]`. -/
theorem gammaGate_zero_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) :
    GammaGate t = 0 := by
  rw [gammaGate_eq_normalized]
  have hzero : (∫ s in (1 / 4 : ℝ)..t, LambdaGate s) = 0 := by
    rw [intervalIntegral.integral_symm]
    have hz : (∫ s in t..(1 / 4 : ℝ), LambdaGate s) = 0 := by
      calc
        (∫ s in t..(1 / 4 : ℝ), LambdaGate s) =
            ∫ s in t..(1 / 4 : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le ht] at hx
          exact lambdaGate_zero_of_le_quarter hx.2
        _ = 0 := by simp
    rw [hz, neg_zero]
  rw [hzero, zero_div]

/-- The normalized primitive is one on `[1/2,+∞)`. -/
theorem gammaGate_one_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) :
    GammaGate t = 1 := by
  rw [gammaGate_eq_normalized]
  have hzero : (∫ s in (1 / 2 : ℝ)..t, LambdaGate s) = 0 := by
    calc
      (∫ s in (1 / 2 : ℝ)..t, LambdaGate s) =
          ∫ s in (1 / 2 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le ht] at hx
        exact lambdaGate_zero_of_half_le hx.1
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (lambdaGate_intervalIntegrable (1 / 4) (1 / 2))
    (lambdaGate_intervalIntegrable (1 / 2) t)
  have hnum : (∫ s in (1 / 4 : ℝ)..t, LambdaGate s) = gateDenom := by
    unfold gateDenom
    linarith
  rw [hnum, div_self (ne_of_gt gateDenom_pos)]

/-- The normalized primitive takes values in `[0,1]`. -/
theorem gammaGate_range_all (t : ℝ) :
    0 ≤ GammaGate t ∧ GammaGate t ≤ 1 := by
  by_cases hlo : t ≤ 1 / 4
  · rw [gammaGate_zero_of_le_quarter hlo]
    constructor <;> norm_num
  · by_cases hhi : 1 / 2 ≤ t
    · rw [gammaGate_one_of_half_le hhi]
      constructor <;> norm_num
    · have hat : (1 / 4 : ℝ) ≤ t := le_of_lt (lt_of_not_ge hlo)
      have htb : t ≤ (1 / 2 : ℝ) := le_of_not_ge hhi
      rw [gammaGate_eq_normalized]
      have hnum0 : 0 ≤ ∫ s in (1 / 4 : ℝ)..t, LambdaGate s :=
        intervalIntegral.integral_nonneg_of_forall hat lambdaGate_nonneg
      have htail0 : 0 ≤ ∫ s in t..(1 / 2 : ℝ), LambdaGate s :=
        intervalIntegral.integral_nonneg_of_forall htb lambdaGate_nonneg
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (lambdaGate_intervalIntegrable (1 / 4) t)
        (lambdaGate_intervalIntegrable t (1 / 2))
      have hnumle : (∫ s in (1 / 4 : ℝ)..t, LambdaGate s) ≤ gateDenom := by
        unfold gateDenom
        linarith
      constructor
      · exact div_nonneg hnum0 gateDenom_pos.le
      · exact (div_le_one gateDenom_pos).2 hnumle

/-- Difference of two normalized primitives is the normalized interval integral between the two
points. -/
theorem gammaGate_sub_eq (s t : ℝ) :
    GammaGate s - GammaGate t = (∫ x in t..s, LambdaGate x) / gateDenom := by
  rw [gammaGate_eq_normalized, gammaGate_eq_normalized, ← sub_div]
  rw [intervalIntegral.integral_interval_sub_left
    (lambdaGate_intervalIntegrable (1 / 4) s)
    (lambdaGate_intervalIntegrable (1 / 4) t)]

/-- The explicit normalized primitive is globally Lipschitz with constant `gateDenom⁻¹`. -/
theorem gammaGate_lipschitz_explicit (s t : ℝ) :
    |GammaGate s - GammaGate t| ≤ explicitMGamma * |s - t| := by
  rw [gammaGate_sub_eq]
  have hbound : |∫ x in t..s, LambdaGate x| ≤ |s - t| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := LambdaGate) (C := (1 : ℝ)) (a := t) (b := s) (fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (lambdaGate_nonneg x)]
        exact lambdaGate_le_one x)
    simpa [Real.norm_eq_abs] using h
  rw [abs_div, abs_of_pos gateDenom_pos]
  have hdiv := div_le_div_of_nonneg_right hbound gateDenom_pos.le
  calc
    |∫ x in t..s, LambdaGate x| / gateDenom
        ≤ |s - t| / gateDenom := hdiv
    _ = explicitMGamma * |s - t| := by
      simp [explicitMGamma, div_eq_mul_inv, mul_comm]

/-- A witness at the progress index whenever the progress is positive. -/
theorem exists_coord_at_prog_of_pos {T : ℕ} (a : ℝ) (u : Vec T)
    (hpos : 0 < prog a u) :
    ∃ i : Fin T, i.1 + 1 = prog a u ∧ a < |u i| := by
  unfold prog at hpos ⊢
  have hne : Nat.findGreatest
      (fun n => ∃ i : Fin T, i.1 + 1 = n ∧ a < |u i|) T ≠ 0 := by
    omega
  exact ((Nat.findGreatest_eq_iff).1 rfl).2.1 hne

/-- If the `1/4` progress lies before `i`, then the entire gated tail from `i` onward vanishes. -/
theorem gatedTail_eq_zero_of_quarter_frontier {T : ℕ} (u : Vec T) (i : Fin T)
    (hi : prog (1 / 4) u < i.1 + 1) :
    gatedTail u i = 0 := by
  funext j
  by_cases hij : i.1 ≤ j.1
  · have hj : prog (1 / 4) u < j.1 + 1 := by omega
    have habs := abs_coord_le_of_prog_lt (1 / 4) u j hj
    simp [gatedTail, hij, gammaGate_zero_of_le_quarter habs]
  · simp [gatedTail, hij]

/-- The scalar step properties imply exactly the lower half of the paper's `Theta` sandwich. -/
theorem thetaGate_lower_explicit {T : ℕ} (u : Vec T) (i : Fin T) :
    (if prog (1 / 4) u < i.1 + 1 then (1 : ℝ) else 0) ≤ ThetaGate u i := by
  by_cases hi : prog (1 / 4) u < i.1 + 1
  · rw [if_pos hi]
    have htail := gatedTail_eq_zero_of_quarter_frontier u i hi
    rw [ThetaGate, htail, norm_zero, sub_zero,
      gammaGate_one_of_half_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  · rw [if_neg hi]
    exact (gammaGate_range_all (1 - ‖gatedTail u i‖)).1

/-- The scalar step properties imply exactly the upper half of the paper's `Theta` sandwich. -/
theorem thetaGate_upper_explicit {T : ℕ} (u : Vec T) (i : Fin T) :
    ThetaGate u i ≤ (if prog (1 / 2) u < i.1 + 1 then (1 : ℝ) else 0) := by
  by_cases hi : prog (1 / 2) u < i.1 + 1
  · rw [if_pos hi]
    exact (gammaGate_range_all (1 - ‖gatedTail u i‖)).2
  · rw [if_neg hi]
    have hiprog : i.1 + 1 ≤ prog (1 / 2) u := Nat.le_of_not_gt hi
    have hprogpos : 0 < prog (1 / 2) u := by omega
    rcases exists_coord_at_prog_of_pos (1 / 2) u hprogpos with ⟨j, hjprog, hjabs⟩
    have hij : i.1 ≤ j.1 := by omega
    have hcoord : gatedTail u i j = 1 := by
      simp [gatedTail, hij, gammaGate_one_of_half_le (le_of_lt hjabs)]
    have hsq := vec_coord_sq_le_norm_sq (gatedTail u i) j
    rw [hcoord] at hsq
    have hnorm0 : 0 ≤ ‖gatedTail u i‖ := norm_nonneg _
    have hnorm1 : 1 ≤ ‖gatedTail u i‖ := by nlinarith
    have harg : 1 - ‖gatedTail u i‖ ≤ 1 / 4 := by linarith
    rw [ThetaGate, gammaGate_zero_of_le_quarter harg]

/-- The exact equation-(20) smooth gate certificate for the paper's explicit bump construction. -/
noncomputable def explicitSmoothGateCertificate : SmoothGateCertificate explicitMGamma where
  mΓ_nonneg := explicitMGamma_pos.le
  gamma_zero := fun _ ht => gammaGate_zero_of_le_quarter ht
  gamma_one := fun _ ht => gammaGate_one_of_half_le ht
  gamma_range := gammaGate_range_all
  gamma_lipschitz := gammaGate_lipschitz_explicit
  theta_sandwich := fun u i => ⟨thetaGate_lower_explicit u i, thetaGate_upper_explicit u i⟩

/-- The standalone existence statement that was left open after v37. -/
theorem smoothGateCertificate_exists :
    ∃ mΓ : ℝ, SmoothGateCertificate mΓ :=
  ⟨explicitMGamma, explicitSmoothGateCertificate⟩

/-- Fully closed Lemma 4.3: the universal gate and all universal numerical constants are now fixed
before the problem parameters. -/
theorem canonicalLemma43 : Lemma43Statement := by
  refine ⟨explicitMGamma, universalS0 explicitMGamma,
    asLemma43C0 (universalS0 explicitMGamma),
    asLemma43C1 (universalS0 explicitMGamma),
    asLemma43C2 (universalS0 explicitMGamma),
    asKappaLowerConstant, asKappaUpperConstant, ?_⟩
  refine ⟨explicitSmoothGateCertificate,
    universalS0_pos explicitMGamma, rfl,
    asLemma43C0_pos (universalS0_pos explicitMGamma),
    asLemma43C1_pos (universalS0_pos explicitMGamma),
    asLemma43C2_pos (universalS0_pos explicitMGamma),
    asKappaLowerConstant_pos, asKappaUpperConstant_pos, ?_⟩
  intro P hs0 hσ0 hκ hsmall0 hsmall1
  have hsmall0' :
      P.ε ^ 2 ≤ asLemma43C0 P.s₀ * P.Lbar * P.Δ := by
    simpa [hs0] using hsmall0
  have hsmall1' :
      P.ε * P.σ ≤ asLemma43C1 P.s₀ * P.Lbar * P.Δ * Real.sqrt P.κ := by
    simpa [hs0] using hsmall1
  simpa [hs0] using
    (canonicalLemma43_for_parameters explicitSmoothGateCertificate P hs0 hσ0 hκ
      hsmall0' hsmall1')


/-! ## v39 proof phase XXX: Lemma 4.3 -> Theorem 4.4 end-to-end assembly

With the explicit smooth gate and Lemma 4.3 now closed, this phase supplies the remaining
algorithmic support induction for the averaged-smooth oracle and converts equation (30) directly
into the Theorem-4.4 round and returned-gradient rates.  The proof mirrors the already verified
bounded-variance assembly, but uses the smooth-gated base oracle from equation (21).
-/

/-- Equation (25) gives the same signal identity `γ q = 2 ε` used by Proposition 2.4. -/
theorem as_gamma_mul_q (P : ASParameters) : P.γ * P.q = 2 * P.ε := by
  rw [P.q_def]
  field_simp [ne_of_gt P.γ_pos]

/-- The canonical AS lift inherits `γ q = 2 ε`. -/
theorem asWitness_gamma_mul_q {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) :
    W.LP.γ * W.LP.q = 2 * P.ε := by
  rw [W.lift_gamma, W.lift_q]
  exact as_gamma_mul_q P

/-- The canonical AS lift inherits the transfer-ratio bound `ℓ₀ h / ν ≤ 1/5`. -/
theorem asWitness_transfer_ratio {T : ℕ} {C : ExplicitZeroChainCertificate T}
    {P : ASParameters} (W : ASConstructionWitness C P) :
    ℓ₀ * W.LP.h / W.LP.ν ≤ 1 / 5 := by
  have h := as_transfer_ratio_le_one_fifth P
  simpa [LiftParameters.ν, ASParameters.ν, W.lift_h, W.lift_mu] using h

/-- On a false seed the smooth-gated base oracle creates no new ordinary support coordinate. -/
theorem asBaseOracle_false_prog_le_zero' {T : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (Gate : SmoothGateCertificate mΓ)
    (p : ℝ) (u : Vec T) :
    prog 0 (asBaseOracle C p u false) ≤ prog 0 u := by
  exact le_trans (asBaseOracle_prog_false_le C Gate p u)
    (prog_threshold_le_zero (1 / 4) (by norm_num) u)

/-- On a true seed the smooth-gated base oracle advances ordinary support by at most one. -/
theorem asBaseOracle_true_prog_le_succ_zero {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (u : Vec T) :
    prog 0 (asBaseOracle C p u true) ≤ prog 0 u + 1 := by
  have h := asBaseOracle_prog_le_succ C p u true
  have hq := prog_threshold_le_zero (1 / 4) (by norm_num) u
  omega

/-- For the exact AS construction, a false Bernoulli seed creates no new pair coordinate. -/
theorem asConstructed_response_false_pairProg_le {T : ℕ} {mΓ : ℝ}
    {C : ExplicitZeroChainCertificate T} {P : ASParameters}
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (x y : Vec T) :
    pairProg (liftedGx W.LP x y false) (liftedGy W.B W.LP x y false) ≤
      pairProg x y := by
  have hx : prog 0 (liftedGx W.LP x y false) ≤ pairProg x y :=
    liftedGx_prog_le_pairProg W.LP x y false
  have hbase0 : prog 0 (W.B.g (W.LP.β • y) false) ≤ prog 0 y := by
    rw [W.base_oracle_def]
    exact le_trans (asBaseOracle_false_prog_le_zero' C Gate P.p (W.LP.β • y))
      (prog_zero_smul_le W.LP.β y)
  have hbase : prog 0 (W.LP.q • W.B.g (W.LP.β • y) false) ≤ prog 0 y :=
    le_trans (prog_zero_smul_le W.LP.q (W.B.g (W.LP.β • y) false)) hbase0
  have hdet : prog 0 (W.LP.ν • (y - W.LP.γ • x)) ≤ pairProg x y :=
    lift_dual_coupling_prog_le_pairProg W.LP x y
  have hy0 := prog_zero_sub_le_max
    (W.LP.q • W.B.g (W.LP.β • y) false)
    (W.LP.ν • (y - W.LP.γ • x))
  have hy : prog 0 (liftedGy W.B W.LP x y false) ≤ pairProg x y := by
    unfold liftedGy
    exact le_trans hy0 (max_le (le_trans hbase (Nat.le_max_right _ _)) hdet)
  exact max_le hx hy

/-- For the exact AS construction, a true Bernoulli seed creates at most one new pair
coordinate. -/
theorem asConstructed_response_true_pairProg_le_succ {T : ℕ}
    {C : ExplicitZeroChainCertificate T} {P : ASParameters}
    (W : ASConstructionWitness C P) (x y : Vec T) :
    pairProg (liftedGx W.LP x y true) (liftedGy W.B W.LP x y true) ≤
      pairProg x y + 1 := by
  have hx0 : prog 0 (liftedGx W.LP x y true) ≤ pairProg x y :=
    liftedGx_prog_le_pairProg W.LP x y true
  have hx : prog 0 (liftedGx W.LP x y true) ≤ pairProg x y + 1 :=
    le_trans hx0 (Nat.le_add_right _ _)
  have hbase0 : prog 0 (W.B.g (W.LP.β • y) true) ≤ prog 0 y + 1 := by
    rw [W.base_oracle_def]
    have h := asBaseOracle_true_prog_le_succ_zero C P.p (W.LP.β • y)
    have hs := prog_zero_smul_le W.LP.β y
    omega
  have hbase : prog 0 (W.LP.q • W.B.g (W.LP.β • y) true) ≤ pairProg x y + 1 := by
    have hs := prog_zero_smul_le W.LP.q (W.B.g (W.LP.β • y) true)
    have hy : prog 0 y ≤ pairProg x y := Nat.le_max_right _ _
    omega
  have hdet0 : prog 0 (W.LP.ν • (y - W.LP.γ • x)) ≤ pairProg x y :=
    lift_dual_coupling_prog_le_pairProg W.LP x y
  have hdet : prog 0 (W.LP.ν • (y - W.LP.γ • x)) ≤ pairProg x y + 1 :=
    le_trans hdet0 (Nat.le_add_right _ _)
  have hy0 := prog_zero_sub_le_max
    (W.LP.q • W.B.g (W.LP.β • y) true)
    (W.LP.ν • (y - W.LP.γ • x))
  have hy : prog 0 (liftedGy W.B W.LP x y true) ≤ pairProg x y + 1 := by
    unfold liftedGy
    exact le_trans hy0 (max_le hbase hdet)
  exact max_le hx hy

/-- Every response before prefix `n` has pair progress at most the number of successful
Bernoulli seeds in that prefix, for the explicit AS oracle. -/
theorem as_response_pairProg_le_successPrefix {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (A : BernoulliRun T R K (asConstructedOracle W))
    (w : RoundWorld R) :
    ∀ n : ℕ, n ≤ R →
      ∀ s : Fin R, s.1 < n → ∀ k : Fin K, ∀ r : Vec T × Vec T,
        (A.trace w).response s k = some r →
          pairProg r.1 r.2 ≤ roundSuccessPrefixR w n := by
  intro n
  induction n with
  | zero =>
      intro hn s hs
      omega
  | succ n ih =>
      intro hn s hs k r hrs
      have hnr : n < R := by omega
      have hprefix := roundSuccessPrefixR_succ w n hnr
      by_cases hsn : s.1 < n
      · have hprev := ih (Nat.le_of_lt hnr) s hsn k r hrs
        have hinc0 : 0 ≤ seedSuccessIncrement ⟨n, hnr⟩ w := Nat.zero_le _
        omega
      · have hseqval : s.1 = n := by omega
        have hseq : s = (⟨n, hnr⟩ : Fin R) := Fin.ext hseqval
        subst s
        let t : Fin R := ⟨n, hnr⟩
        have hprior : ∀ s' : Fin R, s'.1 < t.1 → ∀ k' : Fin K,
            ∀ r' : Vec T × Vec T, (A.trace w).response s' k' = some r' →
              pairProg r'.1 r'.2 ≤ roundSuccessPrefixR w n := by
          intro s' hs' k' r' hrs'
          exact ih (Nat.le_of_lt hnr) s' hs' k' r' hrs'
        cases hq : (A.trace w).query t k with
        | none =>
            have hc := A.response_consistent w t k
            rw [hq] at hc
            rw [hrs] at hc
            simp at hc
        | some q =>
            have hqprog := zeroRespecting_query_pairProg_le
              (A.trace w) (A.zero_respecting w) t (roundSuccessPrefixR w n)
              hprior k q hq
            have hc := A.response_consistent w t k
            rw [hq] at hc
            rw [hrs] at hc
            have hrpair : r =
                ((asConstructedOracle W).Gx q.1 q.2 (w t),
                 (asConstructedOracle W).Gy q.1 q.2 (w t)) := by
              exact Option.some.inj hc
            rw [hrpair]
            simp only [Prod.fst, Prod.snd]
            cases hz : w t with
            | false =>
                have hresp := asConstructed_response_false_pairProg_le W Gate q.1 q.2
                have hprefix' : roundSuccessPrefixR w (n + 1) = roundSuccessPrefixR w n := by
                  simpa [t, seedSuccessIncrement, hz] using hprefix
                calc
                  pairProg ((asConstructedOracle W).Gx q.1 q.2 false)
                      ((asConstructedOracle W).Gy q.1 q.2 false)
                      ≤ pairProg q.1 q.2 := hresp
                  _ ≤ roundSuccessPrefixR w n := hqprog
                  _ = roundSuccessPrefixR w (n + 1) := hprefix'.symm
            | true =>
                have hresp := asConstructed_response_true_pairProg_le_succ W q.1 q.2
                have hprefix' :
                    roundSuccessPrefixR w (n + 1) = roundSuccessPrefixR w n + 1 := by
                  simpa [t, seedSuccessIncrement, hz] using hprefix
                have hstep : pairProg q.1 q.2 + 1 ≤ roundSuccessPrefixR w n + 1 :=
                  Nat.add_le_add_right hqprog 1
                calc
                  pairProg ((asConstructedOracle W).Gx q.1 q.2 true)
                      ((asConstructedOracle W).Gy q.1 q.2 true)
                      ≤ pairProg q.1 q.2 + 1 := hresp
                  _ ≤ roundSuccessPrefixR w n + 1 := hstep
                  _ = roundSuccessPrefixR w (n + 1) := hprefix'.symm

/-- Fewer than `T` successful AS reveals imply that the terminal coordinate is still absent. -/
theorem as_successes_lt_T_implies_terminal_unrevealed {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (A : BernoulliRun T R K (asConstructedOracle W))
    (w : RoundWorld R)
    (hsucc : (∑ t : Fin R, seedSuccessIncrement t w) < T) :
    w ∈ terminalUnrevealedEvent C.dim_pos A := by
  intro hrev
  rcases hrev with ⟨s, k, r, hrs, hmem⟩
  have hrb := as_response_pairProg_le_successPrefix C P W Gate A w R (Nat.le_refl R)
    s s.2 k r hrs
  rw [roundSuccessPrefixR_total] at hrb
  have hidx := index_succ_le_pairProg_of_mem_psupp hmem
  have hlast : (lastIndexOfPos C.dim_pos).1 + 1 = T := by
    simp [lastIndexOfPos]
    omega
  rw [hlast] at hidx
  omega

/-- The Bernoulli seed-success process is the canonical progress witness for the AS oracle. -/
def asCanonicalRunProgressWitness {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (A : BernoulliRun T R K (asConstructedOracle W)) :
    RunProgressWitness C.dim_pos P.p A where
  inc := seedSuccessIncrement
  zero_one := seedSuccessIncrement_zero_one
  adapted := seedSuccessIncrement_adapted
  reveal_prob := by
    intro t w
    rw [seedSuccessIncrement_reveal_prob]
  unfinished_implies_terminal_unrevealed := by
    intro w hsum
    exact as_successes_lt_T_implies_terminal_unrevealed C P W Gate A w hsum

/-- Proposition 2.4 specialized end-to-end to the exact averaged-smooth construction. -/
theorem proposition24_as {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (asConstructedOracle W))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    P.ε ^ 2 < stationarityRisk P.p (asConstructedPopulation W).gradPhi A := by
  apply proposition24_of_runProgress C W.B W.LP W.lift_properties P.p P.ε
    P.p_pos (as_p_le_one P) P.ε_pos (asWitness_gamma_mul_q W)
    (asWitness_transfer_ratio W) hT A
    (asCanonicalRunProgressWitness C P W Gate A) hR

/-- Every AS run attaining the target risk needs more than `T/(4p)` rounds. -/
theorem as_round_lower_bound {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (hT : 8 ≤ T)
    (A : BernoulliRun T R K (asConstructedOracle W))
    (hrisk : stationarityRisk P.p (asConstructedPopulation W).gradPhi A ≤ P.ε ^ 2) :
    (T : ℝ) / (4 * P.p) < R := by
  by_contra hnot
  have hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p) := le_of_not_gt hnot
  have hbad := proposition24_as C P W Gate hT A hR
  linarith

/-- Equation (30) and Proposition 2.4 yield the Theorem-4.4 round-rate lower bound. -/
theorem as_rate_round_lower_bound_of_lemma43 {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (c₂ cκLo cκHi : ℝ)
    (D : Lemma43Conclusion C P W mΓ Gate c₂ cκLo cκHi)
    (A : BernoulliRun T R K (asConstructedOracle W))
    (hrisk : stationarityRisk P.p (asConstructedPopulation W).gradPhi A ≤ P.ε ^ 2) :
    (c₂ / 4) * asChainRate P.Lbar P.Δ P.ε P.κ P.p ≤ (R : ℝ) := by
  have hround : (T : ℝ) / (4 * P.p) ≤ (R : ℝ) :=
    le_of_lt (as_round_lower_bound C P W Gate D.T_ge_eight A hrisk)
  have hq : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have hscale := mul_le_mul_of_nonneg_left D.eq30 hq
  calc
    (c₂ / 4) * asChainRate P.Lbar P.Δ P.ε P.κ P.p =
        (1 / 4) * (c₂ * (P.Lbar * P.Δ / P.ε ^ 2) *
          min (1 / P.p) (P.κ / Real.sqrt P.p)) := by
            simp [asChainRate]
            ring
    _ ≤ (1 / 4) * ((T : ℝ) / P.p) := hscale
    _ = (T : ℝ) / (4 * P.p) := by
      field_simp [ne_of_gt P.p_pos]
    _ ≤ (R : ℝ) := hround

/-- The same Theorem-4.4 rate lower-bounds every returned-gradient count of a legal batch trace. -/
theorem as_rate_gradient_lower_bound_of_lemma43 {T R K : ℕ} {mΓ : ℝ}
    (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ)
    (c₂ cκLo cκHi : ℝ)
    (D : Lemma43Conclusion C P W mΓ Gate c₂ cκLo cκHi)
    (A : BernoulliRun T R K (asConstructedOracle W))
    (hrisk : stationarityRisk P.p (asConstructedPopulation W).gradPhi A ≤ P.ε ^ 2)
    (hbatch : ∀ w, ValidBatchSizes (A.trace w)) :
    ∀ w, (c₂ / 4) * asChainRate P.Lbar P.Δ P.ε P.κ P.p ≤
      (returnedGradientCount (A.trace w) : ℝ) := by
  intro w
  have hround := as_rate_round_lower_bound_of_lemma43 C P W Gate c₂ cκLo cκHi D A hrisk
  have hcount : R ≤ returnedGradientCount (A.trace w) :=
    (gradientCountAccounting T R K (A.trace w) (hbatch w)).1
  have hcast : (R : ℝ) ≤ returnedGradientCount (A.trace w) := by
    exact_mod_cast hcount
  exact le_trans hround hcast

/-- Canonical external-parameter record used to instantiate Lemma 4.3 inside Theorem 4.4. -/
noncomputable def canonicalASParameters
    (Lbar μ Δ σ ε s₀ : ℝ)
    (hL : 0 < Lbar) (hμ : 0 < μ) (hε : 0 < ε) (hs₀ : 0 < s₀)
    (_hκ : 8 ≤ Lbar / μ) : ASParameters := by
  let κ : ℝ := Lbar / μ
  let γ : ℝ := Real.sqrt (κ / 4)
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact div_pos hL hμ
  have hγarg : 0 ≤ κ / 4 := by positivity
  have hγpos : 0 < γ := by
    dsimp [γ]
    exact Real.sqrt_pos.2 (by positivity)
  let q : ℝ := 2 * ε / γ
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos (by norm_num) hε) hγpos
  let p : ℝ := if σ = 0 then 1 else min 1 (q ^ 2 * g₀ ^ 2 / σ ^ 2)
  have hppos : 0 < p := by
    dsimp [p]
    by_cases hσ : σ = 0
    · simp [hσ]
    · rw [if_neg hσ]
      have hg : 0 < g₀ := by norm_num [g₀]
      have hratio : 0 < q ^ 2 * g₀ ^ 2 / σ ^ 2 := by
        exact div_pos (mul_pos (sq_pos_of_pos hqpos) (sq_pos_of_pos hg))
          (sq_pos_of_ne_zero hσ)
      exact lt_min (by norm_num) hratio
  exact
    { Lbar := Lbar
      μ := μ
      ε := ε
      σ := σ
      Δ := Δ
      κ := κ
      γ := γ
      q := q
      p := p
      s₀ := s₀
      Lbar_pos := hL
      μ_pos := hμ
      ε_pos := hε
      p_pos := hppos
      s₀_pos := hs₀
      κ_def := rfl
      γ_sq := by
        dsimp [γ]
        exact Real.sq_sqrt hγarg
      γ_pos := hγpos
      q_def := rfl
      p_def := rfl }

/-- The canonical AS record has exactly the external data of Theorem 4.4. -/
theorem canonicalASParameters_match
    (Lbar μ Δ σ ε s₀ : ℝ)
    (hL : 0 < Lbar) (hμ : 0 < μ) (hε : 0 < ε) (hs₀ : 0 < s₀)
    (hκ : 8 ≤ Lbar / μ) :
    ASParameterMatch (canonicalASParameters Lbar μ Δ σ ε s₀ hL hμ hε hs₀ hκ)
      Lbar μ Δ σ ε s₀ := by
  simp [ASParameterMatch, canonicalASParameters]

/-- Proof-theoretic assembly of the averaged-smooth main theorem from Lemma 4.3. -/
theorem theorem44_of_lemma43 (h43 : Lemma43Statement) : Theorem44Statement := by
  rcases h43 with ⟨mΓ, s₀, c₀, c₁, c₂, cκLo, cκHi, Gate,
    hs₀, hs₀eq, hc₀, hc₁, hc₂, hcκLo, hcκHi, hlemma43⟩
  let c : ℝ := c₂ / 4
  have hc : 0 < c := div_pos hc₂ (by norm_num)
  refine ⟨c, c₀, c₁, mΓ, s₀, Gate, hc, hc₀, hc₁, hs₀, hs₀eq, ?_⟩
  intro K hK Lbar μ Δ σ ε hL hμ hε hσ hΔ hκ hsmall0 hsmall1
  let P : ASParameters := canonicalASParameters Lbar μ Δ σ ε s₀ hL hμ hε hs₀ hκ
  have hPs0 : P.s₀ = s₀ := by
    simp [P, canonicalASParameters]
  have hPsigma : 0 ≤ P.σ := by
    simpa [P, canonicalASParameters] using hσ
  have hPkappa : 8 ≤ P.κ := by
    simpa [P, canonicalASParameters] using hκ
  have hPsmall0 : P.ε ^ 2 ≤ c₀ * P.Lbar * P.Δ := by
    simpa [P, canonicalASParameters] using hsmall0
  have hPsmall1 :
      P.ε * P.σ ≤ c₁ * P.Lbar * P.Δ * Real.sqrt P.κ := by
    simpa [P, canonicalASParameters] using hsmall1
  rcases hlemma43 P hPs0 hPsigma hPkappa hPsmall0 hPsmall1 with ⟨T, C, W, hD⟩
  rcases hD with ⟨D⟩
  refine ⟨P, T, C, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalASParameters_match Lbar μ Δ σ ε s₀ hL hμ hε hs₀ hκ
  · exact ⟨by simpa [hPs0] using D.base_certificate⟩
  · simpa [P, canonicalASParameters] using D.ncsc
  · simpa [P, canonicalASParameters] using D.unbiased
  · simpa [P, canonicalASParameters] using D.variance
  · simpa [P, canonicalASParameters] using D.averaged_smooth
  · simpa [P, canonicalASParameters] using D.p_scaling
  · intro R A hbatch hrisk
    have hriskP :
        stationarityRisk P.p (asConstructedPopulation W).gradPhi A ≤ P.ε ^ 2 := by
      simpa [P, canonicalASParameters] using hrisk
    have hround := as_rate_round_lower_bound_of_lemma43
      C P W Gate c₂ cκLo cκHi D A hriskP
    have hgrads := as_rate_gradient_lower_bound_of_lemma43
      C P W Gate c₂ cκLo cκHi D A hriskP hbatch
    constructor
    · simpa [c, P, canonicalASParameters] using hround
    · intro w
      simpa [c, P, canonicalASParameters] using hgrads w


/-- Universal comparison constant used when eliminating the exact reveal probability from the
averaged-smooth chain rate.  The factor `16 g₀²` is exactly the constant in equation (27). -/
def asConsequenceConstant : ℝ := 1 / (16 * g₀ ^ 2)

theorem asConsequenceConstant_pos : 0 < asConsequenceConstant := by
  norm_num [asConsequenceConstant, g₀]

theorem asConsequenceConstant_le_one : asConsequenceConstant ≤ 1 := by
  norm_num [asConsequenceConstant, g₀]

theorem asConsequenceConstant_le_linear :
    asConsequenceConstant ≤ 1 / (4 * g₀) := by
  norm_num [asConsequenceConstant, g₀]

/-- On the nontrivial stochastic branch `σ>0`, `p<1`, equation (27) selects its second
argument rather than the cap at one. -/
theorem asp_stochastic_p_exact (p κ σ ε : ℝ)
    (hσ : 0 < σ) (hp1 : p < 1) (hscale : ASPScalingExact p κ σ ε) :
    p = 16 * g₀ ^ 2 * ε ^ 2 / (κ * σ ^ 2) := by
  rcases hscale with hzero | hnonzero
  · rcases hzero with ⟨hσ0, _⟩
    linarith
  · rcases hnonzero with ⟨hσne, hpdef⟩
    let r : ℝ := 16 * g₀ ^ 2 * ε ^ 2 / (κ * σ ^ 2)
    have hrle : r ≤ 1 := by
      by_contra hnot
      have hlt : 1 < r := lt_of_not_ge hnot
      have hpone : p = 1 := by
        rw [hpdef, min_eq_left (le_of_lt hlt)]
      linarith
    simpa [r, min_eq_right hrle] using hpdef

/-- Reciprocal form of the stochastic `p` identity. -/
theorem asp_stochastic_inv_p_exact (p κ σ ε : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 < σ) (hp1 : p < 1)
    (hscale : ASPScalingExact p κ σ ε) :
    1 / p = asConsequenceConstant * (κ * σ ^ 2 / ε ^ 2) := by
  have hp := asp_stochastic_p_exact p κ σ ε hσ hp1 hscale
  rw [hp, asConsequenceConstant]
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hε0 : ε ≠ 0 := ne_of_gt hε
  norm_num [g₀]
  field_simp [hκ0, hσ0, hε0]

/-- Square-root form of the stochastic `p` identity. -/
theorem asp_stochastic_sqrt_p_exact (p κ σ ε : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 < σ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hscale : ASPScalingExact p κ σ ε) :
    Real.sqrt p = 4 * g₀ * ε / (Real.sqrt κ * σ) := by
  have hp := asp_stochastic_p_exact p κ σ ε hσ hp1 hscale
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsκ0 : Real.sqrt κ ≠ 0 := ne_of_gt hsκ
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hsquareκ : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt (le_of_lt hκ)
  have hrhspos : 0 < 4 * g₀ * ε / (Real.sqrt κ * σ) := by
    have hg : 0 < g₀ := by norm_num [g₀]
    exact div_pos (mul_pos (mul_pos (by norm_num) hg) hε) (mul_pos hsκ hσ)
  have hsqp : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt (le_of_lt hp0)
  have hden : (Real.sqrt κ * σ) ^ 2 = κ * σ ^ 2 := by
    rw [mul_pow, hsquareκ]
  have hsqrhs : (4 * g₀ * ε / (Real.sqrt κ * σ)) ^ 2 = p := by
    calc
      (4 * g₀ * ε / (Real.sqrt κ * σ)) ^ 2 =
          (4 * g₀ * ε) ^ 2 / (Real.sqrt κ * σ) ^ 2 := by
            rw [div_pow]
      _ = (4 * g₀ * ε) ^ 2 / (κ * σ ^ 2) := by
            rw [hden]
      _ = 16 * g₀ ^ 2 * ε ^ 2 / (κ * σ ^ 2) := by
            ring
      _ = p := hp.symm
  have hsqp_nonneg : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  nlinarith

/-- The second branch appearing in the chain rate after eliminating `sqrt p`. -/
theorem asp_stochastic_kappa_div_sqrt_exact (p κ σ ε : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 < σ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hscale : ASPScalingExact p κ σ ε) :
    κ / Real.sqrt p = (1 / (4 * g₀)) *
      (κ * Real.sqrt κ * σ / ε) := by
  rw [asp_stochastic_sqrt_p_exact p κ σ ε hε hκ hσ hp0 hp1 hscale]
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsκ0 : Real.sqrt κ ≠ 0 := ne_of_gt hsκ
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hg0 : g₀ ≠ 0 := by norm_num [g₀]
  field_simp [hsκ0, hσ0, hε0, hg0]
  ring

/-- Equation (32) at the scalar-rate level: on the branch `p<1`, the exact reveal-probability
chain rate dominates the mixed stochastic expression up to one universal constant. -/
theorem as_mixed_rate_le_chain_rate_of_stochastic_scaling
    (Lbar Δ ε κ σ p : ℝ)
    (hL : 0 < Lbar) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hκ : 0 < κ) (hσ : 0 < σ) (hp0 : 0 < p) (hp1 : p < 1)
    (hscale : ASPScalingExact p κ σ ε) :
    asConsequenceConstant * asMixedRate Lbar Δ ε κ σ ≤
      asChainRate Lbar Δ ε κ p := by
  let A : ℝ := κ * σ ^ 2 / ε ^ 2
  let B : ℝ := κ * Real.sqrt κ * σ / ε
  have hc0 : 0 ≤ asConsequenceConstant := le_of_lt asConsequenceConstant_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg (le_of_lt hκ) (sq_nonneg σ)) (sq_nonneg ε)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt hκ) (Real.sqrt_nonneg _)) (le_of_lt hσ))
      (le_of_lt hε)
  have hinv := asp_stochastic_inv_p_exact p κ σ ε hε hκ hσ hp1 hscale
  have hkroot := asp_stochastic_kappa_div_sqrt_exact
    p κ σ ε hε hκ hσ hp0 hp1 hscale
  have hmin :
      asConsequenceConstant * min A B ≤
        min (1 / p) (κ / Real.sqrt p) := by
    rw [hinv, hkroot]
    apply le_min
    · exact mul_le_mul_of_nonneg_left (min_le_left A B) hc0
    · calc
        asConsequenceConstant * min A B ≤ asConsequenceConstant * B :=
          mul_le_mul_of_nonneg_left (min_le_right A B) hc0
        _ ≤ (1 / (4 * g₀)) * B :=
          mul_le_mul_of_nonneg_right asConsequenceConstant_le_linear hB
  have hbase : 0 ≤ Lbar * Δ / ε ^ 2 :=
    div_nonneg (mul_nonneg (le_of_lt hL) hΔ) (sq_nonneg ε)
  have hmixed :
      asMixedRate Lbar Δ ε κ σ =
        (Lbar * Δ / ε ^ 2) * min A B := by
    have hε0 : ε ≠ 0 := ne_of_gt hε
    have hscale0 : 0 ≤ 1 / ε ^ 2 := by positivity
    have hx :
        κ * σ ^ 2 / ε ^ 4 = (1 / ε ^ 2) * A := by
      dsimp [A]
      field_simp [hε0] <;> ring
    have hy :
        κ * Real.sqrt κ * σ / ε ^ 3 = (1 / ε ^ 2) * B := by
      dsimp [B]
      field_simp [hε0] <;> ring
    rw [asMixedRate, hx, hy]
    by_cases hAB : A ≤ B
    · have hscaled : (1 / ε ^ 2) * A ≤ (1 / ε ^ 2) * B :=
        mul_le_mul_of_nonneg_left hAB hscale0
      rw [min_eq_left hAB, min_eq_left hscaled]
      ring
    · have hBA : B ≤ A := le_of_not_ge hAB
      have hscaled : (1 / ε ^ 2) * B ≤ (1 / ε ^ 2) * A :=
        mul_le_mul_of_nonneg_left hBA hscale0
      rw [min_eq_right hBA, min_eq_right hscaled]
      ring
  rw [hmixed, asChainRate]
  calc
    asConsequenceConstant * ((Lbar * Δ / ε ^ 2) * min A B) =
        (Lbar * Δ / ε ^ 2) * (asConsequenceConstant * min A B) := by ring
    _ ≤ (Lbar * Δ / ε ^ 2) * min (1 / p) (κ / Real.sqrt p) :=
      mul_le_mul_of_nonneg_left hmin hbase

/-- Fully proved equation-(32) consequence schema. -/
theorem equation32_consequence : Equation32ConsequenceStatement := by
  refine ⟨1, asConsequenceConstant, by norm_num, asConsequenceConstant_pos, ?_⟩
  intro R Lbar Δ ε κ σ p hL hΔ hε hκ hσ hp0 hp1 hscale hR
  have hcmp := as_mixed_rate_le_chain_rate_of_stochastic_scaling
    Lbar Δ ε κ σ p hL hΔ hε hκ hσ hp0 hp1 hscale
  exact le_trans hcmp (by simpa using hR)

/-- The quadratic branch of the mixed rate is active below the upper regime boundary. -/
theorem as_quadratic_term_le_linear_term
    (ε κ σ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 ≤ σ)
    (hupper : σ ≤ Real.sqrt κ * ε) :
    κ * σ ^ 2 / ε ^ 4 ≤ κ * Real.sqrt κ * σ / ε ^ 3 := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hfac : 0 ≤ κ * σ / ε ^ 4 := by
    exact div_nonneg (mul_nonneg (le_of_lt hκ) hσ) (pow_nonneg (le_of_lt hε) _)
  have hm := mul_le_mul_of_nonneg_left hupper hfac
  calc
    κ * σ ^ 2 / ε ^ 4 = (κ * σ / ε ^ 4) * σ := by
      field_simp [hε0]
      ring
    _ ≤ (κ * σ / ε ^ 4) * (Real.sqrt κ * ε) := hm
    _ = κ * Real.sqrt κ * σ / ε ^ 3 := by
      field_simp [hε0]
      ring

/-- Above the upper regime boundary, the linear-in-`σ` branch is the smaller mixed term. -/
theorem as_linear_term_le_quadratic_term
    (ε κ σ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 ≤ σ)
    (hlower : Real.sqrt κ * ε ≤ σ) :
    κ * Real.sqrt κ * σ / ε ^ 3 ≤ κ * σ ^ 2 / ε ^ 4 := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hfac : 0 ≤ κ * σ / ε ^ 4 := by
    exact div_nonneg (mul_nonneg (le_of_lt hκ) hσ) (pow_nonneg (le_of_lt hε) _)
  have hm := mul_le_mul_of_nonneg_left hlower hfac
  calc
    κ * Real.sqrt κ * σ / ε ^ 3 =
        (κ * σ / ε ^ 4) * (Real.sqrt κ * ε) := by
      field_simp [hε0]
      ring
    _ ≤ (κ * σ / ε ^ 4) * σ := hm
    _ = κ * σ ^ 2 / ε ^ 4 := by
      field_simp [hε0]
      ring

/-- If the exact stochastic scaling is capped at `p=1`, the uncapped quadratic factor is at
most `16 g₀²`. -/
theorem asp_sigma_factor_le_of_p_eq_one
    (p κ σ ε : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 < σ)
    (hpone : p = 1) (hscale : ASPScalingExact p κ σ ε) :
    κ * σ ^ 2 / ε ^ 2 ≤ 16 * g₀ ^ 2 := by
  rcases hscale with hzero | hnonzero
  · linarith [hzero.1]
  · rcases hnonzero with ⟨hσne, hpdef⟩
    let r : ℝ := 16 * g₀ ^ 2 * ε ^ 2 / (κ * σ ^ 2)
    have hminone : min 1 r = 1 := by
      calc
        min 1 r = p := by simpa [r] using hpdef.symm
        _ = 1 := hpone
    have hr : 1 ≤ r := by
      by_contra hnot
      have hrlt : r < 1 := lt_of_not_ge hnot
      have hrle : r ≤ 1 := le_of_lt hrlt
      rw [min_eq_right hrle] at hminone
      linarith
    have hden : 0 < κ * σ ^ 2 := mul_pos hκ (sq_pos_of_pos hσ)
    have hcross : κ * σ ^ 2 ≤ 16 * g₀ ^ 2 * ε ^ 2 := by
      have ht := (le_div_iff₀ hden).1 (by simpa [r] using hr)
      simpa using ht
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    exact (div_le_iff₀ hε2).2 (by simpa [mul_assoc] using hcross)

/-- The low-noise regime is incompatible with the uncapped stochastic branch `p<1`. -/
theorem asp_not_low_sigma_of_p_lt_one
    (p κ σ ε : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (hσ : 0 < σ)
    (hp0 : 0 < p) (hp1 : p < 1) (hscale : ASPScalingExact p κ σ ε) :
    ¬ σ ≤ ε / Real.sqrt κ := by
  intro hlow
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hmul : σ * Real.sqrt κ ≤ ε := (le_div_iff₀ hsκ).1 hlow
  have hleft0 : 0 ≤ σ * Real.sqrt κ :=
    mul_nonneg (le_of_lt hσ) (Real.sqrt_nonneg _)
  have hsquares := mul_self_le_mul_self hleft0 hmul
  have hκσ : κ * σ ^ 2 ≤ ε ^ 2 := by
    calc
      κ * σ ^ 2 = (σ * Real.sqrt κ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hκ)]
        ring
      _ ≤ ε ^ 2 := by simpa [pow_two] using hsquares
  have hden : 0 < κ * σ ^ 2 := mul_pos hκ (sq_pos_of_pos hσ)
  have hratio : 1 ≤ ε ^ 2 / (κ * σ ^ 2) := by
    exact (le_div_iff₀ hden).2 (by simpa using hκσ)
  have hp := asp_stochastic_p_exact p κ σ ε hσ hp1 hscale
  have hconst0 : 0 ≤ 16 * g₀ ^ 2 := by norm_num [g₀]
  have hpge : 16 * g₀ ^ 2 ≤ p := by
    rw [hp]
    calc
      16 * g₀ ^ 2 = (16 * g₀ ^ 2) * 1 := by ring
      _ ≤ (16 * g₀ ^ 2) * (ε ^ 2 / (κ * σ ^ 2)) :=
        mul_le_mul_of_nonneg_left hratio hconst0
      _ = 16 * g₀ ^ 2 * ε ^ 2 / (κ * σ ^ 2) := by ring
  have hbig : 1 < 16 * g₀ ^ 2 := by norm_num [g₀]
  linarith

/-- Remark 4.5, now proved from the exact capped/uncapped `p` scaling.  The theorem keeps the
paper's `κ≥8` context explicit; without at least `κ≥1`, the low-noise `p=1` branch would not
uniformly dominate the deterministic base rate. -/
theorem remark45_consequence : Remark45ConsequenceStatement := by
  refine ⟨1, asConsequenceConstant, by norm_num, asConsequenceConstant_pos, ?_⟩
  intro R Lbar Δ ε κ σ p hL hΔ hε hκ hκ8 hσ0 hp0 hpLe hscale hR
  have hbase : 0 ≤ Lbar * Δ / ε ^ 2 :=
    div_nonneg (mul_nonneg (le_of_lt hL) hΔ) (sq_nonneg ε)
  have hLD : 0 ≤ Lbar * Δ := mul_nonneg (le_of_lt hL) hΔ
  have hκone : 1 ≤ κ := by linarith
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hchainR : asChainRate Lbar Δ ε κ p ≤ R := by simpa using hR
  by_cases hσzero : σ = 0
  · have hpone : p = 1 := by
      rcases hscale with hzero | hnonzero
      · exact hzero.2
      · exact False.elim (hnonzero.1 hσzero)
    have hlow : σ ≤ ε / Real.sqrt κ := by
      rw [hσzero]
      positivity
    have hpiece : asPiecewiseRate Lbar Δ ε κ σ = Lbar * Δ / ε ^ 2 := by
      simp [asPiecewiseRate, hlow]
    have hchain : asChainRate Lbar Δ ε κ p = Lbar * Δ / ε ^ 2 := by
      rw [hpone]
      simp [asChainRate, min_eq_left hκone]
    calc
      asConsequenceConstant * asPiecewiseRate Lbar Δ ε κ σ =
          asConsequenceConstant * (Lbar * Δ / ε ^ 2) := by rw [hpiece]
      _ ≤ 1 * (Lbar * Δ / ε ^ 2) :=
        mul_le_mul_of_nonneg_right asConsequenceConstant_le_one hbase
      _ = asChainRate Lbar Δ ε κ p := by rw [hchain]; ring
      _ ≤ R := hchainR
  · have hσ : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσzero)
    by_cases hpLt : p < 1
    · have hnotlow := asp_not_low_sigma_of_p_lt_one
        p κ σ ε hε hκ hσ hp0 hpLt hscale
      by_cases hmid : σ ≤ Real.sqrt κ * ε
      · have hquad := as_quadratic_term_le_linear_term
          ε κ σ hε hκ (le_of_lt hσ) hmid
        have hpieceMixed :
            asPiecewiseRate Lbar Δ ε κ σ = asMixedRate Lbar Δ ε κ σ := by
          rw [asPiecewiseRate, if_neg hnotlow, if_pos hmid, asMixedRate,
            min_eq_left hquad]
          ring
        calc
          asConsequenceConstant * asPiecewiseRate Lbar Δ ε κ σ =
              asConsequenceConstant * asMixedRate Lbar Δ ε κ σ := by rw [hpieceMixed]
          _ ≤ asChainRate Lbar Δ ε κ p :=
            as_mixed_rate_le_chain_rate_of_stochastic_scaling
              Lbar Δ ε κ σ p hL hΔ hε hκ hσ hp0 hpLt hscale
          _ ≤ R := hchainR
      · have hhigh : Real.sqrt κ * ε ≤ σ := le_of_lt (lt_of_not_ge hmid)
        have hlin := as_linear_term_le_quadratic_term
          ε κ σ hε hκ (le_of_lt hσ) hhigh
        have hpieceMixed :
            asPiecewiseRate Lbar Δ ε κ σ = asMixedRate Lbar Δ ε κ σ := by
          rw [asPiecewiseRate, if_neg hnotlow, if_neg hmid, asMixedRate,
            min_eq_right hlin]
          ring
        calc
          asConsequenceConstant * asPiecewiseRate Lbar Δ ε κ σ =
              asConsequenceConstant * asMixedRate Lbar Δ ε κ σ := by rw [hpieceMixed]
          _ ≤ asChainRate Lbar Δ ε κ p :=
            as_mixed_rate_le_chain_rate_of_stochastic_scaling
              Lbar Δ ε κ σ p hL hΔ hε hκ hσ hp0 hpLt hscale
          _ ≤ R := hchainR
    · have hpone : p = 1 := le_antisymm hpLe (le_of_not_gt hpLt)
      have hfactor := asp_sigma_factor_le_of_p_eq_one
        p κ σ ε hε hκ hσ hpone hscale
      have hchain : asChainRate Lbar Δ ε κ p = Lbar * Δ / ε ^ 2 := by
        rw [hpone]
        simp [asChainRate, min_eq_left hκone]
      have hquadEq :
          Lbar * Δ * κ * σ ^ 2 / ε ^ 4 =
            (Lbar * Δ / ε ^ 2) * (κ * σ ^ 2 / ε ^ 2) := by
        have hε0 : ε ≠ 0 := ne_of_gt hε
        field_simp [hε0]
        ring
      have hquadLe :
          Lbar * Δ * κ * σ ^ 2 / ε ^ 4 ≤
            (16 * g₀ ^ 2) * (Lbar * Δ / ε ^ 2) := by
        rw [hquadEq]
        calc
          (Lbar * Δ / ε ^ 2) * (κ * σ ^ 2 / ε ^ 2) ≤
              (Lbar * Δ / ε ^ 2) * (16 * g₀ ^ 2) :=
            mul_le_mul_of_nonneg_left hfactor hbase
          _ = (16 * g₀ ^ 2) * (Lbar * Δ / ε ^ 2) := by ring
      have hcollapse :
          asConsequenceConstant *
              ((16 * g₀ ^ 2) * (Lbar * Δ / ε ^ 2)) =
            Lbar * Δ / ε ^ 2 := by
        norm_num [asConsequenceConstant, g₀] <;> ring
      by_cases hlow : σ ≤ ε / Real.sqrt κ
      · have hpiece :
            asPiecewiseRate Lbar Δ ε κ σ = Lbar * Δ / ε ^ 2 := by
          simp [asPiecewiseRate, hlow]
        calc
          asConsequenceConstant * asPiecewiseRate Lbar Δ ε κ σ =
              asConsequenceConstant * (Lbar * Δ / ε ^ 2) := by rw [hpiece]
          _ ≤ 1 * (Lbar * Δ / ε ^ 2) :=
            mul_le_mul_of_nonneg_right asConsequenceConstant_le_one hbase
          _ = asChainRate Lbar Δ ε κ p := by rw [hchain]; ring
          _ ≤ R := hchainR
      · by_cases hmid : σ ≤ Real.sqrt κ * ε
        · have hpiece :
              asPiecewiseRate Lbar Δ ε κ σ =
                Lbar * Δ * κ * σ ^ 2 / ε ^ 4 := by
            simp [asPiecewiseRate, hlow, hmid]
          calc
            asConsequenceConstant * asPiecewiseRate Lbar Δ ε κ σ =
                asConsequenceConstant * (Lbar * Δ * κ * σ ^ 2 / ε ^ 4) := by rw [hpiece]
            _ ≤ asConsequenceConstant *
                ((16 * g₀ ^ 2) * (Lbar * Δ / ε ^ 2)) :=
              mul_le_mul_of_nonneg_left hquadLe
                (le_of_lt asConsequenceConstant_pos)
            _ = Lbar * Δ / ε ^ 2 := hcollapse
            _ = asChainRate Lbar Δ ε κ p := hchain.symm
            _ ≤ R := hchainR
        · have hhigh : Real.sqrt κ * ε ≤ σ := le_of_lt (lt_of_not_ge hmid)
          have hlinTerm := as_linear_term_le_quadratic_term
            ε κ σ hε hκ (le_of_lt hσ) hhigh
          have hlinLeQuad :
              Lbar * Δ * κ * Real.sqrt κ * σ / ε ^ 3 ≤
                Lbar * Δ * κ * σ ^ 2 / ε ^ 4 := by
            have hm := mul_le_mul_of_nonneg_left hlinTerm hLD
            ring_nf at hm ⊢
            exact hm
          have hpiece :
              asPiecewiseRate Lbar Δ ε κ σ =
                Lbar * Δ * κ * Real.sqrt κ * σ / ε ^ 3 := by
            simp [asPiecewiseRate, hlow, hmid]
          calc
            asConsequenceConstant * asPiecewiseRate Lbar Δ ε κ σ =
                asConsequenceConstant *
                  (Lbar * Δ * κ * Real.sqrt κ * σ / ε ^ 3) := by rw [hpiece]
            _ ≤ asConsequenceConstant *
                (Lbar * Δ * κ * σ ^ 2 / ε ^ 4) :=
              mul_le_mul_of_nonneg_left hlinLeQuad
                (le_of_lt asConsequenceConstant_pos)
            _ ≤ asConsequenceConstant *
                ((16 * g₀ ^ 2) * (Lbar * Δ / ε ^ 2)) :=
              mul_le_mul_of_nonneg_left hquadLe
                (le_of_lt asConsequenceConstant_pos)
            _ = Lbar * Δ / ε ^ 2 := hcollapse
            _ = asChainRate Lbar Δ ε κ p := hchain.symm
            _ ≤ R := hchainR

/-- Fully closed paper Theorem 4.4, obtained from the fully closed Lemma 4.3. -/
theorem canonicalTheorem44 : Theorem44Statement :=
  theorem44_of_lemma43 canonicalLemma43

/-- Equation (32) is now a proved consequence rather than only a statement marker. -/
theorem canonicalEquation32Consequence : Equation32ConsequenceStatement :=
  equation32_consequence

/-- Remark 4.5 is now a proved consequence, in the same `κ≥8` regime as Theorem 4.4. -/
theorem canonicalRemark45Consequence : Remark45ConsequenceStatement :=
  remark45_consequence


/-! ### v41: Proposition 4.6 Gaussian-location analytic core -/

/-- The two-point displacement is chosen so that `L̄ a = 4 ε`. -/
theorem gaussian_Lbar_mul_a (Lbar ε : ℝ) (hL : 0 < Lbar) :
    Lbar * gaussianA Lbar ε = 4 * ε := by
  rw [gaussianA]
  field_simp [ne_of_gt hL]

/-- Consequently the two sufficient-statistic means differ by exactly `8 ε`. -/
theorem gaussian_mean_separation_exact (Lbar ε : ℝ) (hL : 0 < Lbar) :
    2 * Lbar * gaussianA Lbar ε = 8 * ε := by
  rw [mul_assoc, gaussian_Lbar_mul_a Lbar ε hL]
  ring

/-- Exact initial value-function gap of either Gaussian-location member. -/
theorem gaussian_initial_gap_value_exact (Lbar ε : ℝ) (hL : 0 < Lbar) :
    Lbar * (gaussianA Lbar ε) ^ 2 / 2 = 8 * ε ^ 2 / Lbar := by
  rw [gaussianA]
  field_simp [ne_of_gt hL]
  ring

/-- The paper's small-accuracy assumption implies the required initial-gap budget. -/
theorem gaussian_initial_gap_le_delta (Lbar Δ ε : ℝ)
    (hL : 0 < Lbar) (hsmall : ε ^ 2 ≤ Lbar * Δ / 8) :
    Lbar * (gaussianA Lbar ε) ^ 2 / 2 ≤ Δ := by
  rw [gaussian_initial_gap_value_exact Lbar ε hL]
  have hL8 : 0 < 8 * Lbar := by positivity
  have hs := (le_div_iff₀ (show (0 : ℝ) < 8 by norm_num)).1 hsmall
  have hscale : 8 * ε ^ 2 ≤ Lbar * Δ := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hs
  exact (div_le_iff₀ hL).2 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hscale)

/-- Same-seed differences cancel the Gaussian noise exactly. -/
theorem gaussianOracleX_same_seed_difference (Lbar θ x x' ζ : ℝ) :
    gaussianOracleX Lbar θ x ζ - gaussianOracleX Lbar θ x' ζ =
      Lbar * (x - x') := by
  simp [gaussianOracleX]
  ring

/-- Mathlib's `gaussianReal` is a probability measure, hence the noise law has mass one. -/
theorem gaussianNoiseMeasure_probability (σ : ℝ) :
    gaussianNoiseMeasure σ Set.univ = 1 := by
  simp [gaussianNoiseMeasure]

open MeasureTheory

/-- Every real exponential moment of the centered Gaussian noise is integrable.

Mathlib 4.19 predates the convenience theorems `integral_id_gaussianReal` and
`variance_id_gaussianReal`.  We instead use the Gaussian MGF formula, whose strictly positive
value together with `mgf_pos_iff` forces integrability. -/
theorem gaussianNoiseMeasure_exp_integrable (σ t : ℝ) :
    Integrable (fun ζ : ℝ => Real.exp (t * ζ)) (gaussianNoiseMeasure σ) := by
  letI : IsProbabilityMeasure (gaussianNoiseMeasure σ) := by
    unfold gaussianNoiseMeasure
    infer_instance
  letI : NeZero (gaussianNoiseMeasure σ) :=
    ⟨IsProbabilityMeasure.ne_zero (gaussianNoiseMeasure σ)⟩
  apply (ProbabilityTheory.mgf_pos_iff).mp
  have hmap : Measure.map id (gaussianNoiseMeasure σ) =
      ProbabilityTheory.gaussianReal 0 (gaussianVariance σ) := by
    simp [gaussianNoiseMeasure]
  change 0 < ProbabilityTheory.mgf id (gaussianNoiseMeasure σ) t
  rw [ProbabilityTheory.mgf_gaussianReal hmap t]
  positivity

/-- Zero lies in the interior of the Gaussian MGF domain.  This is the hypothesis needed by
Mathlib 4.19's `iteratedDeriv_complexMGF` theorem. -/
theorem gaussianNoiseMeasure_zero_mem_interior_integrableExpSet (σ : ℝ) :
    (0 : ℝ) ∈ interior
      (ProbabilityTheory.integrableExpSet id (gaussianNoiseMeasure σ)) := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset]
  refine ⟨(-1 : ℝ), (1 : ℝ), by norm_num, ?_⟩
  intro t ht
  change Integrable (fun ζ : ℝ => Real.exp (t * ζ)) (gaussianNoiseMeasure σ)
  exact ProbabilityTheory.integrable_exp_mul_of_le_of_le
    (by simpa using gaussianNoiseMeasure_exp_integrable σ (-1))
    (by simpa using gaussianNoiseMeasure_exp_integrable σ 1)
    (le_of_lt ht.1) (le_of_lt ht.2)

/-- The explicit entire function equal to the complex MGF of the centered Gaussian. -/
noncomputable def gaussianNoiseComplexMGF (σ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((gaussianVariance σ : ℂ) * z ^ 2 / 2)

/-- The complex MGF is the standard centered-Gaussian exponential quadratic. -/
theorem gaussianNoiseMeasure_complexMGF_eq (σ : ℝ) :
    ProbabilityTheory.complexMGF id (gaussianNoiseMeasure σ) =
      gaussianNoiseComplexMGF σ := by
  funext z
  rw [gaussianNoiseMeasure]
  simpa [gaussianNoiseComplexMGF] using
    (ProbabilityTheory.complexMGF_id_gaussianReal
      (μ := (0 : ℝ)) (v := gaussianVariance σ) z)

/-- First derivative of the explicit Gaussian complex MGF. -/
theorem gaussianNoiseComplexMGF_hasDerivAt (σ : ℝ) (z : ℂ) :
    HasDerivAt (gaussianNoiseComplexMGF σ)
      ((gaussianVariance σ : ℂ) * z * gaussianNoiseComplexMGF σ z) z := by
  have hinner :
      HasDerivAt (fun w : ℂ => (gaussianVariance σ : ℂ) * w ^ 2 / 2)
        ((gaussianVariance σ : ℂ) * z) z := by
    convert ((hasDerivAt_pow 2 z).const_mul
      (gaussianVariance σ : ℂ)).div_const 2 using 1 <;> norm_num <;> ring
  have h := hinner.cexp
  convert h using 1 <;> simp [gaussianNoiseComplexMGF] <;> ring

/-- The first iterated derivative at zero vanishes. -/
theorem gaussianNoiseComplexMGF_first_iteratedDeriv_zero (σ : ℝ) :
    iteratedDeriv 1 (gaussianNoiseComplexMGF σ) 0 = 0 := by
  calc
    iteratedDeriv 1 (gaussianNoiseComplexMGF σ) 0 =
        deriv (gaussianNoiseComplexMGF σ) 0 := by simp [iteratedDeriv_succ]
    _ = 0 := by
      simpa [gaussianNoiseComplexMGF] using
        (gaussianNoiseComplexMGF_hasDerivAt σ 0).deriv

/-- The second iterated derivative at zero is exactly the Gaussian variance parameter. -/
theorem gaussianNoiseComplexMGF_second_iteratedDeriv_zero (σ : ℝ) :
    iteratedDeriv 2 (gaussianNoiseComplexMGF σ) 0 =
      (gaussianVariance σ : ℂ) := by
  let f : ℂ → ℂ := gaussianNoiseComplexMGF σ
  let g : ℂ → ℂ := fun z => (gaussianVariance σ : ℂ) * z * f z
  have hfderiv : deriv f = g := by
    funext z
    exact (gaussianNoiseComplexMGF_hasDerivAt σ z).deriv
  have hlin : HasDerivAt (fun z : ℂ => (gaussianVariance σ : ℂ) * z)
      (gaussianVariance σ : ℂ) 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℂ)).const_mul (gaussianVariance σ : ℂ)
  have hf0 : HasDerivAt f 0 0 := by
    simpa [f, gaussianNoiseComplexMGF] using
      gaussianNoiseComplexMGF_hasDerivAt σ 0
  have hg : HasDerivAt g (gaussianVariance σ : ℂ) 0 := by
    dsimp [g]
    convert hlin.mul hf0 using 1 <;> simp [f, gaussianNoiseComplexMGF]
  calc
    iteratedDeriv 2 f 0 = deriv (deriv f) 0 := by simp [iteratedDeriv_succ]
    _ = deriv g 0 := by rw [hfderiv]
    _ = (gaussianVariance σ : ℂ) := hg.deriv

/-- The centered Gaussian noise has mean zero.

This is derived from the first derivative at zero of the complex MGF, rather than from the
post-4.19 convenience lemma `integral_id_gaussianReal`. -/
theorem gaussianNoiseMeasure_mean_zero (σ : ℝ) :
    (∫ ζ : ℝ, ζ ∂(gaussianNoiseMeasure σ)) = 0 := by
  have h0r := gaussianNoiseMeasure_zero_mem_interior_integrableExpSet σ
  have h0c : (0 : ℂ).re ∈ interior
      (ProbabilityTheory.integrableExpSet id (gaussianNoiseMeasure σ)) := by
    simpa using h0r
  have hm := ProbabilityTheory.iteratedDeriv_complexMGF
    (X := id) (μ := gaussianNoiseMeasure σ) (z := (0 : ℂ)) h0c 1
  rw [gaussianNoiseMeasure_complexMGF_eq σ,
    gaussianNoiseComplexMGF_first_iteratedDeriv_zero σ] at hm
  have hc : (∫ ζ : ℝ, (ζ : ℂ) ∂(gaussianNoiseMeasure σ)) = 0 := by
    simpa [id_eq] using hm.symm
  have hcast : (((∫ ζ : ℝ, ζ ∂(gaussianNoiseMeasure σ)) : ℝ) : ℂ) = 0 := by
    rw [← integral_complex_ofReal]
    exact hc
  exact_mod_cast hcast

/-- The centered Gaussian noise has second moment exactly `σ²`.

Again we use the second derivative at zero of the complex MGF.  This route is available in the
project's pinned Mathlib 4.19 even though the later `variance_id_gaussianReal` wrapper is not. -/
theorem gaussianNoiseMeasure_second_moment (σ : ℝ) :
    (∫ ζ : ℝ, ζ ^ 2 ∂(gaussianNoiseMeasure σ)) = σ ^ 2 := by
  have h0r := gaussianNoiseMeasure_zero_mem_interior_integrableExpSet σ
  have h0c : (0 : ℂ).re ∈ interior
      (ProbabilityTheory.integrableExpSet id (gaussianNoiseMeasure σ)) := by
    simpa using h0r
  have hm := ProbabilityTheory.iteratedDeriv_complexMGF
    (X := id) (μ := gaussianNoiseMeasure σ) (z := (0 : ℂ)) h0c 2
  rw [gaussianNoiseMeasure_complexMGF_eq σ,
    gaussianNoiseComplexMGF_second_iteratedDeriv_zero σ] at hm
  have hc :
      (∫ ζ : ℝ, ((ζ ^ 2 : ℝ) : ℂ) ∂(gaussianNoiseMeasure σ)) =
        (gaussianVariance σ : ℂ) := by
    simpa [id_eq] using hm.symm
  have hcast :
      (((∫ ζ : ℝ, ζ ^ 2 ∂(gaussianNoiseMeasure σ)) : ℝ) : ℂ) =
        ((gaussianVariance σ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simpa using hc
  have hreal :
      (∫ ζ : ℝ, ζ ^ 2 ∂(gaussianNoiseMeasure σ)) =
        (gaussianVariance σ : ℝ) := by
    exact_mod_cast hcast
  simpa [gaussianVariance] using hreal

/-- The Gaussian-location separation `a = 4ε/L̄` is strictly positive. -/
theorem gaussianA_pos (Lbar ε : ℝ) (hL : 0 < Lbar) (hε : 0 < ε) :
    0 < gaussianA Lbar ε := by
  rw [gaussianA]
  positivity

/-- If the output has the wrong sign for either endpoint, its population gradient is at least
`4 ε` in magnitude.  This is the deterministic last step of Proposition 4.6. -/
theorem gaussian_wrong_sign_gradient (Lbar ε x θ : ℝ)
    (hL : 0 < Lbar) (hε : 0 < ε)
    (hθ : θ = gaussianA Lbar ε ∨ θ = - gaussianA Lbar ε)
    (hsign : x * θ ≤ 0) :
    4 * ε ≤ |gaussianLocationGradPhi Lbar θ x| := by
  have ha : 0 < gaussianA Lbar ε := gaussianA_pos Lbar ε hL hε
  have hLa : Lbar * gaussianA Lbar ε = 4 * ε :=
    gaussian_Lbar_mul_a Lbar ε hL
  rcases hθ with rfl | rfl
  · have hx : x ≤ 0 := by
      by_contra hnx
      have hxpos : 0 < x := lt_of_not_ge hnx
      have : 0 < x * gaussianA Lbar ε := mul_pos hxpos ha
      linarith
    have hxm : x - gaussianA Lbar ε ≤ 0 := by linarith
    have hxterm : Lbar * x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hL) hx
    have hprod : Lbar * (x - gaussianA Lbar ε) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hL) hxm
    rw [gaussianLocationGradPhi, abs_of_nonpos hprod]
    nlinarith
  · have hx : 0 ≤ x := by
      by_contra hnx
      have hxneg : x < 0 := lt_of_not_ge hnx
      have hnegA : -gaussianA Lbar ε < 0 := neg_lt_zero.mpr ha
      have : 0 < x * (-gaussianA Lbar ε) := mul_pos_of_neg_of_neg hxneg hnegA
      linarith
    have hxp : 0 ≤ x - (-gaussianA Lbar ε) := by linarith
    have hxterm : 0 ≤ Lbar * x := mul_nonneg (le_of_lt hL) hx
    have hprod : 0 ≤ Lbar * (x - (-gaussianA Lbar ε)) :=
      mul_nonneg (le_of_lt hL) hxp
    rw [gaussianLocationGradPhi, abs_of_nonneg hprod]
    nlinarith

/-- The sign-test error probability `1/4` times the squared wrong-sign gradient `16ε²`
strictly exceeds the target risk `ε²`. -/
theorem gaussian_risk_endpoint_exact (ε : ℝ) (hε : 0 < ε) :
    ε ^ 2 < (1 / 4 : ℝ) * (4 * ε) ^ 2 := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  nlinarith

/-- A compact package of the Gaussian facts that do not involve product-transcript KL/Pinsker or
algorithm-to-statistic causality.  These are exactly the elementary analytic fields consumed by the
later Proposition-4.6 assembly. -/
structure GaussianPrimitiveCertificate (Lbar Δ σ ε : ℝ) where
  mean_separation : 2 * Lbar * gaussianA Lbar ε = 8 * ε
  initial_gap_value : Lbar * (gaussianA Lbar ε) ^ 2 / 2 = 8 * ε ^ 2 / Lbar
  initial_gap_bound : Lbar * (gaussianA Lbar ε) ^ 2 / 2 ≤ Δ
  noise_probability : gaussianNoiseMeasure σ Set.univ = 1
  noise_mean_zero : (∫ ζ : ℝ, ζ ∂(gaussianNoiseMeasure σ)) = 0
  noise_second_moment : (∫ ζ : ℝ, ζ ^ 2 ∂(gaussianNoiseMeasure σ)) = σ ^ 2
  same_seed_difference : ∀ x x' θ ζ,
    gaussianOracleX Lbar θ x ζ - gaussianOracleX Lbar θ x' ζ = Lbar * (x - x')
  wrong_sign_gradient : ∀ x θ,
    (θ = gaussianA Lbar ε ∨ θ = -gaussianA Lbar ε) → x * θ ≤ 0 →
      4 * ε ≤ |gaussianLocationGradPhi Lbar θ x|
  risk_endpoint : ε ^ 2 < (1 / 4 : ℝ) * (4 * ε) ^ 2

/-- Canonical proof of the elementary Gaussian-location block from Proposition 4.6. -/
noncomputable def canonicalGaussianPrimitiveCertificate
    (Lbar Δ σ ε : ℝ) (hL : 0 < Lbar) (hε : 0 < ε)
    (hsmall : ε ^ 2 ≤ Lbar * Δ / 8) :
    GaussianPrimitiveCertificate Lbar Δ σ ε where
  mean_separation := gaussian_mean_separation_exact Lbar ε hL
  initial_gap_value := gaussian_initial_gap_value_exact Lbar ε hL
  initial_gap_bound := gaussian_initial_gap_le_delta Lbar Δ ε hL hsmall
  noise_probability := gaussianNoiseMeasure_probability σ
  noise_mean_zero := gaussianNoiseMeasure_mean_zero σ
  noise_second_moment := gaussianNoiseMeasure_second_moment σ
  same_seed_difference := fun x x' θ ζ =>
    gaussianOracleX_same_seed_difference Lbar θ x x' ζ
  wrong_sign_gradient := fun x θ hθ hs =>
    gaussian_wrong_sign_gradient Lbar ε x θ hL hε hθ hs
  risk_endpoint := gaussian_risk_endpoint_exact ε hε

end PaperExact
end NCSCPureStochasticLB


namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

theorem gaussian_two_point_oracle_x_same_statistic
    {Lbar μ Δ σ ε : ℝ} (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (x y : Vec 1) (s : ℝ) :
    F.plusO.Gx x y (s + Lbar * gaussianA Lbar ε) =
      F.minusO.Gx x y (s - Lbar * gaussianA Lbar ε) := by
  rw [F.plus_oracle_x_def, F.minus_oracle_x_def]
  funext i
  simp only [vecOfScalar1, gaussianOracleX]
  ring

theorem gaussian_two_point_oracle_y_same_statistic
    {Lbar μ Δ σ ε : ℝ} (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (x y : Vec 1) (sp sm : ℝ) :
    F.plusO.Gy x y sp = F.minusO.Gy x y sm := by
  rw [F.plus_oracle_y_def, F.minus_oracle_y_def]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

theorem gaussian_two_point_same_responses
    {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO)
    (s : Fin R → ℝ) :
    ∀ t : Fin R, ∀ k : Fin K,
      (A.plus.trace s).response t k = (A.minus.trace s).response t k := by
  have hp : ∀ n : ℕ, n ≤ R →
      ∀ t : Fin R, t.1 < n → ∀ k : Fin K,
        (A.plus.trace s).response t k = (A.minus.trace s).response t k := by
    intro n
    induction n with
    | zero =>
        intro hn t ht k
        omega
    | succ n ih =>
        intro hn t ht k
        by_cases htn : t.1 < n
        · exact ih (by omega) t htn k
        · have hteq : t.1 = n := by omega
          have hq := A.shared_queries s s t (by
            intro r hr j
            exact ih (by omega) r (by omega) j)
          have hplus := A.plus.response_consistent s t k
          have hminus := A.minus.response_consistent s t k
          rw [hplus, hminus, hq]
          cases hslot : (A.minus.trace s).query t k with
          | none => simp [hslot]
          | some q =>
              rcases q with ⟨x, y⟩
              simp only [hslot, Option.some.injEq, Prod.mk.injEq]
              constructor
              · simpa [sub_eq_add_neg, mul_neg] using
                  gaussian_two_point_oracle_x_same_statistic F x y (s t)
              · exact gaussian_two_point_oracle_y_same_statistic F x y
                  (s t + Lbar * gaussianA Lbar ε)
                  (s t + Lbar * (-gaussianA Lbar ε))
  intro t k
  exact hp R (le_refl R) t t.2 k

theorem gaussian_two_point_same_output
    {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO)
    (s : Fin R → ℝ) :
    (A.plus.trace s).output = (A.minus.trace s).output := by
  exact A.shared_output s s (gaussian_two_point_same_responses F A s)

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

theorem norm_vecOfScalar1_sq (r : ℝ) : ‖vecOfScalar1 r‖ ^ 2 = r ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  simp [vecOfScalar1, Real.sq_sqrt, sq_nonneg]

theorem gaussian_plus_gradPhi_norm_sq
    {Lbar μ Δ σ ε : ℝ} (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (x : Vec 1) :
    ‖F.plusI.gradPhi x‖ ^ 2 =
      (Lbar * (scalarOfVec1 x - gaussianA Lbar ε)) ^ 2 := by
  rw [F.plus_gradPhi_def]
  exact norm_vecOfScalar1_sq _

theorem gaussian_minus_gradPhi_norm_sq
    {Lbar μ Δ σ ε : ℝ} (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (x : Vec 1) :
    ‖F.minusI.gradPhi x‖ ^ 2 =
      (Lbar * (scalarOfVec1 x + gaussianA Lbar ε)) ^ 2 := by
  rw [F.minus_gradPhi_def]
  simpa [gaussianLocationGradPhi] using
    norm_vecOfScalar1_sq (gaussianLocationGradPhi Lbar (-gaussianA Lbar ε) (scalarOfVec1 x))

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

noncomputable def canonicalGaussianAlgorithmReduction
    {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO) :
    GaussianAlgorithmToStatisticReduction F E A where
  estimator := {
    toFun := fun s => scalarOfVec1 ((A.plus.trace s).output)
    measurable_toFun := A.plus.output_measurable }
  plus_output := fun _ => rfl
  minus_output := by
    intro s
    rw [← gaussian_two_point_same_output F A s]
  plus_risk_eq := by
    change (∫⁻ s, ENNReal.ofReal (‖F.plusI.gradPhi ((A.plus.trace s).output)‖ ^ 2)
        ∂E.plusMeasure) =
      ∫⁻ s, ENNReal.ofReal ((Lbar *
        (scalarOfVec1 ((A.plus.trace s).output) - gaussianA Lbar ε)) ^ 2)
        ∂E.plusMeasure
    congr 1
    funext s
    rw [gaussian_plus_gradPhi_norm_sq]
  minus_risk_eq := by
    change (∫⁻ s, ENNReal.ofReal (‖F.minusI.gradPhi ((A.minus.trace s).output)‖ ^ 2)
        ∂E.minusMeasure) =
      ∫⁻ s, ENNReal.ofReal ((Lbar *
        (scalarOfVec1 ((A.plus.trace s).output) + gaussianA Lbar ε)) ^ 2)
        ∂E.minusMeasure
    congr 1
    funext s
    rw [gaussian_minus_gradPhi_norm_sq,
      ← gaussian_two_point_same_output F A s]

end PaperExact
end NCSCPureStochasticLB


namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

theorem vecOfScalar1_scalarOfVec1 (x : Vec 1) :
    vecOfScalar1 (scalarOfVec1 x) = x := by
  funext i
  fin_cases i
  rfl

theorem norm_sub_vecOfScalar1_sq (x : Vec 1) (θ : ℝ) :
    ‖x - vecOfScalar1 θ‖ ^ 2 = (scalarOfVec1 x - θ) ^ 2 := by
  have h : x - vecOfScalar1 θ =
      vecOfScalar1 (scalarOfVec1 x - θ) := by
    funext i
    fin_cases i
    rfl
  rw [h, norm_vecOfScalar1_sq]

theorem quadratic_hasGradientAt (c : ℝ) (a x : Vec 1) :
    HasGradientAt (fun z : Vec 1 => c / 2 * ‖z - a‖ ^ 2)
      (c • (x - a)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsub0 : HasFDerivAt (fun z : Vec 1 => z - a)
      ((1 : Vec 1 →L[ℝ] Vec 1) - 0) x :=
    (hasFDerivAt_id x).sub (hasFDerivAt_const  a x)
  have hsub : HasFDerivAt (fun z : Vec 1 => z - a)
      (1 : Vec 1 →L[ℝ] Vec 1) x := by
    simpa using hsub0
  have hsq := hsub.norm_sq
  have hmul := hsq.const_smul (c / 2)
  have hD :
      (c / 2) • (2 • (innerSL ℝ (x - a)).comp
        (1 : Vec 1 →L[ℝ] Vec 1)) =
      InnerProductSpace.toDual ℝ (Vec 1) (c • (x - a)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left,
      real_inner_smul_right]
    ring
  rw [hD] at hmul
  simpa [smul_eq_mul] using hmul

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

noncomputable def canonicalGaussianPopulation
    (Lbar μ θ : ℝ) (hμ : 0 < μ) : PopulationObjective 1 where
  f := fun x y => Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y‖ ^ 2
  gradX := fun x _ => Lbar • (x - vecOfScalar1 θ)
  gradY := fun _ y => (-μ) • y
  Phi := fun x => Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2
  gradPhi := fun x => Lbar • (x - vecOfScalar1 θ)
  gradX_spec := by
    intro x y
    change HasGradientAt (fun x' : Vec 1 =>
        Lbar / 2 * ‖x' - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y‖ ^ 2)
      (Lbar • (x - vecOfScalar1 θ)) x
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := (quadratic_hasGradientAt Lbar (vecOfScalar1 θ) x).hasFDerivAt
    have hc : HasFDerivAt (fun _ : Vec 1 => μ / 2 * ‖y‖ ^ 2)
        (0 : Vec 1 →L[ℝ] ℝ) x :=
      hasFDerivAt_const (μ / 2 * ‖y‖ ^ 2) x
    simpa using h.sub hc
  gradY_spec := by
    intro x y
    change HasGradientAt (fun y' : Vec 1 =>
        Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y'‖ ^ 2)
      ((-μ) • y) y
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := (quadratic_hasGradientAt (-μ) (0 : Vec 1) y).hasFDerivAt
    have hc : HasFDerivAt (fun _ : Vec 1 =>
        Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2)
        (0 : Vec 1 →L[ℝ] ℝ) y :=
      hasFDerivAt_const (Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2) y
    have hfun :
        (fun z : Vec 1 => Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖z‖ ^ 2) =
        (fun z : Vec 1 => Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 +
          (-μ) / 2 * ‖z‖ ^ 2) := by
      funext z
      ring
    rw [hfun]
    simpa using hc.add h
  gradPhi_spec := by
    intro x
    exact quadratic_hasGradientAt Lbar (vecOfScalar1 θ) x
  value_is_max := by
    intro x
    refine ⟨0, ?_, ?_⟩
    · simp
    · intro y
      change Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y‖ ^ 2 ≤
        Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2
      have hsq : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      have hfac : 0 ≤ μ / 2 := by positivity
      nlinarith [mul_nonneg hfac hsq]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

theorem canonicalGaussian_strong
    (Lbar μ θ : ℝ) (hμ : 0 < μ) :
    StronglyConcaveY (canonicalGaussianPopulation Lbar μ θ hμ) μ := by
  intro x y y'
  change Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y'‖ ^ 2 ≤
    Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y‖ ^ 2 +
      @inner ℝ (Vec 1) _ ((-μ) • y) (y' - y) - μ / 2 * ‖y' - y‖ ^ 2
  have hvec : y' = y + (y' - y) := by module
  have hnorm : ‖y'‖ ^ 2 = ‖y‖ ^ 2 +
      2 * @inner ℝ (Vec 1) _ y (y' - y) + ‖y' - y‖ ^ 2 := by
    calc
      ‖y'‖ ^ 2 = ‖y + (y' - y)‖ ^ 2 := congrArg (fun z => ‖z‖ ^ 2) hvec
      _ = _ := norm_add_sq_real y (y' - y)
  rw [hnorm]
  simp only [real_inner_smul_left]
  nlinarith

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

theorem pairNorm_two_smul_le
    (L μ : ℝ) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hle : μ ≤ L)
    (dx dy : Vec 1) :
    pairNorm (L • dx) ((-μ) • dy) ≤ L * pairNorm dx dy := by
  have hμsq : μ ^ 2 ≤ L ^ 2 := by nlinarith
  have hA : pairNorm (L • dx) ((-μ) • dy) ^ 2 =
      L ^ 2 * ‖dx‖ ^ 2 + μ ^ 2 * ‖dy‖ ^ 2 := by
    rw [pairNorm_sq_eq]
    simp only [norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg hL, abs_of_nonpos (neg_nonpos.mpr hμ)]
    ring
  have hB : (L * pairNorm dx dy) ^ 2 =
      L ^ 2 * (‖dx‖ ^ 2 + ‖dy‖ ^ 2) := by
    rw [mul_pow, pairNorm_sq_eq]
  have hterm : 0 ≤ (L ^ 2 - μ ^ 2) * ‖dy‖ ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hμsq) (sq_nonneg _)
  have hA0 : 0 ≤ pairNorm (L • dx) ((-μ) • dy) := pairNorm_nonneg _ _
  have hB0 : 0 ≤ L * pairNorm dx dy :=
    mul_nonneg hL (pairNorm_nonneg _ _)
  nlinarith

theorem canonicalGaussian_jointSmooth
    (Lbar μ θ : ℝ) (hL : 0 < Lbar) (hμ : 0 < μ) (hle : μ ≤ Lbar) :
    JointSmooth (canonicalGaussianPopulation Lbar μ θ hμ) Lbar := by
  intro x y x' y'
  change pairNorm
      (Lbar • (x - vecOfScalar1 θ) - Lbar • (x' - vecOfScalar1 θ))
      ((-μ) • y - (-μ) • y') ≤
    Lbar * pairNorm (x - x') (y - y')
  have hx : Lbar • (x - vecOfScalar1 θ) - Lbar • (x' - vecOfScalar1 θ) =
      Lbar • (x - x') := by module
  have hy : (-μ) • y - (-μ) • y' = (-μ) • (y - y') := by module
  rw [hx, hy]
  exact pairNorm_two_smul_le Lbar μ (le_of_lt hL) (le_of_lt hμ) hle _ _

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

theorem canonicalGaussian_bddBelow
    (Lbar μ θ : ℝ) (hL : 0 < Lbar) (hμ : 0 < μ) :
    BddBelow (Set.range (canonicalGaussianPopulation Lbar μ θ hμ).Phi) := by
  refine ⟨0, ?_⟩
  rintro z ⟨x, rfl⟩
  change 0 ≤ Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2
  positivity

theorem canonicalGaussian_initialGap
    (Lbar μ θ Δ : ℝ) (hL : 0 < Lbar) (hμ : 0 < μ)
    (hbudget : Lbar * θ ^ 2 / 2 ≤ Δ) :
    InitialGap (canonicalGaussianPopulation Lbar μ θ hμ) Δ := by
  let I := canonicalGaussianPopulation Lbar μ θ hμ
  have h0 : (0 : ℝ) ∈ Set.range I.Phi := by
    refine ⟨vecOfScalar1 θ, ?_⟩
    simp [I, canonicalGaussianPopulation]
  have hnonneg : ∀ z ∈ Set.range I.Phi, 0 ≤ z := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    change 0 ≤ Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2
    positivity
  have hbelow : BddBelow (Set.range I.Phi) := ⟨0, hnonneg⟩
  have hinf : sInf (Set.range I.Phi) = 0 := by
    apply le_antisymm
    · exact csInf_le hbelow h0
    · exact le_csInf (Set.range_nonempty _) hnonneg
  have horigin : I.Phi 0 = Lbar * θ ^ 2 / 2 := by
    change Lbar / 2 * ‖(0 : Vec 1) - vecOfScalar1 θ‖ ^ 2 =
      Lbar * θ ^ 2 / 2
    rw [norm_sub_vecOfScalar1_sq]
    simp [scalarOfVec1]
    ring
  change I.Phi 0 - sInf (Set.range I.Phi) ≤ Δ
  rw [hinf, horigin]
  simpa using hbudget

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

theorem gaussianNoiseMeasure_integrable_id (σ : ℝ) :
    Integrable (fun ζ : ℝ => ζ) (gaussianNoiseMeasure σ) := by
  have h := gaussianNoiseMeasure_zero_mem_interior_integrableExpSet σ
  have hi := ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet h 1
  simpa using hi

theorem vecOfScalar1_eq_smul (ζ : ℝ) :
    vecOfScalar1 ζ = ζ • vecOfScalar1 1 := by
  funext i
  fin_cases i
  simp [vecOfScalar1]

theorem gaussianNoiseMeasure_integrable_vec (σ : ℝ) :
    Integrable (fun ζ : ℝ => vecOfScalar1 ζ) (gaussianNoiseMeasure σ) := by
  have h := (gaussianNoiseMeasure_integrable_id σ).smul_const (vecOfScalar1 1)
  simpa only [← vecOfScalar1_eq_smul] using h

theorem gaussianNoiseMeasure_integral_vec (σ : ℝ) :
    (∫ ζ : ℝ, vecOfScalar1 ζ ∂(gaussianNoiseMeasure σ)) = 0 := by
  have hfun : (fun ζ : ℝ => vecOfScalar1 ζ) =
      (fun ζ : ℝ => ζ • vecOfScalar1 1) := by
    funext ζ
    exact vecOfScalar1_eq_smul ζ
  rw [hfun, integral_smul_const, gaussianNoiseMeasure_mean_zero σ]
  simp

noncomputable def canonicalGaussianOracle (Lbar μ θ : ℝ) :
    StochasticOracle 1 ℝ where
  Gx := fun x _ ζ => Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ
  Gy := fun _ y _ => (-μ) • y

theorem canonicalGaussianOracle_x_def (Lbar μ θ : ℝ)
    (x y : Vec 1) (ζ : ℝ) :
    (canonicalGaussianOracle Lbar μ θ).Gx x y ζ =
      vecOfScalar1 (gaussianOracleX Lbar θ (scalarOfVec1 x) ζ) := by
  funext i
  fin_cases i
  simp [canonicalGaussianOracle, vecOfScalar1, gaussianOracleX,
    scalarOfVec1]

theorem canonicalGaussianOracle_y_def (Lbar μ θ : ℝ)
    (x y : Vec 1) (ζ : ℝ) :
    (canonicalGaussianOracle Lbar μ θ).Gy x y ζ =
      vecOfScalar1 (gaussianOracleY μ (scalarOfVec1 y)) := by
  funext i
  fin_cases i
  simp [canonicalGaussianOracle, vecOfScalar1, gaussianOracleY,
    scalarOfVec1]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

theorem canonicalGaussian_unbiased
    (Lbar μ θ σ : ℝ) (hμ : 0 < μ) :
    OracleUnbiased (canonicalGaussianPopulation Lbar μ θ hμ)
      (gaussianLaw σ) (canonicalGaussianOracle Lbar μ θ) := by
  letI : IsProbabilityMeasure (gaussianNoiseMeasure σ) := by
    unfold gaussianNoiseMeasure
    infer_instance
  intro x y
  constructor
  · change (∫ ζ : ℝ,
        Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ
        ∂(gaussianNoiseMeasure σ)) = Lbar • (x - vecOfScalar1 θ)
    rw [integral_add (integrable_const _) (gaussianNoiseMeasure_integrable_vec σ),
      integral_const, gaussianNoiseMeasure_integral_vec σ]
    simp
  · change (∫ ζ : ℝ, (-μ) • y ∂(gaussianNoiseMeasure σ)) = (-μ) • y
    simp

theorem canonicalGaussian_variance
    (Lbar μ θ σ : ℝ) (hμ : 0 < μ) :
    OracleBoundedVariance (canonicalGaussianPopulation Lbar μ θ hμ)
      (gaussianLaw σ) (canonicalGaussianOracle Lbar μ θ) σ := by
  intro x y
  change (∫ ζ : ℝ,
      ‖(Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ) -
        Lbar • (x - vecOfScalar1 θ)‖ ^ 2 +
      ‖(-μ) • y - (-μ) • y‖ ^ 2
      ∂(gaussianNoiseMeasure σ)) ≤ σ ^ 2
  have hfun :
      (fun ζ : ℝ =>
        ‖(Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ) -
          Lbar • (x - vecOfScalar1 θ)‖ ^ 2 +
        ‖(-μ) • y - (-μ) • y‖ ^ 2) =
      (fun ζ : ℝ => ζ ^ 2) := by
    funext ζ
    simp [norm_vecOfScalar1_sq]
  rw [hfun, gaussianNoiseMeasure_second_moment σ]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

open MeasureTheory

theorem canonicalGaussian_averagedSmooth
    (Lbar μ θ σ : ℝ) (hL : 0 < Lbar) (hμ : 0 < μ) (hle : μ ≤ Lbar) :
    OracleAveragedSmooth (gaussianLaw σ)
      (canonicalGaussianOracle Lbar μ θ) Lbar := by
  letI : IsProbabilityMeasure (gaussianNoiseMeasure σ) := by
    unfold gaussianNoiseMeasure
    infer_instance
  intro x y x' y'
  change (∫ ζ : ℝ,
      ‖(Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ) -
        (Lbar • (x' - vecOfScalar1 θ) + vecOfScalar1 ζ)‖ ^ 2 +
      ‖(-μ) • y - (-μ) • y'‖ ^ 2
      ∂(gaussianNoiseMeasure σ)) ≤
    Lbar ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  have hx : ∀ ζ : ℝ,
      (Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ) -
        (Lbar • (x' - vecOfScalar1 θ) + vecOfScalar1 ζ) =
      Lbar • (x - x') := by
    intro ζ
    module
  have hy : (-μ) • y - (-μ) • y' = (-μ) • (y - y') := by module
  have hfun :
      (fun ζ : ℝ =>
        ‖(Lbar • (x - vecOfScalar1 θ) + vecOfScalar1 ζ) -
          (Lbar • (x' - vecOfScalar1 θ) + vecOfScalar1 ζ)‖ ^ 2 +
        ‖(-μ) • y - (-μ) • y'‖ ^ 2) =
      (fun _ : ℝ => pairNorm (Lbar • (x - x')) ((-μ) • (y - y')) ^ 2) := by
    funext ζ
    rw [hx ζ, hy, pairNorm_sq_eq]
  rw [hfun]
  simp only [integral_const]
  have hmass : (gaussianNoiseMeasure σ).real Set.univ = 1 := by
    simp [Measure.real, gaussianNoiseMeasure_probability σ]
  rw [hmass]
  simp only [one_smul]
  have hroot := pairNorm_two_smul_le Lbar μ
    (le_of_lt hL) (le_of_lt hμ) hle (x - x') (y - y')
  have hA0 := pairNorm_nonneg (Lbar • (x - x')) ((-μ) • (y - y'))
  have hB0 : 0 ≤ Lbar * pairNorm (x - x') (y - y') :=
    mul_nonneg (le_of_lt hL) (pairNorm_nonneg _ _)
  have hsq :
      pairNorm (Lbar • (x - x')) ((-μ) • (y - y')) ^ 2 ≤
        (Lbar * pairNorm (x - x') (y - y')) ^ 2 := by
    nlinarith
  calc
    pairNorm (Lbar • (x - x')) ((-μ) • (y - y')) ^ 2 ≤
        (Lbar * pairNorm (x - x') (y - y')) ^ 2 := hsq
    _ = Lbar ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
      rw [mul_pow, pairNorm_sq_eq]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

theorem norm_vec1_sq (x : Vec 1) :
    ‖x‖ ^ 2 = (scalarOfVec1 x) ^ 2 := by
  conv_lhs => rw [← vecOfScalar1_scalarOfVec1 x]
  exact norm_vecOfScalar1_sq _

theorem gaussian_population_f_def (Lbar μ θ : ℝ) (hμ : 0 < μ)
    (x y : Vec 1) :
    (canonicalGaussianPopulation Lbar μ θ hμ).f x y =
      gaussianLocationF Lbar μ θ (scalarOfVec1 x) (scalarOfVec1 y) := by
  change Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 - μ / 2 * ‖y‖ ^ 2 =
    gaussianLocationF Lbar μ θ (scalarOfVec1 x) (scalarOfVec1 y)
  rw [norm_sub_vecOfScalar1_sq, norm_vec1_sq]
  rfl

theorem gaussian_population_phi_def (Lbar μ θ : ℝ) (hμ : 0 < μ)
    (x : Vec 1) :
    (canonicalGaussianPopulation Lbar μ θ hμ).Phi x =
      gaussianLocationPhi Lbar θ (scalarOfVec1 x) := by
  change Lbar / 2 * ‖x - vecOfScalar1 θ‖ ^ 2 =
    gaussianLocationPhi Lbar θ (scalarOfVec1 x)
  rw [norm_sub_vecOfScalar1_sq]
  rfl

theorem gaussian_population_gradPhi_def (Lbar μ θ : ℝ) (hμ : 0 < μ)
    (x : Vec 1) :
    (canonicalGaussianPopulation Lbar μ θ hμ).gradPhi x =
      vecOfScalar1 (gaussianLocationGradPhi Lbar θ (scalarOfVec1 x)) := by
  funext i
  fin_cases i
  simp [canonicalGaussianPopulation, vecOfScalar1, gaussianLocationGradPhi,
    scalarOfVec1]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact

noncomputable def canonicalGaussianFamily
    (Lbar μ Δ σ ε : ℝ) (hL : 0 < Lbar) (hμ : 0 < μ)
    (hle : μ ≤ Lbar) (hε : 0 < ε)
    (hsmall : ε ^ 2 ≤ Lbar * Δ / 8) :
    GaussianFamilyCertificate Lbar μ Δ σ ε where
  plusI := canonicalGaussianPopulation Lbar μ (gaussianA Lbar ε) hμ
  minusI := canonicalGaussianPopulation Lbar μ (-gaussianA Lbar ε) hμ
  plusO := canonicalGaussianOracle Lbar μ (gaussianA Lbar ε)
  minusO := canonicalGaussianOracle Lbar μ (-gaussianA Lbar ε)
  plus_f_def := fun x y => gaussian_population_f_def Lbar μ (gaussianA Lbar ε) hμ x y
  minus_f_def := fun x y => gaussian_population_f_def Lbar μ (-gaussianA Lbar ε) hμ x y
  plus_phi_def := fun x => gaussian_population_phi_def Lbar μ (gaussianA Lbar ε) hμ x
  minus_phi_def := fun x => gaussian_population_phi_def Lbar μ (-gaussianA Lbar ε) hμ x
  plus_gradPhi_def := fun x => gaussian_population_gradPhi_def Lbar μ (gaussianA Lbar ε) hμ x
  minus_gradPhi_def := fun x => gaussian_population_gradPhi_def Lbar μ (-gaussianA Lbar ε) hμ x
  plus_oracle_x_def := fun x y ζ => canonicalGaussianOracle_x_def Lbar μ (gaussianA Lbar ε) x y ζ
  minus_oracle_x_def := fun x y ζ => canonicalGaussianOracle_x_def Lbar μ (-gaussianA Lbar ε) x y ζ
  plus_oracle_y_def := fun x y ζ => canonicalGaussianOracle_y_def Lbar μ (gaussianA Lbar ε) x y ζ
  minus_oracle_y_def := fun x y ζ => canonicalGaussianOracle_y_def Lbar μ (-gaussianA Lbar ε) x y ζ
  plus_ncsc := by
    exact ⟨canonicalGaussian_jointSmooth Lbar μ (gaussianA Lbar ε) hL hμ hle,
      canonicalGaussian_strong Lbar μ (gaussianA Lbar ε) hμ,
      canonicalGaussian_initialGap Lbar μ (gaussianA Lbar ε) Δ hL hμ
        (gaussian_initial_gap_le_delta Lbar Δ ε hL hsmall),
      canonicalGaussian_bddBelow Lbar μ (gaussianA Lbar ε) hL hμ⟩
  minus_ncsc := by
    have hbudget : Lbar * (-gaussianA Lbar ε) ^ 2 / 2 ≤ Δ := by
      simpa only [Even.neg_pow (by norm_num : Even 2)] using
        gaussian_initial_gap_le_delta Lbar Δ ε hL hsmall
    exact ⟨canonicalGaussian_jointSmooth Lbar μ (-gaussianA Lbar ε) hL hμ hle,
      canonicalGaussian_strong Lbar μ (-gaussianA Lbar ε) hμ,
      canonicalGaussian_initialGap Lbar μ (-gaussianA Lbar ε) Δ hL hμ hbudget,
      canonicalGaussian_bddBelow Lbar μ (-gaussianA Lbar ε) hL hμ⟩
  plus_unbiased := canonicalGaussian_unbiased Lbar μ (gaussianA Lbar ε) σ hμ
  minus_unbiased := canonicalGaussian_unbiased Lbar μ (-gaussianA Lbar ε) σ hμ
  plus_variance := canonicalGaussian_variance Lbar μ (gaussianA Lbar ε) σ hμ
  minus_variance := canonicalGaussian_variance Lbar μ (-gaussianA Lbar ε) σ hμ
  plus_averaged_smooth := canonicalGaussian_averagedSmooth Lbar μ (gaussianA Lbar ε) σ hL hμ hle
  minus_averaged_smooth := canonicalGaussian_averagedSmooth Lbar μ (-gaussianA Lbar ε) σ hL hμ hle
  noise_probability := gaussianNoiseMeasure_probability σ
  initial_gap_value := gaussian_initial_gap_value_exact Lbar ε hL
  initial_gap_bound := gaussian_initial_gap_le_delta Lbar Δ ε hL hsmall
  noise_mean_zero := gaussianNoiseMeasure_mean_zero σ
  noise_second_moment := gaussianNoiseMeasure_second_moment σ
  same_seed_difference := fun x x' θ ζ => gaussianOracleX_same_seed_difference Lbar θ x x' ζ

end PaperExact
end NCSCPureStochasticLB
namespace NCSCPureStochasticLB
namespace PaperExact

theorem proposition46_of_location_certificates
    (c : ℝ) (hc : 0 < c)
    (hloc : ∀ (R : ℕ) (Lbar σ ε : ℝ),
      0 < Lbar → 0 < ε → 0 < σ →
      (R : ℝ) ≤ c * σ ^ 2 / ε ^ 2 →
      Nonempty (GaussianLocationProofCertificate R Lbar σ ε)) :
    Proposition46Statement := by
  refine ⟨c, hc, ?_⟩
  intro Lbar μ Δ σ ε hL hμ hle hε hσ hsmall
  let F := canonicalGaussianFamily Lbar μ Δ σ ε hL hμ hle hε hsmall
  refine ⟨F, ?_⟩
  intro R hR
  obtain ⟨P⟩ := hloc R Lbar σ ε hL hε hσ hR
  refine ⟨P, ?_⟩
  intro K hK A
  let Red := canonicalGaussianAlgorithmReduction F P.experiment A
  refine ⟨Red, ?_, ?_⟩
  · exact P.every_estimator Red.estimator
  · rw [Red.plus_risk_eq, Red.minus_risk_eq]
    exact P.every_estimator Red.estimator


end PaperExact
end NCSCPureStochasticLB
namespace NCSCPureStochasticLB
namespace PaperExact
open MeasureTheory ProbabilityTheory

private theorem product_gaussian_marginal {R : ℕ} (m : Measure ℝ)
    [IsProbabilityMeasure m] (i : Fin R) :
    Measure.map (fun s : Fin R → ℝ => s i) (Measure.pi fun _ : Fin R => m) = m := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have heq : (fun s' : Fin R → ℝ => s' i) ⁻¹' s =
      Set.univ.pi (fun j : Fin R => if j = i then s else Set.univ) := by
    ext x
    simp [Set.mem_pi]
  rw [heq, Measure.pi_pi]
  have hm : m Set.univ = 1 := measure_univ
  simpa only [apply_ite, hm, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

private theorem product_gaussian_independent {R : ℕ} (m : Measure ℝ)
    [IsProbabilityMeasure m] :
    ProbabilityTheory.iIndepFun (fun i : Fin R => fun s : Fin R → ℝ => s i)
      (Measure.pi fun _ : Fin R => m) := by
  classical
  have hmeas : ∀ i : Fin R,
      AEMeasurable (fun s : Fin R → ℝ => s i) (Measure.pi fun _ : Fin R => m) := by
    intro i
    exact (measurable_pi_apply i).aemeasurable
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hmeas]
  have hmap : (Measure.pi fun _ : Fin R => m).map
      (fun s : Fin R → ℝ => fun i : Fin R => s i) =
      Measure.pi fun _ : Fin R => m := by
    simpa using Measure.map_id (Measure.pi fun _ : Fin R => m)
  rw [hmap]
  simp only [product_gaussian_marginal]

end PaperExact
end NCSCPureStochasticLB

namespace NCSCPureStochasticLB
namespace PaperExact
open MeasureTheory ProbabilityTheory

noncomputable def canonicalGaussianTranscript
    (R : ℕ) (Lbar a σ : ℝ)
    (hKL : (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar a σ)
      (Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar (-a) σ)).toReal =
      (R : ℝ) * (2 * Lbar * a) ^ 2 / (2 * σ ^ 2)) :
    GaussianTranscriptExperiment R Lbar a σ where
  plusMeasure := Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar a σ
  minusMeasure := Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar (-a) σ
  plus_probability := by
    haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar a σ) := by
      unfold gaussianStatisticMeasure
      infer_instance
    haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin R =>
      gaussianStatisticMeasure Lbar a σ) := inferInstance
    exact measure_univ
  minus_probability := by
    haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar (-a) σ) := by
      unfold gaussianStatisticMeasure
      infer_instance
    haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin R =>
      gaussianStatisticMeasure Lbar (-a) σ) := inferInstance
    exact measure_univ
  plus_marginal := by
    haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar a σ) := by
      unfold gaussianStatisticMeasure
      infer_instance
    intro t
    exact product_gaussian_marginal (gaussianStatisticMeasure Lbar a σ) t
  minus_marginal := by
    haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar (-a) σ) := by
      unfold gaussianStatisticMeasure
      infer_instance
    intro t
    exact product_gaussian_marginal (gaussianStatisticMeasure Lbar (-a) σ) t
  plus_independent := by
    haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar a σ) := by
      unfold gaussianStatisticMeasure
      infer_instance
    exact product_gaussian_independent (gaussianStatisticMeasure Lbar a σ)
  minus_independent := by
    haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar (-a) σ) := by
      unfold gaussianStatisticMeasure
      infer_instance
    exact product_gaussian_independent (gaussianStatisticMeasure Lbar (-a) σ)
  KL_value := hKL

end PaperExact
end NCSCPureStochasticLB
namespace NCSCPureStochasticLB
namespace PaperExact
open MeasureTheory

private theorem gaussian_plus_wrong_sign_risk {R : ℕ} {Lbar σ ε : ℝ}
    (hL : 0 < Lbar) (hε : 0 < ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (A : MeasurableEstimator R) :
    ENNReal.ofReal ((4 * ε) ^ 2) *
      E.plusMeasure {s | A.toFun s * gaussianA Lbar ε ≤ 0} ≤
      gaussianEstimatorRisk E true A := by
  let a := gaussianA Lbar ε
  let S : Set (Fin R → ℝ) := {s | A.toFun s * a ≤ 0}
  have hS : MeasurableSet S := by
    dsimp [S]
    simpa only [Set.preimage, Set.mem_Iic] using
      (A.measurable_toFun.mul_const a) measurableSet_Iic
  rw [← lintegral_indicator_const hS]
  change (∫⁻ s, S.indicator (fun _ => ENNReal.ofReal ((4 * ε) ^ 2)) s
      ∂E.plusMeasure) ≤
    ∫⁻ s, ENNReal.ofReal ((Lbar * (A.toFun s - a)) ^ 2) ∂E.plusMeasure
  apply lintegral_mono
  intro s
  by_cases hs : s ∈ S
  · rw [Set.indicator_of_mem hs]
    have hsgn : A.toFun s * a ≤ 0 := hs
    have hg := gaussian_wrong_sign_gradient Lbar ε (A.toFun s) a hL hε
      (Or.inl rfl) hsgn
    have hsq : (4 * ε) ^ 2 ≤ (Lbar * (A.toFun s - a)) ^ 2 := by
      rw [gaussianLocationGradPhi] at hg
      have := (sq_le_sq₀ (by positivity)
        (abs_nonneg (Lbar * (A.toFun s - a)))).mpr hg
      simpa only [sq_abs] using this
    exact ENNReal.ofReal_le_ofReal hsq
  · rw [Set.indicator_of_not_mem hs]
    exact bot_le


private theorem gaussian_minus_wrong_sign_risk {R : ℕ} {Lbar σ ε : ℝ}
    (hL : 0 < Lbar) (hε : 0 < ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (A : MeasurableEstimator R) :
    ENNReal.ofReal ((4 * ε) ^ 2) *
      E.minusMeasure {s | A.toFun s * (-gaussianA Lbar ε) ≤ 0} ≤
      gaussianEstimatorRisk E false A := by
  let a := -gaussianA Lbar ε
  let S : Set (Fin R → ℝ) := {s | A.toFun s * a ≤ 0}
  have hS : MeasurableSet S := by
    dsimp [S]
    simpa only [Set.preimage, Set.mem_Iic] using
      (A.measurable_toFun.mul_const a) measurableSet_Iic
  rw [← lintegral_indicator_const hS]
  change (∫⁻ s, S.indicator (fun _ => ENNReal.ofReal ((4 * ε) ^ 2)) s
      ∂E.minusMeasure) ≤
    ∫⁻ s, ENNReal.ofReal ((Lbar * (A.toFun s + gaussianA Lbar ε)) ^ 2) ∂E.minusMeasure
  apply lintegral_mono
  intro s
  by_cases hs : s ∈ S
  · rw [Set.indicator_of_mem hs]
    have hsgn : A.toFun s * a ≤ 0 := hs
    have hg := gaussian_wrong_sign_gradient Lbar ε (A.toFun s) a hL hε
      (Or.inr rfl) hsgn
    have hsq : (4 * ε) ^ 2 ≤ (Lbar * (A.toFun s + gaussianA Lbar ε)) ^ 2 := by
      rw [gaussianLocationGradPhi] at hg
      have hsub : A.toFun s - a = A.toFun s + gaussianA Lbar ε := by
        dsimp [a]
        ring
      rw [hsub] at hg
      have := (sq_le_sq₀ (by positivity)
        (abs_nonneg (Lbar * (A.toFun s + gaussianA Lbar ε)))).mpr hg
      simpa only [sq_abs] using this
    exact ENNReal.ofReal_le_ofReal hsq
  · rw [Set.indicator_of_not_mem hs]
    exact bot_le


theorem gaussian_every_estimator_of_sign_error {R : ℕ} {Lbar σ ε : ℝ}
    (hL : 0 < Lbar) (hε : 0 < ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (hsign : ∀ A : MeasurableEstimator R,
      1 / 4 ≤ gaussianAverageSignError E A)
    (A : MeasurableEstimator R) :
    ENNReal.ofReal (ε ^ 2) <
      max (gaussianEstimatorRisk E true A)
        (gaussianEstimatorRisk E false A) := by
  let p := E.plusMeasure {s | A.toFun s * gaussianA Lbar ε ≤ 0}
  let m := E.minusMeasure {s | A.toFun s * (-gaussianA Lbar ε) ≤ 0}
  have hpfin : p ≠ ⊤ := by
    have hp : p ≤ 1 := by
      calc
        p ≤ E.plusMeasure Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := E.plus_probability
    exact (lt_of_le_of_lt hp (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hmfin : m ≠ ⊤ := by
    have hm : m ≤ 1 := by
      calc
        m ≤ E.minusMeasure Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := E.minus_probability
    exact (lt_of_le_of_lt hm (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hsum : (1 / 2 : ℝ) ≤ p.toReal + m.toReal := by
    have h := hsign A
    change 1 / 4 ≤ (p.toReal + m.toReal) / 2 at h
    linarith
  have hchoice : (1 / 4 : ℝ) ≤ p.toReal ∨
      (1 / 4 : ℝ) ≤ m.toReal := by
    by_contra hn
    push_neg at hn
    linarith
  have hendpoint : ENNReal.ofReal (ε ^ 2) <
      ENNReal.ofReal ((4 * ε) ^ 2) * ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg (4 * ε))]
    have h := gaussian_risk_endpoint_exact ε hε
    rw [mul_comm (1 / 4 : ℝ) ((4 * ε) ^ 2)] at h
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h
  rcases hchoice with hp | hm
  · have hp' : ENNReal.ofReal (1 / 4 : ℝ) ≤ p :=
      (ENNReal.ofReal_le_iff_le_toReal hpfin).mpr hp
    have hrisk := gaussian_plus_wrong_sign_risk hL hε E A
    exact lt_of_lt_of_le hendpoint
      (le_trans (mul_le_mul_left' hp' _) (le_trans hrisk (le_max_left _ _)))
  · have hm' : ENNReal.ofReal (1 / 4 : ℝ) ≤ m :=
      (ENNReal.ofReal_le_iff_le_toReal hmfin).mpr hm
    have hrisk := gaussian_minus_wrong_sign_risk hL hε E A
    exact lt_of_lt_of_le hendpoint
      (le_trans (mul_le_mul_left' hm' _) (le_trans hrisk (le_max_right _ _)))


/-- A sum-form strengthening of the Gaussian testing conclusion.  It is the form needed to
average over an independent internal algorithmic seed: the *same* lower bound holds for every
seed realization before integration, so the bad hidden sign cannot swap with the seed and defeat
the minimax conclusion. -/
theorem gaussian_every_estimator_sum_lower_of_sign_error {R : ℕ} {Lbar σ ε : ℝ}
    (hL : 0 < Lbar) (hε : 0 < ε)
    (E : GaussianTranscriptExperiment R Lbar (gaussianA Lbar ε) σ)
    (hsign : ∀ A : MeasurableEstimator R,
      1 / 4 ≤ gaussianAverageSignError E A)
    (A : MeasurableEstimator R) :
    ENNReal.ofReal (4 * ε ^ 2) ≤
      gaussianEstimatorRisk E true A + gaussianEstimatorRisk E false A := by
  let p := E.plusMeasure {s | A.toFun s * gaussianA Lbar ε ≤ 0}
  let m := E.minusMeasure {s | A.toFun s * (-gaussianA Lbar ε) ≤ 0}
  have hpfin : p ≠ ⊤ := by
    have hp : p ≤ 1 := by
      calc
        p ≤ E.plusMeasure Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := E.plus_probability
    exact (lt_of_le_of_lt hp (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hmfin : m ≠ ⊤ := by
    have hm : m ≤ 1 := by
      calc
        m ≤ E.minusMeasure Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := E.minus_probability
    exact (lt_of_le_of_lt hm (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hsum : (1 / 2 : ℝ) ≤ p.toReal + m.toReal := by
    have h := hsign A
    change 1 / 4 ≤ (p.toReal + m.toReal) / 2 at h
    linarith
  have hp_le : p ≤ 1 := by
    calc
      p ≤ E.plusMeasure Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := E.plus_probability
  have hm_le : m ≤ 1 := by
    calc
      m ≤ E.minusMeasure Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := E.minus_probability
  have hpmfin : p + m ≠ ⊤ := by
    have hpm_le : p + m ≤ (2 : ENNReal) := by
      calc
        p + m ≤ 1 + 1 := add_le_add hp_le hm_le
        _ = 2 := by norm_num
    exact ne_top_of_le_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hpm_le
  have hpm : ENNReal.ofReal (1 / 2 : ℝ) ≤ p + m := by
    apply (ENNReal.ofReal_le_iff_le_toReal hpmfin).mpr
    rw [ENNReal.toReal_add hpfin hmfin]
    exact hsum
  have hplus := gaussian_plus_wrong_sign_risk hL hε E A
  have hminus := gaussian_minus_wrong_sign_risk hL hε E A
  have hrisks :
      ENNReal.ofReal ((4 * ε) ^ 2) * (p + m) ≤
        gaussianEstimatorRisk E true A + gaussianEstimatorRisk E false A := by
    rw [mul_add]
    exact add_le_add hplus hminus
  have hconst :
      ENNReal.ofReal (4 * ε ^ 2) ≤
        ENNReal.ofReal ((4 * ε) ^ 2) * ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg (4 * ε))]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg ε]
  exact hconst.trans <|
    (mul_le_mul_left' hpm (ENNReal.ofReal ((4 * ε) ^ 2))).trans hrisks

/-- Sum-risk form for an actual legal same-seed response-causal run.  The statistical reduction
uses one estimator under both hidden signs, so the estimator sum bound transfers exactly back to
the oracle run. -/
theorem gaussian_run_risk_sum_lower
    {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (P : GaussianLocationProofCertificate R Lbar σ ε)
    (A : GaussianTwoPointRun R K Lbar (gaussianA Lbar ε) F.plusO F.minusO) :
    ENNReal.ofReal (4 * ε ^ 2) ≤
      gaussianRunRisk F P.experiment A true +
        gaussianRunRisk F P.experiment A false := by
  let Red := canonicalGaussianAlgorithmReduction F P.experiment A
  rw [Red.plus_risk_eq, Red.minus_risk_eq]
  exact gaussian_every_estimator_sum_lower_of_sign_error
    P.Lbar_pos P.epsilon_pos P.experiment P.pinsker_sign_error Red.estimator

/-- v43 randomized completion of Proposition 4.6.  For every fixed internal seed, the two hidden
instances have a uniform *sum* risk lower bound.  Integrating this inequality against the same
independent seed law prevents the bad hidden sign from depending on the seed.  Consequently one
of the two fully randomized risks is still strictly larger than `ε²`. -/
theorem gaussian_internal_random_risk_lower
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {R K : ℕ} {Lbar μ Δ σ ε : ℝ}
    (F : GaussianFamilyCertificate Lbar μ Δ σ ε)
    (P : GaussianLocationProofCertificate R Lbar σ ε)
    (A : GaussianInternalRandomRun Ω ρ (R := R) (K := K) F P.experiment) :
    ENNReal.ofReal (ε ^ 2) <
      max (gaussianInternalRandomRisk ρ F P.experiment A true)
        (gaussianInternalRandomRisk ρ F P.experiment A false) := by
  have hsum : ENNReal.ofReal (4 * ε ^ 2) ≤
      gaussianInternalRandomRisk ρ F P.experiment A true +
        gaussianInternalRandomRisk ρ F P.experiment A false := by
    calc
      ENNReal.ofReal (4 * ε ^ 2) =
          ∫⁻ _ω : Ω, ENNReal.ofReal (4 * ε ^ 2) ∂ρ := by simp
      _ ≤ ∫⁻ ω,
          gaussianRunRisk F P.experiment (A.run ω) true +
            gaussianRunRisk F P.experiment (A.run ω) false ∂ρ := by
        apply lintegral_mono
        intro ω
        exact gaussian_run_risk_sum_lower F P (A.run ω)
      _ = gaussianInternalRandomRisk ρ F P.experiment A true +
          gaussianInternalRandomRisk ρ F P.experiment A false := by
        rw [lintegral_add_left A.plus_risk_measurable]
        rfl
  by_contra hn
  have hmax :
      max (gaussianInternalRandomRisk ρ F P.experiment A true)
          (gaussianInternalRandomRisk ρ F P.experiment A false) ≤
        ENNReal.ofReal (ε ^ 2) := le_of_not_gt hn
  have hplus : gaussianInternalRandomRisk ρ F P.experiment A true ≤
      ENNReal.ofReal (ε ^ 2) :=
    (le_max_left _ _).trans hmax
  have hminus : gaussianInternalRandomRisk ρ F P.experiment A false ≤
      ENNReal.ofReal (ε ^ 2) :=
    (le_max_right _ _).trans hmax
  have hsum_le :
      gaussianInternalRandomRisk ρ F P.experiment A true +
          gaussianInternalRandomRisk ρ F P.experiment A false ≤
        ENNReal.ofReal (ε ^ 2) + ENNReal.ofReal (ε ^ 2) :=
    add_le_add hplus hminus
  have htwo_lt_four :
      ENNReal.ofReal (ε ^ 2) + ENNReal.ofReal (ε ^ 2) <
        ENNReal.ofReal (4 * ε ^ 2) := by
    rw [← ENNReal.ofReal_add (sq_nonneg ε) (sq_nonneg ε)]
    have heps : 0 < 4 * ε ^ 2 := by nlinarith [sq_pos_of_pos P.epsilon_pos]
    apply (ENNReal.ofReal_lt_ofReal_iff heps).2
    nlinarith [sq_pos_of_pos P.epsilon_pos]
  exact (not_le_of_gt htwo_lt_four) (hsum.trans hsum_le)

/-- Assemble the v43 randomized Proposition 4.6 from the same exact Gaussian-location
certificates used by the deterministic response-causal statement. -/
theorem proposition46_randomized_of_location_certificates
    (c : ℝ) (hc : 0 < c)
    (hloc : ∀ (R : ℕ) (Lbar σ ε : ℝ),
      0 < Lbar → 0 < ε → 0 < σ →
      (R : ℝ) ≤ c * σ ^ 2 / ε ^ 2 →
      Nonempty (GaussianLocationProofCertificate R Lbar σ ε)) :
    Proposition46RandomizedStatement.{uΩ} := by
  refine ⟨c, hc, ?_⟩
  intro Lbar μ Δ σ ε hL hμ hle hε hσ hsmall
  let F := canonicalGaussianFamily Lbar μ Δ σ ε hL hμ hle hε hsmall
  refine ⟨F, ?_⟩
  intro R hR
  obtain ⟨P⟩ := hloc R Lbar σ ε hL hε hσ hR
  refine ⟨P, ?_⟩
  intro Ω _ ρ _ K hK A
  exact gaussian_internal_random_risk_lower ρ F P A


end PaperExact
end NCSCPureStochasticLB
namespace NCSCPureStochasticLB
namespace PaperExact
open MeasureTheory

noncomputable def canonicalGaussianLocationProofCertificate
    (R : ℕ) (Lbar σ ε : ℝ)
    (hL : 0 < Lbar) (hσ : 0 < σ) (hε : 0 < ε)
    (hKL : (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (gaussianA Lbar ε) σ)
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (-gaussianA Lbar ε) σ)).toReal =
      (R : ℝ) * (2 * Lbar * gaussianA Lbar ε) ^ 2 / (2 * σ ^ 2))
    (hsign : ∀ A : MeasurableEstimator R,
      1 / 4 ≤ gaussianAverageSignError
        (canonicalGaussianTranscript R Lbar (gaussianA Lbar ε) σ hKL) A) :
    GaussianLocationProofCertificate R Lbar σ ε where
  Lbar_pos := hL
  epsilon_pos := hε
  sigma_pos := hσ
  experiment := canonicalGaussianTranscript R Lbar (gaussianA Lbar ε) σ hKL
  mean_separation := gaussian_mean_separation_exact Lbar ε hL
  KL_formula := by
    have h := (canonicalGaussianTranscript R Lbar (gaussianA Lbar ε) σ hKL).KL_value
    rw [gaussian_mean_separation_exact Lbar ε hL] at h
    exact h
  pinsker_sign_error := hsign
  wrong_sign_gradient := fun x θ hθ hs =>
    gaussian_wrong_sign_gradient Lbar ε x θ hL hε hθ hs
  risk_endpoint := gaussian_risk_endpoint_exact ε hε
  every_estimator := gaussian_every_estimator_of_sign_error hL hε
    (canonicalGaussianTranscript R Lbar (gaussianA Lbar ε) σ hKL) hsign

end PaperExact
end NCSCPureStochasticLB
