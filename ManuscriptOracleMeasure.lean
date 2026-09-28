import ManuscriptRectangular
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

def bernoulliMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

instance bernoulliMeasure_finite (p : ℝ) : IsFiniteMeasure (bernoulliMeasure p) := by
  constructor
  simp [bernoulliMeasure]

theorem bernoulliMeasure_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p) := by
  constructor
  simp only [bernoulliMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  norm_num

theorem bernoulliMeasure_singleton (p : ℝ) (b : Bool) :
    bernoulliMeasure p {b} = ENNReal.ofReal (if b then p else 1 - p) := by
  cases b <;> simp [bernoulliMeasure]

theorem integral_bernoulliMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → E) :
    (∫ b, f b ∂bernoulliMeasure p) = p • f true + (1 - p) • f false := by
  rw [integral_fintype f Integrable.of_finite]
  simp [Measure.real, bernoulliMeasure_singleton, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1), add_comm]

theorem integral_bernoulliReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    (∫ b, f b ∂bernoulliMeasure p) = (bernoulliLaw p).expectReal f := by
  rw [integral_bernoulliMeasure p hp0 hp1]
  rfl

theorem integral_bernoulliVec {T : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → Vec T) :
    (∫ b, f b ∂bernoulliMeasure p) = (bernoulliLaw p).expectVec f := by
  rw [integral_bernoulliMeasure p hp0 hp1]
  rfl

/-- A genuine finite product: every round uses an independent seed with law ν. -/
def iidRoundMeasure {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) (N : ℕ) :
    Measure (Fin N → Seed) := Measure.pi (fun _ => ν)

theorem iidRoundMeasure_probability {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    IsProbabilityMeasure (iidRoundMeasure ν N) := by
  unfold iidRoundMeasure
  infer_instance

theorem iidRoundMeasure_rectangle {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) (s : Fin N → Set Seed) :
    iidRoundMeasure ν N (Set.univ.pi s) = ∏ t, ν (s t) :=
  Measure.pi_pi (fun _ : Fin N => ν) s

theorem roundMeasure_singleton (p : ℝ) {N : ℕ} (w : RoundWorld N) :
    roundMeasure p N {w} = ENNReal.ofReal (roundWeight p w) := by
  rw [roundMeasure, Measure.sum_apply _ (measurableSet_singleton w), tsum_fintype]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply]
  simp

/-- The earlier weighted finite-world law is exactly the i.i.d. product law. -/
theorem iidRoundMeasure_bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    iidRoundMeasure (bernoulliMeasure p) N = roundMeasure p N := by
  apply Measure.ext_of_singleton
  intro w
  have hs : ({w} : Set (Fin N → Bool)) = Set.univ.pi (fun t => {w t}) := by
    ext v
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_const]
    exact funext_iff
  rw [roundMeasure_singleton, iidRoundMeasure, hs, Measure.pi_pi]
  simp only [bernoulliMeasure_singleton, roundWeight]
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro t ht
  cases w t <;> simp [hp0, sub_nonneg.mpr hp1]

namespace MeasuredOracle

universe u

/-- A rectangular instance with an arbitrary probability space for fresh oracle seeds. -/
structure Instance where
  dx : ℕ
  dy : ℕ
  population : Rectangular.Population dx dy
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  oracle : Rectangular.Oracle dx dy Seed

attribute [instance] Instance.seedSpace Instance.probability

namespace Instance

def PopulationValid (M μ Δ : ℝ) (I : Instance) : Prop :=
  (∀ x y x' y',
    Real.sqrt (‖I.population.gradX x y - I.population.gradX x' y'‖ ^ 2 +
      ‖I.population.gradY x y - I.population.gradY x' y'‖ ^ 2) ≤
      M * Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)) ∧
  (∀ x y y', I.population.f x y' ≤ I.population.f x y +
    @inner ℝ (Vec I.dy) _ (I.population.gradY x y) (y' - y) - μ / 2 * ‖y' - y‖ ^ 2) ∧
  (I.population.Phi 0 - sInf (Set.range I.population.Phi) ≤ Δ) ∧
  BddBelow (Set.range I.population.Phi)

/-- Integrability is explicit: a nonintegrable Bochner integral cannot certify a bound. -/
def ValidBV (M μ Δ σ : ℝ) (I : Instance) : Prop :=
  I.PopulationValid M μ Δ ∧
  (∀ x y, Integrable (fun ξ => I.oracle.Gx x y ξ) I.law ∧
    Integrable (fun ξ => I.oracle.Gy x y ξ) I.law ∧
    (∫ ξ, I.oracle.Gx x y ξ ∂I.law) = I.population.gradX x y ∧
    (∫ ξ, I.oracle.Gy x y ξ ∂I.law) = I.population.gradY x y) ∧
  (∀ x y, Integrable (fun ξ => ‖I.oracle.Gx x y ξ - I.population.gradX x y‖ ^ 2 +
      ‖I.oracle.Gy x y ξ - I.population.gradY x y‖ ^ 2) I.law ∧
    (∫ ξ, ‖I.oracle.Gx x y ξ - I.population.gradX x y‖ ^ 2 +
      ‖I.oracle.Gy x y ξ - I.population.gradY x y‖ ^ 2 ∂I.law) ≤ σ ^ 2)

def ValidAS (M μ Δ σ : ℝ) (I : Instance) : Prop :=
  I.ValidBV M μ Δ σ ∧ ∀ x y x' y',
    Integrable (fun ξ => ‖I.oracle.Gx x y ξ - I.oracle.Gx x' y' ξ‖ ^ 2 +
      ‖I.oracle.Gy x y ξ - I.oracle.Gy x' y' ξ‖ ^ 2) I.law ∧
    (∫ ξ, ‖I.oracle.Gx x y ξ - I.oracle.Gx x' y' ξ‖ ^ 2 +
      ‖I.oracle.Gy x y ξ - I.oracle.Gy x' y' ξ‖ ^ 2 ∂I.law) ≤
      M ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)

def ofBernoulli (I : Rectangular.Instance) : Instance :=
  ⟨I.dx, I.dy, I.population, Bool, inferInstance, bernoulliMeasure I.p,
    bernoulliMeasure_probability I.p (le_of_lt I.p_pos) I.p_le_one, I.oracle⟩

theorem ofBernoulli_validBV (I : Rectangular.Instance) (M μ Δ σ : ℝ) :
    (ofBernoulli I).ValidBV M μ Δ σ ↔ I.ValidBV M μ Δ σ := by
  simp only [ValidBV, PopulationValid, ofBernoulli, Integrable.of_finite,
    integral_bernoulliVec I.p (le_of_lt I.p_pos) I.p_le_one,
    integral_bernoulliReal I.p (le_of_lt I.p_pos) I.p_le_one, true_and]
  rfl

theorem ofBernoulli_validAS (I : Rectangular.Instance) (M μ Δ σ : ℝ) :
    (ofBernoulli I).ValidAS M μ Δ σ ↔ I.ValidAS M μ Δ σ := by
  rw [ValidAS, ofBernoulli_validBV]
  simp only [ofBernoulli, Integrable.of_finite,
    integral_bernoulliReal I.p (le_of_lt I.p_pos) I.p_le_one, true_and]
  rfl

def field (m : StationarityObjective) (M : ℝ) (I : Instance) : Vec I.dx → Vec I.dx :=
  match m with
  | .primal => I.population.gradPhi
  | .moreau => gradient (fun x => sInf (Set.range (fun v => I.population.Phi v + M * ‖v - x‖ ^ 2)))

theorem field_ofBernoulli (m : StationarityObjective) (M : ℝ) (I : Rectangular.Instance) :
    field m M (ofBernoulli I) = Rectangular.Instance.field m M I := by cases m <;> rfl

end Instance

def trace {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ} {Seed : Type}
    (A : Rectangular.Policy Ω dx dy K) (O : Rectangular.Oracle dx dy Seed) (N : ℕ)
    (z : Ω × (Fin N → Seed)) : Rectangular.Trace dx dy N K :=
  (A.run? O N 0 (z.1, Fin.elim0) z.2).getD (Rectangular.haltTrace 0 dy N K)

def loss {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ} {Seed : Type}
    (A : Rectangular.Policy Ω dx dy K) (c : StationarityCriterion)
    (O : Rectangular.Oracle dx dy Seed) (g : Vec dx → Vec dx) (N : ℕ)
    (z : Ω × (Fin N → Seed)) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g (trace A O N z).output‖
  | .squared => ENNReal.ofReal (‖g (trace A O N z).output‖ ^ 2)

def Legal {K : ℕ} (A : Rectangular.Family.{u} K) (valid : Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I →
    (∀ z : A.Seed I.dx I.dy × (Fin N → I.Seed), ∃ tr,
      (A.policy I.dx I.dy).run? I.oracle N 0 (z.1, Fin.elim0) z.2 = some tr ∧
        Rectangular.calls tr ≤ N) ∧
    ∀ᵐ z ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N),
      Rectangular.StandardSupport (trace (A.policy I.dx I.dy) I.oracle N z)

def risk {K : ℕ} (A : Rectangular.Family.{u} K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : Instance) : ℝ≥0∞ :=
  ∫⁻ z, loss (A.policy I.dx I.dy) c I.oracle (Instance.field m M I) N z
    ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N)

theorem legal_restrict {K N : ℕ} (A : Rectangular.Family.{u} K) {valid : Instance → Prop}
    (hA : Legal A valid N) : A.Legal (fun I => valid (Instance.ofBernoulli I)) N := by
  intro I hI
  have h := hA (Instance.ofBernoulli I) hI
  constructor
  · exact h.1
  · simpa only [Instance.ofBernoulli,
      iidRoundMeasure_bernoulli I.p (le_of_lt I.p_pos) I.p_le_one] using h.2

theorem risk_ofBernoulli {K : ℕ} (A : Rectangular.Family.{u} K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : Rectangular.Instance) :
    risk A c m M N (Instance.ofBernoulli I) = A.risk c m M N I := by
  unfold risk
  rw [Instance.field_ofBernoulli]
  simp only [Instance.ofBernoulli, iidRoundMeasure_bernoulli I.p (le_of_lt I.p_pos) I.p_le_one]
  rfl

abbrev BudgetAlgorithm (valid : Instance → Prop) (K N : ℕ) :=
  {A : Rectangular.Family.{u} K // Legal A valid N}

theorem origin_legal (valid : Instance → Prop) (K N : ℕ) :
    Legal (Rectangular.originFamily.{u} K) valid N := by
  intro I hI
  constructor
  · intro z
    refine ⟨Rectangular.haltTrace 0 I.dy N K, Rectangular.Policy.origin_run I.oracle N 0 _ _, ?_⟩
    simp [Rectangular.calls, Rectangular.haltTrace, Rectangular.batchSize]
  · apply Filter.Eventually.of_forall
    intro z
    change Rectangular.StandardSupport
      (trace (Rectangular.Policy.origin (ULift.{u} Unit) I.dx I.dy K) I.oracle N z)
    simp only [trace, Rectangular.Policy.origin_run, Option.getD_some]
    constructor
    · intro t k q hq
      cases hq
    · intro c hc
      cases c <;> simp [Rectangular.support, Rectangular.haltTrace] at hc

theorem budgetAlgorithm_nonempty (valid : Instance → Prop) (K N : ℕ) :
    Nonempty (BudgetAlgorithm.{u} valid K N) :=
  ⟨⟨Rectangular.originFamily K, origin_legal valid K N⟩⟩

def complexity (valid : Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) : ℝ≥0∞ :=
  uniformBudgetComplexity valid
    (fun N (A : BudgetAlgorithm.{u} valid K N) I => risk A.val c m M N I) (c.target ε)

theorem complexity_bernoulli_le (valid : Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) :
    Rectangular.complexity.{u} (fun I => valid (Instance.ofBernoulli I)) K c m M ε ≤
      complexity.{u} valid K c m M ε := by
  apply uniformBudgetComplexity_le_of_restriction (fun I => valid (Instance.ofBernoulli I)) valid
    (fun N (A : Rectangular.BudgetAlgorithm.{u} (fun I => valid (Instance.ofBernoulli I)) K N) I =>
      A.val.risk c m M N I)
    (fun N (A : BudgetAlgorithm.{u} valid K N) I => risk A.val c m M N I)
    Instance.ofBernoulli (fun _ h => h) (fun _ A => ⟨A.val, legal_restrict A.val A.property⟩)
  intro N A I hI
  exact le_of_eq (risk_ofBernoulli A.val c m M N I).symm

theorem bv_complexity_lower (P : ManuscriptBVProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity.{u} (Instance.ValidBV P.M P.μ P.Δ P.σ) K c m P.M P.ε := by
  have hv : (fun I => (Instance.ofBernoulli I).ValidBV P.M P.μ P.Δ P.σ) =
      Rectangular.Instance.ValidBV P.M P.μ P.Δ P.σ := by
    funext I
    exact propext (Instance.ofBernoulli_validBV I P.M P.μ P.Δ P.σ)
  have h := complexity_bernoulli_le.{u} (Instance.ValidBV P.M P.μ P.Δ P.σ) K c m P.M P.ε
  rw [hv] at h
  exact (Rectangular.bv_complexity_lower P hK c m).trans h

theorem as_complexity_lower (P : ManuscriptASProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity.{u} (Instance.ValidAS P.M P.μ P.Δ P.σ) K c m P.M P.ε := by
  have hv : (fun I => (Instance.ofBernoulli I).ValidAS P.M P.μ P.Δ P.σ) =
      Rectangular.Instance.ValidAS P.M P.μ P.Δ P.σ := by
    funext I
    exact propext (Instance.ofBernoulli_validAS I P.M P.μ P.Δ P.σ)
  have h := complexity_bernoulli_le.{u} (Instance.ValidAS P.M P.μ P.Δ P.σ) K c m P.M P.ε
  rw [hv] at h
  exact (Rectangular.as_complexity_lower P hK c m).trans h

end MeasuredOracle
end NCSCPureStochasticLB.PaperExact
