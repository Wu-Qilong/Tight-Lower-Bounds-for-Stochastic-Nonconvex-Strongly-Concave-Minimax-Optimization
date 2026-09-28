import ManuscriptUniformStopping

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact
namespace Rectangular

universe u

abbrev Pair (dx dy : ℕ) := Vec dx × Vec dy
abbrev Batch (dx dy K : ℕ) := Fin K → Option (Pair dx dy)
abbrev Code (dx dy K : ℕ) := Fin K → Bool × Pair dx dy
abbrev History (Ω : Type u) (dx dy K n : ℕ) := Ω × (Fin n → Code dx dy K × Code dx dy K)

def encode {dx dy K : ℕ} (q : Batch dx dy K) : Code dx dy K := fun k =>
  match q k with
  | none => (false, 0, 0)
  | some z => (true, z)

theorem encode_square {T K : ℕ} (q : Batch T T K) : batchCode q = encode q := by
  funext k
  cases h : q k <;> simp [batchCode, encode, h]

def batchSize {dx dy K : ℕ} (q : Batch dx dy K) : ℕ :=
  ∑ k, if (q k).isSome then 1 else 0

structure NonemptyBatch (dx dy K : ℕ) where
  points : Batch dx dy K
  size_pos : 1 ≤ batchSize points
  size_le : batchSize points ≤ K

def NonemptyBatch.toSquare {T K : ℕ} (q : NonemptyBatch T T K) : NonemptyOnlineBatch T K :=
  ⟨q.points, q.size_pos, q.size_le⟩

structure Oracle (dx dy : ℕ) (Seed : Type) where
  Gx : Vec dx → Vec dy → Seed → Vec dx
  Gy : Vec dx → Vec dy → Seed → Vec dy

def Oracle.toSquare {T : ℕ} {Seed : Type} (O : Oracle T T Seed) : StochasticOracle T Seed :=
  ⟨O.Gx, O.Gy⟩

def answer {dx dy K : ℕ} {Seed : Type} (O : Oracle dx dy Seed) (q : Batch dx dy K)
    (ξ : Seed) : Batch dx dy K := fun k =>
  match q k with
  | none => none
  | some z => some (O.Gx z.1 z.2 ξ, O.Gy z.1 z.2 ξ)

theorem answer_square {T K : ℕ} {Seed : Type} (O : Oracle T T Seed) (q : Batch T T K)
    (ξ : Seed) : OnlinePolicy.answer O.toSquare q ξ = answer O q ξ := by
  funext k
  cases h : q k <;> simp [OnlinePolicy.answer, answer, Oracle.toSquare, h]

structure Trace (dx dy H K : ℕ) where
  query : Fin H → Batch dx dy K
  response : Fin H → Batch dx dy K
  output : Vec dx

def Trace.toSquare {T H K : ℕ} (tr : Trace T T H K) : InteractionTrace T H K :=
  ⟨tr.query, tr.response, tr.output⟩

def haltTrace {dx : ℕ} (x : Vec dx) (dy H K : ℕ) : Trace dx dy H K :=
  ⟨fun _ _ => none, fun _ _ => none, x⟩

def prepend {dx dy H K : ℕ} (q r : Batch dx dy K) (tr : Trace dx dy H K) :
    Trace dx dy (H + 1) K := ⟨Fin.cases q tr.query, Fin.cases r tr.response, tr.output⟩

def support {dx dy : ℕ} (z : Pair dx dy) : Set (Fin dx ⊕ Fin dy) :=
  {c | Sum.elim z.1 z.2 c ≠ 0}

def StandardSupport {dx dy H K : ℕ} (tr : Trace dx dy H K) : Prop :=
  (∀ t k q, tr.query t k = some q → ∀ c ∈ support q,
    ∃ s : Fin H, s.val < t.val ∧ ∃ j r, tr.response s j = some r ∧ c ∈ support r) ∧
  (∀ c ∈ support (tr.output, (0 : Vec dy)), ∃ s j r,
    tr.response s j = some r ∧ c ∈ support r)

def calls {dx dy H K : ℕ} (tr : Trace dx dy H K) : ℕ := ∑ t, batchSize (tr.query t)

theorem support_toSquare {T H K : ℕ} (tr : Trace T T H K) :
    StandardZeroRespectingTrace tr.toSquare ↔ StandardSupport tr := Iff.rfl

theorem calls_toSquare {T H K : ℕ} (tr : Trace T T H K) :
    returnedGradientCount tr.toSquare = calls tr := rfl

/-- Native rectangular history rules; no encoding into a square problem is assumed. -/
structure Policy (Ω : Type u) [MeasurableSpace Ω] (dx dy K : ℕ) where
  domain : ∀ n, Set (History Ω dx dy K n)
  domain_measurable : ∀ n, MeasurableSet (domain n)
  stop : ∀ n, domain n → Bool
  stop_measurable : ∀ n, Measurable (stop n)
  output : ∀ n, {s : domain n // stop n s = true} → Vec dx
  batch : ∀ n, {s : domain n // stop n s ≠ true} → NonemptyBatch dx dy K
  output_measurable : ∀ n, Measurable (output n)
  batch_measurable : ∀ n, Measurable (fun s => encode (batch n s).points)

def append {Ω : Type u} {dx dy K n : ℕ} (s : History Ω dx dy K n)
    (r : Code dx dy K × Code dx dy K) : History Ω dx dy K (n + 1) :=
  (s.1, Fin.lastCases r s.2)

namespace Policy
variable {Ω : Type u} [MeasurableSpace Ω] {dx dy T K : ℕ}

def origin (Ω : Type u) [MeasurableSpace Ω] (dx dy K : ℕ) : Policy Ω dx dy K where
  domain _ := Set.univ
  domain_measurable _ := MeasurableSet.univ
  stop _ _ := true
  stop_measurable _ := measurable_const
  output _ _ := 0
  output_measurable _ := measurable_const
  batch _ s := False.elim (s.property rfl)
  batch_measurable n := by
    letI : IsEmpty {s : (Set.univ : Set (History Ω dx dy K n)) // (true : Bool) ≠ true} :=
      ⟨fun s => s.property rfl⟩
    exact measurable_of_empty _

def toSquare (P : Policy Ω T T K) : StoppingHistoryPolicy Ω T K where
  domain := P.domain
  domain_measurable := P.domain_measurable
  stop := P.stop
  stop_measurable := P.stop_measurable
  output := P.output
  output_measurable := P.output_measurable
  batch n s := (P.batch n s).toSquare
  batch_measurable n := by
    simpa only [NonemptyBatch.toSquare, encode_square] using P.batch_measurable n

def run? {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) :
    (H n : ℕ) → History Ω dx dy K n → (Fin H → Seed) → Option (Trace dx dy H K)
  | 0, n, s, _ => by
    classical
    exact if hd : s ∈ P.domain n then
      if hs : P.stop n ⟨s, hd⟩ = true then some (haltTrace (P.output n ⟨⟨s, hd⟩, hs⟩) dy 0 K)
      else none
    else none
  | H + 1, n, s, w => by
    classical
    exact if hd : s ∈ P.domain n then
      if hs : P.stop n ⟨s, hd⟩ = true then some (haltTrace (P.output n ⟨⟨s, hd⟩, hs⟩) dy (H + 1) K)
      else
        let q := (P.batch n ⟨⟨s, hd⟩, hs⟩).points
        let r := answer O q (w 0)
        (P.run? O H (n + 1) (append s (encode q, encode r))
          (fun t => w t.succ)).map (prepend q r)
    else none

/-- Restriction to the diagonal preserves the entire partial execution, including failure. -/
theorem run_toSquare {Seed : Type} (P : Policy Ω T T K) (O : Oracle T T Seed) :
    ∀ H n (s : History Ω T T K n) (w : Fin H → Seed),
      P.toSquare.run? O.toSquare H n s w = (P.run? O H n s w).map Trace.toSquare := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true <;>
        simp [run?, StoppingHistoryPolicy.run?, toSquare, hd, hs, haltTrace,
          PartialHistoryPolicy.haltTrace, Trace.toSquare]
    · simp [run?, StoppingHistoryPolicy.run?, toSquare, hd]
  | succ H ih =>
    intro n s w
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp [run?, StoppingHistoryPolicy.run?, toSquare, hd, hs, haltTrace,
          PartialHistoryPolicy.haltTrace, Trace.toSquare]
      · simp only [StoppingHistoryPolicy.run?, run?, toSquare, dif_pos hd, dif_neg hs]
        change (P.toSquare.run? O.toSquare H (n + 1) _ _).map _ = _
        rw [ih]
        simp only [Option.map_map, NonemptyBatch.toSquare, answer_square, encode_square]
        rfl
    · simp [run?, StoppingHistoryPolicy.run?, toSquare, hd]

def trace (P : Policy Ω dx dy K) (O : Oracle dx dy Bool) (N : ℕ)
    (z : Ω × RoundWorld N) : Trace dx dy N K :=
  (P.run? O N 0 (z.1, Fin.elim0) z.2).getD (haltTrace 0 dy N K)

theorem origin_run {Seed : Type} (O : Oracle dx dy Seed) (H n : ℕ)
    (s : History Ω dx dy K n) (w : Fin H → Seed) :
    (origin Ω dx dy K).run? O H n s w = some (haltTrace 0 dy H K) := by
  cases H <;> simp [run?, origin]

theorem trace_toSquare (P : Policy Ω T T K) (O : Oracle T T Bool) (N : ℕ)
    (z : Ω × RoundWorld N) :
    P.toSquare.trace O.toSquare N z = (P.trace O N z).toSquare := by
  simp only [StoppingHistoryPolicy.trace, trace, run_toSquare, FiniteHistoryPolicy.initial]
  cases P.run? O N 0 (z.1, Fin.elim0) z.2 <;> rfl

def TerminatesWithinBudget (P : Policy Ω dx dy K) (O : Oracle dx dy Bool) (N : ℕ) : Prop :=
  ∀ z : Ω × RoundWorld N, ∃ tr,
    P.run? O N 0 (z.1, Fin.elim0) z.2 = some tr ∧ calls tr ≤ N

theorem budget_toSquare (P : Policy Ω T T K) (O : Oracle T T Bool) (N : ℕ)
    (h : P.TerminatesWithinBudget O N) : P.toSquare.TerminatesWithinBudget O.toSquare N := by
  intro z
  obtain ⟨tr, hr, hb⟩ := h z
  refine ⟨tr.toSquare, ?_, hb⟩
  rw [run_toSquare]
  simp only [FiniteHistoryPolicy.initial]
  rw [hr]
  rfl

def loss (P : Policy Ω dx dy K) (c : StationarityCriterion) (O : Oracle dx dy Bool)
    (g : Vec dx → Vec dx) (N : ℕ) (z : Ω × RoundWorld N) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g (P.trace O N z).output‖
  | .squared => ENNReal.ofReal (‖g (P.trace O N z).output‖ ^ 2)

def risk (P : Policy Ω dx dy K) (c : StationarityCriterion) (ρ : Measure Ω)
    (O : Oracle dx dy Bool) (p : ℝ) (g : Vec dx → Vec dx) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ z, P.loss c O g N z ∂ρ.prod (roundMeasure p N)

theorem risk_toSquare (P : Policy Ω T T K) (c : StationarityCriterion) (ρ : Measure Ω)
    (O : Oracle T T Bool) (p : ℝ) (g : Vec T → Vec T) (N : ℕ) :
    P.toSquare.risk c ρ O.toSquare p g N = P.risk c ρ O p g N := by
  apply lintegral_congr
  intro z
  cases c <;> simp only [StoppingHistoryPolicy.loss, loss, trace_toSquare, Trace.toSquare]

end Policy

/-- The analytic data and conditions use independent primal and dual dimensions. -/
structure Population (dx dy : ℕ) where
  f : Vec dx → Vec dy → ℝ
  gradX : Vec dx → Vec dy → Vec dx
  gradY : Vec dx → Vec dy → Vec dy
  Phi : Vec dx → ℝ
  gradPhi : Vec dx → Vec dx
  gradX_spec : ∀ x y, HasGradientAt (fun x' => f x' y) (gradX x y) x
  gradY_spec : ∀ x y, HasGradientAt (fun y' => f x y') (gradY x y) y
  gradPhi_spec : ∀ x, HasGradientAt Phi (gradPhi x) x
  value_is_max : ∀ x, ∃ ystar : Vec dy, Phi x = f x ystar ∧ ∀ y, f x y ≤ Phi x

structure Instance where
  dx : ℕ
  dy : ℕ
  population : Population dx dy
  oracle : Oracle dx dy Bool
  p : ℝ
  p_pos : 0 < p
  p_le_one : p ≤ 1

namespace Instance

def ValidBV (M μ Δ σ : ℝ) (I : Instance) : Prop :=
  ((∀ x y x' y',
    Real.sqrt (‖I.population.gradX x y - I.population.gradX x' y'‖ ^ 2 +
      ‖I.population.gradY x y - I.population.gradY x' y'‖ ^ 2) ≤
      M * Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)) ∧
   (∀ x y y', I.population.f x y' ≤ I.population.f x y +
      @inner ℝ (Vec I.dy) _ (I.population.gradY x y) (y' - y) - μ / 2 * ‖y' - y‖ ^ 2) ∧
   (I.population.Phi 0 - sInf (Set.range I.population.Phi) ≤ Δ) ∧
   BddBelow (Set.range I.population.Phi)) ∧
  (∀ x y, (bernoulliLaw I.p).expectVec (fun ξ => I.oracle.Gx x y ξ) = I.population.gradX x y ∧
    (bernoulliLaw I.p).expectVec (fun ξ => I.oracle.Gy x y ξ) = I.population.gradY x y) ∧
  (∀ x y, (bernoulliLaw I.p).expectReal (fun ξ =>
    ‖I.oracle.Gx x y ξ - I.population.gradX x y‖ ^ 2 +
    ‖I.oracle.Gy x y ξ - I.population.gradY x y‖ ^ 2) ≤ σ ^ 2)

def ValidAS (M μ Δ σ : ℝ) (I : Instance) : Prop :=
  I.ValidBV M μ Δ σ ∧ ∀ x y x' y', (bernoulliLaw I.p).expectReal (fun ξ =>
    ‖I.oracle.Gx x y ξ - I.oracle.Gx x' y' ξ‖ ^ 2 +
    ‖I.oracle.Gy x y ξ - I.oracle.Gy x' y' ξ‖ ^ 2) ≤
      M ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)

def ofSquare (I : BernoulliInstance) : Instance where
  dx := I.T
  dy := I.T
  population := ⟨I.population.f, I.population.gradX, I.population.gradY, I.population.Phi,
    I.population.gradPhi, I.population.gradX_spec, I.population.gradY_spec,
    I.population.gradPhi_spec, I.population.value_is_max⟩
  oracle := ⟨I.oracle.Gx, I.oracle.Gy⟩
  p := I.p
  p_pos := I.p_pos
  p_le_one := I.p_le_one

theorem ofSquare_validBV (I : BernoulliInstance) (M μ Δ σ : ℝ) :
    (ofSquare I).ValidBV M μ Δ σ ↔ I.ValidBV M μ Δ σ := Iff.rfl

theorem ofSquare_validAS (I : BernoulliInstance) (M μ Δ σ : ℝ) :
    (ofSquare I).ValidAS M μ Δ σ ↔ I.ValidAS M μ Δ σ := Iff.rfl

def field (m : StationarityObjective) (M : ℝ) (I : Instance) : Vec I.dx → Vec I.dx :=
  match m with
  | .primal => I.population.gradPhi
  | .moreau => gradient (fun x => sInf (Set.range (fun v => I.population.Phi v + M * ‖v - x‖ ^ 2)))

theorem field_ofSquare (m : StationarityObjective) (M : ℝ) (I : BernoulliInstance) :
    field m M (ofSquare I) = m.field M I := by cases m <;> rfl

end Instance

/-- The strategy and its internal law may depend on both dimensions, not the instance. -/
structure Family (K : ℕ) where
  Seed : ℕ → ℕ → Type u
  seedSpace : ∀ dx dy, MeasurableSpace (Seed dx dy)
  law : ∀ dx dy, @Measure (Seed dx dy) (seedSpace dx dy)
  probability : ∀ dx dy, @IsProbabilityMeasure (Seed dx dy) (seedSpace dx dy) (law dx dy)
  policy : ∀ dx dy, @Policy (Seed dx dy) (seedSpace dx dy) dx dy K

attribute [instance] Family.seedSpace Family.probability

namespace Family

def diagonal {K : ℕ} (A : Family K) : RandomizedStoppingFamily.{u} K where
  Seed T := A.Seed T T
  seedSpace T := A.seedSpace T T
  law T := A.law T T
  probability T := A.probability T T
  policy T := (A.policy T T).toSquare

def Legal {K : ℕ} (A : Family K) (valid : Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I →
    (A.policy I.dx I.dy).TerminatesWithinBudget I.oracle N ∧
    ∀ᵐ z ∂(A.law I.dx I.dy).prod (roundMeasure I.p N),
      StandardSupport ((A.policy I.dx I.dy).trace I.oracle N z)

theorem diagonal_legal {K N : ℕ} (A : Family K) {valid : Instance → Prop}
    (hA : A.Legal valid N) : A.diagonal.Legal (fun I => valid (Instance.ofSquare I)) N := by
  intro I hI
  have h := hA (Instance.ofSquare I) hI
  constructor
  · exact (A.policy I.T I.T).budget_toSquare (Instance.ofSquare I).oracle N h.1
  · filter_upwards [h.2] with z hz
    change StandardZeroRespectingTrace ((A.policy I.T I.T).toSquare.trace
      (Instance.ofSquare I).oracle.toSquare N z)
    rw [Policy.trace_toSquare]
    exact (support_toSquare _).mpr hz

def risk {K : ℕ} (A : Family K) (c : StationarityCriterion) (m : StationarityObjective)
    (M : ℝ) (N : ℕ) (I : Instance) : ℝ≥0∞ :=
  (A.policy I.dx I.dy).risk c (A.law I.dx I.dy) I.oracle I.p (Instance.field m M I) N

theorem risk_diagonal {K : ℕ} (A : Family K) (c : StationarityCriterion) (m : StationarityObjective)
    (M : ℝ) (N : ℕ) (I : BernoulliInstance) :
    A.diagonal.risk c m M N I = A.risk c m M N (Instance.ofSquare I) := by
  unfold risk RandomizedStoppingFamily.risk
  rw [Instance.field_ofSquare]
  exact (A.policy I.T I.T).risk_toSquare c (A.law I.T I.T) (Instance.ofSquare I).oracle
    I.p (m.field M I) N

end Family

abbrev BudgetAlgorithm (valid : Instance → Prop) (K N : ℕ) :=
  {A : Family.{u} K // A.Legal valid N}

def originFamily (K : ℕ) : Family.{u} K := by
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  exact ⟨fun _ _ => ULift.{u} Unit, fun _ _ => inferInstance,
    fun _ _ => Measure.dirac (ULift.up ()), fun _ _ => inferInstance,
    fun dx dy => Policy.origin (ULift.{u} Unit) dx dy K⟩

theorem originFamily_legal (valid : Instance → Prop) (K N : ℕ) :
    (originFamily.{u} K).Legal valid N := by
  intro I hI
  constructor
  · intro z
    refine ⟨haltTrace 0 I.dy N K, Policy.origin_run I.oracle N 0 _ _, ?_⟩
    simp [calls, haltTrace, batchSize]
  · apply Filter.Eventually.of_forall
    intro z
    change StandardSupport ((Policy.origin (ULift.{u} Unit) I.dx I.dy K).trace I.oracle N z)
    simp only [Policy.trace, Policy.origin_run, Option.getD_some]
    constructor
    · intro t k q hq
      cases hq
    · intro c hc
      cases c <;> simp [support, haltTrace] at hc

theorem budgetAlgorithm_nonempty (valid : Instance → Prop) (K N : ℕ) :
    Nonempty (BudgetAlgorithm.{u} valid K N) :=
  ⟨⟨originFamily K, originFamily_legal valid K N⟩⟩

def complexity (valid : Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) : ℝ≥0∞ :=
  uniformBudgetComplexity valid
    (fun N (A : BudgetAlgorithm.{u} valid K N) I => A.val.risk c m M N I) (c.target ε)

/-- Concrete restriction theorem: neither execution nor risk equality is a hypothesis. -/
theorem complexity_diagonal_le (valid : Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) :
    uniformStoppingComplexity.{u} (fun I => valid (Instance.ofSquare I)) K c m M ε ≤
      complexity.{u} valid K c m M ε := by
  apply uniformBudgetComplexity_le_of_restriction (fun I => valid (Instance.ofSquare I)) valid
    (fun N (A : UniformStoppingBudgetAlgorithm.{u} (fun I => valid (Instance.ofSquare I)) K N) I =>
      A.val.risk c m M N I)
    (fun N (A : BudgetAlgorithm.{u} valid K N) I => A.val.risk c m M N I)
    Instance.ofSquare (fun _ h => h)
    (fun _ A => ⟨A.val.diagonal, A.val.diagonal_legal A.property⟩)
  intro N A I hI
  exact le_of_eq (A.val.risk_diagonal c m M N I)

theorem bv_complexity_lower (P : ManuscriptBVProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity.{u} (Instance.ValidBV P.M P.μ P.Δ P.σ) K c m P.M P.ε :=
  (P.uniform_stopping_complexity_lower hK c m).trans
    (complexity_diagonal_le (Instance.ValidBV P.M P.μ P.Δ P.σ) K c m P.M P.ε)

theorem as_complexity_lower (P : ManuscriptASProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity.{u} (Instance.ValidAS P.M P.μ P.Δ P.σ) K c m P.M P.ε :=
  (P.uniform_stopping_complexity_lower hK c m).trans
    (complexity_diagonal_le (Instance.ValidAS P.M P.μ P.Δ P.σ) K c m P.M P.ε)

end Rectangular
end NCSCPureStochasticLB.PaperExact
