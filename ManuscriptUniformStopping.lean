import ManuscriptStoppingHistory

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u v w x y

namespace StoppingHistoryPolicy

/-- Always stop at the origin. No batch is needed, even when K = 0. -/
def origin (Ω : Type u) [MeasurableSpace Ω] (T K : ℕ) : StoppingHistoryPolicy Ω T K where
  domain _ := Set.univ
  domain_measurable _ := MeasurableSet.univ
  stop _ _ := true
  stop_measurable _ := measurable_const
  output _ _ := 0
  output_measurable _ := measurable_const
  batch _ s := False.elim (s.property rfl)
  batch_measurable n := by
    letI : IsEmpty {s : (Set.univ : Set (FiniteHistory Ω T K n)) // (true : Bool) ≠ true} :=
      ⟨fun s => s.property rfl⟩
    exact measurable_of_empty _

theorem origin_run {Ω : Type u} [MeasurableSpace Ω] {T K : ℕ} {Seed : Type}
    (O : StochasticOracle T Seed) (H n : ℕ) (s : FiniteHistory Ω T K n) (w : Fin H → Seed) :
    (origin Ω T K).run? O H n s w = some (PartialHistoryPolicy.haltTrace 0 H K) := by
  cases H <;> simp [run?, origin]

theorem origin_trace {Ω : Type u} [MeasurableSpace Ω] {T K : ℕ}
    (O : StochasticOracle T Bool) (N : ℕ) (z : Ω × RoundWorld N) :
    (origin Ω T K).trace O N z = PartialHistoryPolicy.haltTrace 0 N K := by
  simp [trace, origin_run]

end StoppingHistoryPolicy

/-- The algorithm chooses its own internal probability space at each dimension. Policies receive the
dimension and observable history, but not the objective, oracle or hidden seed law. -/
structure RandomizedStoppingFamily (K : ℕ) where
  Seed : ℕ → Type u
  seedSpace : ∀ T, MeasurableSpace (Seed T)
  law : ∀ T, @Measure (Seed T) (seedSpace T)
  probability : ∀ T, @IsProbabilityMeasure (Seed T) (seedSpace T) (law T)
  policy : ∀ T, @StoppingHistoryPolicy (Seed T) (seedSpace T) T K

attribute [instance] RandomizedStoppingFamily.seedSpace RandomizedStoppingFamily.probability

namespace RandomizedStoppingFamily

def ofPolicies {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {K : ℕ} (A : ∀ T, StoppingHistoryPolicy Ω T K) : RandomizedStoppingFamily.{u} K :=
  ⟨fun _ => Ω, fun _ => inferInstance, fun _ => ρ, fun _ => inferInstance, A⟩

/-- Termination and calls are bounded on every run; standard support is a.s.
The same dimension-indexed policy is used at every valid instance. -/
def Legal {K : ℕ} (A : RandomizedStoppingFamily K) (valid : BernoulliInstance → Prop)
    (N : ℕ) : Prop :=
  ∀ I, valid I →
    (A.policy I.T).TerminatesWithinBudget I.oracle N ∧
    ∀ᵐ z ∂(A.law I.T).prod (roundMeasure I.p N),
      StandardZeroRespectingTrace ((A.policy I.T).trace I.oracle N z)

theorem admissible {K N : ℕ} (A : RandomizedStoppingFamily K)
    {valid : BernoulliInstance → Prop} (hA : A.Legal valid N)
    (I : BernoulliInstance) (hI : valid I) :
    (A.policy I.T).Admissible (A.law I.T) I.oracle I.p N :=
  (A.policy I.T).admissible_of_pathwise_budget (A.law I.T) I.oracle I.p N
    (hA I hI).1 (hA I hI).2

def risk {K : ℕ} (A : RandomizedStoppingFamily K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : BernoulliInstance) : ℝ≥0∞ :=
  (A.policy I.T).risk c (A.law I.T) I.oracle I.p (m.field M I) N

end RandomizedStoppingFamily

abbrev UniformStoppingBudgetAlgorithm (valid : BernoulliInstance → Prop) (K N : ℕ) :=
  {A : RandomizedStoppingFamily.{u} K // A.Legal valid N}

/-- A legal algorithm exists independently of the validity predicate and budget. -/
def originStoppingBudgetAlgorithm {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (valid : BernoulliInstance → Prop) (K N : ℕ) : UniformStoppingBudgetAlgorithm.{u} valid K N := by
  refine ⟨RandomizedStoppingFamily.ofPolicies ρ (fun T => StoppingHistoryPolicy.origin Ω T K), ?_⟩
  intro I hI
  constructor
  · intro z
    refine ⟨PartialHistoryPolicy.haltTrace 0 N K, StoppingHistoryPolicy.origin_run I.oracle N 0 _ _, ?_⟩
    exact (OnlinePolicy.halt_zero_legal I.oracle N N K z.2).2
  · apply Filter.Eventually.of_forall
    intro z
    simpa only [RandomizedStoppingFamily.ofPolicies, StoppingHistoryPolicy.origin_trace] using
      (OnlinePolicy.halt_zero_legal I.oracle N N K z.2).1

theorem uniformStoppingBudgetAlgorithm_nonempty
    (valid : BernoulliInstance → Prop) (K N : ℕ) :
    Nonempty (UniformStoppingBudgetAlgorithm.{u} valid K N) := by
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  exact ⟨originStoppingBudgetAlgorithm (Measure.dirac (ULift.up () : ULift.{u} Unit)) valid K N⟩

/-- Formula-(12) budget infimum for branch-specific measurable policies, now
quantifying over algorithm-owned internal probability spaces in Type u. -/
def uniformStoppingComplexity (valid : BernoulliInstance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) : ℝ≥0∞ :=
  uniformBudgetComplexity valid
    (fun N (A : UniformStoppingBudgetAlgorithm.{u} valid K N) I => A.val.risk c m M N I)
    (c.target ε)

/-- Generic subclass restriction: simulation may only reduce the risk.
This is a transfer principle, not an assumed representation of the full paper class. -/
theorem uniformBudgetComplexity_le_of_restriction
    {SmallInstance : Type v} {FullInstance : Type w}
    {SmallAlgorithm : ℕ → Type x} {FullAlgorithm : ℕ → Type y}
    (smallValid : SmallInstance → Prop) (fullValid : FullInstance → Prop)
    (smallRisk : ∀ N, SmallAlgorithm N → SmallInstance → ℝ≥0∞)
    (fullRisk : ∀ N, FullAlgorithm N → FullInstance → ℝ≥0∞)
    (embed : SmallInstance → FullInstance)
    (valid_embed : ∀ I, smallValid I → fullValid (embed I))
    (restrict : ∀ N, FullAlgorithm N → SmallAlgorithm N)
    (risk_le : ∀ N A I, smallValid I → smallRisk N (restrict N A) I ≤ fullRisk N A (embed I))
    (target : ℝ≥0∞) :
    uniformBudgetComplexity smallValid smallRisk target ≤
      uniformBudgetComplexity fullValid fullRisk target := by
  apply le_sInf
  rintro b ⟨N, rfl, A, hA⟩
  apply sInf_le
  refine ⟨N, rfl, restrict N A, ?_⟩
  apply (worstCaseBudgetRisk_le_iff smallValid smallRisk N (restrict N A) target).mpr
  intro I hI
  exact (risk_le N A I hI).trans
    ((worstCaseBudgetRisk_le_iff fullValid fullRisk N A target).mp hA (embed I) (valid_embed I hI))

/-- Enlarging the valid instance class cannot make its uniform task easier,
even though legality is itself quantified over that class. -/
theorem uniformStoppingComplexity_mono
    (smallValid fullValid : BernoulliInstance → Prop)
    (hsub : ∀ I, smallValid I → fullValid I) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) :
    uniformStoppingComplexity.{u} smallValid K c m M ε ≤
      uniformStoppingComplexity.{u} fullValid K c m M ε := by
  apply uniformBudgetComplexity_le_of_restriction smallValid fullValid
    (fun N (A : UniformStoppingBudgetAlgorithm.{u} smallValid K N) I => A.val.risk c m M N I)
    (fun N (A : UniformStoppingBudgetAlgorithm.{u} fullValid K N) I => A.val.risk c m M N I)
    id hsub (fun _ A => ⟨A.val, fun I hI => A.property I (hsub I hI)⟩)
  intro N A I hI
  exact le_rfl

namespace ManuscriptBVProblem

theorem uniform_stopping_complexity_lower (P : ManuscriptBVProblem)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformStoppingComplexity.{u} (BernoulliInstance.ValidBV P.M P.μ P.Δ P.σ)
        K c m P.M P.ε := by
  apply uniformBudgetComplexity_lower_of_fixed_instance _ _ _ _ P.onlineInstance P.onlineInstance_valid
  intro N A h
  have hl := A.val.admissible A.property P.onlineInstance P.onlineInstance_valid
  cases m with
  | primal => exact P.stopping_history_product_budget_lower (A.val.law P.T) hK (A.val.policy P.T) c hl h
  | moreau =>
    change (A.val.policy P.T).risk c (A.val.law P.T) P.oracle P.p
      (gradient (P.onlineInstance.moreauValue P.M)) N ≤ c.target P.ε at h
    rw [P.online_moreau_gradient] at h
    exact P.stopping_history_product_moreau_budget_lower (A.val.law P.T) hK (A.val.policy P.T) c hl h

theorem uniform_stopping_superclass_lower (P : ManuscriptBVProblem)
    (valid : BernoulliInstance → Prop)
    (hsub : ∀ I, I.ValidBV P.M P.μ P.Δ P.σ → valid I)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformStoppingComplexity.{u} valid K c m P.M P.ε :=
  (P.uniform_stopping_complexity_lower hK c m).trans
    (uniformStoppingComplexity_mono _ valid hsub K c m P.M P.ε)

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem uniform_stopping_complexity_lower (P : ManuscriptASProblem)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformStoppingComplexity.{u} (BernoulliInstance.ValidAS P.M P.μ P.Δ P.σ)
        K c m P.M P.ε := by
  apply uniformBudgetComplexity_lower_of_fixed_instance _ _ _ _ P.onlineInstance P.onlineInstance_valid
  intro N A h
  have hl := A.val.admissible A.property P.onlineInstance P.onlineInstance_valid
  cases m with
  | primal => exact P.stopping_history_product_budget_lower (A.val.law P.T) hK (A.val.policy P.T) c hl h
  | moreau =>
    change (A.val.policy P.T).risk c (A.val.law P.T) P.oracle P.p
      (gradient (P.onlineInstance.moreauValue P.M)) N ≤ c.target P.ε at h
    rw [P.online_moreau_gradient] at h
    exact P.stopping_history_product_moreau_budget_lower (A.val.law P.T) hK (A.val.policy P.T) c hl h

theorem uniform_stopping_superclass_lower (P : ManuscriptASProblem)
    (valid : BernoulliInstance → Prop)
    (hsub : ∀ I, I.ValidAS P.M P.μ P.Δ P.σ → valid I)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformStoppingComplexity.{u} valid K c m P.M P.ε :=
  (P.uniform_stopping_complexity_lower hK c m).trans
    (uniformStoppingComplexity_mono _ valid hsub K c m P.M P.ε)

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
