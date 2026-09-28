import ManuscriptMeasurability

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- Keep the active flag, so an absent response is distinct from a zero response. -/
abbrev BatchCode (T K : ℕ) := Fin K → Bool × (Vec T × Vec T)

def batchCode {T K : ℕ} (q : OnlineBatch T K) : BatchCode T K := fun k =>
  match q k with
  | none => (false, 0, 0)
  | some z => (true, z)

theorem batchCode_active {T K : ℕ} (q : OnlineBatch T K) (k : Fin K) :
    (batchCode q k).1 = (q k).isSome := by cases h : q k <;> simp [batchCode, h]

theorem batchCode_coordinate {T K : ℕ} (q : OnlineBatch T K) (k : Fin K) (c : Fin T ⊕ Fin T) :
    Sum.elim (batchCode q k).2.1 (batchCode q k).2.2 c = slotCoordinate (q k) c := by
  cases h : q k <;> cases c <;> simp [batchCode, slotCoordinate, h]

def oraclePair {T : ℕ} (O : StochasticOracle T Bool) (ξ : Bool) (z : Vec T × Vec T) : Vec T × Vec T :=
  (O.Gx z.1 z.2 ξ, O.Gy z.1 z.2 ξ)

def MeasurableOracle {T : ℕ} (O : StochasticOracle T Bool) : Prop :=
  ∀ ξ, Measurable (oraclePair O ξ)

theorem measurable_answer_code {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ}
    (O : StochasticOracle T Bool) (hO : MeasurableOracle O) (ξ : Bool)
    (q : Ω → OnlineBatch T K) (hq : Measurable (fun ω => batchCode (q ω))) :
    Measurable (fun ω => batchCode (OnlinePolicy.answer O (q ω) ξ)) := by
  apply measurable_pi_lambda
  intro k
  have hk := (measurable_pi_apply k).comp hq
  have he : (fun ω => batchCode (OnlinePolicy.answer O (q ω) ξ) k) =
      (fun ω => if (batchCode (q ω) k).1 = true then
        (true, oraclePair O ξ (batchCode (q ω) k).2) else (false, (0, 0))) := by
    funext ω
    cases h : q ω k <;> simp [OnlinePolicy.answer, batchCode, oraclePair, h]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun hk.fst measurable_const)
    (measurable_const.prodMk ((hO ξ).comp hk.snd)) measurable_const

structure CodedTraceMeasurable {Ω : Type*} [MeasurableSpace Ω] {T H K : ℕ}
    (tr : Ω → InteractionTrace T H K) : Prop where
  query : ∀ t, Measurable (fun ω => batchCode ((tr ω).query t))
  response : ∀ t, Measurable (fun ω => batchCode ((tr ω).response t))
  output : Measurable (fun ω => (tr ω).output)

theorem CodedTraceMeasurable.observable {Ω : Type*} [MeasurableSpace Ω] {T H K : ℕ}
    {tr : Ω → InteractionTrace T H K} (h : CodedTraceMeasurable tr) : ObservableMeasurable tr := by
  constructor
  · intro t k c
    have hk := (measurable_pi_apply k).comp (h.query t)
    simp only [← batchCode_coordinate]
    cases c with
    | inl i => exact (measurable_pi_apply i).comp hk.snd.fst
    | inr i => exact (measurable_pi_apply i).comp hk.snd.snd
  · intro t k c
    have hk := (measurable_pi_apply k).comp (h.response t)
    simp only [← batchCode_coordinate]
    cases c with
    | inl i => exact (measurable_pi_apply i).comp hk.snd.fst
    | inr i => exact (measurable_pi_apply i).comp hk.snd.snd
  · intro t k
    simp only [← batchCode_active]
    exact measurableSet_eq_fun ((measurable_pi_apply k).comp (h.query t)).fst measurable_const
  · exact h.output

theorem CodedTraceMeasurable.halt {Ω : Type*} [MeasurableSpace Ω] {T H K : ℕ}
    (x : Ω → Vec T) (hx : Measurable x) :
    CodedTraceMeasurable (fun ω => (⟨fun _ _ => none, fun _ _ => none, x ω⟩ : InteractionTrace T H K)) := by
  constructor
  · intro t
    change Measurable (fun _ : Ω => batchCode (fun _ : Fin K => (none : Option (Vec T × Vec T))))
    exact measurable_const
  · intro t
    change Measurable (fun _ : Ω => batchCode (fun _ : Fin K => (none : Option (Vec T × Vec T))))
    exact measurable_const
  · exact hx

theorem CodedTraceMeasurable.prepend {Ω : Type*} [MeasurableSpace Ω] {T H K : ℕ}
    (q r : Ω → OnlineBatch T K) (tr : Ω → InteractionTrace T H K)
    (hq : Measurable (fun ω => batchCode (q ω))) (hr : Measurable (fun ω => batchCode (r ω)))
    (ht : CodedTraceMeasurable tr) :
    CodedTraceMeasurable (fun ω => prependOnlineTrace (q ω) (r ω) (tr ω)) := by
  constructor
  · intro t
    refine Fin.cases hq (fun t => ht.query t) t
  · intro t
    refine Fin.cases hr (fun t => ht.response t) t
  · exact ht.output

theorem CodedTraceMeasurable.ite {Ω : Type*} [MeasurableSpace Ω] {T H K : ℕ}
    (q : Ω → Prop) [DecidablePred q] (hq : MeasurableSet {ω | q ω})
    (a b : Ω → InteractionTrace T H K) (ha : CodedTraceMeasurable a) (hb : CodedTraceMeasurable b) :
    CodedTraceMeasurable (fun ω => if q ω then a ω else b ω) := by
  constructor
  · intro t
    have he : (fun ω => batchCode ((if q ω then a ω else b ω).query t)) =
        (fun ω => if q ω then batchCode ((a ω).query t) else batchCode ((b ω).query t)) := by
      funext ω
      by_cases h : q ω <;> simp [h]
    rw [he]
    exact Measurable.ite hq (ha.query t) (hb.query t)
  · intro t
    have he : (fun ω => batchCode ((if q ω then a ω else b ω).response t)) =
        (fun ω => if q ω then batchCode ((a ω).response t) else batchCode ((b ω).response t)) := by
      funext ω
      by_cases h : q ω <;> simp [h]
    rw [he]
    exact Measurable.ite hq (ha.response t) (hb.response t)
  · simpa only [apply_ite] using Measurable.ite hq ha.output hb.output

/-- Measurable state rules; the state may contain the clock and full response history.
No objective, oracle, or hidden seed is an argument of any rule. -/
structure StatefulPolicy (X : Type*) [MeasurableSpace X] (T K : ℕ) where
  stop : X → Bool
  output : X → Vec T
  batch : X → NonemptyOnlineBatch T K
  update : X × BatchCode T K → X
  stop_measurable : Measurable stop
  output_measurable : Measurable output
  batch_measurable : Measurable (fun s => batchCode (batch s).points)
  update_measurable : Measurable update

namespace StatefulPolicy

variable {X : Type*} [MeasurableSpace X] {T K : ℕ}

def toOnline (P : StatefulPolicy X T K) : (H : ℕ) → X → OnlinePolicy T K H
  | 0, s => .halt (P.output s)
  | H + 1, s => if P.stop s = true then .halt (P.output s) else
      .ask (P.batch s) (fun r => P.toOnline H (P.update (s, batchCode r)))

theorem execute_succ (P : StatefulPolicy X T K) (O : StochasticOracle T Bool)
    (H : ℕ) (s : X) (w : RoundWorld (H + 1)) :
    (P.toOnline (H + 1) s).execute O w =
      if P.stop s = true then ⟨fun _ _ => none, fun _ _ => none, P.output s⟩ else
        prependOnlineTrace (P.batch s).points (OnlinePolicy.answer O (P.batch s).points (w 0))
          ((P.toOnline H (P.update (s, batchCode (OnlinePolicy.answer O (P.batch s).points (w 0))))).execute O
            (fun t => w t.succ)) := by
  by_cases hs : P.stop s = true <;> simp [toOnline, hs, OnlinePolicy.execute, prependOnlineTrace]

theorem execution_measurable (P : StatefulPolicy X T K) (O : StochasticOracle T Bool)
    (hO : MeasurableOracle O) : ∀ H {Ω : Type*} [MeasurableSpace Ω] (s : Ω → X),
      Measurable s → ∀ w : RoundWorld H,
        CodedTraceMeasurable (fun ω => (P.toOnline H (s ω)).execute O w) := by
  intro H
  induction H with
  | zero =>
    intro Ω _ s hs w
    exact CodedTraceMeasurable.halt _ (P.output_measurable.comp hs)
  | succ H ih =>
    intro Ω _ s hs w
    simp only [execute_succ]
    have hq := P.batch_measurable.comp hs
    have hr := measurable_answer_code O hO (w 0) (fun ω => (P.batch (s ω)).points) hq
    have hu := P.update_measurable.comp (hs.prodMk hr)
    exact CodedTraceMeasurable.ite _
      (measurableSet_eq_fun (P.stop_measurable.comp hs) measurable_const) _ _
      (CodedTraceMeasurable.halt _ (P.output_measurable.comp hs))
      (CodedTraceMeasurable.prepend _ _ _ hq hr (ih _ hu (fun t => w t.succ)))

theorem observableOnline (P : StatefulPolicy X T K) (O : StochasticOracle T Bool)
    (hO : MeasurableOracle O) (H : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (s : Ω → X) (hs : Measurable s) : ObservableOnline O (fun ω => P.toOnline H (s ω)) :=
  fun w => (P.execution_measurable O hO H s hs w).observable

end StatefulPolicy
theorem measurable_findGreatest {Ω : Type*} [MeasurableSpace Ω]
    (q : Ω → ℕ → Prop) [∀ ω, DecidablePred (q ω)]
    (hq : ∀ n, MeasurableSet {ω | q ω n}) (n : ℕ) :
    Measurable (fun ω => Nat.findGreatest (q ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [Nat.findGreatest_succ]
    exact Measurable.ite (hq (n + 1)) measurable_const ih

theorem measurable_prog {T : ℕ} (a : ℝ) : Measurable (prog (T := T) a) := by
  unfold prog
  apply measurable_findGreatest
  intro n
  simp only [Set.setOf_exists, Set.setOf_and]
  apply MeasurableSet.iUnion
  intro i
  have hi : Continuous (fun u : Vec T => u i) := by fun_prop
  exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const hi.measurable.abs)

theorem chain_gradient_continuous {T : ℕ} (C : ExplicitZeroChainCertificate T) : Continuous C.gradF := by
  have h : LipschitzWith ⟨ℓ₀, by norm_num [ℓ₀]⟩ C.gradF := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    simpa only [dist_eq_norm] using C.grad_lipschitz u v
  exact h.continuous

theorem measurable_bvBaseOracle {T : ℕ} (C : ExplicitZeroChainCertificate T) (p : ℝ) (ξ : Bool) :
    Measurable (fun u => bvBaseOracle C p u ξ) := by
  apply measurable_pi_lambda
  intro i
  have hg := (measurable_pi_apply i).comp (chain_gradient_continuous C).measurable
  have hf : Measurable (fun u : Vec T => frontierIndicator u i) :=
    Measurable.ite (measurableSet_lt (measurable_prog _) measurable_const) measurable_const measurable_const
  exact hg.mul (measurable_const.add (hf.mul measurable_const))

theorem measurable_asBaseOracle {T : ℕ} (C : ExplicitZeroChainCertificate T) (p : ℝ) (ξ : Bool) :
    Measurable (fun u => asBaseOracle C p u ξ) := by
  apply measurable_pi_lambda
  intro i
  have hg := (measurable_pi_apply i).comp (chain_gradient_continuous C).measurable
  have ht : LipschitzWith ⟨explicitMGamma ^ 2, sq_nonneg _⟩ (fun u : Vec T => ThetaGate u i) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    simpa only [Real.dist_eq, dist_eq_norm] using thetaGate_lipschitz explicitSmoothGateCertificate u v i
  exact hg.mul (measurable_const.add (ht.continuous.measurable.mul measurable_const))

theorem measurable_liftedOracle {T : ℕ} (B : BaseOracle T) (P : LiftParameters)
    (hB : ∀ ξ, Measurable (fun u => B.g u ξ)) : MeasurableOracle (liftedOracle B P) := by
  intro ξ
  have hd : Measurable (fun z : Vec T × Vec T => z.2 - P.γ • z.1) :=
    measurable_snd.sub (measurable_fst.const_smul P.γ)
  have hb : Measurable (fun z : Vec T × Vec T => B.g (P.β • z.2) ξ) :=
    (hB ξ).comp (measurable_snd.const_smul P.β)
  exact (hd.const_smul (P.ν * P.γ)).prodMk ((hb.const_smul P.q).sub (hd.const_smul P.ν))

theorem ManuscriptBVProblem.oracle_measurable (P : ManuscriptBVProblem) : MeasurableOracle P.oracle :=
  measurable_liftedOracle P.base P.calibration.lift (measurable_bvBaseOracle P.chain P.p)

theorem ManuscriptASProblem.oracle_measurable (P : ManuscriptASProblem) : MeasurableOracle P.oracle :=
  measurable_liftedOracle P.base P.calibration.lift (measurable_asBaseOracle P.chain P.p)

namespace ManuscriptBVProblem

theorem stateful_product_budget_lower (P : ManuscriptBVProblem) {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (S : StatefulPolicy X P.T K) (s : Ω → X) (hs : Measurable s)
    (c : StationarityCriterion) (hl : AEOracleLegal ρ P.oracle P.p (fun ω => S.toOnline N (s ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi (fun ω => S.toOnline N (s ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_budget_lower ρ _ c (S.observableOnline P.oracle P.oracle_measurable N s hs) hl h

theorem stateful_product_moreau_budget_lower (P : ManuscriptBVProblem) {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (S : StatefulPolicy X P.T K) (s : Ω → X) (hs : Measurable s)
    (c : StationarityCriterion) (hl : AEOracleLegal ρ P.oracle P.p (fun ω => S.toOnline N (s ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad (fun ω => S.toOnline N (s ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_moreau_budget_lower ρ _ c (S.observableOnline P.oracle P.oracle_measurable N s hs) hl h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem stateful_product_budget_lower (P : ManuscriptASProblem) {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (S : StatefulPolicy X P.T K) (s : Ω → X) (hs : Measurable s)
    (c : StationarityCriterion) (hl : AEOracleLegal ρ P.oracle P.p (fun ω => S.toOnline N (s ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi (fun ω => S.toOnline N (s ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_budget_lower ρ _ c (S.observableOnline P.oracle P.oracle_measurable N s hs) hl h

theorem stateful_product_moreau_budget_lower (P : ManuscriptASProblem) {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (S : StatefulPolicy X P.T K) (s : Ω → X) (hs : Measurable s)
    (c : StationarityCriterion) (hl : AEOracleLegal ρ P.oracle P.p (fun ω => S.toOnline N (s ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad (fun ω => S.toOnline N (s ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_moreau_budget_lower ρ _ c (S.observableOnline P.oracle P.oracle_measurable N s hs) hl h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
