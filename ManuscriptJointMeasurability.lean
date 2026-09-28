import ManuscriptOracleMeasure

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact
namespace Rectangular

universe u

def JointlyMeasurable {dx dy : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) : Prop :=
  Measurable (fun z : Pair dx dy × Seed =>
    (O.Gx z.1.1 z.1.2 z.2, O.Gy z.1.1 z.1.2 z.2))

theorem jointlyMeasurable_bool_iff {dx dy : ℕ} (O : Oracle dx dy Bool) :
    JointlyMeasurable O ↔ ∀ ξ, Measurable (fun z : Pair dx dy => (O.Gx z.1 z.2 ξ, O.Gy z.1 z.2 ξ)) := by
  constructor
  · intro h ξ
    exact h.comp (measurable_id.prodMk measurable_const)
  · intro h
    exact measurable_from_prod_countable h

/-- Code-level response, including the active slot flag. -/
def answerCode {dx dy K : ℕ} {Seed : Type} (O : Oracle dx dy Seed)
    (q : Code dx dy K) (ξ : Seed) : Code dx dy K := fun k =>
  if (q k).1 = true then (true, O.Gx (q k).2.1 (q k).2.2 ξ, O.Gy (q k).2.1 (q k).2.2 ξ)
  else (false, 0, 0)

theorem answerCode_encode {dx dy K : ℕ} {Seed : Type}
    (O : Oracle dx dy Seed) (q : Batch dx dy K) (ξ : Seed) :
    answerCode O (encode q) ξ = encode (answer O q ξ) := by
  funext k
  cases h : q k <;> simp [answerCode, encode, answer, h]

theorem answerCode_measurable {X : Type*} [MeasurableSpace X] {dx dy K : ℕ}
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (q : X → Code dx dy K) (hq : Measurable q) (ξ : X → Seed) (hξ : Measurable ξ) :
    Measurable (fun x => answerCode O (q x) (ξ x)) := by
  apply measurable_pi_lambda
  intro k
  have hk := (measurable_pi_apply k).comp hq
  exact Measurable.ite (measurableSet_eq_fun hk.fst measurable_const)
    (measurable_const.prodMk (hO.comp (hk.snd.prodMk hξ))) measurable_const

theorem append_measurable {Ω : Type u} [MeasurableSpace Ω] {dx dy K n : ℕ} :
    Measurable (fun z : History Ω dx dy K n × (Code dx dy K × Code dx dy K) => append z.1 z.2) := by
  apply Measurable.prodMk measurable_fst.fst
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [append, Fin.lastCases_last] using (measurable_snd : Measurable (fun z :
      History Ω dx dy K n × (Code dx dy K × Code dx dy K) => z.2))
  · simpa only [append, Fin.lastCases_castSucc] using (measurable_pi_apply j).comp
      (measurable_fst.snd : Measurable (fun z :
        History Ω dx dy K n × (Code dx dy K × Code dx dy K) => z.1.2))

namespace Policy
variable {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ}

def totalStop (P : Policy Ω dx dy K) (n : ℕ) : History Ω dx dy K n → Bool :=
  extendHistoryRule (P.domain n) (P.stop n) false

def totalOutput (P : Policy Ω dx dy K) (n : ℕ) : History Ω dx dy K n → Vec dx :=
  extendHistoryRule (P.domain n)
    (extendHistoryRule {s | P.stop n s = true} (P.output n) 0) 0

def totalQuery (P : Policy Ω dx dy K) (n : ℕ) : History Ω dx dy K n → Code dx dy K :=
  extendHistoryRule (P.domain n)
    (extendHistoryRule {s | P.stop n s ≠ true} (fun s => encode (P.batch n s).points)
      (encode (fun _ => none))) (encode (fun _ => none))

theorem totalStop_measurable (P : Policy Ω dx dy K) (n : ℕ) : Measurable (P.totalStop n) :=
  extendHistoryRule_measurable _ (P.domain_measurable n) _ (P.stop_measurable n) _

theorem totalOutput_measurable (P : Policy Ω dx dy K) (n : ℕ) : Measurable (P.totalOutput n) :=
  extendHistoryRule_measurable _ (P.domain_measurable n) _
    (extendHistoryRule_measurable _ ((P.stop_measurable n) (measurableSet_singleton true)) _
      (P.output_measurable n) _) _

theorem totalQuery_measurable (P : Policy Ω dx dy K) (n : ℕ) : Measurable (P.totalQuery n) :=
  extendHistoryRule_measurable _ (P.domain_measurable n) _
    (extendHistoryRule_measurable _ (((P.stop_measurable n) (measurableSet_singleton true)).compl) _
      (P.batch_measurable n) _) _

def nextHistory {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (n : ℕ) (s : History Ω dx dy K n) (ξ : Seed) : History Ω dx dy K (n + 1) :=
  append s (P.totalQuery n s, answerCode O (P.totalQuery n s) ξ)

theorem nextHistory_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (fun z : History Ω dx dy K n × Seed => P.nextHistory O n z.1 z.2) :=
  append_measurable.comp (measurable_fst.prodMk
    (((P.totalQuery_measurable n).comp measurable_fst).prodMk
      (answerCode_measurable O hO _ ((P.totalQuery_measurable n).comp measurable_fst) _ measurable_snd)))

/-- The flag records actual termination. A false flag has zero totalized output. -/
def runSummary {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) :
    (H n : ℕ) → History Ω dx dy K n → (Fin H → Seed) → Bool × Vec dx
  | 0, n, s, _ => by
    classical
    exact if s ∈ P.domain n then
      if P.totalStop n s = true then (true, P.totalOutput n s) else (false, 0)
    else (false, 0)
  | H + 1, n, s, w => by
    classical
    exact if s ∈ P.domain n then
      if P.totalStop n s = true then (true, P.totalOutput n s)
      else P.runSummary O H (n + 1) (P.nextHistory O n s (w 0)) (fun t => w t.succ)
    else (false, 0)

def summarize {H : ℕ} (r : Option (Trace dx dy H K)) : Bool × Vec dx :=
  match r with
  | none => (false, 0)
  | some tr => (true, tr.output)

theorem summarize_prepend {H : ℕ} (q r : Batch dx dy K) (tr : Option (Trace dx dy H K)) :
    summarize (tr.map (prepend q r)) = summarize tr := by cases tr <;> rfl

/-- The measurable summary agrees with the original partial interpreter, not an alternative run. -/
theorem runSummary_eq_run {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed),
      P.runSummary O H n s w = summarize (P.run? O H n s w) := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true <;>
        simp [runSummary, run?, totalStop, totalOutput, extendHistoryRule, hd, hs, summarize, haltTrace]
    · simp [runSummary, run?, hd, summarize]
  | succ H ih =>
    intro n s w
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp [runSummary, run?, totalStop, totalOutput, extendHistoryRule, hd, hs, summarize, haltTrace]
      · simp [runSummary, run?, totalStop, totalOutput, totalQuery, nextHistory,
          extendHistoryRule, hd, hs, answerCode_encode, summarize_prepend, ih]
    · simp [runSummary, run?, hd, summarize]

theorem runSummary_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) :
    ∀ H n, Measurable (fun z : History Ω dx dy K n × (Fin H → Seed) =>
      P.runSummary O H n z.1 z.2) := by
  classical
  intro H
  induction H with
  | zero =>
    intro n
    exact Measurable.ite ((P.domain_measurable n).preimage measurable_fst)
      (Measurable.ite (measurableSet_eq_fun ((P.totalStop_measurable n).comp measurable_fst) measurable_const)
        (measurable_const.prodMk ((P.totalOutput_measurable n).comp measurable_fst)) measurable_const)
      measurable_const
  | succ H ih =>
    intro n
    apply Measurable.ite ((P.domain_measurable n).preimage measurable_fst) _ measurable_const
    apply Measurable.ite
      (measurableSet_eq_fun ((P.totalStop_measurable n).comp measurable_fst) measurable_const)
      (measurable_const.prodMk ((P.totalOutput_measurable n).comp measurable_fst))
    apply (ih (n + 1)).comp (f := fun z : History Ω dx dy K n × (Fin (H + 1) → Seed) =>
      (P.nextHistory O n z.1 (z.2 0), fun t : Fin H => z.2 t.succ))
    apply Measurable.prodMk
    · exact (P.nextHistory_measurable O hO n).comp
        (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    · exact measurable_pi_lambda _ (fun t => (measurable_pi_apply t.succ).comp measurable_snd)

theorem summary_output {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (N : ℕ) (z : Ω × (Fin N → Seed)) :
    (P.runSummary O N 0 (z.1, Fin.elim0) z.2).2 = (MeasuredOracle.trace P O N z).output := by
  rw [runSummary_eq_run]
  unfold MeasuredOracle.trace
  cases P.run? O N 0 (z.1, Fin.elim0) z.2 <;> rfl

theorem summary_defined {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (H n : ℕ) (s : History Ω dx dy K n) (w : Fin H → Seed) :
    (P.runSummary O H n s w).1 = (P.run? O H n s w).isSome := by
  rw [runSummary_eq_run]
  cases P.run? O H n s w <;> rfl

theorem trace_output_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (N : ℕ) :
    Measurable (fun z : Ω × (Fin N → Seed) => (MeasuredOracle.trace P O N z).output) := by
  have hi : Measurable (fun z : Ω × (Fin N → Seed) =>
      (((z.1, Fin.elim0) : History Ω dx dy K 0), z.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hm := (P.runSummary_measurable O hO N 0).comp hi
  simpa only [Function.comp_def, summary_output] using hm.snd

theorem defined_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (N : ℕ) :
    Measurable (fun z : Ω × (Fin N → Seed) => (P.run? O N 0 (z.1, Fin.elim0) z.2).isSome) := by
  have hi : Measurable (fun z : Ω × (Fin N → Seed) =>
      (((z.1, Fin.elim0) : History Ω dx dy K 0), z.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hm := (P.runSummary_measurable O hO N 0).comp hi
  simpa only [Function.comp_def, summary_defined] using hm.fst

end Policy
end Rectangular

namespace MeasuredOracle

theorem loss_measurable {Ω : Type*} [MeasurableSpace Ω] {dx dy K : ℕ}
    {Seed : Type} [MeasurableSpace Seed] (P : Rectangular.Policy Ω dx dy K)
    (c : StationarityCriterion) (O : Rectangular.Oracle dx dy Seed) (hO : Rectangular.JointlyMeasurable O)
    (g : Vec dx → Vec dx) (hg : Measurable g) (N : ℕ) : Measurable (loss P c O g N) := by
  have hm := hg.comp (P.trace_output_measurable O hO N)
  cases c
  · exact hm.norm.ennreal_ofReal
  · exact (hm.norm.pow_const 2).ennreal_ofReal

theorem risk_eq_iterated {K : ℕ} (A : Rectangular.Family K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : Instance)
    (hO : Rectangular.JointlyMeasurable I.oracle) (hg : Measurable (Instance.field m M I)) :
    risk A c m M N I =
      ∫⁻ ω, ∫⁻ w, loss (A.policy I.dx I.dy) c I.oracle (Instance.field m M I) N (ω, w)
        ∂iidRoundMeasure I.law N ∂A.law I.dx I.dy := by
  letI := iidRoundMeasure_probability I.law N
  exact lintegral_prod _ (loss_measurable _ c I.oracle hO _ hg N).aemeasurable

/-- Explicit regularity of the actual oracle and target field, not an assumed measurable risk. -/
def Instance.RegularFor (I : Instance) (m : StationarityObjective) (M : ℝ) : Prop :=
  Rectangular.JointlyMeasurable I.oracle ∧ Measurable (Instance.field m M I)

end MeasuredOracle

theorem CalibratedPrimal.g_measurable {T : ℕ} (P : CalibratedPrimal T) : Measurable P.g := by
  have hl : LipschitzWith ⟨5 * P.M / 64, by have := P.M_pos; positivity⟩ P.g := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm] using P.grad_lip x y
  exact hl.continuous.measurable

theorem CalibratedPrimal.prox_measurable {T : ℕ} (P : CalibratedPrimal T) : Measurable P.prox := by
  have hl : LipschitzWith 2 P.prox := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using P.prox_lipschitz x y
  exact hl.continuous.measurable

theorem CalibratedPrimal.envelopeGrad_measurable {T : ℕ} (P : CalibratedPrimal T) :
    Measurable P.envelopeGrad :=
  measurable_const.smul (measurable_id.sub P.prox_measurable)

theorem ManuscriptBVProblem.measured_oracle_jointlyMeasurable (P : ManuscriptBVProblem) :
    Rectangular.JointlyMeasurable
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)).oracle := by
  apply (Rectangular.jointlyMeasurable_bool_iff _).mpr
  exact P.oracle_measurable

theorem ManuscriptASProblem.measured_oracle_jointlyMeasurable (P : ManuscriptASProblem) :
    Rectangular.JointlyMeasurable
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)).oracle := by
  apply (Rectangular.jointlyMeasurable_bool_iff _).mpr
  exact P.oracle_measurable

theorem ManuscriptBVProblem.measured_field_measurable (P : ManuscriptBVProblem)
    (m : StationarityObjective) : Measurable (MeasuredOracle.Instance.field m P.M
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance))) := by
  cases m with
  | primal => exact P.moreau.g_measurable
  | moreau =>
    change Measurable (gradient (P.onlineInstance.moreauValue P.M))
    rw [P.online_moreau_gradient]
    exact P.moreau.envelopeGrad_measurable

theorem ManuscriptASProblem.measured_field_measurable (P : ManuscriptASProblem)
    (m : StationarityObjective) : Measurable (MeasuredOracle.Instance.field m P.M
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance))) := by
  cases m with
  | primal => exact P.moreau.g_measurable
  | moreau =>
    change Measurable (gradient (P.onlineInstance.moreauValue P.M))
    rw [P.online_moreau_gradient]
    exact P.moreau.envelopeGrad_measurable

theorem ManuscriptBVProblem.measured_budget_lower (P : ManuscriptBVProblem)
    {K N : ℕ} (hK : 1 ≤ K) (A : Rectangular.Family K) (c : StationarityCriterion)
    (m : StationarityObjective) {valid : MeasuredOracle.Instance → Prop}
    (ha : MeasuredOracle.Legal A valid N)
    (hI : valid (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)))
    (h : MeasuredOracle.risk A c m P.M N
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  have hd := A.diagonal_legal (MeasuredOracle.legal_restrict A ha)
  have hl := A.diagonal.admissible hd P.onlineInstance hI
  rw [MeasuredOracle.risk_ofBernoulli, ← A.risk_diagonal] at h
  cases m with
  | primal =>
    exact P.stopping_history_product_budget_lower (A.law P.T P.T) hK
      (A.policy P.T P.T).toSquare c hl h
  | moreau =>
    change (A.policy P.T P.T).toSquare.risk c (A.law P.T P.T) P.oracle P.p
      (gradient (P.onlineInstance.moreauValue P.M)) N ≤ c.target P.ε at h
    rw [P.online_moreau_gradient] at h
    exact P.stopping_history_product_moreau_budget_lower (A.law P.T P.T) hK
      (A.policy P.T P.T).toSquare c hl h

theorem ManuscriptASProblem.measured_budget_lower (P : ManuscriptASProblem)
    {K N : ℕ} (hK : 1 ≤ K) (A : Rectangular.Family K) (c : StationarityCriterion)
    (m : StationarityObjective) {valid : MeasuredOracle.Instance → Prop}
    (ha : MeasuredOracle.Legal A valid N)
    (hI : valid (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)))
    (h : MeasuredOracle.risk A c m P.M N
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  have hd := A.diagonal_legal (MeasuredOracle.legal_restrict A ha)
  have hl := A.diagonal.admissible hd P.onlineInstance hI
  rw [MeasuredOracle.risk_ofBernoulli, ← A.risk_diagonal] at h
  cases m with
  | primal =>
    exact P.stopping_history_product_budget_lower (A.law P.T P.T) hK
      (A.policy P.T P.T).toSquare c hl h
  | moreau =>
    change (A.policy P.T P.T).toSquare.risk c (A.law P.T P.T) P.oracle P.p
      (gradient (P.onlineInstance.moreauValue P.M)) N ≤ c.target P.ε at h
    rw [P.online_moreau_gradient] at h
    exact P.stopping_history_product_moreau_budget_lower (A.law P.T P.T) hK
      (A.policy P.T P.T).toSquare c hl h

universe u

theorem ManuscriptBVProblem.regular_measured_complexity_lower (P : ManuscriptBVProblem)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      MeasuredOracle.complexity.{u}
        (fun I => I.ValidBV P.M P.μ P.Δ P.σ ∧ I.RegularFor m P.M) K c m P.M P.ε := by
  let I := MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)
  have hI : I.ValidBV P.M P.μ P.Δ P.σ ∧ I.RegularFor m P.M :=
    ⟨(MeasuredOracle.Instance.ofBernoulli_validBV _ _ _ _ _).mpr
      ((Rectangular.Instance.ofSquare_validBV _ _ _ _ _).mpr P.onlineInstance_valid),
      P.measured_oracle_jointlyMeasurable, P.measured_field_measurable m⟩
  apply uniformBudgetComplexity_lower_of_fixed_instance _ _ _ _ I hI
  intro N A h
  exact P.measured_budget_lower hK A.val c m A.property hI h

theorem ManuscriptASProblem.regular_measured_complexity_lower (P : ManuscriptASProblem)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      MeasuredOracle.complexity.{u}
        (fun I => I.ValidAS P.M P.μ P.Δ P.σ ∧ I.RegularFor m P.M) K c m P.M P.ε := by
  let I := MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)
  have hI : I.ValidAS P.M P.μ P.Δ P.σ ∧ I.RegularFor m P.M :=
    ⟨(MeasuredOracle.Instance.ofBernoulli_validAS _ _ _ _ _).mpr
      ((Rectangular.Instance.ofSquare_validAS _ _ _ _ _).mpr P.onlineInstance_valid),
      P.measured_oracle_jointlyMeasurable, P.measured_field_measurable m⟩
  apply uniformBudgetComplexity_lower_of_fixed_instance _ _ _ _ I hI
  intro N A h
  exact P.measured_budget_lower hK A.val c m A.property hI h

end NCSCPureStochasticLB.PaperExact
