import ManuscriptCausalGuard

noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact.Rectangular.CausalGuard
open KernelPolicy

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ}

theorem ofActions_run_stop
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) (H n : ℕ)
    (s : History Ω dx dy K n) (w : Fin H → Seed) (hs : (f n s).val.1 = true) :
    (ofActions f hf).run? O H n s w = some (haltTrace (f n s).val.2.1 dy H K) := by
  cases H <;> simp [Policy.run?, ofActions, hs]

theorem ofActions_run_continue
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) (H n : ℕ)
    (s : History Ω dx dy K n) (w : Fin (H + 1) → Seed) (hs : (f n s).val.1 ≠ true) :
    let q := decode (f n s).val.2.2
    let r := answer O q (w 0)
    (ofActions f hf).run? O (H + 1) n s w =
      ((ofActions f hf).run? O H (n + 1) (append s (encode q, encode r))
        (fun t => w t.succ)).map (prepend q r) := by
  simp [Policy.run?, ofActions, hs, continueBatch]

/-- Full trace preservation on successful legal runs. The prefix invariant
`n ≤ spent s.2` follows from nonempty batches, and justifies the round cap. -/
theorem guardedPolicy_preserves_relative (B : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed) (tr : Trace dx dy H K),
      n ≤ spent s.2 → (ofActions f hf).run? O H n s w = some tr →
      Relative s.2 tr → spent s.2 + calls tr ≤ B →
      (guardedPolicy B f hf).run? O H n s w = some tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hn hr hsup hb
    by_cases hs : (f n s).val.1 = true
    · rw [ofActions_run_stop f hf O 0 n s w hs] at hr
      have hr := Option.some.inj hr
      subst tr
      have ha : Allowed B s.2 (f n s) :=
        ⟨by simpa [Supported, hs] using (relative_halt _ _ _).mp hsup, Or.inl hs⟩
      have he := guard_preserves B s.2 (f n s) ha
      simp [Policy.run?, guardedPolicy, ofActions, he, hs]
    · simp [Policy.run?, ofActions, hs] at hr
  | succ H ih =>
    intro n s w tr hn hr hsup hb
    by_cases hs : (f n s).val.1 = true
    · rw [ofActions_run_stop f hf O (H + 1) n s w hs] at hr
      have hr := Option.some.inj hr
      subst tr
      have ha : Allowed B s.2 (f n s) :=
        ⟨by simpa [Supported, hs] using (relative_halt _ _ _).mp hsup, Or.inl hs⟩
      have he := guard_preserves B s.2 (f n s) ha
      simp [Policy.run?, guardedPolicy, ofActions, he, hs]
    · let q := decode (f n s).val.2.2
      let r := answer O q (w 0)
      rw [ofActions_run_continue f hf O H n s w hs] at hr
      change ((ofActions f hf).run? O H (n + 1) (append s (encode q, encode r))
        (fun t => w t.succ)).map (prepend q r) = some tr at hr
      cases ht : (ofActions f hf).run? O H (n + 1) (append s (encode q, encode r))
          (fun t => w t.succ) with
      | none => simp [ht] at hr
      | some tail =>
        rw [ht] at hr
        change some (prepend q r tail) = some tr at hr
        have hr := Option.some.inj hr
        subst tr
        have hparts := (relative_prepend s q r tail).mp hsup
        rw [calls_prepend] at hb
        have hpos : 1 ≤ batchSize q := (continueBatch (f n s) hs).size_pos
        have ha : Allowed B s.2 (f n s) := by
          refine ⟨?_, Or.inr ⟨by omega, by change spent s.2 + batchSize q ≤ B; omega⟩⟩
          simpa [Supported, hs] using hparts.1
        have he := guard_preserves B s.2 (f n s) ha
        have htail := ih (n + 1) (append s (encode q, encode r)) (fun t => w t.succ)
          tail (by rw [spent_append]; omega) ht hparts.2
          (by rw [spent_append]; omega)
        have hgs : (guard B s.2 (f n s)).val.1 ≠ true := by simpa [he] using hs
        rw [show guardedPolicy B f hf = ofActions (fun n s => guard B s.2 (f n s))
          (fun n => (guard_measurable B).comp (measurable_snd.prodMk (hf n))) from rfl]
        rw [ofActions_run_continue _ _ O H n s w hgs]
        simp only [he]
        change ((guardedPolicy B f hf).run? O H (n + 1) (append s (encode q, encode r))
          (fun t => w t.succ)).map (prepend q r) = some (prepend q r tail)
        rw [htail]
        rfl

theorem guardedPolicy_preserves (B H : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) (ω : Ω) (w : Fin H → Seed)
    (tr : Trace dx dy H K) (hr : (ofActions f hf).run? O H 0 (ω, Fin.elim0) w = some tr)
    (hs : StandardSupport tr) (hb : calls tr ≤ B) :
    (guardedPolicy B f hf).run? O H 0 (ω, Fin.elim0) w = some tr :=
  guardedPolicy_preserves_relative B f hf O H 0 (ω, Fin.elim0) w tr
    (Nat.zero_le _) hr ((relative_initial tr).mpr hs) (by simpa [spent] using hb)

/-- Both successful termination and the full trace are retained in the law. -/
def completeCode {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (H : ℕ) (z : Ω × (Fin H → Seed)) : Bool × TraceCode dx dy H K :=
  let r := P.run? O H 0 (z.1, Fin.elim0) z.2
  (r.isSome, partialCode r)

theorem completeCode_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (H : ℕ) :
    Measurable (completeCode P O H) :=
  (P.defined_measurable O hO H).prodMk (P.trace_code_measurable O hO H)

theorem guardedPolicy_ae_run (B H : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed)))
    (h : ∀ᵐ z ∂μ, (ofActions f hf).LegalEvent O H B z) :
    ∀ᵐ z ∂μ, (guardedPolicy B f hf).run? O H 0 (z.1, Fin.elim0) z.2 =
      (ofActions f hf).run? O H 0 (z.1, Fin.elim0) z.2 := by
  filter_upwards [h] with z hz
  obtain ⟨tr, ht, hs, hb⟩ := (Policy.legalEvent_iff_native _ _ _ _ _).mp hz
  rw [ht]
  exact guardedPolicy_preserves B H f hf O z.1 z.2 tr ht hs hb

theorem guardedPolicy_ae_code (B H : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed)))
    (h : ∀ᵐ z ∂μ, (ofActions f hf).LegalEvent O H B z) :
    completeCode (guardedPolicy B f hf) O H =ᵐ[μ] completeCode (ofActions f hf) O H := by
  filter_upwards [guardedPolicy_ae_run B H f hf O μ h] with z hz
  simp only [completeCode, hz]

/-- No countability or full-support assumption on the oracle law is needed. -/
theorem guardedPolicy_law (B H : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed)))
    (h : ∀ᵐ z ∂μ, (ofActions f hf).LegalEvent O H B z) :
    μ.map (completeCode (guardedPolicy B f hf) O H) =
      μ.map (completeCode (ofActions f hf) O H) :=
  Measure.map_congr (guardedPolicy_ae_code B H f hf O μ h)

theorem guardedPolicy_event (B H : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed)))
    (h : ∀ᵐ z ∂μ, (ofActions f hf).LegalEvent O H B z)
    (E : Set (Bool × TraceCode dx dy H K)) :
    (μ.map (completeCode (guardedPolicy B f hf) O H)) E =
      (μ.map (completeCode (ofActions f hf) O H)) E := by
  rw [guardedPolicy_law B H f hf O μ h]

theorem guardedPolicy_risk (B H : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed)))
    (h : ∀ᵐ z ∂μ, (ofActions f hf).LegalEvent O H B z)
    (L : Bool × TraceCode dx dy H K → ENNReal) :
    (∫⁻ z, L (completeCode (guardedPolicy B f hf) O H z) ∂μ) =
      ∫⁻ z, L (completeCode (ofActions f hf) O H z) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [guardedPolicy_ae_code B H f hf O μ h] with z hz
  rw [hz]

theorem stopAction_measurable : Measurable (@stopAction dx dy K) := by
  exact (measurable_const.prodMk (measurable_id.prodMk measurable_const)).subtype_mk

theorem queryAction_rule_measurable {X : Type*} [MeasurableSpace X]
    (q : X → NonemptyBatch dx dy K) (hq : Measurable (fun x => encode (q x).points)) :
    Measurable (fun x => queryAction (q x)) := by
  exact (measurable_const.prodMk (measurable_const.prodMk hq)).subtype_mk

/-- Totalization only consults the current domain and decision. A domain failure
is assigned the fixed zero-stop action; successful native runs are preserved. -/
def policyAction (P : Policy Ω dx dy K) (n : ℕ) : History Ω dx dy K n → Action dx dy K :=
  extendHistoryRule (P.domain n) (fun s =>
    if P.stop n s = true then
      extendHistoryRule {s : P.domain n | P.stop n s = true}
        (fun s => stopAction (P.output n s)) (stopAction 0) s
    else
      extendHistoryRule {s : P.domain n | P.stop n s ≠ true}
        (fun s => queryAction (P.batch n s)) (stopAction 0) s) (stopAction 0)

theorem policyAction_measurable (P : Policy Ω dx dy K) (n : ℕ) :
    Measurable (policyAction P n) := by
  apply extendHistoryRule_measurable _ (P.domain_measurable n)
  have hs := (P.stop_measurable n) (measurableSet_singleton true)
  apply Measurable.ite hs
  · exact extendHistoryRule_measurable _ hs _
      (stopAction_measurable.comp (P.output_measurable n)) _
  · exact extendHistoryRule_measurable _ hs.compl _
      (queryAction_rule_measurable _ (P.batch_measurable n)) _

theorem policyAction_stop (P : Policy Ω dx dy K) (n : ℕ)
    (s : History Ω dx dy K n) (hd : s ∈ P.domain n) (hs : P.stop n ⟨s, hd⟩ = true) :
    policyAction P n s = stopAction (P.output n ⟨⟨s, hd⟩, hs⟩) := by
  simp [policyAction, extendHistoryRule, hd, hs]

theorem policyAction_continue (P : Policy Ω dx dy K) (n : ℕ)
    (s : History Ω dx dy K n) (hd : s ∈ P.domain n) (hs : P.stop n ⟨s, hd⟩ ≠ true) :
    policyAction P n s = queryAction (P.batch n ⟨⟨s, hd⟩, hs⟩) := by
  simp [policyAction, extendHistoryRule, hd, hs]

def totalizedPolicy (P : Policy Ω dx dy K) : Policy Ω dx dy K :=
  ofActions (policyAction P) (policyAction_measurable P)

theorem totalizedPolicy_preserves (P : Policy Ω dx dy K)
    {Seed : Type} (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed) (tr : Trace dx dy H K),
      P.run? O H n s w = some tr → (totalizedPolicy P).run? O H n s w = some tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · have ha := policyAction_stop P n s hd hs
        simp [Policy.run?, hd, hs] at hr
        subst tr
        simp [totalizedPolicy, Policy.run?, ofActions, ha, stopAction]
      · simp [Policy.run?, hd, hs] at hr
    · simp [Policy.run?, hd] at hr
  | succ H ih =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · have ha := policyAction_stop P n s hd hs
        simp [Policy.run?, hd, hs] at hr
        subst tr
        simp [totalizedPolicy, Policy.run?, ofActions, ha, stopAction]
      · let q := (P.batch n ⟨⟨s, hd⟩, hs⟩).points
        let r := answer O q (w 0)
        simp only [Policy.run?, dif_pos hd, dif_neg hs] at hr
        change (P.run? O H (n + 1) (append s (encode q, encode r))
          (fun t => w t.succ)).map (prepend q r) = some tr at hr
        cases ht : P.run? O H (n + 1) (append s (encode q, encode r))
            (fun t => w t.succ) with
        | none => simp [ht] at hr
        | some tail =>
          rw [ht] at hr
          change some (prepend q r tail) = some tr at hr
          have hr := Option.some.inj hr
          subst tr
          have htail := ih (n + 1) _ (fun t => w t.succ) tail ht
          have ha := policyAction_continue P n s hd hs
          have hsa : (policyAction P n s).val.1 ≠ true := by simp [ha, queryAction]
          unfold totalizedPolicy
          rw [ofActions_run_continue _ _ O H n s w hsa]
          simp only [ha, queryAction_roundtrip]
          change ((totalizedPolicy P).run? O H (n + 1) (append s (encode q, encode r))
            (fun t => w t.succ)).map (prepend q r) = some (prepend q r tail)
          rw [htail]
          rfl
    · simp [Policy.run?, hd] at hr

/-- A single causal measurable repair of the original partial history policy. -/
def repairPolicy (P : Policy Ω dx dy K) (B : ℕ) : Policy Ω dx dy K :=
  guardedPolicy B (policyAction P) (policyAction_measurable P)

theorem repairPolicy_legal (P : Policy Ω dx dy K) (B : ℕ)
    {Seed : Type} (O : Oracle dx dy Seed) (ω : Ω) (w : Fin B → Seed) :
    ∃ tr, (repairPolicy P B).run? O B 0 (ω, Fin.elim0) w = some tr ∧
      StandardSupport tr ∧ calls tr ≤ B :=
  guardedPolicy_legal B (policyAction P) (policyAction_measurable P) O ω w

theorem repairPolicy_preserves (P : Policy Ω dx dy K) (B H : ℕ)
    {Seed : Type} (O : Oracle dx dy Seed) (ω : Ω) (w : Fin H → Seed)
    (tr : Trace dx dy H K) (hr : P.run? O H 0 (ω, Fin.elim0) w = some tr)
    (hs : StandardSupport tr) (hb : calls tr ≤ B) :
    (repairPolicy P B).run? O H 0 (ω, Fin.elim0) w = some tr :=
  guardedPolicy_preserves B H (policyAction P) (policyAction_measurable P) O ω w tr
    (totalizedPolicy_preserves P O H 0 (ω, Fin.elim0) w tr hr) hs hb

theorem repairPolicy_ae_run (P : Policy Ω dx dy K) (B H : ℕ)
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed))) (h : ∀ᵐ z ∂μ, P.LegalEvent O H B z) :
    ∀ᵐ z ∂μ, (repairPolicy P B).run? O H 0 (z.1, Fin.elim0) z.2 =
      P.run? O H 0 (z.1, Fin.elim0) z.2 := by
  filter_upwards [h] with z hz
  obtain ⟨tr, ht, hs, hb⟩ := (Policy.legalEvent_iff_native _ _ _ _ _).mp hz
  rw [ht]
  exact repairPolicy_preserves P B H O z.1 z.2 tr ht hs hb

theorem repairPolicy_ae_code (P : Policy Ω dx dy K) (B H : ℕ)
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed))) (h : ∀ᵐ z ∂μ, P.LegalEvent O H B z) :
    completeCode (repairPolicy P B) O H =ᵐ[μ] completeCode P O H := by
  filter_upwards [repairPolicy_ae_run P B H O μ h] with z hz
  simp only [completeCode, hz]

theorem repairPolicy_law (P : Policy Ω dx dy K) (B H : ℕ)
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed))) (h : ∀ᵐ z ∂μ, P.LegalEvent O H B z) :
    μ.map (completeCode (repairPolicy P B) O H) = μ.map (completeCode P O H) :=
  Measure.map_congr (repairPolicy_ae_code P B H O μ h)

theorem repairPolicy_risk (P : Policy Ω dx dy K) (B H : ℕ)
    {Seed : Type} [MeasurableSpace Seed] (O : Oracle dx dy Seed)
    (μ : Measure (Ω × (Fin H → Seed))) (h : ∀ᵐ z ∂μ, P.LegalEvent O H B z)
    (L : Bool × TraceCode dx dy H K → ENNReal) :
    (∫⁻ z, L (completeCode (repairPolicy P B) O H z) ∂μ) =
      ∫⁻ z, L (completeCode P O H z) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [repairPolicy_ae_code P B H O μ h] with z hz
  rw [hz]

/-- The finite-budget class with termination, support and budget required a.e. -/
def AEFamilyLegal (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I → ∀ᵐ z ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N),
    (A.policy I.dx I.dy).LegalEvent I.oracle N N z

def repairFamily (A : Family.{u} K) (N : ℕ) : Family.{u} K where
  Seed := A.Seed
  seedSpace := A.seedSpace
  law := A.law
  probability := A.probability
  policy dx dy := repairPolicy (A.policy dx dy) N

theorem repairFamily_legal (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ) :
    MeasuredOracle.Legal (repairFamily A N) valid N := by
  intro I _
  constructor
  · intro z
    obtain ⟨tr, ht, _, hb⟩ := repairPolicy_legal (A.policy I.dx I.dy) N I.oracle z.1 z.2
    exact ⟨tr, ht, hb⟩
  · apply Filter.Eventually.of_forall
    intro z
    obtain ⟨tr, ht, hs, _⟩ := repairPolicy_legal (A.policy I.dx I.dy) N I.oracle z.1 z.2
    simpa only [MeasuredOracle.trace, repairFamily, ht, Option.getD_some] using hs

theorem legal_implies_ae (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ)
    (h : MeasuredOracle.Legal A valid N) : AEFamilyLegal A valid N := by
  intro I hI
  filter_upwards [(h I hI).2] with z hz
  obtain ⟨tr, ht, hb⟩ := (h I hI).1 z
  apply (Policy.legalEvent_iff_native _ _ _ _ _).mpr
  exact ⟨tr, ht, by simpa only [MeasuredOracle.trace, ht, Option.getD_some] using hz, hb⟩

theorem repairFamily_risk (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ)
    (h : AEFamilyLegal A valid N) (c : StationarityCriterion) (m : StationarityObjective)
    (M : ℝ) (I : MeasuredOracle.Instance) (hI : valid I) :
    MeasuredOracle.risk (repairFamily A N) c m M N I = MeasuredOracle.risk A c m M N I := by
  apply lintegral_congr_ae
  filter_upwards [repairPolicy_ae_run (A.policy I.dx I.dy) N N I.oracle
    ((A.law I.dx I.dy).prod (iidRoundMeasure I.law N)) (h I hI)] with z hz
  change (repairPolicy (A.policy I.dx I.dy) N).run? I.oracle N 0 (z.1, Fin.elim0) z.2 =
    (A.policy I.dx I.dy).run? I.oracle N 0 (z.1, Fin.elim0) z.2 at hz
  cases c <;> simp only [MeasuredOracle.loss, MeasuredOracle.trace, repairFamily, hz]

/-- One dimension-indexed family works for all instances, with the same internal law. -/
theorem exists_pathwise_representative (A : Family.{u} K)
    (valid : MeasuredOracle.Instance → Prop) (N : ℕ) (h : AEFamilyLegal A valid N) :
    ∃ C : Family.{u} K, MeasuredOracle.Legal C valid N ∧
      ∀ c m M I, valid I → MeasuredOracle.risk C c m M N I = MeasuredOracle.risk A c m M N I :=
  ⟨repairFamily A N, repairFamily_legal A valid N, fun c m M I hI =>
    repairFamily_risk A valid N h c m M I hI⟩

theorem ae_feasible_iff (valid : MeasuredOracle.Instance → Prop) (N : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M : ℝ) (target : ENNReal) :
    (∃ A : Family.{u} K, AEFamilyLegal A valid N ∧
      ∀ I, valid I → MeasuredOracle.risk A c m M N I ≤ target) ↔
    ∃ A : MeasuredOracle.BudgetAlgorithm.{u} valid K N,
      ∀ I, valid I → MeasuredOracle.risk A.val c m M N I ≤ target := by
  constructor
  · rintro ⟨A, hA, hr⟩
    refine ⟨⟨repairFamily A N, repairFamily_legal A valid N⟩, ?_⟩
    intro I hI
    change MeasuredOracle.risk (repairFamily A N) c m M N I ≤ target
    rw [repairFamily_risk A valid N hA c m M I hI]
    exact hr I hI
  · rintro ⟨A, hr⟩
    exact ⟨A.val, legal_implies_ae A.val valid N A.property, hr⟩

def aeComplexity (valid : MeasuredOracle.Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) : ENNReal :=
  sInf {b | ∃ N : ℕ, b = (N : ENNReal) ∧ ∃ A : Family.{u} K, AEFamilyLegal A valid N ∧
    ∀ I, valid I → MeasuredOracle.risk A c m M N I ≤ c.target ε}

/-- The a.e. and pathwise finite-budget formulations have exactly the same complexity. -/
theorem aeComplexity_eq (valid : MeasuredOracle.Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) :
    aeComplexity.{u} valid K c m M ε = MeasuredOracle.complexity.{u} valid K c m M ε := by
  unfold aeComplexity MeasuredOracle.complexity uniformBudgetComplexity
  congr 1
  ext b
  simp only [Set.mem_setOf_eq, worstCaseBudgetRisk_le_iff]
  simp_rw [ae_feasible_iff]

end NCSCPureStochasticLB.PaperExact.Rectangular.CausalGuard
