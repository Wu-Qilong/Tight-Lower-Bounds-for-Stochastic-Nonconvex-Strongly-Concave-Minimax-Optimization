import ManuscriptMemoryAELegal

noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact.Rectangular.CausalGuard
open KernelPolicy

variable {dx dy K n : ℕ}

/-- Coordinates actually returned in the recorded history; inactive slots are ignored. -/
def Seen (h : Transcript dx dy K n) (c : Fin dx ⊕ Fin dy) : Prop :=
  ∃ t k, slotCoordinate (decode (h t).2 k) c ≠ 0

def spent (h : Transcript dx dy K n) : ℕ :=
  ∑ t, batchSize (decode (h t).1)

theorem seen_measurable (c : Fin dx ⊕ Fin dy) :
    MeasurableSet {h : Transcript dx dy K n | Seen h c} := by
  unfold Seen
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_eq_fun
    (slotCoordinate_measurable _ (normalizedCode_measurable.comp
      ((measurable_pi_apply t).snd)) k c) measurable_const).compl

theorem batchSize_decode_measurable :
    Measurable (fun q : Code dx dy K => batchSize (decode q)) := by
  unfold batchSize
  apply Finset.measurable_sum
  intro k _
  exact Measurable.ite (measurableSet_eq_fun
    (active_measurable _ normalizedCode_measurable k) measurable_const)
    measurable_const measurable_const

theorem spent_measurable : Measurable (@spent dx dy K n) := by
  unfold spent
  apply Finset.measurable_sum
  intro t _
  exact batchSize_decode_measurable.comp (measurable_pi_apply t).fst

/-- Current output/query support, checked against the past, never future responses. -/
def Supported (h : Transcript dx dy K n) (a : Action dx dy K) : Prop :=
  if a.val.1 = true then
    ∀ c, Sum.elim a.val.2.1 (0 : Vec dy) c ≠ 0 → Seen h c
  else ∀ k c, slotCoordinate (decode a.val.2.2 k) c ≠ 0 → Seen h c

theorem supported_measurable : MeasurableSet
    {z : Transcript dx dy K n × Action dx dy K | Supported z.1 z.2} := by
  have ha : Measurable (fun z : Transcript dx dy K n × Action dx dy K => z.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  have ho : MeasurableSet {z : Transcript dx dy K n × Action dx dy K |
      ∀ c, Sum.elim z.2.val.2.1 (0 : Vec dy) c ≠ 0 → Seen z.1 c} := by
    simp only [imp_iff_not_or, not_not, Set.setOf_forall, Set.setOf_or]
    apply MeasurableSet.iInter
    intro c
    have hc : Measurable (fun z : Transcript dx dy K n × Action dx dy K =>
        Sum.elim z.2.val.2.1 (0 : Vec dy) c) := by
      cases c with
      | inl i => exact (measurable_pi_apply i).comp ha.snd.fst
      | inr i => exact measurable_const
    exact (measurableSet_eq_fun hc measurable_const).union
      ((seen_measurable c).preimage measurable_fst)
  have hq : MeasurableSet {z : Transcript dx dy K n × Action dx dy K |
      ∀ k c, slotCoordinate (decode z.2.val.2.2 k) c ≠ 0 → Seen z.1 c} := by
    simp only [imp_iff_not_or, not_not, Set.setOf_forall, Set.setOf_or]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro c
    exact (measurableSet_eq_fun (slotCoordinate_measurable _
      (normalizedCode_measurable.comp ha.snd.snd) k c) measurable_const).union
      ((seen_measurable c).preimage measurable_fst)
  have hs : MeasurableSet {z : Transcript dx dy K n × Action dx dy K |
      z.2.val.1 = true} := measurableSet_eq_fun ha.fst measurable_const
  have he : {z : Transcript dx dy K n × Action dx dy K | Supported z.1 z.2} =
      ({z | z.2.val.1 = true} ∩ {z | ∀ c,
        Sum.elim z.2.val.2.1 (0 : Vec dy) c ≠ 0 → Seen z.1 c}) ∪
      ({z | z.2.val.1 ≠ true} ∩ {z | ∀ k c,
        slotCoordinate (decode z.2.val.2.2 k) c ≠ 0 → Seen z.1 c}) := by
    ext z
    by_cases h : z.2.val.1 = true <;> simp [Supported, h]
  rw [he]
  exact (hs.inter ho).union (hs.compl.inter hq)

/-- Stop is always budget-permitted. A new call must fit the actual remaining budget.
The explicit round cap makes termination total even on malformed histories. -/
def Allowed (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K) : Prop :=
  Supported h a ∧ (a.val.1 = true ∨
    n < B ∧ spent h + batchSize (decode a.val.2.2) ≤ B)

theorem allowed_measurable (B : ℕ) : MeasurableSet
    {z : Transcript dx dy K n × Action dx dy K | Allowed B z.1 z.2} := by
  have ha : Measurable (fun z : Transcript dx dy K n × Action dx dy K => z.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  unfold Allowed
  simp only [Set.setOf_and, Set.setOf_or]
  exact supported_measurable.inter
    ((measurableSet_eq_fun ha.fst measurable_const).union
      ((MeasurableSet.const _).inter (measurableSet_le
        ((spent_measurable.comp measurable_fst).add
          (batchSize_decode_measurable.comp ha.snd.snd)) measurable_const)))

theorem zero_allowed (B : ℕ) (h : Transcript dx dy K n) :
    Allowed B h (stopAction 0) := by
  simp [Allowed, Supported, stopAction]

/-- One oracle-uniform guard: reject by stopping at zero, without requesting a response. -/
def guard (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K) : Action dx dy K := by
  classical
  exact if Allowed B h a then a else stopAction 0

theorem guard_measurable (B : ℕ) :
    Measurable (fun z : Transcript dx dy K n × Action dx dy K => guard B z.1 z.2) := by
  classical
  exact Measurable.ite (allowed_measurable B) measurable_snd measurable_const

theorem guard_allowed (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K) :
    Allowed B h (guard B h a) := by
  unfold guard
  split
  · assumption
  · exact zero_allowed B h

theorem guard_preserves (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K)
    (ha : Allowed B h a) : guard B h a = a := by simp [guard, ha]

theorem guard_idempotent (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K) :
    guard B h (guard B h a) = guard B h a := guard_preserves B h _ (guard_allowed B h a)

theorem guard_horizon (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K)
    (hn : B ≤ n) : (guard B h a).val.1 = true := by
  have hg := (guard_allowed B h a).2
  rcases hg with hg | hg
  · exact hg
  · omega

theorem guard_continue (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K)
    (hs : (guard B h a).val.1 ≠ true) :
    guard B h a = a ∧ n < B ∧ spent h + batchSize (decode a.val.2.2) ≤ B ∧
      ∀ k c, slotCoordinate (decode a.val.2.2 k) c ≠ 0 → Seen h c := by
  have he : guard B h a = a := by
    by_cases ha : Allowed B h a
    · exact guard_preserves B h a ha
    · simp [guard, ha, stopAction] at hs
  have hg := guard_allowed B h a
  rw [he] at hg hs
  exact ⟨he, (hg.2.resolve_left hs).1, (hg.2.resolve_left hs).2,
    by simpa [Supported, hs] using hg.1⟩

theorem guard_output (B : ℕ) (h : Transcript dx dy K n) (a : Action dx dy K)
    (hs : (guard B h a).val.1 = true) :
    ∀ c, Sum.elim (guard B h a).val.2.1 (0 : Vec dy) c ≠ 0 → Seen h c := by
  simpa [Supported, hs] using (guard_allowed B h a).1

universe u
variable {Ω : Type u}

theorem spent_append (s : History Ω dx dy K n) (q r : Batch dx dy K) :
    spent (append s (encode q, encode r)).2 = spent s.2 + batchSize q := by
  simp [spent, append, Fin.sum_univ_castSucc, decode_encode]

theorem spent_initial (ω : Ω) : spent ((ω, Fin.elim0) : History Ω dx dy K 0).2 = 0 := by
  simp [spent]

theorem seen_append (s : History Ω dx dy K n) (q r : Batch dx dy K)
    (c : Fin dx ⊕ Fin dy) :
    Seen (append s (encode q, encode r)).2 c ↔
      Seen s.2 c ∨ ∃ k, slotCoordinate (r k) c ≠ 0 := by
  constructor
  · rintro ⟨t, k, ht⟩
    refine Fin.lastCases ?_ (fun j => ?_) t ht
    · intro hh
      exact Or.inr ⟨k, by simpa [append, decode_encode] using hh⟩
    · intro hh
      exact Or.inl ⟨j, k, by simpa [append] using hh⟩
  · rintro (⟨t, k, ht⟩ | ⟨k, hk⟩)
    · exact ⟨t.castSucc, k, by simpa [append] using ht⟩
    · exact ⟨Fin.last n, k, by simpa [append, decode_encode] using hk⟩

def Relative (h : Transcript dx dy K n) {H : ℕ} (tr : Trace dx dy H K) : Prop :=
  (∀ t k c, slotCoordinate (tr.query t k) c ≠ 0 → Seen h c ∨
    ∃ s : Fin H, s.val < t.val ∧ ∃ j, slotCoordinate (tr.response s j) c ≠ 0) ∧
  (∀ c, Sum.elim tr.output (0 : Vec dy) c ≠ 0 → Seen h c ∨
    ∃ s j, slotCoordinate (tr.response s j) c ≠ 0)

theorem relative_initial {H : ℕ} (tr : Trace dx dy H K) :
    Relative (Fin.elim0 : Transcript dx dy K 0) tr ↔ StandardSupport tr := by
  simp [Relative, Seen, standardSupport_iff_coordinates]

theorem relative_halt (h : Transcript dx dy K n) (x : Vec dx) (H : ℕ) :
    Relative h (haltTrace x dy H K) ↔
      ∀ c, Sum.elim x (0 : Vec dy) c ≠ 0 → Seen h c := by
  simp [Relative, haltTrace, slotCoordinate]

theorem relative_prepend (s : History Ω dx dy K n) (q r : Batch dx dy K)
    {H : ℕ} (tr : Trace dx dy H K) :
    Relative s.2 (prepend q r tr) ↔
      (∀ k c, slotCoordinate (q k) c ≠ 0 → Seen s.2 c) ∧
      Relative (append s (encode q, encode r)).2 tr := by
  simp only [Relative, prepend, Fin.forall_fin_succ, Fin.cases_zero, Fin.cases_succ,
    Fin.val_zero, Fin.val_succ, Fin.exists_fin_succ, Nat.not_lt_zero,
    false_and, exists_false, or_false, Nat.zero_lt_succ, true_and,
    Nat.succ_lt_succ_iff, seen_append, or_assoc, and_assoc]

variable [MeasurableSpace Ω]

/-- Compile arbitrary measurable action rules; no resampling or new randomness. -/
def ofActions (f : ∀ n, History Ω dx dy K n → Action dx dy K)
    (hf : ∀ n, Measurable (f n)) : Policy Ω dx dy K where
  domain _ := Set.univ
  domain_measurable _ := MeasurableSet.univ
  stop n s := (f n s.val).val.1
  stop_measurable n := (measurable_subtype_coe.comp ((hf n).comp measurable_subtype_coe)).fst
  output n s := (f n s.val.val).val.2.1
  output_measurable n := (measurable_subtype_coe.comp ((hf n).comp
    (measurable_subtype_coe.comp measurable_subtype_coe))).snd.fst
  batch n s := continueBatch (f n s.val.val) s.property
  batch_measurable n := normalizedCode_measurable.comp
    (measurable_subtype_coe.comp ((hf n).comp
      (measurable_subtype_coe.comp measurable_subtype_coe))).snd.snd

def guardedPolicy (B : ℕ) (f : ∀ n, History Ω dx dy K n → Action dx dy K)
    (hf : ∀ n, Measurable (f n)) : Policy Ω dx dy K :=
  ofActions (fun n s => guard B s.2 (f n s))
    (fun n => (guard_measurable B).comp (measurable_snd.prodMk (hf n)))

/-- Every seed path terminates by the fixed cap, even outside any co-null set. -/
theorem guardedPolicy_terminates (B : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed), B ≤ n + H →
      ∃ tr, (guardedPolicy B f hf).run? O H n s w = some tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w hn
    have hs := guard_horizon B s.2 (f n s) (by omega)
    simp [Policy.run?, guardedPolicy, ofActions, hs]
  | succ H ih =>
    intro n s w hn
    by_cases hs : (guard B s.2 (f n s)).val.1 = true
    · simp [Policy.run?, guardedPolicy, ofActions, hs]
    · let q := (continueBatch (guard B s.2 (f n s)) hs).points
      let r := answer O q (w 0)
      obtain ⟨tr, ht⟩ := ih (n + 1) (append s (encode q, encode r))
        (fun t => w t.succ) (by omega)
      simp only [Policy.run?, guardedPolicy, ofActions, Set.mem_univ, dite_true,
        hs, Bool.false_eq_true, dite_false]
      change ∃ tr', ((guardedPolicy B f hf).run? O H (n + 1)
        (append s (encode q, encode r)) (fun t => w t.succ)).map (prepend q r) = some tr'
      rw [ht]
      exact ⟨_, rfl⟩

/-- The bound counts individual active query slots, not merely rounds. -/
theorem guardedPolicy_budget (B : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed) (tr : Trace dx dy H K),
      spent s.2 ≤ B → (guardedPolicy B f hf).run? O H n s w = some tr →
      spent s.2 + calls tr ≤ B := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hb hr
    by_cases hs : (guard B s.2 (f n s)).val.1 = true
    · simp [Policy.run?, guardedPolicy, ofActions, hs] at hr
      subst tr
      simpa [calls_haltTrace] using hb
    · simp [Policy.run?, guardedPolicy, ofActions, hs] at hr
  | succ H ih =>
    intro n s w tr hb hr
    by_cases hs : (guard B s.2 (f n s)).val.1 = true
    · simp [Policy.run?, guardedPolicy, ofActions, hs] at hr
      subst tr
      simpa [calls_haltTrace] using hb
    · let q := (continueBatch (guard B s.2 (f n s)) hs).points
      let r := answer O q (w 0)
      have hq : spent s.2 + batchSize q ≤ B :=
        ((guard_allowed B s.2 (f n s)).2.resolve_left hs).2
      have hb' : spent (append s (encode q, encode r)).2 ≤ B := by
        rw [spent_append]
        exact hq
      simp only [Policy.run?, guardedPolicy, ofActions, Set.mem_univ, dite_true,
        hs, Bool.false_eq_true, dite_false] at hr
      change ((guardedPolicy B f hf).run? O H (n + 1)
        (append s (encode q, encode r)) (fun t => w t.succ)).map (prepend q r) = some tr at hr
      cases ht : (guardedPolicy B f hf).run? O H (n + 1)
          (append s (encode q, encode r)) (fun t => w t.succ) with
      | none => simp [ht] at hr
      | some tail =>
        rw [ht] at hr
        change some (prepend q r tail) = some tr at hr
        have hr := Option.some.inj hr
        subst tr
        have htail := ih (n + 1) _ (fun t => w t.succ) tail hb' ht
        rw [spent_append] at htail
        simpa only [calls_prepend, Nat.add_assoc] using htail

theorem guardedPolicy_initial_budget (B : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) (ω : Ω) (w : Fin B → Seed) :
    ∃ tr, (guardedPolicy B f hf).run? O B 0 (ω, Fin.elim0) w = some tr ∧ calls tr ≤ B := by
  obtain ⟨tr, ht⟩ := guardedPolicy_terminates B f hf O B 0 (ω, Fin.elim0) w (by omega)
  refine ⟨tr, ht, ?_⟩
  simpa [spent] using
    guardedPolicy_budget B f hf O B 0 (ω, Fin.elim0) w tr
      (by simp [spent]) ht

theorem guardedPolicy_support (B : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed) (tr : Trace dx dy H K),
      (guardedPolicy B f hf).run? O H n s w = some tr → Relative s.2 tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hr
    by_cases hs : (guard B s.2 (f n s)).val.1 = true
    · simp [Policy.run?, guardedPolicy, ofActions, hs] at hr
      subst tr
      exact (relative_halt _ _ _).mpr (guard_output B s.2 (f n s) hs)
    · simp [Policy.run?, guardedPolicy, ofActions, hs] at hr
  | succ H ih =>
    intro n s w tr hr
    by_cases hs : (guard B s.2 (f n s)).val.1 = true
    · simp [Policy.run?, guardedPolicy, ofActions, hs] at hr
      subst tr
      exact (relative_halt _ _ _).mpr (guard_output B s.2 (f n s) hs)
    · let q := (continueBatch (guard B s.2 (f n s)) hs).points
      let r := answer O q (w 0)
      have hq : ∀ k c, slotCoordinate (q k) c ≠ 0 → Seen s.2 c := by
        simpa [Supported, hs] using (guard_allowed B s.2 (f n s)).1
      simp only [Policy.run?, guardedPolicy, ofActions, Set.mem_univ, dite_true,
        hs, Bool.false_eq_true, dite_false] at hr
      change ((guardedPolicy B f hf).run? O H (n + 1)
        (append s (encode q, encode r)) (fun t => w t.succ)).map (prepend q r) = some tr at hr
      cases ht : (guardedPolicy B f hf).run? O H (n + 1)
          (append s (encode q, encode r)) (fun t => w t.succ) with
      | none => simp [ht] at hr
      | some tail =>
        rw [ht] at hr
        change some (prepend q r tail) = some tr at hr
        have hr := Option.some.inj hr
        subst tr
        exact (relative_prepend s q r tail).mpr ⟨hq, ih (n + 1) _ _ tail ht⟩

/-- One measurable policy is pathwise legal for every oracle and seed path.
This theorem alone does not yet assert preservation of the original execution law. -/
theorem guardedPolicy_legal (B : ℕ)
    (f : ∀ n, History Ω dx dy K n → Action dx dy K) (hf : ∀ n, Measurable (f n))
    {Seed : Type} (O : Oracle dx dy Seed) (ω : Ω) (w : Fin B → Seed) :
    ∃ tr, (guardedPolicy B f hf).run? O B 0 (ω, Fin.elim0) w = some tr ∧
      StandardSupport tr ∧ calls tr ≤ B := by
  obtain ⟨tr, ht, hb⟩ := guardedPolicy_initial_budget B f hf O ω w
  exact ⟨tr, ht, (relative_initial tr).mp
    (guardedPolicy_support B f hf O B 0 (ω, Fin.elim0) w tr ht), hb⟩

end NCSCPureStochasticLB.PaperExact.Rectangular.CausalGuard
