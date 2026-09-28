import ManuscriptTraceEvents

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact
namespace Rectangular

/-- Extend a finite trace by empty slots; this contains no extra oracle calls. -/
def Trace.queryAt {dx dy H K : ℕ} (tr : Trace dx dy H K) (t : ℕ) : Batch dx dy K :=
  if h : t < H then tr.query ⟨t, h⟩ else fun _ => none

def Trace.responseAt {dx dy H K : ℕ} (tr : Trace dx dy H K) (t : ℕ) : Batch dx dy K :=
  if h : t < H then tr.response ⟨t, h⟩ else fun _ => none

/-- Equality of the full observable transcript, ignoring only empty padding. -/
def Trace.Same {dx dy H J K : ℕ} (a : Trace dx dy H K) (b : Trace dx dy J K) : Prop :=
  a.queryAt = b.queryAt ∧ a.responseAt = b.responseAt ∧ a.output = b.output

theorem Trace.Same.symm {dx dy H J K : ℕ} {a : Trace dx dy H K} {b : Trace dx dy J K}
    (h : a.Same b) : b.Same a := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem Trace.Same.trans {dx dy H J L K : ℕ} {a : Trace dx dy H K} {b : Trace dx dy J K}
    {c : Trace dx dy L K} (hab : a.Same b) (hbc : b.Same c) : a.Same c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

@[simp] theorem queryAt_fin {dx dy H K : ℕ} (tr : Trace dx dy H K) (t : Fin H) :
    tr.queryAt t.val = tr.query t := by simp [Trace.queryAt, t.isLt]

@[simp] theorem responseAt_fin {dx dy H K : ℕ} (tr : Trace dx dy H K) (t : Fin H) :
    tr.responseAt t.val = tr.response t := by simp [Trace.responseAt, t.isLt]

theorem queryAt_some_lt {dx dy H K : ℕ} (tr : Trace dx dy H K) (t : ℕ) (k : Fin K)
    (q : Pair dx dy) (h : tr.queryAt t k = some q) : t < H := by
  by_contra hn
  simp [Trace.queryAt, hn] at h

theorem responseAt_some_lt {dx dy H K : ℕ} (tr : Trace dx dy H K) (t : ℕ) (k : Fin K)
    (q : Pair dx dy) (h : tr.responseAt t k = some q) : t < H := by
  by_contra hn
  simp [Trace.responseAt, hn] at h

theorem standardSupport_iff_nat {dx dy H K : ℕ} (tr : Trace dx dy H K) :
    StandardSupport tr ↔
      (∀ t k q, tr.queryAt t k = some q → ∀ c ∈ support q,
        ∃ s : ℕ, s < t ∧ ∃ j r, tr.responseAt s j = some r ∧ c ∈ support r) ∧
      (∀ c ∈ support (tr.output, (0 : Vec dy)), ∃ s : ℕ, ∃ j r,
        tr.responseAt s j = some r ∧ c ∈ support r) := by
  constructor
  · intro h
    constructor
    · intro t k q ht c hc
      have hlt := queryAt_some_lt tr t k q ht
      have ht' : tr.query ⟨t, hlt⟩ k = some q := by simpa [Trace.queryAt, hlt] using ht
      obtain ⟨s, hs, j, r, hr, hc⟩ := h.1 ⟨t, hlt⟩ k q ht' c hc
      exact ⟨s.val, hs, j, r, by simpa only [responseAt_fin] using hr, hc⟩
    · intro c hc
      obtain ⟨s, j, r, hr, hc⟩ := h.2 c hc
      exact ⟨s.val, j, r, by simpa only [responseAt_fin] using hr, hc⟩
  · intro h
    constructor
    · intro t k q ht c hc
      obtain ⟨s, hs, j, r, hr, hc⟩ := h.1 t.val k q (by simpa only [queryAt_fin] using ht) c hc
      have hlt := responseAt_some_lt tr s j r hr
      exact ⟨⟨s, hlt⟩, hs, j, r, by simpa [Trace.responseAt, hlt] using hr, hc⟩
    · intro c hc
      obtain ⟨s, j, r, hr, hc⟩ := h.2 c hc
      have hlt := responseAt_some_lt tr s j r hr
      exact ⟨⟨s, hlt⟩, j, r, by simpa [Trace.responseAt, hlt] using hr, hc⟩

theorem Trace.Same.support_iff {dx dy H J K : ℕ} {a : Trace dx dy H K} {b : Trace dx dy J K}
    (h : a.Same b) : StandardSupport a ↔ StandardSupport b := by
  simp only [standardSupport_iff_nat, h.1, h.2.1, h.2.2]

theorem haltTrace_same {dx dy H J K : ℕ} (x : Vec dx) :
    (haltTrace x dy H K).Same (haltTrace x dy J K) := by
  constructor
  · funext t
    simp [Trace.queryAt, haltTrace]
  · constructor
    · funext t
      simp [Trace.responseAt, haltTrace]
    · rfl

theorem queryAt_prepend_zero {dx dy H K : ℕ} (q r : Batch dx dy K) (tr : Trace dx dy H K) :
    (prepend q r tr).queryAt 0 = q := by simp [Trace.queryAt, prepend]

theorem queryAt_prepend_succ {dx dy H K : ℕ} (q r : Batch dx dy K) (tr : Trace dx dy H K)
    (t : ℕ) : (prepend q r tr).queryAt (t + 1) = tr.queryAt t := by
  by_cases h : t < H
  · simp [Trace.queryAt, prepend, h, Nat.succ_lt_succ_iff]
  · simp [Trace.queryAt, prepend, h, Nat.succ_lt_succ_iff]

theorem responseAt_prepend_zero {dx dy H K : ℕ} (q r : Batch dx dy K) (tr : Trace dx dy H K) :
    (prepend q r tr).responseAt 0 = r := by simp [Trace.responseAt, prepend]

theorem responseAt_prepend_succ {dx dy H K : ℕ} (q r : Batch dx dy K) (tr : Trace dx dy H K)
    (t : ℕ) : (prepend q r tr).responseAt (t + 1) = tr.responseAt t := by
  by_cases h : t < H
  · simp [Trace.responseAt, prepend, h, Nat.succ_lt_succ_iff]
  · simp [Trace.responseAt, prepend, h, Nat.succ_lt_succ_iff]

theorem prepend_same {dx dy H J K : ℕ} (q r : Batch dx dy K)
    {a : Trace dx dy H K} {b : Trace dx dy J K} (h : a.Same b) :
    (prepend q r a).Same (prepend q r b) := by
  constructor
  · funext t
    cases t with
    | zero => simp only [queryAt_prepend_zero]
    | succ t => simpa only [queryAt_prepend_succ] using congrFun h.1 t
  · constructor
    · funext t
      cases t with
      | zero => simp only [responseAt_prepend_zero]
      | succ t => simpa only [responseAt_prepend_succ] using congrFun h.2.1 t
    · exact h.2.2

theorem calls_haltTrace {dx : ℕ} (x : Vec dx) (dy H K : ℕ) :
    calls (haltTrace x dy H K) = 0 := by simp [calls, batchSize, haltTrace]

theorem calls_prepend {dx dy H K : ℕ} (q r : Batch dx dy K) (tr : Trace dx dy H K) :
    calls (prepend q r tr) = batchSize q + calls tr := by
  simp [calls, prepend, Fin.sum_univ_succ]

namespace Policy
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ}

/-- A common seed stream compares different finite fuels without changing any seed. -/
def runNat? {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (H n : ℕ) (s : History Ω dx dy K n) (w : ℕ → Seed) : Option (Trace dx dy H K) :=
  P.run? O H n s (fun t => w t.val)

/-- Every successful finite run fits within any fuel at least its actual call count. -/
theorem runNat_budget_normalize {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : ℕ → Seed) (tr : Trace dx dy H K),
      P.runNat? O H n s w = some tr → ∀ N, calls tr ≤ N →
      ∃ out : Trace dx dy N K, P.runNat? O N n s w = some out ∧
        out.Same tr ∧ calls out = calls tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hr N hb
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp only [runNat?, run?, dif_pos hd, dif_pos hs, Option.some.injEq] at hr
        subst tr
        refine ⟨haltTrace (P.output n ⟨⟨s, hd⟩, hs⟩) dy N K, ?_, haltTrace_same _, ?_⟩
        · cases N <;> simp [runNat?, run?, hd, hs]
        · simp only [calls_haltTrace]
      · simp [runNat?, run?, hd, hs] at hr
    · simp [runNat?, run?, hd] at hr
  | succ H ih =>
    intro n s w tr hr N hb
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp only [runNat?, run?, dif_pos hd, dif_pos hs, Option.some.injEq] at hr
        subst tr
        refine ⟨haltTrace (P.output n ⟨⟨s, hd⟩, hs⟩) dy N K, ?_, haltTrace_same _, ?_⟩
        · cases N <;> simp [runNat?, run?, hd, hs]
        · simp only [calls_haltTrace]
      · let q := (P.batch n ⟨⟨s, hd⟩, hs⟩).points
        let r := answer O q (w 0)
        let s' := append s (encode q, encode r)
        let w' := fun t => w (t + 1)
        have he : P.runNat? O (H + 1) n s w = (P.runNat? O H (n + 1) s' w').map (prepend q r) := by
          simp only [runNat?, run?, dif_pos hd, dif_neg hs]
          rfl
        rw [he] at hr
        cases ht : P.runNat? O H (n + 1) s' w' with
        | none => simp [ht] at hr
        | some tail =>
          rw [ht] at hr
          change some (prepend q r tail) = some tr at hr
          have hr := Option.some.inj hr
          subst tr
          have hq : 1 ≤ batchSize q := (P.batch n ⟨⟨s, hd⟩, hs⟩).size_pos
          rw [calls_prepend] at hb
          cases N with
          | zero => omega
          | succ N =>
            have hb' : calls tail ≤ N := by omega
            obtain ⟨out, hout, hsame, hcalls⟩ := ih (n + 1) s' w' tail ht N hb'
            refine ⟨prepend q r out, ?_, prepend_same q r hsame, ?_⟩
            · change P.runNat? O (N + 1) n s w = some (prepend q r out)
              have he' : P.runNat? O (N + 1) n s w =
                  (P.runNat? O N (n + 1) s' w').map (prepend q r) := by
                simp only [runNat?, run?, dif_pos hd, dif_neg hs]
                rfl
              rw [he', hout]
              rfl
            · simp only [calls_prepend, hcalls]
    · simp [runNat?, run?, hd] at hr

theorem runNat_budget_normalize_legal {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : History Ω dx dy K n) (w : ℕ → Seed)
    (tr : Trace dx dy H K) (hr : P.runNat? O H n s w = some tr)
    (hs : StandardSupport tr) (N : ℕ) (hb : calls tr ≤ N) :
    ∃ out : Trace dx dy N K, P.runNat? O N n s w = some out ∧
      StandardSupport out ∧ calls out ≤ N ∧ out.Same tr := by
  obtain ⟨out, ho, he, hc⟩ := P.runNat_budget_normalize O H n s w tr hr N hb
  exact ⟨out, ho, he.support_iff.mpr hs, hc ▸ hb, he⟩

theorem runNat_query_empty_after_calls {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : History Ω dx dy K n) (w : ℕ → Seed)
    (tr : Trace dx dy H K) (hr : P.runNat? O H n s w = some tr) (t : ℕ) (ht : calls tr ≤ t) :
    tr.queryAt t = fun _ => none := by
  obtain ⟨out, _, he, _⟩ := P.runNat_budget_normalize O H n s w tr hr (calls tr) le_rfl
  rw [← he.1]
  simp [Trace.queryAt, not_lt.mpr ht]

theorem runNat_response_empty_after_calls {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : History Ω dx dy K n) (w : ℕ → Seed)
    (tr : Trace dx dy H K) (hr : P.runNat? O H n s w = some tr) (t : ℕ) (ht : calls tr ≤ t) :
    tr.responseAt t = fun _ => none := by
  obtain ⟨out, _, he, _⟩ := P.runNat_budget_normalize O H n s w tr hr (calls tr) le_rfl
  rw [← he.2.1]
  simp [Trace.responseAt, not_lt.mpr ht]

/-- Different successful fuel choices produce exactly the same transcript and call count. -/
theorem runNat_success_unique {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H J n : ℕ) (s : History Ω dx dy K n) (w : ℕ → Seed)
    (a : Trace dx dy H K) (b : Trace dx dy J K)
    (ha : P.runNat? O H n s w = some a) (hb : P.runNat? O J n s w = some b) :
    a.Same b ∧ calls a = calls b := by
  obtain ⟨a', ha', hsa, hca⟩ := P.runNat_budget_normalize O H n s w a ha
    (calls a + calls b) (Nat.le_add_right _ _)
  obtain ⟨b', hb', hsb, hcb⟩ := P.runNat_budget_normalize O J n s w b hb
    (calls a + calls b) (Nat.le_add_left _ _)
  have he : a' = b' := Option.some.inj (ha'.symm.trans hb')
  subst b'
  exact ⟨hsa.symm.trans hsb, hca.symm.trans hcb⟩

/-- The first N seeds suffice for any successful execution with at most N calls. -/
theorem runNat_budget_prefix {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H n N : ℕ) (s : History Ω dx dy K n) (w v : ℕ → Seed)
    (tr : Trace dx dy H K) (hr : P.runNat? O H n s w = some tr) (hb : calls tr ≤ N)
    (hp : ∀ t < N, v t = w t) :
    ∃ out : Trace dx dy N K, P.runNat? O N n s v = some out ∧ out.Same tr ∧ calls out = calls tr := by
  obtain ⟨out, ho, he, hc⟩ := P.runNat_budget_normalize O H n s w tr hr N hb
  have hw : (fun t : Fin N => v t.val) = (fun t : Fin N => w t.val) :=
    funext (fun t => hp t.val t.isLt)
  exact ⟨out, by simpa only [runNat?, hw] using ho, he, hc⟩

theorem trace_same_of_runNat {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H N : ℕ) (ω : Ω) (w : ℕ → Seed)
    (tr : Trace dx dy H K) (hr : P.runNat? O H 0 (ω, Fin.elim0) w = some tr)
    (hb : calls tr ≤ N) :
    (MeasuredOracle.trace P O N (ω, fun t => w t.val)).Same tr ∧
      calls (MeasuredOracle.trace P O N (ω, fun t => w t.val)) = calls tr := by
  obtain ⟨out, ho, he, hc⟩ := P.runNat_budget_normalize O H 0 _ w tr hr N hb
  change ((P.runNat? O N 0 (ω, Fin.elim0) w).getD (haltTrace 0 dy N K)).Same tr ∧
    calls ((P.runNat? O N 0 (ω, Fin.elim0) w).getD (haltTrace 0 dy N K)) = calls tr
  rw [ho]
  exact ⟨he, hc⟩

theorem loss_eq_of_runNat {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (H N : ℕ) (ω : Ω) (w : ℕ → Seed)
    (tr : Trace dx dy H K) (hr : P.runNat? O H 0 (ω, Fin.elim0) w = some tr)
    (hb : calls tr ≤ N) (c : StationarityCriterion) (g : Vec dx → Vec dx) :
    MeasuredOracle.loss P c O g N (ω, fun t => w t.val) =
      match c with
      | .norm => ENNReal.ofReal ‖g tr.output‖
      | .squared => ENNReal.ofReal (‖g tr.output‖ ^ 2) := by
  have ho := (P.trace_same_of_runNat O H N ω w tr hr hb).1.2.2
  cases c <;> simp only [MeasuredOracle.loss, ho]

/-- Existence of a finite supported execution with bounded calls; no round limit is fixed. -/
def EventuallyLegal {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (N : ℕ) (ω : Ω) (w : ℕ → Seed) : Prop :=
  ∃ H, ∃ tr : Trace dx dy H K, P.runNat? O H 0 (ω, Fin.elim0) w = some tr ∧
    StandardSupport tr ∧ calls tr ≤ N

theorem eventuallyLegal_iff {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (N : ℕ) (ω : Ω) (w : ℕ → Seed) :
    P.EventuallyLegal O N ω w ↔ P.LegalEvent O N N (ω, fun t => w t.val) := by
  rw [legalEvent_iff_native]
  constructor
  · rintro ⟨H, tr, hr, hs, hb⟩
    obtain ⟨out, ho, hs', hb', _⟩ := P.runNat_budget_normalize_legal O H 0 _ w tr hr hs N hb
    exact ⟨out, ho, hs', hb'⟩
  · rintro ⟨tr, hr, hs, hb⟩
    exact ⟨N, tr, hr, hs, hb⟩

theorem eventuallyLegal_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (N : ℕ) :
    MeasurableSet {z : Ω × (ℕ → Seed) | P.EventuallyLegal O N z.1 z.2} := by
  have hm : Measurable (fun z : Ω × (ℕ → Seed) => (z.1, fun t : Fin N => z.2 t.val)) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun t => (measurable_pi_apply t.val).comp measurable_snd))
  simpa only [Set.preimage_setOf_eq, ← eventuallyLegal_iff] using
    (P.legalEvent_measurable O hO N N).preimage hm

/-- Every stream terminates after some finite number of rounds, using at most N calls.
The stopping horizon is allowed to depend on both the internal seed and oracle stream. -/
def EventualBudget {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (N : ℕ) : Prop :=
  ∀ ω w, ∃ H, ∃ tr : Trace dx dy H K,
    P.runNat? O H 0 (ω, Fin.elim0) w = some tr ∧ calls tr ≤ N

def extendWorld {Seed : Type} {N : ℕ} (seed : Seed) (w : Fin N → Seed) (t : ℕ) : Seed :=
  if h : t < N then w ⟨t, h⟩ else seed

@[simp] theorem extendWorld_fin {Seed : Type} {N : ℕ} (seed : Seed) (w : Fin N → Seed)
    (t : Fin N) : extendWorld seed w t.val = w t := by simp [extendWorld, t.isLt]

theorem eventualBudget_iff_finite {Seed : Type} [Nonempty Seed]
    (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) (N : ℕ) :
    P.EventualBudget O N ↔ ∀ z : Ω × (Fin N → Seed), ∃ tr,
      P.run? O N 0 (z.1, Fin.elim0) z.2 = some tr ∧ calls tr ≤ N := by
  constructor
  · intro h z
    obtain ⟨H, tr, hr, hb⟩ := h z.1 (extendWorld (Classical.choice ‹Nonempty Seed›) z.2)
    obtain ⟨out, ho, _, hc⟩ := P.runNat_budget_normalize O H 0 _ _ tr hr N hb
    refine ⟨out, ?_, hc ▸ hb⟩
    simpa only [runNat?, extendWorld_fin] using ho
  · intro h ω w
    obtain ⟨tr, hr, hb⟩ := h (ω, fun t => w t.val)
    exact ⟨N, tr, hr, hb⟩

end Policy
end Rectangular

namespace MeasuredOracle
universe u

theorem Instance.seed_nonempty (I : Instance) : Nonempty I.Seed := by
  obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (show I.law Set.univ ≠ 0 by simp)
  exact ⟨x⟩

/-- The same legal class, expressed with path-dependent finite termination horizons. -/
def EventualLegal {K : ℕ} (A : Rectangular.Family.{u} K) (valid : Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I → (A.policy I.dx I.dy).EventualBudget I.oracle N ∧
    ∀ᵐ z ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N),
      Rectangular.StandardSupport (trace (A.policy I.dx I.dy) I.oracle N z)

theorem eventualLegal_iff {K N : ℕ} (A : Rectangular.Family.{u} K) (valid : Instance → Prop) :
    EventualLegal A valid N ↔ Legal A valid N := by
  unfold EventualLegal Legal
  apply forall_congr'
  intro I
  letI := I.seed_nonempty
  apply forall_congr'
  intro hI
  exact and_congr_left (fun _ => (A.policy I.dx I.dy).eventualBudget_iff_finite I.oracle N)

end MeasuredOracle

theorem ManuscriptBVProblem.eventual_measured_budget_lower (P : ManuscriptBVProblem)
    {K N : ℕ} (hK : 1 ≤ K) (A : Rectangular.Family K) (c : StationarityCriterion)
    (m : StationarityObjective) {valid : MeasuredOracle.Instance → Prop}
    (ha : MeasuredOracle.EventualLegal A valid N)
    (hI : valid (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)))
    (h : MeasuredOracle.risk A c m P.M N
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.measured_budget_lower hK A c m ((MeasuredOracle.eventualLegal_iff A valid).mp ha) hI h

theorem ManuscriptASProblem.eventual_measured_budget_lower (P : ManuscriptASProblem)
    {K N : ℕ} (hK : 1 ≤ K) (A : Rectangular.Family K) (c : StationarityCriterion)
    (m : StationarityObjective) {valid : MeasuredOracle.Instance → Prop}
    (ha : MeasuredOracle.EventualLegal A valid N)
    (hI : valid (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)))
    (h : MeasuredOracle.risk A c m P.M N
      (MeasuredOracle.Instance.ofBernoulli (Rectangular.Instance.ofSquare P.onlineInstance)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.measured_budget_lower hK A c m ((MeasuredOracle.eventualLegal_iff A valid).mp ha) hI h

end NCSCPureStochasticLB.PaperExact
