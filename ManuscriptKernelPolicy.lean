import ManuscriptKernelRandomization
import ManuscriptAlgorithmRepresentation

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace NCSCPureStochasticLB.PaperExact
namespace Rectangular.KernelPolicy

variable {dx dy K : ℕ}

instance code_standardBorel : StandardBorelSpace (Code dx dy K) := by
  exact @StandardBorelSpace.pi_countable (Fin K) inferInstance
    (fun _ => Bool × Pair dx dy) (fun _ => inferInstance) (fun _ => inferInstance)

/-- Stop flag, output, and finitely many query slots. Inactive coordinates are ignored. -/
abbrev RawAction (dx dy K : ℕ) := Bool × Vec dx × Code dx dy K

def ValidAction (a : RawAction dx dy K) : Prop :=
  a.1 = true ∨ ∃ k, (a.2.2 k).1 = true

theorem validAction_measurable : MeasurableSet {a : RawAction dx dy K | ValidAction a} := by
  unfold ValidAction
  simp only [setOf_or, setOf_exists]
  exact (measurableSet_eq_fun measurable_fst measurable_const).union
    (MeasurableSet.iUnion (fun k => measurableSet_eq_fun
      (((measurable_pi_apply k).comp measurable_snd.snd).fst) measurable_const)
    )

/-- A legal decision stops or contains a nonempty batch of at most K queries. -/
abbrev Action (dx dy K : ℕ) := {a : RawAction dx dy K // ValidAction a}

instance action_nonempty : Nonempty (Action dx dy K) :=
  ⟨⟨(true, 0, fun _ => (false, 0, 0)), Or.inl rfl⟩⟩

instance action_standardBorel : StandardBorelSpace (Action dx dy K) :=
  (validAction_measurable (dx := dx) (dy := dy) (K := K)).standardBorel

def decode (q : Code dx dy K) : Batch dx dy K :=
  fun k => if (q k).1 = true then some (q k).2 else none

theorem decode_encode (q : Batch dx dy K) : decode (encode q) = q := by
  funext k
  cases h : q k <;> simp [decode, encode, h]

theorem normalizedCode_measurable : Measurable (fun q : Code dx dy K => encode (decode q)) := by
  apply measurable_pi_lambda
  intro k
  have hk : Measurable (fun q : Code dx dy K => q k) := measurable_pi_apply k
  have he : (fun q : Code dx dy K => encode (decode q) k) =
      (fun q => if (q k).1 = true then (true, (q k).2) else (false, 0, 0)) := by
    funext q
    by_cases h : (q k).1 = true <;> simp [encode, decode, h]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun hk.fst measurable_const)
    (measurable_const.prodMk hk.snd) measurable_const

def continueBatch (a : Action dx dy K) (h : a.val.1 ≠ true) : NonemptyBatch dx dy K where
  points := decode a.val.2.2
  size_pos := by
    obtain ⟨k, hk⟩ := a.property.resolve_left h
    have hsum := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin K))) =>
        Nat.zero_le (if (decode a.val.2.2 j).isSome then 1 else 0)) (Finset.mem_univ k)
    simpa [batchSize, decode, hk] using hsum
  size_le := by
    unfold batchSize
    calc
      _ ≤ ∑ _ : Fin K, 1 := Finset.sum_le_sum (by intro k _; split <;> omega)
      _ = K := by simp

def stopAction (x : Vec dx) : Action dx dy K :=
  ⟨(true, x, encode (fun _ => none)), Or.inl rfl⟩

/-- Every original nonempty batch is representable, including arbitrary active slot patterns. -/
def queryAction (q : NonemptyBatch dx dy K) : Action dx dy K := by
  refine ⟨(false, 0, encode q.points), Or.inr ?_⟩
  apply Classical.byContradiction
  intro hn
  have hz : batchSize q.points = 0 := by
    unfold batchSize
    apply Finset.sum_eq_zero
    intro k _
    have hk : (encode q.points k).1 ≠ true := fun h => hn ⟨k, h⟩
    cases h : q.points k <;> simp [encode, h] at hk ⊢
  have hp := q.size_pos
  omega

theorem queryAction_roundtrip (q : NonemptyBatch dx dy K) :
    decode (queryAction q).val.2.2 = q.points := decode_encode q.points

abbrev Transcript (dx dy K n : ℕ) := Fin n → Code dx dy K × Code dx dy K

/-- History-dependent internal decisions; no oracle or hidden oracle-seed argument. -/
structure RandomizedPolicy (dx dy K : ℕ) where
  decision : ∀ n, Kernel (Transcript dx dy K n) (Action dx dy K)
  markov : ∀ n, IsMarkovKernel (decision n)

attribute [instance] RandomizedPolicy.markov

def sample (P : RandomizedPolicy dx dy K) (n : ℕ) : Transcript dx dy K n → ℝ → Action dx dy K :=
  (KernelRandomization.standardBorel_kernel_randomization (P.decision n)).choose

theorem sample_measurable (P : RandomizedPolicy dx dy K) (n : ℕ) :
    Measurable (Function.uncurry (sample P n)) :=
  (KernelRandomization.standardBorel_kernel_randomization (P.decision n)).choose_spec.1

theorem sample_law (P : RandomizedPolicy dx dy K) (n : ℕ) (s : Transcript dx dy K n) :
    KernelRandomization.uniform.map (sample P n s) = P.decision n s :=
  (KernelRandomization.standardBorel_kernel_randomization (P.decision n)).choose_spec.2 s

/-- Read only the current internal tape coordinate and the recorded transcript. -/
def decisionAt (P : RandomizedPolicy dx dy K) (n : ℕ)
    (s : History (ℕ → ℝ) dx dy K n) : Action dx dy K := sample P n s.2 (s.1 n)

theorem decisionAt_measurable (P : RandomizedPolicy dx dy K) (n : ℕ) :
    Measurable (decisionAt P n) :=
  (sample_measurable P n).comp
    (measurable_snd.prodMk ((measurable_pi_apply n).comp measurable_fst))

theorem decisionAt_causal (P : RandomizedPolicy dx dy K) (n : ℕ)
    (s t : History (ℕ → ℝ) dx dy K n) (hh : s.2 = t.2) (hu : s.1 n = t.1 n) :
    decisionAt P n s = decisionAt P n t := by
  simp only [decisionAt, hh, hu]

/-- Compile the randomized decisions into the existing native rectangular policy. -/
def toPolicy (P : RandomizedPolicy dx dy K) : Policy (ℕ → ℝ) dx dy K where
  domain _ := Set.univ
  domain_measurable _ := MeasurableSet.univ
  stop n s := (decisionAt P n s.val).val.1
  stop_measurable n :=
    (measurable_subtype_coe.comp ((decisionAt_measurable P n).comp measurable_subtype_coe)).fst
  output n s := (decisionAt P n s.val.val).val.2.1
  output_measurable n :=
    (measurable_subtype_coe.comp ((decisionAt_measurable P n).comp
      (measurable_subtype_coe.comp measurable_subtype_coe))).snd.fst
  batch n s := continueBatch (decisionAt P n s.val.val) s.property
  batch_measurable n := normalizedCode_measurable.comp
    (measurable_subtype_coe.comp ((decisionAt_measurable P n).comp
      (measurable_subtype_coe.comp measurable_subtype_coe))).snd.snd

theorem toPolicy_stop (P : RandomizedPolicy dx dy K) (n : ℕ)
    (s : History (ℕ → ℝ) dx dy K n) :
    (toPolicy P).stop n ⟨s, Set.mem_univ s⟩ = (decisionAt P n s).val.1 := rfl

theorem toPolicy_output (P : RandomizedPolicy dx dy K) (n : ℕ)
    (s : History (ℕ → ℝ) dx dy K n) (h : (decisionAt P n s).val.1 = true) :
    (toPolicy P).output n ⟨⟨s, Set.mem_univ s⟩, h⟩ = (decisionAt P n s).val.2.1 := rfl

theorem toPolicy_batch (P : RandomizedPolicy dx dy K) (n : ℕ)
    (s : History (ℕ → ℝ) dx dy K n) (h : (decisionAt P n s).val.1 ≠ true) :
    ((toPolicy P).batch n ⟨⟨s, Set.mem_univ s⟩, h⟩).points =
      decode (decisionAt P n s).val.2.2 := rfl

/-- Stopping issues no oracle query. Continuing uses the original finite slot encoding. -/
def query (a : Action dx dy K) : Code dx dy K :=
  if a.val.1 = true then encode (fun _ => none) else encode (decode a.val.2.2)

theorem query_measurable : Measurable (@query dx dy K) := by
  exact Measurable.ite
    (measurableSet_eq_fun measurable_subtype_coe.fst measurable_const)
    measurable_const (normalizedCode_measurable.comp measurable_subtype_coe.snd.snd)

/-- A single round records stopping/output and the chosen queries and same-seed responses. -/
def observation {Seed : Type} (O : Oracle dx dy Seed) (a : Action dx dy K) (ξ : Seed) :
    Bool × Vec dx × (Code dx dy K × Code dx dy K) :=
  (a.val.1, a.val.2.1, query a, answerCode O (query a) ξ)

theorem observation_measurable {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) :
    Measurable (Function.uncurry (@observation dx dy K Seed O)) := by
  have ha : Measurable (fun z : Action dx dy K × Seed => z.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  exact ha.fst.prodMk (ha.snd.fst.prodMk
    ((query_measurable.comp measurable_fst).prodMk
      (answerCode_measurable O hO _ (query_measurable.comp measurable_fst) _ measurable_snd)))

theorem observation_stop {Seed : Type} (O : Oracle dx dy Seed)
    (a : Action dx dy K) (ξ : Seed) (h : a.val.1 = true) :
    observation O a ξ = (true, a.val.2.1, encode (fun _ => none), encode (fun _ => none)) := by
  simp [observation, query, h, answerCode, encode]
  funext k
  simp [answerCode, encode]

/-- The compiled native query and response agree with the recorded observation. -/
theorem observation_continue {Seed : Type} (O : Oracle dx dy Seed)
    (P : RandomizedPolicy dx dy K) (n : ℕ) (s : History (ℕ → ℝ) dx dy K n)
    (ξ : Seed) (h : (decisionAt P n s).val.1 ≠ true) :
    let q := ((toPolicy P).batch n ⟨⟨s, Set.mem_univ s⟩, h⟩).points
    (observation O (decisionAt P n s) ξ).2.2 = (encode q, encode (answer O q ξ)) := by
  dsimp only
  rw [toPolicy_batch]
  simp only [observation, query, if_neg h, answerCode_encode]

/-- One fixed compiler works for every external oracle and every independent oracle-seed law.
The source law is explicitly a product, so internal and oracle seeds are not shared. -/
theorem sample_observation_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (n : ℕ) (s : Transcript dx dy K n)
    (ρ : Measure Seed) [SFinite ρ] (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) :
    (KernelRandomization.uniform.prod ρ).map
      (fun z => observation O (sample P n s z.1) z.2) =
    ((P.decision n s).prod ρ).map (Function.uncurry (@observation dx dy K Seed O)) := by
  have hf : Measurable (sample P n s) := (sample_measurable P n).comp
    (measurable_const.prodMk measurable_id : Measurable (fun u : ℝ => (s, u)))
  change (KernelRandomization.uniform.prod ρ).map
    (Function.uncurry (observation O) ∘ Prod.map (sample P n s) id) = _
  rw [← Measure.map_map (observation_measurable O hO) (hf.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, sample_law]

/-- One infinite internal tape, whose law is fixed independently of the oracle. -/
def internalTapeLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => KernelRandomization.uniform)

instance internalTapeLaw_probability : IsProbabilityMeasure internalTapeLaw := by
  unfold internalTapeLaw
  infer_instance

/-- Every finite selection of internal coordinates has the independent uniform product law. -/
theorem internalTapeLaw_restrict (I : Finset ℕ) :
    internalTapeLaw.map I.restrict = Measure.pi (fun _ : I => KernelRandomization.uniform) :=
  Measure.infinitePi_map_restrict _

end Rectangular.KernelPolicy
end NCSCPureStochasticLB.PaperExact
