import ManuscriptMemoryNative

noncomputable section
open MeasureTheory ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact.Rectangular.StochasticMemory
open KernelPolicy
variable {dx dy H K : ℕ}

/-- Decode a trace code; inactive slots are normalized to `none`. -/
def decodeTrace (c : TraceCode dx dy H K) : Trace dx dy H K :=
  ⟨fun t => decode (c.1 t), fun t => decode (c.2.1 t), c.2.2⟩

theorem decodeTrace_code (tr : Trace dx dy H K) : decodeTrace tr.code = tr := by
  cases tr with
  | mk q r x =>
    simp only [decodeTrace, Trace.code, Trace.mk.injEq, and_true]
    exact ⟨funext (fun _ => decode_encode _), funext (fun _ => decode_encode _)⟩

theorem decodeTrace_code_measurable :
    Measurable (fun c : TraceCode dx dy H K => (decodeTrace c).code) := by
  change Measurable (fun c : TraceCode dx dy H K =>
    ((fun t => encode (decode (c.1 t))), (fun t => encode (decode (c.2.1 t))), c.2.2))
  exact (measurable_pi_lambda _ (fun t : Fin H => (@normalizedCode_measurable dx dy K).comp
    ((measurable_pi_apply t).comp measurable_fst))).prodMk
      ((measurable_pi_lambda _ (fun t : Fin H => (@normalizedCode_measurable dx dy K).comp
        ((measurable_pi_apply t).comp measurable_snd.fst))).prodMk measurable_snd.snd)

theorem decodeTrace_measurable : Measurable (@decodeTrace dx dy H K) :=
  (measurable_trace_iff_code _).mpr decodeTrace_code_measurable

/-- True termination, pair-zero-respecting trace and actual returned-gradient
budget. The Boolean flag prevents failure from passing via the default trace. -/
def LegalCode (B : ℕ) (c : Bool × TraceCode dx dy H K) : Prop :=
  c.1 = true ∧ StandardSupport (decodeTrace c.2) ∧ calls (decodeTrace c.2) ≤ B

theorem legalCode_measurable (B : ℕ) :
    MeasurableSet {c : Bool × TraceCode dx dy H K | LegalCode B c} :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    ((support_event_measurable (fun c : Bool × TraceCode dx dy H K => decodeTrace c.2)
      (decodeTrace_code_measurable.comp measurable_snd)).inter
      (measurableSet_le
        (calls_measurable (fun c : Bool × TraceCode dx dy H K => decodeTrace c.2)
          (decodeTrace_code_measurable.comp measurable_snd)) measurable_const))

theorem legalCode_partial_iff (B : ℕ) (r : Option (Trace dx dy H K)) :
    LegalCode B (r.isSome, partialCode r) ↔
      ∃ tr, r = some tr ∧ StandardSupport tr ∧ calls tr ≤ B := by
  cases r with
  | none => simp [LegalCode]
  | some tr => simp [LegalCode, partialCode, decodeTrace_code]

theorem native_legalCode_iff (M : Model dx dy K) {Seed : Type}
    (O : Oracle dx dy Seed) (H B : ℕ) (z : RandomTape × (Fin H → Seed)) :
    LegalCode B (nativeCompleteCode M O H z) ↔
      ∃ tr, (toMemory M).run? O H 0 ((toMemory M).initial z.1) z.2 = some tr ∧
        StandardSupport tr ∧ calls tr ≤ B :=
  legalCode_partial_iff B _

theorem native_legalCode_iff_policy (M : Model dx dy K) {Seed : Type}
    (O : Oracle dx dy Seed) (H B : ℕ) (z : RandomTape × (Fin H → Seed)) :
    LegalCode B (nativeCompleteCode M O H z) ↔ (toMemory M).toPolicy.LegalEvent O H B z := by
  rw [native_legalCode_iff, Policy.legalEvent_iff_native, MemoryAlgorithm.toPolicy_initial_run]

/-- Every measurable a.e. trace predicate transfers, without replacing a.e.
quantification by a universal quantifier over oracle paths. -/
theorem native_memory_kernel_ae (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ)
    (P : Bool × TraceCode dx dy H K → Prop) (hP : MeasurableSet {c | P c}) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))), P (nativeCompleteCode M O H z)) ↔
      ∀ᵐ s ∂IndexedKernelRun.initializedLaw (jointKernel M O hO ρ)
        (M.initial.map (jointInitial M)) (H + 1), P (forwardCompleteCode H s.1) := by
  have hm : Measurable (fun s : JointState M (H + 1) => forwardCompleteCode H s.1) :=
    (forwardCompleteCode_measurable H).comp measurable_fst
  rw [← ae_map_iff (nativeCompleteCode_measurable M O hO H).aemeasurable hP,
    native_memory_kernel_law M O hO ρ H, ae_map_iff hm.aemeasurable hP]

theorem native_memory_ae_legal_iff (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H B : ℕ) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))),
      ∃ tr, (toMemory M).run? O H 0 ((toMemory M).initial z.1) z.2 = some tr ∧
        StandardSupport tr ∧ calls tr ≤ B) ↔
    ∀ᵐ s ∂IndexedKernelRun.initializedLaw (jointKernel M O hO ρ)
      (M.initial.map (jointInitial M)) (H + 1), LegalCode B (forwardCompleteCode H s.1) := by
  simpa only [native_legalCode_iff] using
    native_memory_kernel_ae M O hO ρ H (LegalCode B) (legalCode_measurable B)

/-- Fubini form: the exceptional set of oracle paths may depend on the internal tape. -/
theorem native_memory_ae_legal_iterated (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H B : ℕ) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))),
      LegalCode B (nativeCompleteCode M O H z)) ↔
    ∀ᵐ u ∂randomTapeLaw, ∀ᵐ w ∂Measure.pi (fun _ : Fin H => ρ),
      LegalCode B (nativeCompleteCode M O H (u, w)) :=
  Measure.ae_prod_iff_ae_ae ((legalCode_measurable B).preimage (nativeCompleteCode_measurable M O hO H))

/-- Countable oracle spaces permit one co-null set of internal tapes on which
all positive-mass finite paths are legal. Zero-mass paths are not constrained. -/
theorem native_memory_ae_positive_paths (M : Model dx dy K) {Seed : Type}
    [MeasurableSpace Seed] [Countable Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H B : ℕ) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))),
      LegalCode B (nativeCompleteCode M O H z)) ↔
    ∀ᵐ u ∂randomTapeLaw, ∀ w : Fin H → Seed,
      (Measure.pi (fun _ : Fin H => ρ)) {w} ≠ 0 →
        LegalCode B (nativeCompleteCode M O H (u, w)) := by
  rw [native_memory_ae_legal_iterated M O hO ρ H B]
  simp only [ae_iff_of_countable]

/-- Only under an explicit full-atom hypothesis does a.e. legality yield all
oracle paths on one co-null internal set. This is not used for continuous seeds. -/
theorem native_memory_ae_all_paths (M : Model dx dy K) {Seed : Type}
    [MeasurableSpace Seed] [Countable Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H B : ℕ)
    (hatom : ∀ w : Fin H → Seed, (Measure.pi (fun _ : Fin H => ρ)) {w} ≠ 0) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))),
      LegalCode B (nativeCompleteCode M O H z)) ↔
    ∀ᵐ u ∂randomTapeLaw, ∀ w : Fin H → Seed,
      LegalCode B (nativeCompleteCode M O H (u, w)) := by
  rw [native_memory_ae_positive_paths M O hO ρ H B]
  apply Filter.eventually_congr
  filter_upwards [] with u
  constructor
  · intro h w
    exact h w (hatom w)
  · intro h w _
    exact h w

theorem bernoulli_path_atom (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (H : ℕ) (w : Fin H → Bool) :
    (Measure.pi (fun _ : Fin H => bernoulliMeasure p)) {w} ≠ 0 ↔ 0 < roundWeight p w := by
  change iidRoundMeasure (bernoulliMeasure p) H {w} ≠ 0 ↔ _
  rw [iidRoundMeasure_bernoulli p hp0 hp1, roundMeasure_singleton]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]

/-- For a nondegenerate Bernoulli oracle all finite paths have positive mass.
The common internal co-null set is obtained without a pathwise assumption. -/
theorem native_memory_bernoulli_all_paths (M : Model dx dy K)
    (O : Oracle dx dy Bool) (hO : JointlyMeasurable O)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (H B : ℕ) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => bernoulliMeasure p))),
      LegalCode B (nativeCompleteCode M O H z)) ↔
    ∀ᵐ u ∂randomTapeLaw, ∀ w : Fin H → Bool,
      LegalCode B (nativeCompleteCode M O H (u, w)) := by
  letI := bernoulliMeasure_probability p hp0.le hp1.le
  apply native_memory_ae_all_paths M O hO (bernoulliMeasure p) H B
  intro w
  exact (bernoulli_path_atom p hp0.le hp1.le H w).mpr
    (roundWeight_pos_of_non_degenerate p hp0 hp1 w)

/-- At p=1 only the actual all-true path is constrained, not zero-mass paths. -/
theorem native_memory_bernoulli_one (M : Model dx dy K)
    (O : Oracle dx dy Bool) (hO : JointlyMeasurable O) (H B : ℕ) :
    (∀ᵐ z ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => bernoulliMeasure 1))),
      LegalCode B (nativeCompleteCode M O H z)) ↔
    ∀ᵐ u ∂randomTapeLaw,
      LegalCode B (nativeCompleteCode M O H (u, trueOracleWorld H)) := by
  letI := bernoulliMeasure_probability 1 (by norm_num) (by norm_num)
  have h := native_memory_ae_positive_paths M O hO (bernoulliMeasure 1) H B
  simp only [bernoulli_path_atom 1 (by norm_num) (by norm_num), roundWeight_one_pos_iff] at h
  rw [h]
  apply Filter.eventually_congr
  filter_upwards [] with u
  constructor
  · intro hw
    exact hw _ rfl
  · intro hu w hw
    simpa only [hw] using hu

end NCSCPureStochasticLB.PaperExact.Rectangular.StochasticMemory
