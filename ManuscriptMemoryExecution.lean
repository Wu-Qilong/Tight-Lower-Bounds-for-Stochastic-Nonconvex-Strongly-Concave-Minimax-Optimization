import ManuscriptStochasticMemory

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact
namespace IndexedKernelRun

/-- Compose two sampled transitions without discarding correlations. -/
theorem sequential_sample_law {X Y Z E F : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace E] [MeasurableSpace F]
    (η : Kernel X Y) (ζ : Kernel Y Z) (ρ : Measure E) (σ : Measure F)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (f : X → E → Y) (g : Y → F → Z)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hlf : ∀ x, ρ.map (f x) = η x) (hlg : ∀ y, σ.map (g y) = ζ y) (x : X) :
    (ρ.prod σ).map (fun z => g (f x z.1) z.2) = (ζ ∘ₖ η) x := by
  have hx : Measurable (f x) := hf.comp (measurable_const.prodMk measurable_id)
  change (ρ.prod σ).map (Function.uncurry g ∘ Prod.map (f x) id) = _
  rw [← Measure.map_map hg (hx.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hx measurable_id, Measure.map_id]
  rw [independent_step ζ σ g hg hlg, hlf, Kernel.comp_apply]

/-- Retaining the old state alongside a sampled update preserves the joint law. -/
theorem retained_sample_law {X Y E : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace E]
    (η : Kernel X Y) [IsSFiniteKernel η] (ρ : Measure E) (f : X → E → Y)
    (hf : Measurable (Function.uncurry f)) (hlaw : ∀ x, ρ.map (f x) = η x) (x : X) :
    ρ.map (fun u => (x, f x u)) = (Kernel.id ×ₖ η) x := by
  have hx : Measurable (f x) := hf.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (Prod.mk x : Y → X × Y) := measurable_const.prodMk measurable_id
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, ← hlaw x,
    Measure.map_map hm hx]
  rfl

variable {A : ℕ → Type} [∀ n, MeasurableSpace (A n)]

/-- A chronological tape whose first coordinate initializes private memory. -/
def InitialTape (E : Type) : ℕ → Type
  | 0 => ℝ
  | n + 1 => InitialTape E n × E

instance initialTapeMeasurableSpace {E : Type} [MeasurableSpace E] :
    (n : ℕ) → MeasurableSpace (InitialTape E n)
  | 0 => inferInstanceAs (MeasurableSpace ℝ)
  | n + 1 => by
    letI := initialTapeMeasurableSpace (E := E) n
    exact inferInstanceAs (MeasurableSpace (InitialTape E n × E))

def initialTapeLaw {E : Type} [MeasurableSpace E] (ρ : Measure E) :
    (n : ℕ) → Measure (InitialTape E n)
  | 0 => KernelRandomization.uniform
  | n + 1 => (initialTapeLaw ρ n).prod ρ

instance initialTapeLaw_probability {E : Type} [MeasurableSpace E]
    (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (initialTapeLaw ρ n) := by
  induction n with
  | zero => change IsProbabilityMeasure KernelRandomization.uniform; infer_instance
  | succ n ih => change IsProbabilityMeasure ((initialTapeLaw ρ n).prod ρ); infer_instance

def initializedRun {E : Type} (f : ∀ n, A n → E → A (n + 1))
    (initial : ℝ → A 0) : (n : ℕ) → InitialTape E n → A n
  | 0, u => initial u
  | n + 1, w => f n (initializedRun f initial n w.1) w.2

theorem initializedRun_measurable {E : Type} [MeasurableSpace E]
    (f : ∀ n, A n → E → A (n + 1)) (initial : ℝ → A 0)
    (hf : ∀ n, Measurable (Function.uncurry (f n))) (hi : Measurable initial) (n : ℕ) :
    Measurable (initializedRun f initial n) := by
  induction n with
  | zero => exact hi
  | succ n ih => exact (hf n).comp ((ih.comp measurable_fst).prodMk measurable_snd)

/-- Original kernel composition starting from a random initial law. -/
def initializedLaw (η : ∀ n, Kernel (A n) (A (n + 1)))
    (μ : Measure (A 0)) : (n : ℕ) → Measure (A n)
  | 0 => μ
  | n + 1 => η n ∘ₘ initializedLaw η μ n

theorem initializedRun_law {E : Type} [MeasurableSpace E]
    (η : ∀ n, Kernel (A n) (A (n + 1))) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (f : ∀ n, A n → E → A (n + 1)) (initial : ℝ → A 0) (μ : Measure (A 0))
    (hf : ∀ n, Measurable (Function.uncurry (f n))) (hi : Measurable initial)
    (hlaw : ∀ n a, ρ.map (f n a) = η n a)
    (hilaw : KernelRandomization.uniform.map initial = μ) (n : ℕ) :
    (initialTapeLaw ρ n).map (initializedRun f initial n) = initializedLaw η μ n := by
  induction n with
  | zero => exact hilaw
  | succ n ih =>
    have hr := initializedRun_measurable f initial hf hi n
    change ((initialTapeLaw ρ n).prod ρ).map
      (Function.uncurry (f n) ∘ Prod.map (initializedRun f initial n) id) =
        η n ∘ₘ initializedLaw η μ n
    rw [← Measure.map_map (hf n) (hr.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hr measurable_id, Measure.map_id,
      independent_step (η n) ρ (f n) (hf n) (hlaw n), ih]

end IndexedKernelRun

namespace Rectangular.StochasticMemory
open KernelPolicy
variable {dx dy K : ℕ}

/-- Full public stopped history together with correlated private memory. -/
abbrev JointState (M : Model dx dy K) (n : ℕ) := ExecutionState dx dy K n × M.State n

abbrev RoundContext (M : Model dx dy K) (Seed : Type) (n : ℕ) :=
  JointState M n × (Action dx dy K × Seed)

def contextInput (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (n : ℕ) (z : RoundContext M Seed n) := roundInput M O n z.1.2 z.2.1 z.2.2

theorem contextInput_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (contextInput M O n) :=
  measurable_fst.snd.prodMk (measurable_snd.fst.prodMk
    ((query_measurable.comp measurable_snd.fst).prodMk
      (answerCode_measurable O hO _ (query_measurable.comp measurable_snd.fst) _ measurable_snd.snd)))

def preKernel (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (ρ : Measure Seed) (n : ℕ) : Kernel (JointState M n) (RoundContext M Seed n) :=
  Kernel.id ×ₖ ((M.decision n).comap Prod.snd measurable_snd ×ₖ Kernel.const _ ρ)

def preSample (M : Model dx dy K) {Seed : Type} (n : ℕ)
    (s : JointState M n) (z : ℝ × Seed) : RoundContext M Seed n :=
  (s, decisionSample M n s.2 z.1, z.2)

theorem preSample_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (n : ℕ) : Measurable (Function.uncurry (@preSample dx dy K M Seed n)) :=
  measurable_fst.prodMk (((decisionSample_measurable M n).comp
    (measurable_fst.snd.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

theorem preSample_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (ρ : Measure Seed) [SFinite ρ] (n : ℕ) (s : JointState M n) :
    (KernelRandomization.uniform.prod ρ).map (preSample M n s) = preKernel M ρ n s := by
  have hd : Measurable (decisionSample M n s.2) := (decisionSample_measurable M n).comp
    (measurable_const.prodMk measurable_id)
  have hm : Measurable (Prod.mk s : Action dx dy K × Seed → RoundContext M Seed n) :=
    measurable_const.prodMk measurable_id
  rw [preKernel, Kernel.prod_apply, Kernel.id_apply, Kernel.prod_apply,
    Kernel.comap_apply, Kernel.const_apply, Measure.dirac_prod]
  change (KernelRandomization.uniform.prod ρ).map
    (Prod.mk s ∘ Prod.map (decisionSample M n s.2) id) = _
  rw [← Measure.map_map hm (hd.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hd measurable_id, Measure.map_id, decisionSample_law]

def finishState (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (n : ℕ) (z : RoundContext M Seed n × M.State (n + 1)) : JointState M (n + 1) :=
  (advanceState O n z.1.1.1 z.1.2.1 z.1.2.2, z.2)

theorem finishState_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (finishState M O n) :=
  ((advanceState_measurable O hO n).comp
    (measurable_fst.fst.fst.prodMk measurable_fst.snd)).prodMk measurable_snd

/-- Public history is absorbing after stopping. Later private updates are merely
padding; they do not issue a recorded query or change the public output. -/
def finishKernel (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Kernel (RoundContext M Seed n) (JointState M (n + 1)) :=
  (Kernel.id ×ₖ (M.update n).comap (contextInput M O n)
    (contextInput_measurable M O hO n)).map (finishState M O n)

def finishSample (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (n : ℕ) (z : RoundContext M Seed n) (v : ℝ) : JointState M (n + 1) :=
  finishState M O n (z, updateSample M n (contextInput M O n z) v)

theorem finishSample_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (Function.uncurry (finishSample M O n)) :=
  (finishState_measurable M O hO n).comp (measurable_fst.prodMk
    ((updateSample_measurable M n).comp
      (((contextInput_measurable M O hO n).comp measurable_fst).prodMk measurable_snd)))

theorem finishSample_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) (z : RoundContext M Seed n) :
    KernelRandomization.uniform.map (finishSample M O n z) = finishKernel M O hO n z := by
  have hf : Measurable (Function.uncurry (fun c u =>
      updateSample M n (contextInput M O n c) u)) :=
    (updateSample_measurable M n).comp
      (((contextInput_measurable M O hO n).comp measurable_fst).prodMk measurable_snd)
  have hl : ∀ c, KernelRandomization.uniform.map
      (fun u => updateSample M n (contextInput M O n c) u) =
      ((M.update n).comap (contextInput M O n) (contextInput_measurable M O hO n)) c :=
    fun c => updateSample_law M n (contextInput M O n c)
  have hm : Measurable (fun u : ℝ => (z, updateSample M n (contextInput M O n z) u)) :=
    measurable_const.prodMk
      (hf.comp (measurable_const.prodMk measurable_id : Measurable (fun u : ℝ => (z, u))))
  rw [finishKernel, Kernel.map_apply _ (finishState_measurable M O hO n),
    ← IndexedKernelRun.retained_sample_law _ _ _ hf hl z,
    Measure.map_map (finishState_measurable M O hO n) hm]
  rfl

def jointKernel (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (ρ : Measure Seed) (n : ℕ) :=
  finishKernel M O hO n ∘ₖ preKernel M ρ n

def jointSample (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (n : ℕ) (s : JointState M n) (z : (ℝ × Seed) × ℝ) : JointState M (n + 1) :=
  finishSample M O n (preSample M n s z.1) z.2

theorem jointSample_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (Function.uncurry (jointSample M O n)) :=
  (finishSample_measurable M O hO n).comp
    (((preSample_measurable M n).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

theorem jointSample_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ) (s : JointState M n) :
    ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform).map
      (jointSample M O n s) = jointKernel M O hO ρ n s :=
  IndexedKernelRun.sequential_sample_law _ _ _ _ _ _ (preSample_measurable M n)
    (finishSample_measurable M O hO n) (preSample_law M ρ n) (finishSample_law M O hO n) s

instance jointKernel_markov (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsMarkovKernel (jointKernel M O hO ρ n) where
  isProbabilityMeasure s := by
    rw [← jointSample_law M O hO ρ n s]
    exact isProbabilityMeasure_map
      (((jointSample_measurable M O hO n).comp
        (measurable_const.prodMk measurable_id)).aemeasurable)

def jointInitial (M : Model dx dy K) (m : M.State 0) : JointState M 0 :=
  (initialExecutionState, m)

theorem jointInitial_measurable (M : Model dx dy K) : Measurable (jointInitial M) :=
  measurable_const.prodMk measurable_id

theorem jointInitial_law (M : Model dx dy K) :
    KernelRandomization.uniform.map (jointInitial M ∘ initialSample M) =
      M.initial.map (jointInitial M) := by
  rw [← Measure.map_map (jointInitial_measurable M) (initialSample_measurable M), initialSample_law]

/-- Joint law of the entire padded history, output, stopping flag and current
private memory, with random initialization. No target execution law is assumed. -/
theorem joint_execution_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ) :
    (IndexedKernelRun.initialTapeLaw
      ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform) N).map
        (IndexedKernelRun.initializedRun (jointSample M O) (jointInitial M ∘ initialSample M) N) =
    IndexedKernelRun.initializedLaw (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) N :=
  IndexedKernelRun.initializedRun_law _ _ _ _ _ (jointSample_measurable M O hO)
    ((jointInitial_measurable M).comp (initialSample_measurable M))
    (jointSample_law M O hO ρ) (jointInitial_law M) N

theorem joint_execution_event (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ)
    (B : Set (JointState M N)) (hB : MeasurableSet B) :
    IndexedKernelRun.initialTapeLaw
      ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform) N
        ((IndexedKernelRun.initializedRun (jointSample M O)
          (jointInitial M ∘ initialSample M) N) ⁻¹' B) =
    IndexedKernelRun.initializedLaw (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) N B := by
  have h := congrArg (fun μ : Measure (JointState M N) => μ B) (joint_execution_law M O hO ρ N)
  dsimp only at h
  rw [Measure.map_apply (IndexedKernelRun.initializedRun_measurable _ _
    (jointSample_measurable M O hO)
    ((jointInitial_measurable M).comp (initialSample_measurable M)) N) hB] at h
  exact h

theorem joint_execution_risk (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ)
    (loss : JointState M N → ENNReal) (hloss : Measurable loss) :
    (∫⁻ w, loss (IndexedKernelRun.initializedRun (jointSample M O)
      (jointInitial M ∘ initialSample M) N w)
      ∂IndexedKernelRun.initialTapeLaw
        ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform) N) =
    ∫⁻ s, loss s ∂IndexedKernelRun.initializedLaw
      (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) N := by
  rw [← lintegral_map hloss (IndexedKernelRun.initializedRun_measurable _ _
    (jointSample_measurable M O hO)
    ((jointInitial_measurable M).comp (initialSample_measurable M)) N), joint_execution_law]

theorem jointSample_stop (M : Model dx dy K) {Seed : Type}
    (O : Oracle dx dy Seed) (n : ℕ) (s : JointState M n)
    (z : (ℝ × Seed) × ℝ) (hs : s.1.1 ≠ true)
    (ha : (decisionSample M n s.2 z.1.1).val.1 = true) :
    (jointSample M O n s z).1 =
      (true, (decisionSample M n s.2 z.1.1).val.2.1,
        Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.1.2.2) := by
  simp [jointSample, finishSample, finishState, preSample, advanceState, hs, ha]

theorem jointSample_stopped (M : Model dx dy K) {Seed : Type}
    (O : Oracle dx dy Seed) (n : ℕ) (s : JointState M n)
    (z : (ℝ × Seed) × ℝ) (hs : s.1.1 = true) :
    (jointSample M O n s z).1 =
      (true, s.1.2.1, Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.1.2.2) :=
  advanceState_stopped O n s.1 _ _ hs

/-- The active memory transition is exactly the native compiler's update on the
recorded same-seed response, rather than an independently resampled memory. -/
theorem jointSample_continue (M : Model dx dy K) {Seed : Type}
    (O : Oracle dx dy Seed) (n : ℕ) (s : JointState M n) (u : RandomTape) (ξ : Seed)
    (hs : s.1.1 ≠ true) (ha : (actionAt M n (u, s.2)).val.1 ≠ true) :
    let q := decode (actionAt M n (u, s.2)).val.2.2
    jointSample M O n s ((u.2.1 n, ξ), u.2.2 n) =
      ((false, 0, Fin.lastCases (encode q, encode (answer O q ξ)) s.1.2.2),
        ((toMemory M).advance n ((u, s.2), encode q, encode (answer O q ξ))).2) := by
  dsimp only
  have ha' : (decisionSample M n s.2 (u.2.1 n)).val.1 ≠ true := ha
  simp [jointSample, finishSample, finishState, preSample, contextInput, roundInput,
    advanceState, hs, ha', query, answerCode_encode, actionAt, toMemory]

end Rectangular.StochasticMemory
end NCSCPureStochasticLB.PaperExact
