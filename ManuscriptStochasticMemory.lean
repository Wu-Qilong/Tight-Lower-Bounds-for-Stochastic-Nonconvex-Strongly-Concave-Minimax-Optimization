import ManuscriptNativeTraceBridge
import ManuscriptAlgorithmRepresentation

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact.Rectangular
namespace StochasticMemory
open KernelPolicy

/-- Private standard-Borel memory, randomized decisions and observation-dependent
updates. Neither kernel has access to the oracle instance or its hidden seed. -/
structure Model (dx dy K : ℕ) where
  State : ℕ → Type
  stateSpace : ∀ n, MeasurableSpace (State n)
  standardBorel : ∀ n, @StandardBorelSpace (State n) (stateSpace n)
  nonempty : ∀ n, Nonempty (State n)
  initial : @Measure (State 0) (stateSpace 0)
  initial_probability : @IsProbabilityMeasure (State 0) (stateSpace 0) initial
  decision : ∀ n, @Kernel (State n) (Action dx dy K) (stateSpace n) _
  decision_markov : ∀ n, IsMarkovKernel (decision n)
  update : ∀ n, @Kernel (State n × (Action dx dy K × (Code dx dy K × Code dx dy K)))
    (State (n + 1)) (@MeasurableSpace.prod _ _ (stateSpace n) inferInstance) (stateSpace (n + 1))
  update_markov : ∀ n, IsMarkovKernel (update n)

attribute [instance] Model.stateSpace Model.standardBorel Model.nonempty
  Model.initial_probability Model.decision_markov Model.update_markov

variable {dx dy K : ℕ}

def initialSample (M : Model dx dy K) : ℝ → M.State 0 :=
  (KernelRandomization.standardBorel_kernel_randomization
    (Kernel.const Unit M.initial)).choose ()

theorem initialSample_measurable (M : Model dx dy K) : Measurable (initialSample M) :=
  (KernelRandomization.standardBorel_kernel_randomization
    (Kernel.const Unit M.initial)).choose_spec.1.comp
      (measurable_const.prodMk measurable_id)

theorem initialSample_law (M : Model dx dy K) :
    KernelRandomization.uniform.map (initialSample M) = M.initial :=
  (KernelRandomization.standardBorel_kernel_randomization
    (Kernel.const Unit M.initial)).choose_spec.2 ()

def decisionSample (M : Model dx dy K) (n : ℕ) : M.State n → ℝ → Action dx dy K :=
  (KernelRandomization.standardBorel_kernel_randomization (M.decision n)).choose

theorem decisionSample_measurable (M : Model dx dy K) (n : ℕ) :
    Measurable (Function.uncurry (decisionSample M n)) :=
  (KernelRandomization.standardBorel_kernel_randomization (M.decision n)).choose_spec.1

theorem decisionSample_law (M : Model dx dy K) (n : ℕ) (s : M.State n) :
    KernelRandomization.uniform.map (decisionSample M n s) = M.decision n s :=
  (KernelRandomization.standardBorel_kernel_randomization (M.decision n)).choose_spec.2 s

def updateSample (M : Model dx dy K) (n : ℕ) :
    (M.State n × (Action dx dy K × (Code dx dy K × Code dx dy K))) → ℝ → M.State (n + 1) :=
  (KernelRandomization.standardBorel_kernel_randomization (M.update n)).choose

theorem updateSample_measurable (M : Model dx dy K) (n : ℕ) :
    Measurable (Function.uncurry (updateSample M n)) :=
  (KernelRandomization.standardBorel_kernel_randomization (M.update n)).choose_spec.1

theorem updateSample_law (M : Model dx dy K) (n : ℕ)
    (s : M.State n × (Action dx dy K × (Code dx dy K × Code dx dy K))) :
    KernelRandomization.uniform.map (updateSample M n s) = M.update n s :=
  (KernelRandomization.standardBorel_kernel_randomization (M.update n)).choose_spec.2 s

/-- Independent initialization, decision and update coordinates. -/
abbrev RandomTape := ℝ × ((ℕ → ℝ) × (ℕ → ℝ))

def randomTapeLaw : Measure RandomTape := KernelRandomization.uniform.prod
  (internalTapeLaw.prod internalTapeLaw)

instance randomTapeLaw_probability : IsProbabilityMeasure randomTapeLaw := by
  unfold randomTapeLaw
  infer_instance

def actionAt (M : Model dx dy K) (n : ℕ) (s : RandomTape × M.State n) : Action dx dy K :=
  decisionSample M n s.2 (s.1.2.1 n)

theorem actionAt_measurable (M : Model dx dy K) (n : ℕ) : Measurable (actionAt M n) :=
  (decisionSample_measurable M n).comp
    (measurable_snd.prodMk ((measurable_pi_apply n).comp measurable_fst.snd.fst))

/-- The compiled memory machine retains private memory. It does not replace it
by a conditional distribution given the public transcript. -/
def toMemory (M : Model dx dy K) : MemoryAlgorithm RandomTape dx dy K where
  State n := RandomTape × M.State n
  stateSpace _ := inferInstance
  initial u := (u, initialSample M u.1)
  initial_measurable := measurable_id.prodMk ((initialSample_measurable M).comp measurable_fst)
  domain _ := Set.univ
  domain_measurable _ := MeasurableSet.univ
  stop n s := (actionAt M n s.val).val.1
  stop_measurable n :=
    (measurable_subtype_coe.comp ((actionAt_measurable M n).comp measurable_subtype_coe)).fst
  output n s := (actionAt M n s.val.val).val.2.1
  output_measurable n :=
    (measurable_subtype_coe.comp ((actionAt_measurable M n).comp
      (measurable_subtype_coe.comp measurable_subtype_coe))).snd.fst
  batch n s := continueBatch (actionAt M n s.val.val) s.property
  batch_measurable n := normalizedCode_measurable.comp
    (measurable_subtype_coe.comp ((actionAt_measurable M n).comp
      (measurable_subtype_coe.comp measurable_subtype_coe))).snd.snd
  advance n z := (z.1.1, updateSample M n (z.1.2, actionAt M n z.1, z.2) (z.1.1.2.2 n))
  advance_measurable n := measurable_fst.fst.prodMk
    ((updateSample_measurable M n).comp
      ((measurable_fst.snd.prodMk
        (((actionAt_measurable M n).comp measurable_fst).prodMk measurable_snd)).prodMk
          ((measurable_pi_apply n).comp measurable_fst.fst.snd.snd)))

theorem toMemory_initial (M : Model dx dy K) (u : RandomTape) :
    (toMemory M).initial u = (u, initialSample M u.1) := rfl

theorem toMemory_advance (M : Model dx dy K) (n : ℕ)
    (s : RandomTape × M.State n) (r : Code dx dy K × Code dx dy K) :
    (toMemory M).advance n (s, r) =
      (s.1, updateSample M n (s.2, actionAt M n s, r) (s.1.2.2 n)) := rfl

/-- Pointwise transfer to the established native history-policy execution. -/
theorem toPolicy_run (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (H : ℕ) (u : RandomTape) (w : Fin H → Seed) :
    (toMemory M).toPolicy.run? O H 0 (u, Fin.elim0) w =
      (toMemory M).run? O H 0 ((toMemory M).initial u) w :=
  (toMemory M).toPolicy_initial_run O H u w

/-- Update randomization is valid under every adaptive input law; inputs may
include private memory, the chosen action, and the observed response. -/
theorem update_independent_law (M : Model dx dy K) (n : ℕ)
    (μ : Measure (M.State n × (Action dx dy K × (Code dx dy K × Code dx dy K))))
    [SFinite μ] :
    (μ.prod KernelRandomization.uniform).map (Function.uncurry (updateSample M n)) =
      M.update n ∘ₘ μ :=
  KernelRandomization.independent_seed_step (M.update n) (updateSample M n)
    (updateSample_measurable M n) (updateSample_law M n) μ

theorem decision_independent_law (M : Model dx dy K) (n : ℕ)
    (μ : Measure (M.State n)) [SFinite μ] :
    (μ.prod KernelRandomization.uniform).map (Function.uncurry (decisionSample M n)) =
      M.decision n ∘ₘ μ :=
  KernelRandomization.independent_seed_step (M.decision n) (decisionSample M n)
    (decisionSample_measurable M n) (decisionSample_law M n) μ

/-- Input to a private update: the old memory, actual action, and query/response
pair. All slots of the response use the same oracle seed. -/
def roundInput (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (n : ℕ) (s : M.State n) (a : Action dx dy K) (ξ : Seed) :=
  (s, a, query a, answerCode O (query a) ξ)

theorem roundInput_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) (s : M.State n) :
    Measurable (fun z : Action dx dy K × Seed => roundInput M O n s z.1 z.2) :=
  measurable_const.prodMk (measurable_fst.prodMk
    ((query_measurable.comp measurable_fst).prodMk
      (answerCode_measurable O hO _ (query_measurable.comp measurable_fst) _ measurable_snd)))

/-- The original one-round update law, defined with kernels, not with samplers.
For a stopping action this is an auxiliary padded update, not an oracle call. -/
def roundLaw (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (ρ : Measure Seed) (n : ℕ) (s : M.State n) :
    Measure (M.State (n + 1)) :=
  M.update n ∘ₘ ((M.decision n s).prod ρ).map
    (fun z => roundInput M O n s z.1 z.2)

def roundSample (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (n : ℕ) (s : M.State n) (z : (ℝ × Seed) × ℝ) : M.State (n + 1) :=
  updateSample M n (roundInput M O n s (decisionSample M n s z.1.1) z.1.2) z.2

theorem roundSample_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ) (s : M.State n) :
    ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform).map
      (roundSample M O n s) = roundLaw M O ρ n s := by
  let f : ℝ × Seed → M.State n × (Action dx dy K × (Code dx dy K × Code dx dy K)) :=
    fun z => roundInput M O n s (decisionSample M n s z.1) z.2
  have hd : Measurable (decisionSample M n s) := (decisionSample_measurable M n).comp
    (measurable_const.prodMk measurable_id)
  have hi := roundInput_measurable M O hO n s
  have hf : Measurable f := hi.comp (hd.prodMap measurable_id)
  have hflaw : (KernelRandomization.uniform.prod ρ).map f =
      ((M.decision n s).prod ρ).map (fun z => roundInput M O n s z.1 z.2) := by
    change (KernelRandomization.uniform.prod ρ).map
      ((fun z : Action dx dy K × Seed => roundInput M O n s z.1 z.2) ∘
        Prod.map (decisionSample M n s) id) = _
    rw [← Measure.map_map hi (hd.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hd measurable_id, Measure.map_id, decisionSample_law]
  change ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform).map
    (Function.uncurry (updateSample M n) ∘ Prod.map f id) = _
  rw [← Measure.map_map (updateSample_measurable M n) (hf.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id,
    update_independent_law, hflaw]
  rfl

end StochasticMemory
end NCSCPureStochasticLB.PaperExact.Rectangular
