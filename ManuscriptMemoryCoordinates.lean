import ManuscriptMemoryExecution

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact
namespace IndexedKernelRun

theorem prod_unassoc_law {A B C : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite ν] [SFinite ρ] :
    (μ.prod (ν.prod ρ)).map (fun z => ((z.1, z.2.1), z.2.2)) = (μ.prod ν).prod ρ :=
  (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ν ρ)).map_eq

theorem prod_middle_swap_law {A B C : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    ((μ.prod ν).prod ρ).map (fun z => ((z.1.1, z.2), z.1.2)) = (μ.prod ρ).prod ν := by
  have h₁ := (measurePreserving_prodAssoc μ ν ρ).map_eq
  have h₂ := Measure.map_prod_map μ (ν.prod ρ)
    (measurable_id : Measurable (id : A → A)) measurable_swap
  rw [Measure.map_id, Measure.prod_swap] at h₂
  have h₃ := prod_unassoc_law μ ρ ν
  rw [h₂, ← h₁, Measure.map_map (measurable_id.prodMap measurable_swap)
    MeasurableEquiv.prodAssoc.measurable] at h₃
  have hm : Measurable (fun z : A × (C × B) => ((z.1, z.2.1), z.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  rw [Measure.map_map hm
    ((measurable_id.prodMap measurable_swap).comp MeasurableEquiv.prodAssoc.measurable)] at h₃
  exact h₃

variable {E : Type} [MeasurableSpace E]

/-- Attach a single initialization coordinate to a chronological transition tape. -/
def attachInitial : (n : ℕ) → ℝ × Tape E n → InitialTape E n
  | 0, z => z.1
  | n + 1, z => (attachInitial n (z.1, z.2.1), z.2.2)

theorem attachInitial_measurable (n : ℕ) : Measurable (@attachInitial E n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd

theorem attachInitial_law (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    (KernelRandomization.uniform.prod (tapeLaw ρ n)).map (attachInitial n) = initialTapeLaw ρ n := by
  induction n with
  | zero =>
    change (KernelRandomization.uniform.prod (tapeLaw ρ 0)).map Prod.fst = KernelRandomization.uniform
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  | succ n ih =>
    have hm : Measurable (fun z : ℝ × (Tape E n × E) => ((z.1, z.2.1), z.2.2)) :=
      (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
    change (KernelRandomization.uniform.prod ((tapeLaw ρ n).prod ρ)).map
      (Prod.map (attachInitial n) id ∘ (fun z => ((z.1, z.2.1), z.2.2))) = _
    rw [← Measure.map_map ((attachInitial_measurable n).prodMap measurable_id) hm,
      prod_unassoc_law, ← Measure.map_prod_map _ _ (attachInitial_measurable n) measurable_id,
      Measure.map_id, ih]
    rfl

def initialPack (n : ℕ) (z : ℝ × (Fin n → E)) : InitialTape E n :=
  attachInitial n (z.1, pack n z.2)

theorem initialPack_measurable (n : ℕ) : Measurable (@initialPack E n) :=
  (attachInitial_measurable n).comp (measurable_id.prodMap (pack_measurable n))

theorem initialPack_law (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    (KernelRandomization.uniform.prod (Measure.pi (fun _ : Fin n => ρ))).map
      (initialPack n) = initialTapeLaw ρ n := by
  change (KernelRandomization.uniform.prod (Measure.pi (fun _ : Fin n => ρ))).map
    (attachInitial n ∘ Prod.map id (pack n)) = _
  rw [← Measure.map_map (attachInitial_measurable n) (measurable_id.prodMap (pack_measurable n)),
    ← Measure.map_prod_map _ _ measurable_id (pack_measurable n), Measure.map_id,
    pack_law, attachInitial_law]

end IndexedKernelRun

namespace Rectangular.StochasticMemory
open KernelPolicy
variable {dx dy K : ℕ}

theorem internal_oracle_vector_law {Seed : Type} [MeasurableSpace Seed]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ) :
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin N => ρ))).map
      (fun z => fun i : Fin N => (z.1 i.val, z.2 i)) =
      Measure.pi (fun _ : Fin N => KernelRandomization.uniform.prod ρ) := by
  have hi : Measurable (fun u : ℕ → ℝ => fun i : Fin N => u i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hp : Measurable (fun z : (Fin N → ℝ) × (Fin N → Seed) => fun i => (z.1 i, z.2 i)) :=
    measurable_pi_lambda _ (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have h := IndexedKernelRun.paired_vector_law KernelRandomization.uniform ρ N
  rw [← internalTapeLaw_prefix N, Measure.map_id (μ := Measure.pi (fun _ : Fin N => ρ)) |>.symm,
    Measure.map_prod_map _ _ hi measurable_id, Measure.map_map hp (hi.prodMap measurable_id)] at h
  exact h

def roundVector {Seed : Type} (N : ℕ)
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (Fin N → Seed)) : Fin N → (ℝ × Seed) × ℝ :=
  fun i => ((z.1.1 i.val, z.2 i), z.1.2 i.val)

theorem roundVector_measurable {Seed : Type} [MeasurableSpace Seed] (N : ℕ) :
    Measurable (@roundVector Seed N) :=
  measurable_pi_lambda _ (fun i =>
    (((measurable_pi_apply i.val).comp measurable_fst.fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)).prodMk
        ((measurable_pi_apply i.val).comp measurable_fst.snd))

theorem roundVector_law {Seed : Type} [MeasurableSpace Seed]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ) :
    ((internalTapeLaw.prod internalTapeLaw).prod (Measure.pi (fun _ : Fin N => ρ))).map
      (roundVector N) = Measure.pi (fun _ : Fin N =>
        (KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform) := by
  let f : (ℕ → ℝ) × (Fin N → Seed) → Fin N → ℝ × Seed := fun z i => (z.1 i.val, z.2 i)
  let g : (ℕ → ℝ) → Fin N → ℝ := fun u i => u i.val
  have hf : Measurable f := measurable_pi_lambda _ (fun i =>
    ((measurable_pi_apply i.val).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have hg : Measurable g := measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hp : Measurable (fun z : (Fin N → ℝ × Seed) × (Fin N → ℝ) => fun i => (z.1 i, z.2 i)) :=
    measurable_pi_lambda _ (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have hm : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (Fin N → Seed) =>
      ((z.1.1, z.2), z.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have h := IndexedKernelRun.paired_vector_law (KernelRandomization.uniform.prod ρ)
    KernelRandomization.uniform N
  rw [← internal_oracle_vector_law ρ N, ← internalTapeLaw_prefix N,
    Measure.map_prod_map _ _ hf hg,
    ← IndexedKernelRun.prod_middle_swap_law internalTapeLaw internalTapeLaw
      (Measure.pi (fun _ : Fin N => ρ)),
    Measure.map_map (hf.prodMap hg) hm, Measure.map_map hp ((hf.prodMap hg).comp hm)] at h
  exact h

def separatedPack {Seed : Type} (N : ℕ) (z : RandomTape × (Fin N → Seed)) :
    IndexedKernelRun.InitialTape ((ℝ × Seed) × ℝ) N :=
  IndexedKernelRun.initialPack N (z.1.1, roundVector N (z.1.2, z.2))

theorem separatedPack_measurable {Seed : Type} [MeasurableSpace Seed] (N : ℕ) :
    Measurable (@separatedPack Seed N) :=
  (IndexedKernelRun.initialPack_measurable N).comp
    (measurable_fst.fst.prodMk ((roundVector_measurable N).comp
      (measurable_fst.snd.prodMk measurable_snd)))

theorem separatedPack_law {Seed : Type} [MeasurableSpace Seed]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin N => ρ))).map (separatedPack N) =
      IndexedKernelRun.initialTapeLaw
        ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform) N := by
  have h := IndexedKernelRun.initialPack_law
    ((KernelRandomization.uniform.prod ρ).prod KernelRandomization.uniform) N
  have hp : Measurable (Prod.map (id : ℝ → ℝ) (@roundVector Seed N)) :=
    measurable_id.prodMap (roundVector_measurable N)
  rw [← roundVector_law ρ N, ← Measure.map_id (μ := KernelRandomization.uniform),
    Measure.map_prod_map _ _ measurable_id (roundVector_measurable N),
    ← (measurePreserving_prodAssoc KernelRandomization.uniform
      (internalTapeLaw.prod internalTapeLaw) (Measure.pi (fun _ : Fin N => ρ))).map_eq,
    Measure.map_map hp MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (IndexedKernelRun.initialPack_measurable N)
      (hp.comp MeasurableEquiv.prodAssoc.measurable)] at h
  simpa only [Measure.map_id] using h

def separatedRun (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (N : ℕ) (z : RandomTape × (Fin N → Seed)) : JointState M N :=
  IndexedKernelRun.initializedRun (jointSample M O) (jointInitial M ∘ initialSample M) N
    (separatedPack N z)

theorem separatedRun_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (N : ℕ) : Measurable (separatedRun M O N) :=
  (IndexedKernelRun.initializedRun_measurable _ _ (jointSample_measurable M O hO)
    ((jointInitial_measurable M).comp (initialSample_measurable M)) N).comp
      (separatedPack_measurable N)

theorem separated_joint_execution_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin N => ρ))).map (separatedRun M O N) =
      IndexedKernelRun.initializedLaw (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) N := by
  have h := joint_execution_law M O hO ρ N
  rw [← separatedPack_law ρ N, Measure.map_map
    (IndexedKernelRun.initializedRun_measurable _ _ (jointSample_measurable M O hO)
      ((jointInitial_measurable M).comp (initialSample_measurable M)) N)
    (separatedPack_measurable N)] at h
  exact h

theorem separated_joint_execution_event (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ)
    (B : Set (JointState M N)) (hB : MeasurableSet B) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin N => ρ))) ((separatedRun M O N) ⁻¹' B) =
      IndexedKernelRun.initializedLaw (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) N B := by
  have h := congrArg (fun μ : Measure (JointState M N) => μ B)
    (separated_joint_execution_law M O hO ρ N)
  dsimp only at h
  rw [Measure.map_apply (separatedRun_measurable M O hO N) hB] at h
  exact h

theorem separated_joint_execution_risk (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (N : ℕ)
    (loss : JointState M N → ENNReal) (hloss : Measurable loss) :
    (∫⁻ z, loss (separatedRun M O N z) ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin N => ρ)))) =
      ∫⁻ s, loss s ∂IndexedKernelRun.initializedLaw
        (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) N := by
  rw [← lintegral_map hloss (separatedRun_measurable M O hO N), separated_joint_execution_law]

/-- Project the H+1-round forward process to the complete success/partial-trace
encoding. Identifying this with the native run is a separate pointwise theorem. -/
theorem projected_joint_execution_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin (H + 1) => ρ))).map
      (fun z => forwardCompleteCode H (separatedRun M O (H + 1) z).1) =
    (IndexedKernelRun.initializedLaw (jointKernel M O hO ρ)
      (M.initial.map (jointInitial M)) (H + 1)).map (fun s => forwardCompleteCode H s.1) := by
  have hm : Measurable (fun s : JointState M (H + 1) => forwardCompleteCode H s.1) :=
    (forwardCompleteCode_measurable H).comp measurable_fst
  have h := congrArg (Measure.map (fun s : JointState M (H + 1) => forwardCompleteCode H s.1))
    (separated_joint_execution_law M O hO ρ (H + 1))
  rw [Measure.map_map hm (separatedRun_measurable M O hO (H + 1))] at h
  exact h

def nativeCompleteCode (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (H : ℕ) (z : RandomTape × (Fin H → Seed)) : Bool × TraceCode dx dy H K :=
  let r := (toMemory M).run? O H 0 ((toMemory M).initial z.1) z.2
  (r.isSome, partialCode r)

theorem nativeCompleteCode_measurable (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (H : ℕ) :
    Measurable (nativeCompleteCode M O H) := by
  have hi : Measurable (fun z : RandomTape × (Fin H → Seed) =>
      ((z.1, (Fin.elim0 : Transcript dx dy K 0)), z.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hs := ((toMemory M).toPolicy.runSummary_measurable O hO H 0).comp hi
  have ht := ((toMemory M).toPolicy.runCode_measurable O hO H 0).comp hi
  simpa only [nativeCompleteCode, Function.comp_def, Policy.summary_defined,
    Policy.runCode_eq_run, MemoryAlgorithm.toPolicy_initial_run] using hs.fst.prodMk ht

/-- The extra forward oracle coordinate is unused by the native H-call run.
This equality includes failure on horizon exhaustion, not just successful output. -/
theorem native_dummy_seed_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin (H + 1) => ρ))).map
      (fun z => nativeCompleteCode M O H (z.1, fun i => z.2 i.castSucc)) =
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))).map (nativeCompleteCode M O H) := by
  have hd : Measurable (fun w : Fin (H + 1) → Seed => fun i : Fin H => w i.castSucc) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)
  have hm := Measure.map_prod_map randomTapeLaw (Measure.pi (fun _ : Fin (H + 1) => ρ))
    (measurable_id : Measurable (id : RandomTape → RandomTape)) hd
  rw [Measure.map_id, IndexedKernelRun.drop_last_law] at hm
  rw [hm, Measure.map_map (nativeCompleteCode_measurable M O hO H) (measurable_id.prodMap hd)]
  rfl

end Rectangular.StochasticMemory
end NCSCPureStochasticLB.PaperExact
