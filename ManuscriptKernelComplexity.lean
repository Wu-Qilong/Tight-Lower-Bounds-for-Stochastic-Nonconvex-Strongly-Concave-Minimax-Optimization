import ManuscriptGuardPreservation
import ManuscriptGeneralMoreau

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact
namespace KernelModel
open Rectangular Rectangular.StochasticMemory

/-- Dimension-indexed stochastic-kernel algorithms. All private states are
standard Borel; no oracle instance or hidden oracle seed is an input to the family. -/
structure Family (K : ℕ) where
  model : ∀ dx dy, StochasticMemory.Model dx dy K

/-- The public finite-transcript spaces used in Section 3.2 are standard Borel. -/
instance transcript_standardBorel (dx dy K n : ℕ) :
    StandardBorelSpace (KernelPolicy.Transcript dx dy K n) := by
  unfold KernelPolicy.Transcript
  infer_instance

/-- History-dependent decision kernels are included in the private-memory model.
The deterministic update retains exactly the returned query/response transcript. -/
def historyModel {dx dy K : ℕ} (P : KernelPolicy.RandomizedPolicy dx dy K) :
    StochasticMemory.Model dx dy K where
  State n := KernelPolicy.Transcript dx dy K n
  stateSpace _ := inferInstance
  standardBorel _ := inferInstance
  nonempty _ := inferInstance
  initial := Measure.dirac Fin.elim0
  initial_probability := inferInstance
  decision := P.decision
  decision_markov := P.markov
  update n := Kernel.deterministic (fun s => Fin.lastCases s.2.2 s.1) (by
    apply measurable_pi_lambda
    intro t
    refine Fin.lastCases ?_ (fun i => ?_) t
    · simpa only [Fin.lastCases_last] using
        (measurable_snd.snd : Measurable (fun s : KernelPolicy.Transcript dx dy K n ×
          (KernelPolicy.Action dx dy K × (Code dx dy K × Code dx dy K)) => s.2.2))
    · simpa only [Fin.lastCases_castSucc] using
        ((measurable_pi_apply i).comp measurable_fst : Measurable (fun s :
          KernelPolicy.Transcript dx dy K n ×
          (KernelPolicy.Action dx dy K × (Code dx dy K × Code dx dy K)) => s.1 i)))
  update_markov _ := inferInstance

def Family.compile {K : ℕ} (A : Family K) : Rectangular.Family K where
  Seed _ _ := RandomTape
  seedSpace _ _ := inferInstance
  law _ _ := randomTapeLaw
  probability _ _ := inferInstance
  policy dx dy := (toMemory (A.model dx dy)).toPolicy

/-- The trace law is defined from kernel execution, not from the compiled tape. -/
def executionLaw {K : ℕ} (A : Family K) (N : ℕ) (I : MeasuredOracle.Instance)
    (hO : JointlyMeasurable I.oracle) : Measure (Bool × TraceCode I.dx I.dy N K) :=
  (IndexedKernelRun.initializedLaw (jointKernel (A.model I.dx I.dy) I.oracle hO I.law)
    ((A.model I.dx I.dy).initial.map (jointInitial (A.model I.dx I.dy))) (N + 1)).map
      (fun s => KernelPolicy.forwardCompleteCode N s.1)

theorem compile_completeCode {K : ℕ} (A : Family K) (N : ℕ) (I : MeasuredOracle.Instance) :
    CausalGuard.completeCode (A.compile.policy I.dx I.dy) I.oracle N =
      nativeCompleteCode (A.model I.dx I.dy) I.oracle N := by
  funext z
  simp only [CausalGuard.completeCode, Family.compile, nativeCompleteCode,
    MemoryAlgorithm.toPolicy_initial_run]

theorem compile_law {K : ℕ} (A : Family K) (N : ℕ) (I : MeasuredOracle.Instance)
    (hO : JointlyMeasurable I.oracle) :
    ((A.compile.law I.dx I.dy).prod (iidRoundMeasure I.law N)).map
      (CausalGuard.completeCode (A.compile.policy I.dx I.dy) I.oracle N) = executionLaw A N I hO := by
  rw [compile_completeCode]
  exact native_memory_kernel_law (A.model I.dx I.dy) I.oracle hO I.law N

/-- Almost-sure termination, zero-respecting support and a finite call budget
are imposed on the original kernel execution law. -/
def Legal {K : ℕ} (A : Family K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I → ∃ hO : JointlyMeasurable I.oracle,
    ∀ᵐ c ∂executionLaw A N I hO, LegalCode N c

theorem legal_iff_compile {K : ℕ} (A : Family K) (valid : MeasuredOracle.Instance → Prop)
    (hvalid : ∀ I, valid I → JointlyMeasurable I.oracle) (N : ℕ) :
    Legal A valid N ↔ CausalGuard.AEFamilyLegal A.compile valid N := by
  constructor
  · intro h I hI
    obtain ⟨hO, hh⟩ := h I hI
    rw [← compile_law A N I hO, compile_completeCode] at hh
    have hm := nativeCompleteCode_measurable (A.model I.dx I.dy) I.oracle hO N
    have he := (ae_map_iff hm.aemeasurable (legalCode_measurable N)).mp hh
    filter_upwards [he] with z hz
    exact (native_legalCode_iff_policy _ _ _ _ _).mp hz
  · intro h I hI
    refine ⟨hvalid I hI, ?_⟩
    rw [← compile_law A N I (hvalid I hI), compile_completeCode]
    apply (ae_map_iff (nativeCompleteCode_measurable _ _ (hvalid I hI) N).aemeasurable
      (legalCode_measurable N)).mpr
    filter_upwards [h I hI] with z hz
    exact (native_legalCode_iff_policy _ _ _ _ _).mpr hz

def codeLoss {dx dy N K : ℕ} (c : StationarityCriterion) (g : Vec dx → Vec dx)
    (s : Bool × TraceCode dx dy N K) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g s.2.2.2‖
  | .squared => ENNReal.ofReal (‖g s.2.2.2‖ ^ 2)

theorem codeLoss_measurable {dx dy N K : ℕ} (c : StationarityCriterion)
    (g : Vec dx → Vec dx) (hg : Measurable g) :
    Measurable (codeLoss (dy := dy) (N := N) (K := K) c g) := by
  have hm : Measurable (fun s : Bool × TraceCode dx dy N K => g s.2.2.2) :=
    hg.comp measurable_snd.snd.snd
  cases c
  · exact hm.norm.ennreal_ofReal
  · exact (hm.norm.pow_const 2).ennreal_ofReal

/-- On an invalid nonmeasurable oracle the risk is zero; all admissible instances
in the theorems below explicitly have a jointly measurable oracle. -/
def risk {K : ℕ} (A : Family K) (c : StationarityCriterion) (m : StationarityObjective)
    (M : ℝ) (N : ℕ) (I : MeasuredOracle.Instance) : ℝ≥0∞ := by
  classical
  exact if hO : JointlyMeasurable I.oracle then
    ∫⁻ s, codeLoss c (I.field m M) s ∂executionLaw A N I hO else 0

theorem compile_risk {K : ℕ} (A : Family K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : MeasuredOracle.Instance)
    (hO : JointlyMeasurable I.oracle) :
    MeasuredOracle.risk A.compile c m M N I = risk A c m M N I := by
  rw [risk, dif_pos hO, ← compile_law A N I hO]
  rw [lintegral_map (codeLoss_measurable c _ (I.field_measurable m M))
    (CausalGuard.completeCode_measurable _ _ hO N)]
  unfold MeasuredOracle.risk
  congr 1

def Family.representative {K : ℕ} (A : Family K) (N : ℕ) : Rectangular.Family K :=
  CausalGuard.repairFamily A.compile N

theorem representative_legal {K : ℕ} (A : Family K) (valid : MeasuredOracle.Instance → Prop)
    (N : ℕ) : MeasuredOracle.Legal (A.representative N) valid N :=
  CausalGuard.repairFamily_legal A.compile valid N

theorem representative_pathwise {K : ℕ} (A : Family K) (N : ℕ)
    (I : MeasuredOracle.Instance) (u : RandomTape) (w : Fin N → I.Seed) :
    ∃ tr, ((A.representative N).policy I.dx I.dy).run? I.oracle N 0
      (u, Fin.elim0) w = some tr ∧ StandardSupport tr ∧ calls tr ≤ N :=
  CausalGuard.repairPolicy_legal (A.compile.policy I.dx I.dy) N I.oracle u w

/-- Complete trace-law preservation, including success, queries, responses and output. -/
theorem representative_law {K : ℕ} (A : Family K) (valid : MeasuredOracle.Instance → Prop)
    (hvalid : ∀ I, valid I → JointlyMeasurable I.oracle) (N : ℕ) (hA : Legal A valid N)
    (I : MeasuredOracle.Instance) (hI : valid I) :
    (((A.representative N).law I.dx I.dy).prod (iidRoundMeasure I.law N)).map
      (CausalGuard.completeCode ((A.representative N).policy I.dx I.dy) I.oracle N) =
      executionLaw A N I (hvalid I hI) := by
  change ((A.compile.law I.dx I.dy).prod (iidRoundMeasure I.law N)).map
    (CausalGuard.completeCode (CausalGuard.repairPolicy (A.compile.policy I.dx I.dy) N) I.oracle N) = _
  rw [CausalGuard.repairPolicy_law _ N N _ _ ((legal_iff_compile A valid hvalid N).mp hA I hI)]
  exact compile_law A N I (hvalid I hI)

theorem representative_risk {K : ℕ} (A : Family K) (valid : MeasuredOracle.Instance → Prop)
    (hvalid : ∀ I, valid I → JointlyMeasurable I.oracle) (N : ℕ) (hA : Legal A valid N)
    (c : StationarityCriterion) (m : StationarityObjective) (M : ℝ)
    (I : MeasuredOracle.Instance) (hI : valid I) :
    MeasuredOracle.risk (A.representative N) c m M N I = risk A c m M N I := by
  rw [Family.representative, CausalGuard.repairFamily_risk A.compile valid N
    ((legal_iff_compile A valid hvalid N).mp hA) c m M I hI]
  exact compile_risk A c m M N I (hvalid I hI)

/-- A single representative, chosen before the instance, preserves every risk.
The budget, dimension dependence, stopping, internal randomness and full trace
law are handled by the compiler and causal guard; no per-instance algorithm is chosen. -/
theorem exists_uniform_representative {K : ℕ} (A : Family K)
    (valid : MeasuredOracle.Instance → Prop) (hvalid : ∀ I, valid I → JointlyMeasurable I.oracle)
    (N : ℕ) (hA : Legal A valid N) :
    ∃ P : Rectangular.Family.{0} K, MeasuredOracle.Legal P valid N ∧
      ∀ c m M I, valid I → MeasuredOracle.risk P c m M N I = risk A c m M N I :=
  ⟨A.representative N, representative_legal A valid N,
    fun c m M I hI => representative_risk A valid hvalid N hA c m M I hI⟩

abbrev BudgetAlgorithm (valid : MeasuredOracle.Instance → Prop) (K N : ℕ) :=
  {A : Family K // Legal A valid N}

def complexity (valid : MeasuredOracle.Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) : ℝ≥0∞ :=
  uniformBudgetComplexity valid
    (fun N (A : BudgetAlgorithm valid K N) I => risk A.val c m M N I) (c.target ε)

theorem measured_complexity_le (valid : MeasuredOracle.Instance → Prop)
    (hvalid : ∀ I, valid I → JointlyMeasurable I.oracle) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) :
    MeasuredOracle.complexity.{0} valid K c m M ε ≤ complexity valid K c m M ε := by
  apply uniformBudgetComplexity_le_of_restriction valid valid
    (fun N (A : MeasuredOracle.BudgetAlgorithm.{0} valid K N) I => MeasuredOracle.risk A.val c m M N I)
    (fun N (A : BudgetAlgorithm valid K N) I => risk A.val c m M N I)
    id (fun _ h => h) (fun N A => ⟨A.val.representative N, representative_legal A.val valid N⟩)
  intro N A I hI
  exact le_of_eq (representative_risk A.val valid hvalid N A.property c m M I hI)

theorem bv_complexity_lower (P : ManuscriptBVProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity (fun I => I.ValidBV P.M P.μ P.Δ P.σ ∧ JointlyMeasurable I.oracle)
        K c m P.M P.ε := by
  have h := MemoryModel.bv_complexity_lower_jointlyMeasurable.{0} P hK c m
  rw [MemoryModel.complexity_eq_history] at h
  exact h.trans (measured_complexity_le _ (fun _ hI => hI.2) K c m P.M P.ε)

theorem as_complexity_lower (P : ManuscriptASProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity (fun I => I.ValidAS P.M P.μ P.Δ P.σ ∧ JointlyMeasurable I.oracle)
        K c m P.M P.ε := by
  have h := MemoryModel.as_complexity_lower_jointlyMeasurable.{0} P hK c m
  rw [MemoryModel.complexity_eq_history] at h
  exact h.trans (measured_complexity_le _ (fun _ hI => hI.2) K c m P.M P.ε)

end KernelModel
end NCSCPureStochasticLB.PaperExact
