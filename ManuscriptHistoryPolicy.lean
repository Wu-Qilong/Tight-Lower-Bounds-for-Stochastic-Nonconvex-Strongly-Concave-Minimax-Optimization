import ManuscriptStatefulPolicy

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- A round records both the query batch and its returned response batch. -/
abbrev RoundRecord (T K : ℕ) := BatchCode T K × BatchCode T K

/-- Internal randomness, number of completed rounds, and a padded transcript. -/
abbrev HistoryState (Ω : Type*) (T K : ℕ) := Ω × (ℕ × (ℕ → RoundRecord T K))

def initialHistory {Ω : Type*} {T K : ℕ} (ω : Ω) : HistoryState Ω T K :=
  (ω, 0, fun _ => (batchCode (fun _ => none), batchCode (fun _ => none)))

def appendHistory {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K)
    (r : RoundRecord T K) : HistoryState Ω T K :=
  (s.1, s.2.1 + 1, fun t => if t = s.2.1 then r else s.2.2 t)

theorem appendHistory_seed {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K) (r : RoundRecord T K) :
    (appendHistory s r).1 = s.1 := rfl

theorem appendHistory_clock {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K) (r : RoundRecord T K) :
    (appendHistory s r).2.1 = s.2.1 + 1 := rfl

theorem appendHistory_latest {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K) (r : RoundRecord T K) :
    (appendHistory s r).2.2 s.2.1 = r := by simp [appendHistory]

theorem appendHistory_past {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K)
    (r : RoundRecord T K) (t : ℕ) (ht : t < s.2.1) :
    (appendHistory s r).2.2 t = s.2.2 t := by simp [appendHistory, ne_of_lt ht]

theorem initialHistory_measurable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ} :
    Measurable (initialHistory (Ω := Ω) (T := T) (K := K)) :=
  measurable_id.prodMk (measurable_const.prodMk measurable_const)

theorem appendHistory_measurable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ} :
    Measurable (fun z : HistoryState Ω T K × RoundRecord T K => appendHistory z.1 z.2) := by
  apply Measurable.prodMk measurable_fst.fst
  have hn : Measurable (fun n : ℕ => n + 1) := measurable_of_countable _
  apply Measurable.prodMk (hn.comp measurable_fst.snd.fst)
  apply measurable_pi_lambda
  intro t
  have ht : MeasurableSet {z : HistoryState Ω T K × RoundRecord T K | t = z.1.2.1} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_comm] using
      (measurableSet_singleton t).preimage (measurable_fst.snd.fst :
        Measurable (fun z : HistoryState Ω T K × RoundRecord T K => z.1.2.1))
  exact Measurable.ite ht
    measurable_snd ((measurable_pi_apply t).comp measurable_fst.snd.snd)

def emptyRoundRecord (T K : ℕ) : RoundRecord T K :=
  (batchCode (fun _ => none), batchCode (fun _ => none))

/-- Entries beyond the completed rounds contain no oracle information. -/
def PaddedHistory {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K) : Prop :=
  ∀ t, s.2.1 ≤ t → s.2.2 t = emptyRoundRecord T K

theorem initialHistory_padded {Ω : Type*} {T K : ℕ} (ω : Ω) :
    PaddedHistory (initialHistory (T := T) (K := K) ω) := by
  intro t ht
  rfl

theorem appendHistory_padded {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K)
    (r : RoundRecord T K) (h : PaddedHistory s) : PaddedHistory (appendHistory s r) := by
  intro t ht
  change s.2.1 + 1 ≤ t at ht
  have hn : t ≠ s.2.1 := by omega
  simpa [appendHistory, hn] using h t (by omega)

/-- Rules on the internal seed and complete recorded history; the transcript update
is fixed by the compiler rather than chosen by the algorithm. Unused entries are padded. -/
structure HistoryPolicy (Ω : Type*) [MeasurableSpace Ω] (T K : ℕ) where
  stop : HistoryState Ω T K → Bool
  output : HistoryState Ω T K → Vec T
  batch : HistoryState Ω T K → NonemptyOnlineBatch T K
  stop_measurable : Measurable stop
  output_measurable : Measurable output
  batch_measurable : Measurable (fun s => batchCode (batch s).points)

namespace HistoryPolicy

variable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ}

def toStateful (P : HistoryPolicy Ω T K) : StatefulPolicy (HistoryState Ω T K) T K where
  stop := P.stop
  output := P.output
  batch := P.batch
  update := fun z => appendHistory z.1 (batchCode (P.batch z.1).points, z.2)
  stop_measurable := P.stop_measurable
  output_measurable := P.output_measurable
  batch_measurable := P.batch_measurable
  update_measurable := appendHistory_measurable.comp
    (measurable_fst.prodMk ((P.batch_measurable.comp measurable_fst).prodMk measurable_snd))

/-- Direct recursive interpretation of the history rules. -/
def toOnline (P : HistoryPolicy Ω T K) : (H : ℕ) → HistoryState Ω T K → OnlinePolicy T K H
  | 0, s => .halt (P.output s)
  | H + 1, s => if P.stop s = true then .halt (P.output s) else
      .ask (P.batch s) (fun r => P.toOnline H
        (appendHistory s (batchCode (P.batch s).points, batchCode r)))

/-- The stateful compiler reproduces the entire online decision tree. -/
theorem toStateful_toOnline (P : HistoryPolicy Ω T K) (H : ℕ) (s : HistoryState Ω T K) :
    P.toStateful.toOnline H s = P.toOnline H s := by
  induction H generalizing s with
  | zero => rfl
  | succ H ih =>
    simp only [StatefulPolicy.toOnline, toOnline, toStateful]
    split
    · rfl
    · congr 1
      funext r
      exact ih _

theorem execute_eq {Seed : Type} (P : HistoryPolicy Ω T K) (O : StochasticOracle T Seed)
    (H : ℕ) (s : HistoryState Ω T K) (w : Fin H → Seed) :
    (P.toStateful.toOnline H s).execute O w = (P.toOnline H s).execute O w := by
  rw [P.toStateful_toOnline]

theorem stop_eq {Seed : Type} (P : HistoryPolicy Ω T K) (O : StochasticOracle T Seed)
    (H : ℕ) (s : HistoryState Ω T K) (w : Fin H → Seed) :
    (P.toStateful.toOnline H s).stop O w = (P.toOnline H s).stop O w := by
  rw [P.toStateful_toOnline]

theorem observableOnline (P : HistoryPolicy Ω T K) (O : StochasticOracle T Bool)
    (hO : MeasurableOracle O) (H : ℕ) :
    ObservableOnline O (fun ω => P.toOnline H (initialHistory ω)) := by
  have h := P.toStateful.observableOnline O hO H initialHistory initialHistory_measurable
  simpa only [P.toStateful_toOnline] using h

/-- Finite-world risk is unchanged by the compiler. -/
theorem risk_eq (P : HistoryPolicy Ω T K) (c : StationarityCriterion) (ρ : Measure Ω)
    (O : StochasticOracle T Bool) (p : ℝ) (g : Vec T → Vec T) (H : ℕ) :
    onlineRisk c ρ O p g (fun ω => P.toStateful.toOnline H (initialHistory ω)) =
      onlineRisk c ρ O p g (fun ω => P.toOnline H (initialHistory ω)) := by
  simp only [P.toStateful_toOnline]

end HistoryPolicy
namespace ManuscriptBVProblem

theorem history_product_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : HistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N (initialHistory ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi (fun ω => A.toOnline N (initialHistory ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

theorem history_product_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : HistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N (initialHistory ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad (fun ω => A.toOnline N (initialHistory ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_moreau_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem history_product_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : HistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N (initialHistory ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi (fun ω => A.toOnline N (initialHistory ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

theorem history_product_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : HistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N (initialHistory ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad (fun ω => A.toOnline N (initialHistory ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_moreau_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
