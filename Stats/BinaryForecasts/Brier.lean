module

/-
  Brier scores on a probability space.
  Taleb, arXiv:1907.11162v3, Theorem 2.

  The finite average of squared forecast errors is measurable and bounded
  between zero and one. Every nonnegative real-order moment is integrable;
  no independence assumptions are needed.
-/
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory Set

namespace TailOptionPricing

/-! ## Brier-score boundedness (paper Theorem 2).

    The Brier score `λ_n := (1/n) Σ (f_t − 𝟙_{X_t ∈ χ_t})²` always lies
    in `[0, 1]` (each summand is at most 1).  Consequently all
    moments `E[λ_n^q]` are finite, regardless of the distribution of
    the underlying `X` — Brier-score-based calibration metrics are
    "thin-tailed" by construction (Remark 2). -/

/-- **Per-term Brier-score bound.**  Each Brier summand `(f − 𝟙)²`
    lies in `[0, 1]` whenever both `f ∈ [0, 1]` and `𝟙 ∈ [0, 1]`. -/
theorem brierTerm_bounded {f y : ℝ}
    (hf_lb : 0 ≤ f) (hf_ub : f ≤ 1) (hy_lb : 0 ≤ y) (hy_ub : y ≤ 1) :
    0 ≤ (f - y) ^ 2 ∧ (f - y) ^ 2 ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h_diff_bound : -1 ≤ f - y ∧ f - y ≤ 1 := by
    constructor <;> linarith
  rcases h_diff_bound with ⟨hl, hr⟩
  have h_abs_le_one : |f - y| ≤ 1 := abs_le.mpr ⟨hl, hr⟩
  calc (f - y) ^ 2 = |f - y| ^ 2 := by rw [sq_abs]
    _ ≤ 1 ^ 2 := by exact pow_le_pow_left₀ (abs_nonneg _) h_abs_le_one 2
    _ = 1 := by ring

/-- **Brier-score moment boundedness (paper Theorem 2).**  Any
    nonnegative real `λ ∈ [0, 1]` raised to any nonnegative power
    `q ≥ 0` stays bounded above by `1`.  Direct corollary; applied
    pointwise to the Brier average, this supplies the domination
    bound used in `integrable_brierAverage_rpow` below. -/
theorem brierScore_moment_bounded {lam q : ℝ}
    (h_lb : 0 ≤ lam) (h_ub : lam ≤ 1) (hq : 0 ≤ q) :
    lam ^ q ≤ 1 := by
  rcases eq_or_lt_of_le h_lb with h_zero | h_pos
  · rcases eq_or_lt_of_le hq with hq_zero | hq_pos
    · rw [← hq_zero, Real.rpow_zero]
    · rw [← h_zero, Real.zero_rpow hq_pos.ne']
      linarith
  · exact Real.rpow_le_one h_pos.le h_ub hq

/-- **Brier-score boundedness with positivity** (`λ ∈ [0, 1]` ⇒
    `0 ≤ λ^q ≤ 1` for any `q ≥ 0`). -/
theorem brierScore_moment_in_unit_interval {lam q : ℝ}
    (h_lb : 0 ≤ lam) (h_ub : lam ≤ 1) (hq : 0 ≤ q) :
    0 ≤ lam ^ q ∧ lam ^ q ≤ 1 :=
  ⟨Real.rpow_nonneg h_lb _, brierScore_moment_bounded h_lb h_ub hq⟩


/-! ## The actual finite-sample score and its moments. -/

/-- The observed indicator for a forecast event. -/
noncomputable def brierOutcome {Ω : Type*} (A : Set Ω) (ω : Ω) : ℝ :=
  A.indicator (fun _ => 1) ω

/-- The paper's Brier average, formed from forecasts and their event outcomes. -/
noncomputable def brierAverage {Ω : Type*} {n : ℕ}
    (f : Fin n → Ω → ℝ) (A : Fin n → Set Ω) (ω : Ω) : ℝ :=
  (∑ i : Fin n, (f i ω - brierOutcome (A i) ω) ^ 2) / (n : ℝ)

theorem brierOutcome_mem_unit_interval {Ω : Type*} (A : Set Ω) (ω : Ω) :
    0 ≤ brierOutcome A ω ∧ brierOutcome A ω ≤ 1 := by
  classical
  by_cases h : ω ∈ A <;> simp [brierOutcome, Set.indicator, h]

theorem measurable_brierOutcome {Ω : Type*} [MeasurableSpace Ω]
    {A : Set Ω} (hA : MeasurableSet A) : Measurable (brierOutcome A) :=
  measurable_const.indicator hA

theorem measurable_brierAverage {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {f : Fin n → Ω → ℝ} {A : Fin n → Set Ω}
    (hf : ∀ i, Measurable (f i)) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (brierAverage f A) := by
  unfold brierAverage
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    ((hf i).sub (measurable_brierOutcome (hA i))).pow_const 2).div_const _

/-- The bound holds for arbitrary dependence between forecasts and outcomes. -/
theorem brierAverage_mem_unit_interval {Ω : Type*} {n : ℕ}
    {f : Fin n → Ω → ℝ} {A : Fin n → Set Ω} (hn : 0 < n)
    (hf : ∀ i ω, 0 ≤ f i ω ∧ f i ω ≤ 1) (ω : Ω) :
    0 ≤ brierAverage f A ω ∧ brierAverage f A ω ≤ 1 := by
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hterms (i : Fin n) :
      0 ≤ (f i ω - brierOutcome (A i) ω) ^ 2 ∧
        (f i ω - brierOutcome (A i) ω) ^ 2 ≤ 1 :=
    brierTerm_bounded (hf i ω).1 (hf i ω).2
      (brierOutcome_mem_unit_interval (A i) ω).1
      (brierOutcome_mem_unit_interval (A i) ω).2
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hterms i).1) hnreal.le
  · apply (div_le_one hnreal).mpr
    calc
      (∑ i : Fin n, (f i ω - brierOutcome (A i) ω) ^ 2) ≤
          ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hterms i).2
      _ = (n : ℝ) := by simp

/-- The Brier average has no upper tail beyond one under any measure. -/
theorem brierAverage_tail_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} {f : Fin n → Ω → ℝ} {A : Fin n → Set Ω}
    {K : ℝ} (hn : 0 < n) (hf : ∀ i ω, 0 ≤ f i ω ∧ f i ω ≤ 1)
    (hK : 1 < K) : μ {ω | K < brierAverage f A ω} = 0 := by
  have hempty : {ω | K < brierAverage f A ω} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (not_lt_of_ge ((brierAverage_mem_unit_interval (A := A) hn hf ω).2.trans
      hK.le)) hω
  rw [hempty, measure_empty]

/-- **Theorem 2:** every nonnegative real-order Brier moment is integrable
on a probability space, without an independence assumption. -/
theorem integrable_brierAverage_rpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {f : Fin n → Ω → ℝ} {A : Fin n → Set Ω} {q : ℝ}
    (hn : 0 < n) (hf_meas : ∀ i, Measurable (f i))
    (hA : ∀ i, MeasurableSet (A i))
    (hf_bounds : ∀ i ω, 0 ≤ f i ω ∧ f i ω ≤ 1) (hq : 0 ≤ q) :
    Integrable (fun ω => (brierAverage f A ω) ^ q) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_brierAverage hf_meas hA).pow_const q).aestronglyMeasurable
  filter_upwards [] with ω
  have hb := brierAverage_mem_unit_interval (A := A) hn hf_bounds ω
  have hp := brierScore_moment_in_unit_interval hb.1 hb.2 hq
  simpa [Real.norm_eq_abs, abs_of_nonneg hp.1] using hp.2

/-- The expectation of every nonnegative real power is between zero and one. -/
theorem brierAverage_moment_mem_unit_interval {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {f : Fin n → Ω → ℝ} {A : Fin n → Set Ω} {q : ℝ}
    (hn : 0 < n) (hf_meas : ∀ i, Measurable (f i))
    (hA : ∀ i, MeasurableSet (A i))
    (hf_bounds : ∀ i ω, 0 ≤ f i ω ∧ f i ω ≤ 1) (hq : 0 ≤ q) :
    0 ≤ ∫ ω, (brierAverage f A ω) ^ q ∂μ ∧
      (∫ ω, (brierAverage f A ω) ^ q ∂μ) ≤ 1 := by
  have hint := integrable_brierAverage_rpow (μ := μ) hn hf_meas hA hf_bounds hq
  have hbound (ω : Ω) :
      0 ≤ (brierAverage f A ω) ^ q ∧ (brierAverage f A ω) ^ q ≤ 1 := by
    have hb := brierAverage_mem_unit_interval (A := A) hn hf_bounds ω
    exact brierScore_moment_in_unit_interval hb.1 hb.2 hq
  constructor
  · exact integral_nonneg fun ω => (hbound ω).1
  · calc
      (∫ ω, (brierAverage f A ω) ^ q ∂μ) ≤ ∫ _ω : Ω, (1 : ℝ) ∂μ :=
        integral_mono hint (integrable_const 1) fun ω => (hbound ω).2
      _ = 1 := by simp

end TailOptionPricing
