/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.MaxIIdBound — Inclusion-exclusion lower bound on iid max.

  The Loulakis argument (paper Section "Lognormal Sums", Appendix B)
  uses the lower bound

      `ℙ(max_{i<n} X_i > t) ≥ n · ℙ(X_0 > t) − (n choose 2) · ℙ(X_0 > t)²`

  for an iid family `(X_i)`.  This file proves it in three steps:

  1.  **Algebraic inequality** (`one_sub_one_sub_pow_ge`):  for
      `p ∈ [0, 1]` and `n ∈ ℕ`,
          `1 − (1 − p)^n ≥ n·p − (n choose 2)·p²`.
      Proof by induction on `n`, using Mathlib's Bernoulli inequality
      `one_add_mul_le_pow` at the step.

  2.  **Probabilistic translation** (`prob_max_iid_eq`):  for iid `X_i`
      with shared distribution of `X_0`,
          `ℙ(max_{i<n} X_i > t) = 1 − (1 − ℙ(X_0 > t))^n`.
      Direct from independence via `iIndepFun.measure_inter_preimage_eq_mul`
      applied to `{X_i ≤ t}` events.

  3.  **Combined** (`prob_max_iid_ge`):
          `ℙ(max_{i<n} X_i > t) ≥ n · ℙ(X_0 > t) − (n choose 2) · ℙ(X_0 > t)²`.

  Used by `Stats.Kappa.Lognormal.Loulakis` (todo5.md Phase C).
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Order.Ring.Pow

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TailOptionPricing.MaxIIdBound

/-! ### Step 1: Algebraic inequality. -/

/-- **Algebraic lower bound on `1 − (1 − p)^n`** for `p ∈ [0, 1]`:
        `1 − (1 − p)^n ≥ n · p − (n choose 2) · p²`.

    Proof by induction on `n` using Bernoulli's inequality
    `(1 − p)^n ≥ 1 − n·p` at the inductive step. -/
theorem one_sub_one_sub_pow_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≥ (n : ℝ) * p - (n.choose 2 : ℝ) * p ^ 2 := by
  induction n with
  | zero =>
    -- 1 − 1 = 0 ≥ 0·p − 0·p² = 0.
    simp
  | succ n ih =>
    -- Step: f_{n+1} − f_n = p · ((1-p)^n − 1 + n·p), Bernoulli ⇒ inner ≥ 0.
    have h_bernoulli : (1 : ℝ) - (n : ℝ) * p ≤ (1 - p) ^ n := by
      have h := one_add_mul_le_pow (a := -p) (by linarith : (-2 : ℝ) ≤ -p) n
      simpa [sub_eq_add_neg, mul_neg] using h
    -- (1 - p)^(n+1) = (1 - p) · (1 - p)^n
    have h_expand : (1 - p) ^ (n + 1) = (1 - p) ^ n - p * (1 - p) ^ n := by
      rw [pow_succ]; ring
    -- C(n+1, 2) = C(n, 2) + n  (Pascal: `choose_succ_succ'`).
    have h_pascal : ((n + 1).choose 2 : ℝ) = (n.choose 2 : ℝ) + (n : ℝ) := by
      have h1 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl]
        exact Nat.choose_succ_succ' n 1
      rw [h1, Nat.choose_one_right]
      push_cast; ring
    rw [h_expand]
    -- Goal: 1 - ((1-p)^n - p (1-p)^n) ≥ (n+1) p - C(n+1, 2) p²
    -- LHS = 1 - (1-p)^n + p (1-p)^n
    -- We use IH on the (1 - (1-p)^n) part, then need to show
    -- p · (1-p)^n ≥ p − n·p² ⇔ (1-p)^n ≥ 1 − n·p (Bernoulli).
    have h_target_simp :
        ((n : ℝ) + 1) * p - ((n.choose 2 : ℝ) + (n : ℝ)) * p ^ 2 -
            ((n : ℝ) * p - (n.choose 2 : ℝ) * p ^ 2)
          = p - (n : ℝ) * p ^ 2 := by ring
    calc 1 - ((1 - p) ^ n - p * (1 - p) ^ n)
        = (1 - (1 - p) ^ n) + p * (1 - p) ^ n := by ring
      _ ≥ ((n : ℝ) * p - (n.choose 2 : ℝ) * p ^ 2) + p * (1 - p) ^ n := by
          linarith
      _ ≥ ((n : ℝ) * p - (n.choose 2 : ℝ) * p ^ 2) + p * (1 - (n : ℝ) * p) := by
          have : p * ((1 : ℝ) - (n : ℝ) * p) ≤ p * (1 - p) ^ n :=
            mul_le_mul_of_nonneg_left h_bernoulli hp0
          linarith
      _ = ((n : ℝ) + 1) * p - ((n.choose 2 : ℝ) + (n : ℝ)) * p ^ 2 := by ring
      _ = ((n + 1 : ℕ) : ℝ) * p - ((n + 1).choose 2 : ℝ) * p ^ 2 := by
          rw [h_pascal]; push_cast; ring

/-! ### Step 2: probabilistic translation `ℙ(max > t) = 1 − ℙ(X₀ ≤ t)^n`. -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Iid-product formula for `ℙ(max ≤ t)`.**  For an iid family
    `X : Fin n → Ω → ℝ` with common law equal to `Y`, the event
    `{ω | ∀ i, X i ω ≤ t}` has measure `ℙ(Y ≤ t)^n`.

    Uses an explicit representative `Y : Ω' → ℝ` (à la Mathlib's
    `cumulant_iid_sum`) to avoid pathology when `n = 0`. -/
theorem prob_all_le_iid {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} {Y : Ω' → ℝ} {X : Fin n → Ω → ℝ}
    (_h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y μ ν)
    (t : ℝ) :
    μ.real {ω | ∀ i, X i ω ≤ t} = (ν.real {ω' | Y ω' ≤ t}) ^ n := by
  -- Reduce to a Finset.univ product, use iIndepFun's measure_inter formula.
  have h_event_eq : {ω | ∀ i, X i ω ≤ t} = ⋂ i, (X i) ⁻¹' Set.Iic t := by
    ext ω; simp [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  rw [h_event_eq]
  -- ⋂ i, X i ⁻¹' Iic t = ⋂ i ∈ Finset.univ, X i ⁻¹' Iic t
  have h_inter_eq : (⋂ i, (X i) ⁻¹' Set.Iic t)
      = ⋂ i ∈ (Finset.univ : Finset (Fin n)), (X i) ⁻¹' Set.Iic t := by
    simp
  rw [h_inter_eq]
  -- Apply iIndepFun.measure_inter_preimage_eq_mul.
  have h_indep_inter := h_indep.measure_inter_preimage_eq_mul
    (sets := fun _ => Set.Iic t)
    (Finset.univ)
    (fun i _ => measurableSet_Iic)
  show (μ (⋂ i ∈ (Finset.univ : Finset (Fin n)),
            (X i) ⁻¹' Set.Iic t)).toReal = _
  rw [h_indep_inter, ENNReal.toReal_prod]
  -- Convert each μ (X i ⁻¹' Iic t) using IdentDistrib transport to ν via Y.
  have h_set_eq : {ω' | Y ω' ≤ t} = Y ⁻¹' Set.Iic t := by
    ext ω'; simp [Set.mem_preimage, Set.mem_Iic]
  have h_eq_each : ∀ i : Fin n,
      (μ ((X i) ⁻¹' Set.Iic t)).toReal = ν.real {ω' | Y ω' ≤ t} := by
    intro i
    show (μ ((X i) ⁻¹' Set.Iic t)).toReal = (ν _).toReal
    rw [h_set_eq]
    congr 1
    exact (h_id i).measure_mem_eq measurableSet_Iic
  calc ∏ i ∈ (Finset.univ : Finset (Fin n)), (μ ((X i) ⁻¹' Set.Iic t)).toReal
      = ∏ i ∈ (Finset.univ : Finset (Fin n)), ν.real {ω' | Y ω' ≤ t} :=
        Finset.prod_congr rfl (fun i _ => h_eq_each i)
    _ = (ν.real {ω' | Y ω' ≤ t}) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`ℙ(max > t) = 1 − ℙ(Y ≤ t)^n`** for an iid family `X : Fin n → Ω → ℝ`
    with representative law `Y`. -/
theorem prob_max_iid_gt {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} {Y : Ω' → ℝ} {X : Fin n → Ω → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y μ ν)
    (t : ℝ) :
    μ.real {ω | ∃ i, X i ω > t}
      = 1 - (ν.real {ω' | Y ω' ≤ t}) ^ n := by
  -- {∃ i, X i ω > t} and {∀ i, X i ω ≤ t} are complements (in Ω).
  have h_compl : {ω | ∃ i, X i ω > t} = {ω | ∀ i, X i ω ≤ t}ᶜ := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le]
  rw [h_compl]
  have h_meas_set : MeasurableSet {ω | ∀ i, X i ω ≤ t} := by
    have : {ω | ∀ i, X i ω ≤ t} = ⋂ i, (X i) ⁻¹' Set.Iic t := by
      ext ω; simp [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
    rw [this]
    exact MeasurableSet.iInter (fun i => (h_meas i) measurableSet_Iic)
  rw [measureReal_compl h_meas_set,
      probReal_univ,
      prob_all_le_iid (ν := ν) (Y := Y) h_meas h_indep h_id t]

/-! ### Step 3: combined inequality. -/

/-- **Loulakis lower bound on the iid max** (paper Section "Lognormal Sums",
    Loulakis remark).  For an iid family `X : Fin n → Ω → ℝ` with
    representative law `Y` on `(Ω', ν)`,
        `ℙ(max_{i<n} X_i > t) ≥ n · ℙ(Y > t) − (n choose 2) · ℙ(Y > t)²`.

    Combines `prob_max_iid_gt` (probabilistic identity) with
    `one_sub_one_sub_pow_ge` (algebraic Bernoulli-style inequality). -/
theorem prob_max_iid_ge {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} {Y : Ω' → ℝ} {X : Fin n → Ω → ℝ}
    (h_meas_Y : Measurable Y)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y μ ν)
    (t : ℝ) :
    (n : ℝ) * ν.real {ω' | Y ω' > t}
        - (n.choose 2 : ℝ) * (ν.real {ω' | Y ω' > t}) ^ 2
      ≤ μ.real {ω | ∃ i, X i ω > t} := by
  -- Let p := ℙ(Y > t) ∈ [0, 1].
  set p : ℝ := ν.real {ω' | Y ω' > t} with hp_def
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  -- ℙ(Y ≤ t) = 1 − p.
  have h_compl : ν.real {ω' | Y ω' ≤ t} = 1 - p := by
    have h_eq : {ω' | Y ω' ≤ t} = {ω' | Y ω' > t}ᶜ := by
      ext ω'; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [h_eq, hp_def]
    rw [show {ω' | Y ω' > t} = Y ⁻¹' Set.Ioi t from by
      ext ω'; simp [Set.mem_preimage, Set.mem_Ioi]]
    rw [measureReal_compl (h_meas_Y measurableSet_Ioi)]
    rw [probReal_univ]
  -- ℙ(max > t) = 1 − (1 − p)^n.
  have h_max_eq : μ.real {ω | ∃ i, X i ω > t} = 1 - (1 - p) ^ n := by
    rw [prob_max_iid_gt (ν := ν) (Y := Y) h_meas h_indep h_id t, h_compl]
  rw [h_max_eq]
  exact one_sub_one_sub_pow_ge hp0 hp1 n

end TailOptionPricing.MaxIIdBound
