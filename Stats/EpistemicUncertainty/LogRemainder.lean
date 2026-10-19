module

/-
  Uniform signed-error remainder for arXiv:1912.00277v2, Section V,
  Eqs. lerrorn–lerrornapprox. The source's informal small-error step
  is replaced by an explicit radius |epsilon| <= r < 1 and a bound
  on the sum of squared errors. Both signs of epsilon are covered.
-/
public import Stats.EpistemicUncertainty

@[expose] public section

open Real Finset Filter Topology

namespace TailOptionPricing

/-- Section V's logarithmic linearization with an explicit uniform
signed-error remainder. The source gives only an informal approximation;
this bound requires |epsilon| <= r < 1 and covers negative errors too. -/
theorem log_one_add_remainder_bounds {ε r : ℝ} (hr : r < 1) (hε : |ε| ≤ r) :
    0 ≤ ε - Real.log (1 + ε) ∧ ε - Real.log (1 + ε) ≤ ε ^ 2 / (1 - r) := by
  have he := (abs_le.mp hε).1
  have hp : 0 < 1 + ε := by linarith
  constructor
  · have hu := Real.log_le_sub_one_of_pos hp
    linarith
  · have hl := Real.one_sub_inv_le_log_of_pos hp
    calc
      ε - Real.log (1 + ε) ≤ ε - (1 - (1 + ε)⁻¹) := by linarith
      _ = ε ^ 2 / (1 + ε) := by field_simp; ring
      _ ≤ ε ^ 2 / (1 - r) :=
        div_le_div_of_nonneg_left (sq_nonneg ε) (by linarith) (by linarith)

/-- Actual accumulated discrepancy between the product's logarithm
and the sum of signed errors in Section V. A uniform small radius gives
a bound by the accumulated squared errors, not by their signed sum. -/
theorem log_multiplicative_error_remainder_bounds {ι : Type*} (s : Finset ι)
    (lamHat : ℝ) (ε : ι → ℝ) {r : ℝ} (hLam : 0 < lamHat) (hr : r < 1)
    (hε : ∀ i ∈ s, |ε i| ≤ r) :
    0 ≤ Real.log lamHat + ∑ i ∈ s, ε i -
        Real.log (lamHat * ∏ i ∈ s, (1 + ε i)) ∧
      Real.log lamHat + ∑ i ∈ s, ε i -
        Real.log (lamHat * ∏ i ∈ s, (1 + ε i)) ≤
          (∑ i ∈ s, (ε i) ^ 2) / (1 - r) := by
  have hp (i : ι) (hi : i ∈ s) : 0 < 1 + ε i := by
    have he := (abs_le.mp (hε i hi)).1
    linarith
  have hprod : 0 < ∏ i ∈ s, (1 + ε i) := Finset.prod_pos hp
  have heq : Real.log lamHat + ∑ i ∈ s, ε i -
      Real.log (lamHat * ∏ i ∈ s, (1 + ε i)) =
        ∑ i ∈ s, (ε i - Real.log (1 + ε i)) := by
    rw [Real.log_mul hLam.ne' hprod.ne', Real.log_prod (fun i hi => (hp i hi).ne'),
      Finset.sum_sub_distrib]
    ring
  rw [heq]
  constructor
  · exact Finset.sum_nonneg (fun i hi => (log_one_add_remainder_bounds hr (hε i hi)).1)
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun i hi => (log_one_add_remainder_bounds hr (hε i hi)).2)

/-- Absolute error in Section V's finite log linearization, with all
positivity and accumulated-error conditions made explicit. -/
theorem log_multiplicative_error_abs_remainder_le {ι : Type*} (s : Finset ι)
    (lamHat : ℝ) (ε : ι → ℝ) {r : ℝ} (hLam : 0 < lamHat) (hr : r < 1)
    (hε : ∀ i ∈ s, |ε i| ≤ r) :
    |Real.log lamHat + ∑ i ∈ s, ε i - Real.log (lamHat * ∏ i ∈ s, (1 + ε i))| ≤
      (∑ i ∈ s, (ε i) ^ 2) / (1 - r) := by
  obtain ⟨hn, hu⟩ := log_multiplicative_error_remainder_bounds s lamHat ε hLam hr hε
  rwa [abs_of_nonneg hn]

/-- A sufficient asymptotic condition for the source's normalized
linearization: squared-error mass must be negligible relative to the
chosen positive normalization. Fixed small signed errors alone do not
supply this condition at a CLT scale. -/
theorem log_multiplicative_error_normalized_remainder_tendsto_zero
    (lamHat : ℝ) (ε : ℕ → ℕ → ℝ) (a : ℕ → ℝ) {r : ℝ}
    (hLam : 0 < lamHat) (hr : r < 1)
    (hε : ∀ n i, i ∈ Finset.range n → |ε n i| ≤ r)
    (ha : ∀ n, 0 < a n)
    (hsmall : Tendsto (fun n => (∑ i ∈ Finset.range n, (ε n i) ^ 2) / a n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      |Real.log lamHat + ∑ i ∈ Finset.range n, ε n i -
        Real.log (lamHat * ∏ i ∈ Finset.range n, (1 + ε n i))| / a n) atTop (𝓝 0) := by
  have ht := hsmall.div_const (1 - r)
  simp only [zero_div] at ht
  apply squeeze_zero (fun n => div_nonneg (abs_nonneg _) (ha n).le) _ ht
  intro n
  calc
    _ ≤ ((∑ i ∈ Finset.range n, (ε n i) ^ 2) / (1 - r)) / a n :=
      div_le_div_of_nonneg_right
        (log_multiplicative_error_abs_remainder_le _ _ _ hLam hr (hε n)) (ha n).le
    _ = ((∑ i ∈ Finset.range n, (ε n i) ^ 2) / a n) / (1 - r) := by ring

example : 0 ≤ (-1 / 100 : ℝ) - Real.log (1 - 1 / 100) ∧
    (-1 / 100 : ℝ) - Real.log (1 - 1 / 100) ≤ (1 / 100 : ℝ) ^ 2 / (1 - 1 / 100) := by
  simpa only [neg_div, neg_sq, sub_eq_add_neg] using log_one_add_remainder_bounds
    (r := (1 / 100 : ℝ)) (ε := (-1 / 100 : ℝ)) (by norm_num) (by norm_num)

example (b : Fin 3 → Bool) :
    0 ≤ Real.log 2 + ∑ i : Fin 3, (if b i then (1 / 100 : ℝ) else -1 / 100) -
        Real.log (2 * ∏ i : Fin 3, (1 + if b i then (1 / 100 : ℝ) else -1 / 100)) ∧
      Real.log 2 + ∑ i : Fin 3, (if b i then (1 / 100 : ℝ) else -1 / 100) -
        Real.log (2 * ∏ i : Fin 3, (1 + if b i then (1 / 100 : ℝ) else -1 / 100)) ≤
          (∑ _i : Fin 3, (1 / 100 : ℝ) ^ 2) / (1 - 1 / 100) := by
  have hb (i : Fin 3) : |if b i then (1 / 100 : ℝ) else -1 / 100| ≤ 1 / 100 := by
    cases b i <;> norm_num
  have hs (i : Fin 3) : (if b i then (1 / 100 : ℝ) else -1 / 100) ^ 2 =
      (1 / 100 : ℝ) ^ 2 := by cases b i <;> norm_num
  simpa only [hs] using log_multiplicative_error_remainder_bounds
    Finset.univ 2 (fun i : Fin 3 => if b i then (1 / 100 : ℝ) else -1 / 100)
    (r := (1 / 100 : ℝ)) (by norm_num) (by norm_num) (fun i _ => hb i)

example : |Real.log 2 + ∑ i ∈ Finset.range 3, (if i = 0 then (1 / 100 : ℝ) else -1 / 100) -
    Real.log (2 * ∏ i ∈ Finset.range 3, (1 + if i = 0 then (1 / 100 : ℝ) else -1 / 100))| ≤
      (∑ i ∈ Finset.range 3, (if i = 0 then (1 / 100 : ℝ) else -1 / 100) ^ 2) /
        (1 - 1 / 100) :=
  log_multiplicative_error_abs_remainder_le _ _ _ (by norm_num) (by norm_num)
    (fun i _ => by split <;> norm_num)

/-- A nonzero shrinking-error example: accumulated log-linearization
error tends to zero even without a growing normalization. The extra
rate condition, unlike fixed small errors, controls the squared sum. -/
example : Tendsto (fun n : ℕ =>
    |Real.log 2 + ∑ _i ∈ Finset.range n, (1 / (2 * ((n : ℝ) + 1))) -
      Real.log (2 * ∏ _i ∈ Finset.range n, (1 + 1 / (2 * ((n : ℝ) + 1))))| / 1)
    atTop (𝓝 0) := by
  have ht := ((tendsto_natCast_div_add_atTop (1 : ℝ)).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 4
  have he (n : ℕ) :
      (∑ _i ∈ Finset.range n, (1 / (2 * ((n : ℝ) + 1))) ^ 2) / 1 =
        ((n : ℝ) / ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))) / 4 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_one]
    field_simp
    ring
  apply log_multiplicative_error_normalized_remainder_tendsto_zero
    (ε := fun n _ => 1 / (2 * ((n : ℝ) + 1))) (r := (1 / 2 : ℝ))
    2 (fun _ => 1) (by norm_num) (by norm_num)
  · intro n i hi
    rw [abs_of_pos (by positivity)]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 2)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  · intro n
    norm_num
  · simp_rw [he]
    simpa using ht

#print axioms log_one_add_remainder_bounds
#print axioms log_multiplicative_error_remainder_bounds
#print axioms log_multiplicative_error_normalized_remainder_tendsto_zero

end TailOptionPricing
