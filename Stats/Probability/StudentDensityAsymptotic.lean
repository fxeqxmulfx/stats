module

/-
  Actual Student density power-law asymptotic, arXiv:1912.00277v2,
  Section VI. Factoring x squared out of the conventional density's
  power base gives an explicit finite positive limit for x^(nu+1)*f(x).
  Its coefficient is independent of location. No tail asymptotic is
  assumed as an input to the density calculation.
-/
public import Stats.Probability.StudentDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Real Set Filter Topology

namespace TailOptionPricing

/-- The explicit coefficient of x^(-(nu+1)) in the conventional
Student density (Section VI). It is derived as an actual limit below. -/
noncomputable def studentDensityTailConstant (ν s : ℝ) : ℝ :=
  Real.Gamma ((ν + 1) / 2) / (Real.Gamma (ν / 2) * √(ν * Real.pi) * s) *
    (1 / (ν * s ^ 2)) ^ (-((ν + 1) / 2))

theorem studentDensityTailConstant_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    0 < studentDensityTailConstant ν s := by
  have hg₁ : 0 < Real.Gamma ((ν + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg₂ : 0 < Real.Gamma (ν / 2) := Real.Gamma_pos_of_pos (by positivity)
  unfold studentDensityTailConstant
  exact mul_pos (div_pos hg₁ (mul_pos (mul_pos hg₂ (Real.sqrt_pos.mpr (by positivity))) hs))
    (Real.rpow_pos_of_pos (by positivity) _)

/-- Algebraic normalization of the actual density for x>0. The
remaining base tends to 1/(nu*s^2), keeping the location term explicit. -/
theorem studentPDFReal_mul_rpow_eq (μ : ℝ) {ν s x : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (hx : 0 < x) :
    x ^ (ν + 1) * studentPDFReal μ ν s x =
      Real.Gamma ((ν + 1) / 2) / (Real.Gamma (ν / 2) * √(ν * Real.pi) * s) *
        (1 / x ^ 2 + ((1 - μ / x) / s) ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
  let b : ℝ := 1 / x ^ 2 + ((1 - μ / x) / s) ^ 2 / ν
  have hb : 0 < b := by dsimp [b]; positivity
  have hf : 1 + ((x - μ) / s) ^ 2 / ν = x ^ 2 * b := by
    dsimp [b]
    field_simp
  have hp : (x ^ 2) ^ (-((ν + 1) / 2)) = x ^ (-(ν + 1)) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  unfold studentPDFReal
  rw [hf, Real.mul_rpow (sq_nonneg x) hb.le, hp, Real.rpow_neg hx.le]
  have hxp : x ^ (ν + 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  calc
    _ = (x ^ (ν + 1) * (x ^ (ν + 1))⁻¹) *
        (Real.Gamma ((ν + 1) / 2) / (Real.Gamma (ν / 2) * √(ν * Real.pi) * s) *
          b ^ (-((ν + 1) / 2))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hxp, one_mul]

/-- The exact remaining base in the normalized density tends to
1/(nu*s^2). All reciprocal outcome terms vanish at infinity. -/
theorem student_density_base_tendsto (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x : ℝ => 1 / x ^ 2 + ((1 - μ / x) / s) ^ 2 / ν)
      atTop (𝓝 (1 / (ν * s ^ 2))) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsq : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hi.pow 2
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hm : Tendsto (fun x : ℝ => 1 - μ / x) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using hc.sub (hi.const_mul μ)
  have hl : Tendsto (fun x : ℝ => 1 / x ^ 2 + ((1 - μ / x) / s) ^ 2 / ν)
      atTop (𝓝 (0 + (1 / s) ^ 2 / ν)) := hsq.add (((hm.div_const s).pow 2).div_const ν)
  have he : (0 : ℝ) + (1 / s) ^ 2 / ν = 1 / (ν * s ^ 2) := by field_simp; ring
  rw [he] at hl
  exact hl

/-- The actual Student density has positive finite power-law
coefficient and exponent nu+1 (Section VI). The parameter conditions
are precisely those of the normalized conventional Student law. -/
theorem studentPDFReal_rpow_tendsto (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x : ℝ => x ^ (ν + 1) * studentPDFReal μ ν s x)
      atTop (𝓝 (studentDensityTailConstant ν s)) := by
  have hb : 0 < 1 / (ν * s ^ 2) := by positivity
  have hl := ((student_density_base_tendsto μ hν hs).rpow_const
    (p := -((ν + 1) / 2)) (Or.inl hb.ne')).const_mul
      (Real.Gamma ((ν + 1) / 2) / (Real.Gamma (ν / 2) * √(ν * Real.pi) * s))
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (studentPDFReal_mul_rpow_eq μ hν hs hx).symm

/-- Quotient of the actual survival derivative and the reference
power-tail derivative, expressed by the normalized actual density. -/
theorem studentPDFReal_powerTail_ratio_eq (μ s : ℝ) {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    (-studentPDFReal μ ν s x) / ((-ν) * x ^ (-ν - 1)) =
      (x ^ (ν + 1) * studentPDFReal μ ν s x) / ν := by
  have hp : x ^ (-ν - 1) = (x ^ (ν + 1))⁻¹ := by
    rw [show -ν - 1 = -(ν + 1) by ring, Real.rpow_neg hx.le]
  rw [hp]
  field_simp [hν.ne', (Real.rpow_pos_of_pos hx (ν + 1)).ne']

theorem studentPDFReal_powerTail_ratio_tendsto (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (-studentPDFReal μ ν s x) / ((-ν) * x ^ (-ν - 1)))
      atTop (𝓝 (studentDensityTailConstant ν s / ν)) := by
  apply ((studentPDFReal_rpow_tendsto μ hν hs).div_const ν).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (studentPDFReal_powerTail_ratio_eq μ s hν hx).symm

/-- The density itself tends to zero, from its proved power-law
normalization rather than an assumed generic property of L1 functions. -/
theorem studentPDFReal_tendsto_zero (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (studentPDFReal μ ν s) atTop (𝓝 0) := by
  have h := (studentPDFReal_rpow_tendsto μ hν hs).mul
    (tendsto_rpow_neg_atTop (show 0 < ν + 1 by linarith))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp [(Real.rpow_pos_of_pos hx (ν + 1)).ne']

example : 0 < studentDensityTailConstant 4 2 := studentDensityTailConstant_pos (by norm_num) (by norm_num)

example : (1 : ℝ) ^ (4 + 1 : ℝ) * studentPDFReal 1 4 2 1 =
    Real.Gamma (((4 : ℝ) + 1) / 2) / (Real.Gamma (4 / 2) * √(4 * Real.pi) * 2) *
      (1 / (1 : ℝ) ^ 2 + ((1 - 1 / 1) / 2) ^ 2 / 4) ^ (-((4 + 1) / 2 : ℝ)) :=
  studentPDFReal_mul_rpow_eq 1 (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun x : ℝ => 1 / x ^ 2 + ((1 - 1 / x) / 2) ^ 2 / 4)
    atTop (𝓝 (1 / (4 * (2 : ℝ) ^ 2))) :=
  student_density_base_tendsto 1 (by norm_num) (by norm_num)

example : Tendsto (fun x : ℝ => x ^ ((1 / 2 : ℝ) + 1) * studentPDFReal 1 (1 / 2) 2 x)
    atTop (𝓝 (studentDensityTailConstant (1 / 2) 2)) :=
  studentPDFReal_rpow_tendsto 1 (by norm_num) (by norm_num)

example : Tendsto (fun x : ℝ => (-studentPDFReal 1 4 2 x) / ((-4) * x ^ (-4 - 1 : ℝ)))
    atTop (𝓝 (studentDensityTailConstant 4 2 / 4)) :=
  studentPDFReal_powerTail_ratio_tendsto 1 (by norm_num) (by norm_num)

example : (-studentPDFReal 1 4 2 1) / ((-4) * (1 : ℝ) ^ (-4 - 1 : ℝ)) =
    ((1 : ℝ) ^ (4 + 1 : ℝ) * studentPDFReal 1 4 2 1) / 4 :=
  studentPDFReal_powerTail_ratio_eq 1 2 (by norm_num) (by norm_num)

example : Tendsto (studentPDFReal 1 (1 / 2) 2) atTop (𝓝 0) :=
  studentPDFReal_tendsto_zero 1 (by norm_num) (by norm_num)

#print axioms studentDensityTailConstant_pos
#print axioms studentPDFReal_mul_rpow_eq
#print axioms student_density_base_tendsto
#print axioms studentPDFReal_rpow_tendsto
#print axioms studentPDFReal_powerTail_ratio_tendsto
#print axioms studentPDFReal_tendsto_zero

end TailOptionPricing
