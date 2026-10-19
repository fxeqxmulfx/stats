module

/-
  Positive-axis power transformations for arXiv:2004.05894v1,
  Proposition 1. The actual hidden moment is C times a positive
  power of the hidden mass. Its inverse and derivative are proved
  here before any density change of variables is made. Restricting
  to positive observations allows all positive real powers, including
  inverse derivatives that are unbounded near zero.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open Real Set

namespace TailOptionPricing

/-- The scaled power appearing in Proposition 1's hidden-moment law. -/
noncomputable def positivePower (C r y : ℝ) : ℝ := C * y ^ r

/-- Its inverse on the positive axis, proved below rather than
assumed as a property of the transformed population. -/
noncomputable def positivePowerInverse (C r z : ℝ) : ℝ := (z / C) ^ (1 / r)

/-- The derivative of the inverse transform, used as the actual
Jacobian in Proposition 1's corrected density calculation. -/
noncomputable def positivePowerJacobian (C r z : ℝ) : ℝ :=
  (1 / r / C) * (z / C) ^ (1 / r - 1)

theorem positivePower_pos {C r y : ℝ} (hC : 0 < C) (hy : 0 < y) :
    0 < positivePower C r y := mul_pos hC (Real.rpow_pos_of_pos hy r)

theorem positivePowerInverse_pos {C r z : ℝ} (hC : 0 < C) (hz : 0 < z) :
    0 < positivePowerInverse C r z := Real.rpow_pos_of_pos (div_pos hz hC) _

/-- The inverse followed by the original scaled power is the identity
on positive observations (Proposition 1's change of variables). -/
theorem positivePower_inverse {C r z : ℝ} (hC : 0 < C) (hr : 0 < r) (hz : 0 < z) :
    positivePower C r (positivePowerInverse C r z) = z := by
  unfold positivePower positivePowerInverse
  rw [← Real.rpow_mul (div_pos hz hC).le, one_div_mul_cancel hr.ne', Real.rpow_one]
  field_simp

/-- The original scaled power followed by the inverse is the identity
on positive observations (Proposition 1's change of variables). -/
theorem positivePowerInverse_power {C r y : ℝ} (hC : 0 < C) (hr : 0 < r) (hy : 0 < y) :
    positivePowerInverse C r (positivePower C r y) = y := by
  unfold positivePowerInverse positivePower
  rw [mul_div_cancel_left₀ _ hC.ne', ← Real.rpow_mul hy.le]
  have he : r * (1 / r) = 1 := by field_simp
  rw [he, Real.rpow_one]

/-- The inverse transformation is increasing on the positive axis.
This is established before applying the monotone Jacobian theorem. -/
theorem positivePowerInverse_monotoneOn {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    MonotoneOn (positivePowerInverse C r) (Ioi 0) := by
  intro x hx y hy hxy
  exact (Real.rpow_le_rpow_iff (div_pos hx hC).le (div_pos hy hC).le
    (one_div_pos.mpr hr)).mpr ((div_le_div_iff_of_pos_right hC).mpr hxy)

/-- The inverse has exactly the displayed Jacobian at each positive
point, including powers whose derivatives diverge at zero. -/
theorem positivePowerInverse_hasDerivAt {C r z : ℝ} (hC : 0 < C) (hz : 0 < z) :
    HasDerivAt (positivePowerInverse C r) (positivePowerJacobian C r z) z := by
  have hd := (Real.hasDerivAt_rpow_const (p := 1 / r)
    (Or.inl (div_pos hz hC).ne')).comp z ((hasDerivAt_id z).div_const C)
  simp only [Function.comp_def, id_eq] at hd
  change HasDerivAt (fun z : ℝ => (z / C) ^ (1 / r))
    ((1 / r / C) * (z / C) ^ (1 / r - 1)) z
  convert hd using 1
  ring

/-- The inverse Jacobian is strictly positive in the interior. -/
theorem positivePowerJacobian_pos {C r z : ℝ} (hC : 0 < C) (hr : 0 < r) (hz : 0 < z) :
    0 < positivePowerJacobian C r z :=
  mul_pos (div_pos (one_div_pos.mpr hr) hC) (Real.rpow_pos_of_pos (div_pos hz hC) _)

/-- The inverse image calculation for an arbitrary target event.
It tracks the whole positive support before density integration. -/
theorem positivePowerInverse_image {C r : ℝ} (hC : 0 < C) (hr : 0 < r) (s : Set ℝ) :
    positivePowerInverse C r '' (Ioi 0 ∩ s) = Ioi 0 ∩ positivePower C r ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨positivePowerInverse_pos hC hz.1, ?_⟩
    change positivePower C r (positivePowerInverse C r z) ∈ s
    rw [positivePower_inverse hC hr hz.1]
    exact hz.2
  · intro hy
    refine ⟨positivePower C r y, ⟨positivePower_pos hC hy.1, hy.2⟩, ?_⟩
    exact positivePowerInverse_power hC hr hy.1

/-- The exact positive-threshold CDF event relation for the scaled
power in Proposition 1's hidden-moment construction. -/
theorem positivePower_le_iff {C r y z : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hy : 0 < y) (hz : 0 < z) :
    positivePower C r y ≤ z ↔ y ≤ positivePowerInverse C r z := by
  calc
    _ ↔ positivePower C r y ≤ positivePower C r (positivePowerInverse C r z) := by
      rw [positivePower_inverse hC hr hz]
    _ ↔ _ := by
      change C * y ^ r ≤ C * (positivePowerInverse C r z) ^ r ↔ _
      rw [mul_le_mul_iff_right₀ hC,
        Real.rpow_le_rpow_iff hy.le (positivePowerInverse_pos hC hz).le hr]

/-- The inverse maps the actual density support (0,C) to (0,1).
This checks the upper endpoint in Proposition 1's finite correction. -/
theorem positivePowerInverse_lt_one_iff {C r z : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hz : 0 < z) :
    positivePowerInverse C r z < 1 ↔ z < C := by
  unfold positivePowerInverse
  calc
    _ ↔ (z / C) ^ (1 / r) < (1 : ℝ) ^ (1 / r) := by rw [Real.one_rpow]
    _ ↔ z / C < 1 := Real.rpow_lt_rpow_iff (div_pos hz hC).le zero_le_one (one_div_pos.mpr hr)
    _ ↔ _ := div_lt_one hC

example : 0 < positivePower 2 3 4 := positivePower_pos (by norm_num) (by norm_num)

example : 0 < positivePowerInverse 2 3 4 := positivePowerInverse_pos (by norm_num) (by norm_num)

example : positivePower 2 3 (positivePowerInverse 2 3 4) = 4 :=
  positivePower_inverse (by norm_num) (by norm_num) (by norm_num)

example : positivePowerInverse 2 3 (positivePower 2 3 4) = 4 :=
  positivePowerInverse_power (by norm_num) (by norm_num) (by norm_num)

example : MonotoneOn (positivePowerInverse 2 3) (Ioi 0) :=
  positivePowerInverse_monotoneOn (by norm_num) (by norm_num)

example : HasDerivAt (positivePowerInverse 2 3) (positivePowerJacobian 2 3 4) 4 :=
  positivePowerInverse_hasDerivAt (by norm_num) (by norm_num)

example : 0 < positivePowerJacobian 2 3 4 :=
  positivePowerJacobian_pos (by norm_num) (by norm_num) (by norm_num)

example : positivePowerInverse 2 3 '' (Ioi 0 ∩ Iic 4) = Ioi 0 ∩ positivePower 2 3 ⁻¹' Iic 4 :=
  positivePowerInverse_image (by norm_num) (by norm_num) _

example : positivePower 2 3 4 ≤ 5 ↔ 4 ≤ positivePowerInverse 2 3 5 :=
  positivePower_le_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : positivePowerInverse 2 3 1 < 1 ↔ (1 : ℝ) < 2 :=
  positivePowerInverse_lt_one_iff (by norm_num) (by norm_num) (by norm_num)

#print axioms positivePower_inverse
#print axioms positivePowerInverse_power
#print axioms positivePowerInverse_monotoneOn
#print axioms positivePowerInverse_hasDerivAt
#print axioms positivePowerJacobian_pos
#print axioms positivePowerInverse_image
#print axioms positivePower_le_iff
#print axioms positivePowerInverse_lt_one_iff

end TailOptionPricing
