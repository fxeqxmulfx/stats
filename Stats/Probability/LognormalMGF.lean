module

/-
  The actual lognormal exponential-moment domain, arXiv:1912.00277v2,
  Section VI. Lognormal survival dominates every exponential tail.
  A hypothetical finite positive exponential moment would give an
  incompatible Chernoff bound. Nonpositive arguments are independently
  integrable by positive support. Zero log variance is an actual atom
  and admits all exponential moments, so the boundary is explicit.
-/
public import Stats.Probability.GammaLognormalTail
public import Mathlib.Probability.Moments.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing.LognormalMeasure

/-- The zero-variance lognormal is an actual Dirac population. This
boundary is excluded from Section VI's continuous heavy-tail claim. -/
theorem lognormalReal_zero_var (m : ℝ) : lognormalReal m 0 = Measure.dirac (Real.exp m) := by
  rw [lognormalReal, gaussianReal_zero_var, Measure.map_dirac]

/-- Every exponential moment exists at zero log variance, independently
of the continuous-case nonintegrability argument (Section VI). -/
theorem lognormalReal_integrable_exp_mul_zero (m t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal m 0) := by
  rw [lognormalReal_zero_var]
  exact integrable_dirac enorm_lt_top

/-- The actual MGF at the atomic boundary is exp(t*exp(m)). -/
theorem mgf_lognormalReal_zero (m t : ℝ) :
    mgf (fun x : ℝ => x) (lognormalReal m 0) t = Real.exp (t * Real.exp m) := by
  rw [mgf, lognormalReal_zero_var, integral_dirac]

/-- Nonpositive exponential arguments are L1 under the actual positive
lognormal law, for any log variance. The independent bound is exp(t*x)<=1
on its proved positive support (Section VI). -/
theorem lognormalReal_integrable_exp_mul_of_nonpos (m : ℝ) (v : NNReal) {t : ℝ}
    (ht : t ≤ 0) : Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal m v) := by
  have hm : Measurable (fun x : ℝ => Real.exp (t * x)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [lognormalReal_ae_pos m v] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ht hx.le)

/-- Every strictly decreasing exponential tail is negligible compared
with the actual nondegenerate lognormal survival. This is the source's
slower-than-exponential claim for lognormal, with all domains explicit. -/
theorem lognormalReal_exponential_tail_ratio_tendsto_zero {m t : ℝ} {v : NNReal}
    (hv : v ≠ 0) (ht : 0 < t) :
    Tendsto (fun x => Real.exp (-t * x) / (lognormalReal m v).real (Ioi x))
      atTop (𝓝 0) := by
  apply (gamma_lognormal_tail_ratio_tendsto_zero
    (a := 1) (r := t) (m := m) (v := v) (by norm_num) ht hv).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [gammaMeasure_shape_one_survival ht hx, neg_mul]

/-- No positive exponential argument is L1 for a nondegenerate actual
lognormal population. A finite exponential moment would put its
survival below a multiple of exp(-t*x), contradicting the actual
tail ratio just proved (Section VI's heavy-tail classification). -/
theorem lognormalReal_not_integrable_exp_mul {m t : ℝ} {v : NNReal}
    (hv : v ≠ 0) (ht : 0 < t) :
    ¬Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal m v) := by
  intro hi
  let C : ℝ := mgf (fun x : ℝ => x) (lognormalReal m v) t
  have hb (x : ℝ) : (lognormalReal m v).real (Ioi x) ≤ Real.exp (-t * x) * C := by
    have h := measure_ge_le_exp_mul_mgf (X := fun y : ℝ => y)
      (μ := lognormalReal m v) x ht.le hi
    change (lognormalReal m v).real (Ici x) ≤ _ at h
    exact (measureReal_mono (show Ioi x ⊆ Ici x from fun _ hy => hy.le)).trans h
  have hl : Tendsto (fun x =>
      (Real.exp (-t * x) / (lognormalReal m v).real (Ioi x)) * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (lognormalReal_exponential_tail_ratio_tendsto_zero hv ht).mul_const C
  have hu : ∀ᶠ x in atTop,
      1 ≤ (Real.exp (-t * x) / (lognormalReal m v).real (Ioi x)) * C := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (lognormalReal_survival_pos hv hx)).mpr
      (by simpa only [one_mul] using hb x)
  obtain ⟨x, hx⟩ := (hu.and (hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))).exists
  exact (not_lt_of_ge hx.1) hx.2

/-- Every positive exponential moment fails for a nondegenerate
lognormal law, even though all its polynomial moments are finite. -/
theorem lognormalReal_no_positive_exponential_moment {m : ℝ} {v : NNReal} (hv : v ≠ 0) :
    ∀ t : ℝ, 0 < t → ¬Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal m v) :=
  fun _ ht => lognormalReal_not_integrable_exp_mul hv ht

/-- Exact exponential-moment integrability domain of the actual law:
all arguments at zero log variance, and only nonpositive arguments
otherwise. The source's continuous claim needs the nonzero boundary. -/
theorem lognormalReal_integrable_exp_mul_iff (m : ℝ) (v : NNReal) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal m v) ↔ v = 0 ∨ t ≤ 0 := by
  constructor
  · intro hi
    by_cases hv : v = 0
    · exact Or.inl hv
    · right
      by_contra! ht
      exact lognormalReal_not_integrable_exp_mul hv ht hi
  · rintro (hv | ht)
    · subst v
      exact lognormalReal_integrable_exp_mul_zero m t
    · exact lognormalReal_integrable_exp_mul_of_nonpos m v ht

/-- A strictly positive finite exponential moment exists precisely
at the atomic zero-variance boundary, not at any continuous lognormal. -/
theorem lognormalReal_has_positive_exponential_moment_iff (m : ℝ) (v : NNReal) :
    (∃ t : ℝ, 0 < t ∧ Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal m v)) ↔
      v = 0 := by
  constructor
  · rintro ⟨t, ht, hi⟩
    rcases (lognormalReal_integrable_exp_mul_iff m v t).mp hi with hv | hneg
    · exact hv
    · linarith
  · intro hv
    subst v
    exact ⟨1, by norm_num, lognormalReal_integrable_exp_mul_zero m 1⟩

example : lognormalReal 0 0 = Measure.dirac (Real.exp 0) := lognormalReal_zero_var 0

example : Integrable (fun x : ℝ => Real.exp (1 * x)) (lognormalReal 0 0) :=
  lognormalReal_integrable_exp_mul_zero 0 1

example : mgf (fun x : ℝ => x) (lognormalReal 0 0) 1 = Real.exp (1 * Real.exp 0) :=
  mgf_lognormalReal_zero 0 1

example : Integrable (fun x : ℝ => Real.exp (-1 * x)) (lognormalReal 0 1) :=
  lognormalReal_integrable_exp_mul_of_nonpos 0 1 (by norm_num)

example : Tendsto (fun x => Real.exp (-1 * x) / (lognormalReal 0 1).real (Ioi x))
    atTop (𝓝 0) := lognormalReal_exponential_tail_ratio_tendsto_zero (by norm_num) (by norm_num)

example : ¬Integrable (fun x : ℝ => Real.exp (1 * x)) (lognormalReal 0 1) :=
  lognormalReal_not_integrable_exp_mul (by norm_num) (by norm_num)

example : ∀ t : ℝ, 0 < t → ¬Integrable (fun x : ℝ => Real.exp (t * x)) (lognormalReal 0 1) :=
  lognormalReal_no_positive_exponential_moment (by norm_num)

#print axioms lognormalReal_integrable_exp_mul_of_nonpos
#print axioms lognormalReal_exponential_tail_ratio_tendsto_zero
#print axioms lognormalReal_not_integrable_exp_mul
#print axioms lognormalReal_integrable_exp_mul_iff
#print axioms lognormalReal_has_positive_exponential_moment_iff

end TailOptionPricing.LognormalMeasure
