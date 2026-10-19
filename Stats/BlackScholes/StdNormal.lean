module

/-
  Standard normal CDF `Φ` and its analytic relationships to the lognormal
  survival function:

  • `stdNormalCdf` definition + monotonicity / bounds / complement / symmetry.
  • Location-scale property `gaussianReal_map_locScale` and the standardisation
    `gaussianReal_real_Ioi_eq` that reduces `𝒩(μ, v)` tails to `𝒩(0, 1)` tails.
  • Bridge theorems `survivalLN_eq_one_sub_stdNormalCdf` and
    `survivalLN_eq_gaussianReal_real_Ioi`.
  • Exponential tilting / Esscher identity `gaussianPDFReal_exp_tilt`.
  • Mills' ratio bound `1 − Φ(c) ≤ φ(c) / c` and supporting derivatives /
    asymptotics.
  • The CDF derivative `stdNormalCdf_hasDerivAt`: `∂Φ/∂x = φ`.
-/
public import Stats.BlackScholes.Survival

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory in
/-- **Standard normal cumulative distribution function** `Φ(x) = ℙ(Z ≤ x)`,
    where `Z ∼ 𝒩(0, 1)`. -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Iic x)

open ProbabilityTheory in
theorem stdNormalCdf_nonneg (x : ℝ) : 0 ≤ stdNormalCdf x := measureReal_nonneg

open ProbabilityTheory in
theorem stdNormalCdf_le_one (x : ℝ) : stdNormalCdf x ≤ 1 := measureReal_le_one

open ProbabilityTheory in
theorem stdNormalCdf_monotone : Monotone stdNormalCdf :=
  fun _ _ h => measureReal_mono (Set.Iic_subset_Iic.mpr h)

open ProbabilityTheory MeasureTheory in
/-- **CDF as set integral of PDF.**  `Φ(q) = ∫_{-∞}^q φ(x) dx`. -/
theorem stdNormalCdf_eq_setIntegral_Iic (q : ℝ) :
    stdNormalCdf q = ∫ x in Set.Iic q, gaussianPDFReal 0 1 x ∂volume := by
  unfold stdNormalCdf
  show ((gaussianReal 0 1) (Set.Iic q)).toReal =
       ∫ x in Set.Iic q, gaussianPDFReal 0 1 x ∂volume
  rw [gaussianReal_apply_eq_integral _ one_ne_zero,
      ENNReal.toReal_ofReal (by
        apply MeasureTheory.setIntegral_nonneg measurableSet_Iic
        intro x _; exact gaussianPDFReal_nonneg 0 1 x)]

open ProbabilityTheory in
/-- The complement of the CDF: `ℙ(Z > c) = 1 - Φ(c)`. -/
theorem one_sub_stdNormalCdf (c : ℝ) :
    1 - stdNormalCdf c = (gaussianReal 0 1).real (Set.Ioi c) := by
  unfold stdNormalCdf
  have h_compl : (Set.Iic c)ᶜ = Set.Ioi c := by ext x; simp
  rw [← h_compl]
  have h_total : (gaussianReal 0 1).real (Set.Iic c) +
      (gaussianReal 0 1).real (Set.Iic c)ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl measurableSet_Iic, probReal_univ]
  linarith

open ProbabilityTheory MeasureTheory in
/-- **Standard normal symmetry.**  `Φ(-c) = 1 - Φ(c)`.  Follows from the fact
    that the standard Gaussian is symmetric about the origin. -/
theorem stdNormalCdf_neg (c : ℝ) : stdNormalCdf (-c) = 1 - stdNormalCdf c := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  -- Symmetry of `gaussianReal 0 1` under negation.
  have h_map : (gaussianReal 0 1).map (fun z : ℝ => -z) = gaussianReal 0 1 := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (-1)
    have h_arg_zero : (-1 : ℝ) * (0 : ℝ) = 0 := by ring
    have h_arg_var : (NNReal.mk ((-1 : ℝ) ^ 2) (sq_nonneg _) * 1 : ℝ≥0) = 1 := by
      rw [mul_one]; apply NNReal.eq
      show ((-1 : ℝ)) ^ 2 = (1 : ℝ); norm_num
    rw [h_arg_zero, h_arg_var] at h
    have h_fun : (fun z : ℝ => -z) = (fun z : ℝ => (-1 : ℝ) * z) := by
      funext z; ring
    rw [h_fun]; exact h
  -- Iic (-c) = (Ici c) under negation; (gaussianReal 0 1).real of complement.
  have h_iic_neg : (gaussianReal 0 1).real (Set.Iic (-c)) =
      (gaussianReal 0 1).real (Set.Ici c) := by
    have h_pre : (fun z : ℝ => -z) ⁻¹' Set.Iic (-c) = Set.Ici c := by
      ext z; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
      constructor <;> intro h <;> linarith
    rw [show (gaussianReal 0 1).real (Set.Iic (-c)) =
          ((gaussianReal 0 1).map (fun z : ℝ => -z)).real (Set.Iic (-c)) from
        by rw [h_map]]
    show (((gaussianReal 0 1).map (fun z : ℝ => -z)) (Set.Iic (-c))).toReal =
         ((gaussianReal 0 1) (Set.Ici c)).toReal
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic, h_pre]
  unfold stdNormalCdf
  rw [h_iic_neg]
  -- Ici c and Iic c partition (no atoms make Iio = Iic a.e.).
  have h_compl_eq : (Set.Ici c)ᶜ = Set.Iio c := by ext; simp
  have h_total : (gaussianReal 0 1).real (Set.Ici c) +
      (gaussianReal 0 1).real (Set.Iio c) = 1 := by
    rw [← h_compl_eq, measureReal_add_measureReal_compl measurableSet_Ici,
        probReal_univ]
  have h_iio_iic : (gaussianReal 0 1).real (Set.Iio c) =
      (gaussianReal 0 1).real (Set.Iic c) := by
    show ((gaussianReal 0 1) (Set.Iio c)).toReal =
         ((gaussianReal 0 1) (Set.Iic c)).toReal
    rw [measure_congr Iio_ae_eq_Iic]
  linarith

open ProbabilityTheory MeasureTheory in
/-- **Exponential tilting / Esscher identity for the Gaussian density.**  For
    `μ : ℝ`, `v : ℝ≥0` with `v ≠ 0`, and any real `t`, `x`:
        `exp(t·x) · φ_{μ,v}(x) = exp(μt + v·t²/2) · φ_{μ + v·t, v}(x)`.
    Multiplying a Gaussian density by `exp(t·x)` shifts the mean by `v·t` and
    scales by `exp(μt + v·t²/2)` (the Gaussian MGF at `t`).  This is the
    completing-the-square identity at the heart of the BS closed form. -/
theorem gaussianPDFReal_exp_tilt {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (t x : ℝ) :
    Real.exp (t * x) * gaussianPDFReal μ v x =
    Real.exp (μ * t + (v : ℝ) * t^2 / 2) *
      gaussianPDFReal (μ + (v : ℝ) * t) v x := by
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have hv_ne : ((v : ℝ)) ≠ 0 := hv_pos.ne'
  unfold gaussianPDFReal
  rw [show Real.exp (t * x) *
        ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
         Real.exp (-(x - μ)^2 / (2 * (v : ℝ)))) =
       ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        (Real.exp (t * x) * Real.exp (-(x - μ)^2 / (2 * (v : ℝ)))) from by ring]
  rw [show Real.exp (μ * t + (v : ℝ) * t^2 / 2) *
        ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
         Real.exp (-(x - (μ + (v : ℝ) * t))^2 / (2 * (v : ℝ)))) =
       ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        (Real.exp (μ * t + (v : ℝ) * t^2 / 2) *
         Real.exp (-(x - (μ + (v : ℝ) * t))^2 / (2 * (v : ℝ)))) from by ring]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

open ProbabilityTheory MeasureTheory in
/-- **Location-scale property of Gaussians.**  Pushing forward the standard
    normal `𝒩(0, 1)` through the affine map `z ↦ σ · z + μ` (with `σ = √v`)
    recovers the general Gaussian `𝒩(μ, v)`. -/
theorem gaussianReal_map_locScale {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z + μ) =
    gaussianReal μ v := by
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have hsqrt_pos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv_pos
  have hsqrt_sq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv_pos.le
  have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (v : ℝ))
  have h_zero : Real.sqrt (v : ℝ) * (0 : ℝ) = 0 := by ring
  have h_var : (NNReal.mk (Real.sqrt (v : ℝ) ^ 2) (sq_nonneg _) * 1 : ℝ≥0) = v := by
    rw [mul_one]
    apply NNReal.eq
    simp [hsqrt_sq]
  rw [h_zero, h_var] at h1
  have h2 := gaussianReal_map_add_const (μ := 0) (v := v) μ
  rw [zero_add] at h2
  have h_meas_mul : Measurable (fun z : ℝ => Real.sqrt (v : ℝ) * z) := by fun_prop
  have h_meas_add : Measurable (fun y : ℝ => y + μ) := by fun_prop
  rw [show (fun z : ℝ => Real.sqrt (v : ℝ) * z + μ) =
        (fun y : ℝ => y + μ) ∘ (fun z : ℝ => Real.sqrt (v : ℝ) * z) from rfl]
  rw [← Measure.map_map h_meas_add h_meas_mul, h1, h2]

open ProbabilityTheory MeasureTheory in
/-- **Standard normal reduction.**  For `X ∼ 𝒩(μ, v)` with `v ≠ 0`,
    `ℙ(X > c) = ℙ(Z > (c - μ) / σ)` where `Z ∼ 𝒩(0, 1)` and `σ = √v`. -/
theorem gaussianReal_real_Ioi_eq {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    (gaussianReal μ v).real (Set.Ioi c) =
    (gaussianReal 0 1).real (Set.Ioi ((c - μ) / Real.sqrt (v : ℝ))) := by
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have hsqrt_pos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv_pos
  have h_preimage : (fun z : ℝ => Real.sqrt (v : ℝ) * z + μ) ⁻¹' Set.Ioi c =
      Set.Ioi ((c - μ) / Real.sqrt (v : ℝ)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ioi]
    rw [div_lt_iff₀ hsqrt_pos]
    constructor <;> intro h <;> nlinarith [mul_comm (Real.sqrt (v : ℝ)) z]
  have h_map := gaussianReal_map_locScale (μ := μ) hv
  rw [show (gaussianReal μ v).real (Set.Ioi c) =
        ((gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z + μ)).real
          (Set.Ioi c) from by rw [h_map]]
  show (((gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z + μ))
      (Set.Ioi c)).toReal = ((gaussianReal 0 1) (Set.Ioi _)).toReal
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, h_preimage]

open ProbabilityTheory MeasureTheory in
/-- **Lognormal survival in standard-normal CDF form.**  For `v ≠ 0`,
    the lognormal tail equals `1 − Φ((log(s/S₀) − μ) / √v)`. -/
theorem survivalLN_eq_one_sub_stdNormalCdf {S₀ μ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (s : ℝ) :
    survivalLN S₀ μ v s =
    1 - stdNormalCdf ((Real.log (s / S₀) - μ) / Real.sqrt (v : ℝ)) := by
  have h_eq : survivalLN S₀ μ v s =
      (gaussianReal μ v).real (Set.Ioi (Real.log (s / S₀))) := by
    unfold survivalLN
    show ∫ x in Set.Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x =
         ((gaussianReal μ v) (Set.Ioi (Real.log (s / S₀)))).toReal
    rw [gaussianReal_apply_eq_integral _ hv,
        ENNReal.toReal_ofReal (by
          apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro x _; exact gaussianPDFReal_nonneg μ v x)]
  rw [h_eq, gaussianReal_real_Ioi_eq hv, ← one_sub_stdNormalCdf]

open ProbabilityTheory in
/-- **Survival = Gaussian-measure tail.**  For `v ≠ 0`, the lognormal survival
    is the `gaussianReal`-measure of the corresponding `Ioi` set. -/
theorem survivalLN_eq_gaussianReal_real_Ioi {S₀ μ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (s : ℝ) :
    survivalLN S₀ μ v s =
    (gaussianReal μ v).real (Set.Ioi (Real.log (s / S₀))) := by
  unfold survivalLN
  show ∫ x in Set.Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x =
       ((gaussianReal μ v) (Set.Ioi (Real.log (s / S₀)))).toReal
  rw [gaussianReal_apply_eq_integral _ hv,
      ENNReal.toReal_ofReal (by
        apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        intro x _; exact gaussianPDFReal_nonneg μ v x)]

/-! ### Mills' ratio for the standard normal.

    For `c > 0`, `1 - Φ(c) ≤ φ(c) / c`.  Sharper than the Markov / Chernoff
    bound used elsewhere in this file, and the analytic ingredient one needs
    to recover the explicit `erfc` form of Eq. (10). -/

open ProbabilityTheory MeasureTheory in
/-- **Antiderivative for `x · φ(x)`.**  Differentiating `-φ(x)` (the negative
    of the standard normal PDF) yields `x · φ(x)`. -/
theorem hasDerivAt_neg_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (fun y : ℝ => -gaussianPDFReal 0 1 y)
               (x * gaussianPDFReal 0 1 x) x := by
  have h_eq : ∀ y : ℝ, gaussianPDFReal 0 1 y =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y^2) / 2) := by
    intro y
    simp [gaussianPDFReal, NNReal.coe_one]
  set Cπ : ℝ := 1 / Real.sqrt (2 * Real.pi) with hCπ_def
  have h_inner : HasDerivAt (fun y : ℝ => -(y^2) / 2) (-x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y^2) (2 * x ^ 1) x := hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun y : ℝ => -(y^2)) (-(2 * x ^ 1)) x := h1.neg
    have h3 : HasDerivAt (fun y : ℝ => -(y^2) / 2) (-(2 * x ^ 1) / 2) x :=
      h2.div_const 2
    convert h3 using 1; ring
  have h_exp : HasDerivAt (fun y : ℝ => Real.exp (-(y^2) / 2))
      (-x * Real.exp (-(x^2) / 2)) x := by
    have h_chain := (Real.hasDerivAt_exp (-(x^2) / 2)).comp x h_inner
    convert h_chain using 1 <;> simp [Function.comp_def, mul_comm]
  have h_g : HasDerivAt (fun y : ℝ => Cπ * Real.exp (-(y^2) / 2))
      (Cπ * (-x * Real.exp (-(x^2) / 2))) x := h_exp.const_mul Cπ
  have h_neg_g : HasDerivAt (fun y : ℝ => -(Cπ * Real.exp (-(y^2) / 2)))
      (-(Cπ * (-x * Real.exp (-(x^2) / 2)))) x := h_g.neg
  have h_fun_eq : (fun y : ℝ => -(Cπ * Real.exp (-(y^2) / 2))) =
      (fun y : ℝ => -gaussianPDFReal 0 1 y) := by
    funext y; rw [h_eq y]
  have h_val_eq : -(Cπ * (-x * Real.exp (-(x^2) / 2))) =
      x * gaussianPDFReal 0 1 x := by
    rw [h_eq x]; ring
  rw [← h_fun_eq, ← h_val_eq]
  exact h_neg_g

open ProbabilityTheory MeasureTheory in
/-- The standard normal PDF tends to `0` at `+∞`. -/
theorem tendsto_gaussianPDFReal_std_atTop :
    Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  have h_eq : ∀ y : ℝ, gaussianPDFReal 0 1 y =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y^2) / 2) := by
    intro y; simp [gaussianPDFReal, NNReal.coe_one]
  have h_sq : Tendsto (fun y : ℝ => y^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_neg : Tendsto (fun y : ℝ => -(y^2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h_sq
  have h_inner : Tendsto (fun y : ℝ => -(y^2) / 2) atTop atBot :=
    h_neg.atBot_div_const (by norm_num : (0:ℝ) < 2)
  have h_exp : Tendsto (fun y : ℝ => Real.exp (-(y^2) / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_inner
  have h_const : Tendsto (fun y : ℝ => (1 / Real.sqrt (2 * Real.pi)) *
      Real.exp (-(y^2) / 2)) atTop (𝓝 ((1 / Real.sqrt (2 * Real.pi)) * 0)) :=
    tendsto_const_nhds.mul h_exp
  rw [mul_zero] at h_const
  refine h_const.congr ?_
  intro y; exact (h_eq y).symm

open ProbabilityTheory MeasureTheory in
/-- **Mills' ratio bound for the standard normal.**  For `c > 0`,
        `1 - Φ(c) ≤ φ(c) / c`,
    where `Φ = stdNormalCdf` is the standard normal CDF and
    `φ = gaussianPDFReal 0 1` is its PDF.  This is the standard one-sided
    Gaussian tail bound, sharper than the Markov / Chernoff bound on the
    quadratic moment. -/
theorem stdNormal_mills_ratio {c : ℝ} (hc : 0 < c) :
    1 - stdNormalCdf c ≤ gaussianPDFReal 0 1 c / c := by
  rw [one_sub_stdNormalCdf]
  have h_meas_eq : (gaussianReal 0 1).real (Set.Ioi c) =
      ∫ x in Set.Ioi c, gaussianPDFReal 0 1 x := by
    show ((gaussianReal 0 1) (Set.Ioi c)).toReal =
         ∫ x in Set.Ioi c, gaussianPDFReal 0 1 x
    rw [gaussianReal_apply_eq_integral _ (one_ne_zero),
        ENNReal.toReal_ofReal (by
          apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro x _; exact gaussianPDFReal_nonneg 0 1 x)]
  rw [h_meas_eq]
  have h_antideriv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -gaussianPDFReal 0 1 y)
      (x * gaussianPDFReal 0 1 x) x := hasDerivAt_neg_gaussianPDFReal_std
  have h_tendsto_neg_pdf : Tendsto (fun x : ℝ => -gaussianPDFReal 0 1 x)
      atTop (𝓝 0) := by simpa using tendsto_gaussianPDFReal_std_atTop.neg
  have h_nonneg : ∀ x ∈ Set.Ioi c, 0 ≤ x * gaussianPDFReal 0 1 x := by
    intro x hx
    have hx_pos : 0 < x := lt_trans hc hx
    exact mul_nonneg hx_pos.le (gaussianPDFReal_nonneg 0 1 x)
  have h_int_xφ : IntegrableOn (fun x : ℝ => x * gaussianPDFReal 0 1 x)
      (Set.Ioi c) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg ?_ ?_ h_nonneg h_tendsto_neg_pdf
    · exact ((h_antideriv c).continuousAt).continuousWithinAt
    · intro x _; exact h_antideriv x
  have h_integral_xφ : ∫ x in Set.Ioi c, x * gaussianPDFReal 0 1 x =
      gaussianPDFReal 0 1 c := by
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun y => -gaussianPDFReal 0 1 y) (a := c) (m := 0)
      (f' := fun x => x * gaussianPDFReal 0 1 x)
      ((h_antideriv c).continuousAt.continuousWithinAt)
      (fun x _ => h_antideriv x) h_int_xφ h_tendsto_neg_pdf
    rw [hFTC]; ring
  have h_int_const_mul : IntegrableOn
      (fun x : ℝ => (1 / c) * (x * gaussianPDFReal 0 1 x))
      (Set.Ioi c) volume := h_int_xφ.const_mul (1 / c)
  have h_eq_div : (fun x : ℝ => (x / c) * gaussianPDFReal 0 1 x) =
      (fun x : ℝ => (1 / c) * (x * gaussianPDFReal 0 1 x)) := by
    funext x; ring
  have h_int_div : IntegrableOn
      (fun x : ℝ => (x / c) * gaussianPDFReal 0 1 x)
      (Set.Ioi c) volume := by rw [h_eq_div]; exact h_int_const_mul
  have h_pointwise : ∀ x ∈ Set.Ioi c,
      gaussianPDFReal 0 1 x ≤ (x / c) * gaussianPDFReal 0 1 x := by
    intro x hx
    have hx_gt : c < x := hx
    have h_ratio : 1 ≤ x / c := (one_le_div hc).mpr hx_gt.le
    nlinarith [gaussianPDFReal_nonneg 0 1 x]
  calc ∫ x in Set.Ioi c, gaussianPDFReal 0 1 x
      ≤ ∫ x in Set.Ioi c, (x / c) * gaussianPDFReal 0 1 x := by
        exact setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          h_int_div measurableSet_Ioi h_pointwise
    _ = (1 / c) * ∫ x in Set.Ioi c, x * gaussianPDFReal 0 1 x := by
        rw [h_eq_div, integral_const_mul]
    _ = (1 / c) * gaussianPDFReal 0 1 c := by rw [h_integral_xφ]
    _ = gaussianPDFReal 0 1 c / c := by ring

open ProbabilityTheory MeasureTheory in
/-- **Derivative of the standard normal CDF.**  `Φ` is differentiable
    everywhere, with derivative `φ`:
        `∂/∂x[Φ(x)] = φ(x) = gaussianPDFReal 0 1 x`.
    Foundational for the strike-derivative-style Greeks that go beyond the
    layer-cake `∂BSC/∂K` (e.g. `Delta`, `Vega`, etc.). -/
theorem stdNormalCdf_hasDerivAt (x : ℝ) :
    HasDerivAt stdNormalCdf (gaussianPDFReal 0 1 x) x := by
  have h_cdf_eq : stdNormalCdf =
      fun c => 1 - (gaussianReal 0 1).real (Set.Ioi c) := by
    funext c; linarith [one_sub_stdNormalCdf c]
  rw [h_cdf_eq]
  have h_int_eq : ∀ c : ℝ, (gaussianReal 0 1).real (Set.Ioi c) =
      ∫ t in Set.Ioi c, gaussianPDFReal 0 1 t ∂volume := by
    intro c
    show ((gaussianReal 0 1) (Set.Ioi c)).toReal =
         ∫ t in Set.Ioi c, gaussianPDFReal 0 1 t ∂volume
    rw [gaussianReal_apply_eq_integral _ one_ne_zero,
        ENNReal.toReal_ofReal (by
          apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro t _; exact gaussianPDFReal_nonneg 0 1 t)]
  have h_eq_int : (fun c : ℝ => 1 - (gaussianReal 0 1).real (Set.Ioi c)) =
      (fun c => 1 - ∫ t in Set.Ioi c, gaussianPDFReal 0 1 t ∂volume) := by
    funext c; rw [h_int_eq]
  rw [h_eq_int]
  have h_pdf_int : Integrable (gaussianPDFReal 0 1) :=
    integrable_gaussianPDFReal 0 1
  have h_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal; fun_prop
  have hx_lt : x - 1 < x := by linarith
  have h_FTC : HasDerivAt
      (fun c : ℝ => ∫ t in Set.Ioi c, gaussianPDFReal 0 1 t ∂volume)
      (-(gaussianPDFReal 0 1 x)) x :=
    hasDerivAt_integral_Ioi hx_lt h_pdf_int.integrableOn h_pdf_cont.continuousOn
  have h_const_sub := h_FTC.const_sub 1
  simpa using h_const_sub

/-! ### Prerequisites for the standard normal quantile (inverse CDF). -/

open ProbabilityTheory in
/-- `gaussianPDFReal 0 1` is strictly positive everywhere. -/
theorem gaussianPDFReal_std_pos (x : ℝ) : 0 < gaussianPDFReal 0 1 x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

/-- `stdNormalCdf` is strictly monotone. -/
theorem stdNormalCdf_strictMono : StrictMono stdNormalCdf :=
  strictMono_of_hasDerivAt_pos stdNormalCdf_hasDerivAt gaussianPDFReal_std_pos

open ProbabilityTheory MeasureTheory in
/-- `stdNormalCdf` tends to 1 at `+∞`. -/
theorem tendsto_stdNormalCdf_atTop_one :
    Tendsto stdNormalCdf atTop (𝓝 1) := by
  have h_meas : Tendsto (fun x : ℝ => (gaussianReal 0 1) (Set.Iic x))
      atTop (𝓝 ((gaussianReal 0 1) Set.univ)) :=
    tendsto_measure_Iic_atTop (gaussianReal 0 1)
  have h_univ : (gaussianReal 0 1) Set.univ = 1 := measure_univ
  rw [h_univ] at h_meas
  have h_one_ne_top : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
  have h_toReal :
      Tendsto (fun x : ℝ => ((gaussianReal 0 1) (Set.Iic x)).toReal) atTop
        (𝓝 ((1 : ENNReal).toReal)) :=
    (ENNReal.tendsto_toReal h_one_ne_top).comp h_meas
  have h_simp : ((1 : ENNReal).toReal : ℝ) = (1 : ℝ) := by simp
  rw [h_simp] at h_toReal
  -- `stdNormalCdf x = ((gaussianReal 0 1) (Iic x)).toReal` by `rfl`.
  exact h_toReal

open ProbabilityTheory MeasureTheory in
/-- `stdNormalCdf` tends to 0 at `-∞`. -/
theorem tendsto_stdNormalCdf_atBot_zero :
    Tendsto stdNormalCdf atBot (𝓝 0) := by
  -- Strategy: stdNormalCdf y = 1 - stdNormalCdf (-y) (from stdNormalCdf_neg with c := -y),
  -- and as y → -∞, -y → +∞ so stdNormalCdf (-y) → 1, giving stdNormalCdf y → 0.
  have h_atTop : Tendsto stdNormalCdf atTop (𝓝 1) := tendsto_stdNormalCdf_atTop_one
  have h_neg_atTop : Tendsto (fun y : ℝ => -y) atBot atTop := tendsto_neg_atBot_atTop
  have h_comp : Tendsto (fun y : ℝ => stdNormalCdf (-y)) atBot (𝓝 1) :=
    h_atTop.comp h_neg_atTop
  have h_sub : Tendsto (fun y : ℝ => 1 - stdNormalCdf (-y)) atBot (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub h_comp
  rw [sub_self] at h_sub
  -- Reinterpret `1 - stdNormalCdf (-y) = stdNormalCdf y` via stdNormalCdf_neg.
  have h_eq : ∀ y : ℝ, 1 - stdNormalCdf (-y) = stdNormalCdf y := by
    intro y
    have h := stdNormalCdf_neg (-y)
    rw [neg_neg] at h
    linarith
  refine h_sub.congr ?_
  intro y; exact h_eq y

open ProbabilityTheory MeasureTheory in
/-- The range of `stdNormalCdf` is exactly `Set.Ioo 0 1`. -/
theorem range_stdNormalCdf : Set.range stdNormalCdf = Set.Ioo (0:ℝ) 1 := by
  have h_cont : Continuous stdNormalCdf :=
    continuous_iff_continuousAt.mpr fun x => (stdNormalCdf_hasDerivAt x).continuousAt
  apply Set.eq_of_subset_of_subset
  · -- range ⊆ Ioo 0 1: from strict monotonicity + nonneg/le_one bounds.
    rintro u ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · -- If stdNormalCdf x = 0, then stdNormalCdf (x-1) < 0 by strict mono,
      -- contradicting nonneg.
      by_contra h_le
      have h_le' : stdNormalCdf x ≤ 0 := not_lt.mp h_le
      have h_zero : stdNormalCdf x = 0 := le_antisymm h_le' (stdNormalCdf_nonneg x)
      have h_lt : stdNormalCdf (x - 1) < stdNormalCdf x :=
        stdNormalCdf_strictMono (by linarith)
      rw [h_zero] at h_lt
      exact absurd (stdNormalCdf_nonneg (x - 1)) (not_le.mpr h_lt)
    · -- Symmetric upper bound.
      by_contra h_ge
      have h_ge' : 1 ≤ stdNormalCdf x := not_lt.mp h_ge
      have h_one : stdNormalCdf x = 1 := le_antisymm (stdNormalCdf_le_one x) h_ge'
      have h_lt : stdNormalCdf x < stdNormalCdf (x + 1) :=
        stdNormalCdf_strictMono (by linarith)
      rw [h_one] at h_lt
      exact absurd (stdNormalCdf_le_one (x + 1)) (not_le.mpr h_lt)
  · -- Ioo 0 1 ⊆ range stdNormalCdf: IVT.
    intro u hu
    have h_preconn : IsPreconnected (Set.univ : Set ℝ) := isPreconnected_univ
    have h_le_univ_bot : (Filter.atBot : Filter ℝ) ≤ Filter.principal Set.univ := by
      simp
    have h_le_univ_top : (Filter.atTop : Filter ℝ) ≤ Filter.principal Set.univ := by
      simp
    have h_cont_on : ContinuousOn stdNormalCdf Set.univ := h_cont.continuousOn
    have h_image_sub : Set.Ioo (0 : ℝ) 1 ⊆ stdNormalCdf '' Set.univ :=
      h_preconn.intermediate_value_Ioo h_le_univ_bot h_le_univ_top h_cont_on
        tendsto_stdNormalCdf_atBot_zero tendsto_stdNormalCdf_atTop_one
    obtain ⟨x, _, hx⟩ := h_image_sub hu
    exact ⟨x, hx⟩

/-- `stdNormalCdf` is strictly positive. -/
theorem stdNormalCdf_pos (x : ℝ) : 0 < stdNormalCdf x := by
  have h : stdNormalCdf x ∈ Set.range stdNormalCdf := ⟨x, rfl⟩
  rw [range_stdNormalCdf] at h
  exact h.1

/-- `stdNormalCdf` is less than `1`. -/
theorem stdNormalCdf_lt_one (x : ℝ) : stdNormalCdf x < 1 := by
  have h : stdNormalCdf x ∈ Set.range stdNormalCdf := ⟨x, rfl⟩
  rw [range_stdNormalCdf] at h
  exact h.2

/-- **Standard normal quantile function (inverse CDF).**
For `u ∈ Set.Ioo 0 1`, `stdNormalQuantile u` is the unique `x : ℝ`
with `stdNormalCdf x = u`.  Outside `Ioo 0 1` the function returns a
junk value (zero), making the definition total.

Built using `Classical.choose` on the surjectivity of `stdNormalCdf`
onto `Ioo 0 1` (which follows from `range_stdNormalCdf`). -/
noncomputable def stdNormalQuantile (u : ℝ) : ℝ := by
  classical
  exact if h : u ∈ Set.range stdNormalCdf then h.choose else 0

/-- For any `u ∈ Set.range stdNormalCdf`, applying `stdNormalCdf` to
its quantile recovers `u`. -/
theorem stdNormalCdf_stdNormalQuantile {u : ℝ}
    (hu : u ∈ Set.range stdNormalCdf) :
    stdNormalCdf (stdNormalQuantile u) = u := by
  unfold stdNormalQuantile
  rw [dite_eq_left hu]
  exact hu.choose_spec

/-- The quantile is a left inverse of `stdNormalCdf`: for any `x : ℝ`,
`stdNormalQuantile (stdNormalCdf x) = x`.  Follows from injectivity
(strict monotonicity). -/
theorem stdNormalQuantile_stdNormalCdf (x : ℝ) :
    stdNormalQuantile (stdNormalCdf x) = x := by
  have h_mem : stdNormalCdf x ∈ Set.range stdNormalCdf := ⟨x, rfl⟩
  have h_inv := stdNormalCdf_stdNormalQuantile h_mem
  exact stdNormalCdf_strictMono.injective h_inv

/-- The quantile, applied to a value in `Set.Ioo 0 1`, is well-defined
and `stdNormalCdf` recovers the input. -/
theorem stdNormalCdf_stdNormalQuantile_of_mem_Ioo {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    stdNormalCdf (stdNormalQuantile u) = u := by
  apply stdNormalCdf_stdNormalQuantile
  rw [range_stdNormalCdf]
  exact hu

end TailOptionPricing
