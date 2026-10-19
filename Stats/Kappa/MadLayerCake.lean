module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.MadLayerCake — Layer-cake identity for MAD.

  For an integrable real RV `X` with mean `m`,
      `𝔼|X − m| = 2 · ∫_{t > 0} ℙ(X > m + t) dt`.

  This is the *ascending* layer cake for `(X − m)⁺`, doubled by the
  symmetry `𝔼(X − m)⁺ = 𝔼(m − X)⁺` that holds when `m = 𝔼X`.

  We deliberately keep the integration on `Ioi 0` (with `m + t` inside
  the threshold) rather than translating to `Ioi m` — this avoids the
  measure-translation step and matches the form needed by the Loulakis
  argument in `Stats.Kappa.Lognormal.Loulakis`.

  Proof outline:

  1.  Write `|X − m| = (X − m)⁺ + (m − X)⁺` pointwise.
  2.  `𝔼(X − m)⁺ = 𝔼(m − X)⁺` when `𝔼X = m` (rearrangement of
      `𝔼(X − m) = 0 = 𝔼(X − m)⁺ − 𝔼(m − X)⁺`).
  3.  Apply Mathlib's `Integrable.integral_eq_integral_meas_lt`:
          `∫ (X − m)⁺ dμ = ∫_{t > 0} μ.real {ω | t < (X ω − m)⁺} dt`.
      Then `{ω | t < (X ω − m)⁺} = {ω | X ω > m + t}` for `t > 0`.
-/
public import Mathlib.MeasureTheory.Integral.Layercake
public import Stats.Kappa.IIdTriangle

@[expose] public section

open MeasureTheory Set Real

namespace TailOptionPricing.MadLayerCake

variable {Ω : Type*} {m_meas : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Step 1: pointwise `|x − m| = (x − m)⁺ + (m − x)⁺`. -/

private lemma abs_sub_eq_max_add_max (x m : ℝ) :
    |x - m| = max (x - m) 0 + max (m - x) 0 := by
  by_cases h : m ≤ x
  · have h1 : 0 ≤ x - m := by linarith
    have h2 : m - x ≤ 0 := by linarith
    rw [abs_of_nonneg h1, max_eq_left h1, max_eq_right h2, add_zero]
  · push Not at h
    have h1 : x - m < 0 := by linarith
    have h2 : 0 < m - x := by linarith
    rw [abs_of_neg h1, max_eq_right h1.le, max_eq_left h2.le, zero_add, neg_sub]

/-! ### Step 2: symmetry under the mean condition. -/

/-- **Pointwise decomposition `X − m = (X − m)⁺ − (m − X)⁺`**. -/
private lemma sub_eq_max_sub_max (x m : ℝ) :
    x - m = max (x - m) 0 - max (m - x) 0 := by
  by_cases h : m ≤ x
  · have h1 : 0 ≤ x - m := by linarith
    have h2 : m - x ≤ 0 := by linarith
    rw [max_eq_left h1, max_eq_right h2, sub_zero]
  · push Not at h
    have h1 : x - m < 0 := by linarith
    have h2 : 0 < m - x := by linarith
    rw [max_eq_right h1.le, max_eq_left h2.le, zero_sub]; linarith

/-- **Symmetric positive parts** of a centred integrable RV.  For `X`
    integrable with mean `m` (under a probability measure),
    `𝔼(X − m)⁺ = 𝔼(m − X)⁺`. -/
private lemma integral_pos_part_eq_neg_part
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (m : ℝ)
    (h_mean : (∫ ω, X ω ∂μ) = m) :
    ∫ ω, max (X ω - m) 0 ∂μ = ∫ ω, max (m - X ω) 0 ∂μ := by
  -- Integrability of the two positive parts.
  have hX_sub : Integrable (fun ω => X ω - m) μ := hX.sub (integrable_const _)
  have hm_sub : Integrable (fun ω => m - X ω) μ := (integrable_const _).sub hX
  have h_pos : Integrable (fun ω => max (X ω - m) 0) μ := hX_sub.pos_part
  have h_neg : Integrable (fun ω => max (m - X ω) 0) μ := hm_sub.pos_part
  -- Pointwise: X ω − m = max (X ω − m) 0 − max (m − X ω) 0.
  have h_decomp : (fun ω => X ω - m)
      = (fun ω => max (X ω - m) 0 - max (m - X ω) 0) := by
    funext ω; exact sub_eq_max_sub_max _ _
  -- Integrate.
  have h_int_zero : ∫ ω, X ω - m ∂μ = 0 := by
    rw [integral_sub hX (integrable_const _), h_mean, integral_const]
    simp
  rw [h_decomp, integral_sub h_pos h_neg] at h_int_zero
  linarith

/-! ### Step 3: layer cake for the positive part. -/

/-- **Layer cake for `(X − m)⁺`** in the `Ioi 0` form (no translation).
    For an integrable `X : Ω → ℝ` and any real `m`,
        `∫ (X − m)⁺ dμ = ∫_{t > 0} μ.real {ω | X ω > m + t} dt`. -/
theorem integral_pos_part_eq_tail_integral
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (m : ℝ) :
    ∫ ω, max (X ω - m) 0 ∂μ
      = ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω > m + t} := by
  -- `f ω := max (X ω − m) 0` is nonneg integrable.
  set f : Ω → ℝ := fun ω => max (X ω - m) 0 with hf_def
  have hX_sub : Integrable (fun ω => X ω - m) μ := hX.sub (integrable_const _)
  have hf_int : Integrable f μ := hX_sub.pos_part
  have hf_nn : 0 ≤ᵐ[μ] f := .of_forall fun ω => le_max_right _ _
  -- Apply Mathlib's ascending layer cake.
  rw [hf_int.integral_eq_integral_meas_lt hf_nn]
  -- Rewrite the indicator predicate: `t < (X ω − m)⁺ ↔ X ω > m + t` for `t > 0`.
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht_pos : 0 < t := ht
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, hf_def]
  constructor
  · intro h
    by_cases h' : 0 ≤ X ω - m
    · rw [max_eq_left h'] at h; linarith
    · push Not at h'
      rw [max_eq_right h'.le] at h; linarith
  · intro h
    have : 0 < X ω - m := by linarith
    rw [max_eq_left this.le]; linarith

/-! ### Step 3b: tail-integrability helper. -/

/-- **Measurability of the tail function** `t ↦ μ.real {X > t}`.
    Antitone in `t` (the larger `t`, the smaller the level set), hence
    measurable. -/
private lemma measurable_tail_real
    (X : Ω → ℝ) :
    Measurable (fun t : ℝ => μ.real {ω | X ω > t}) := by
  refine Measurable.ennreal_toReal ?_
  refine Antitone.measurable (fun s t (hst : s ≤ t) => ?_)
  refine measure_mono ?_
  intro ω (h : t < X ω)
  exact lt_of_le_of_lt hst h

/-- **Tail-integrability of `t ↦ μ.real {f > t}` on `Ioi 0`** for an
    integrable nonneg function `f`.  Auxiliary fact used to discharge
    integrability side-conditions for the Loulakis algebraic bound. -/
theorem integrableOn_measureReal_lt_Ioi
    {X : Ω → ℝ} (hX : Integrable X μ) (hX_nn : 0 ≤ᵐ[μ] X) :
    IntegrableOn (fun t : ℝ => μ.real {ω | X ω > t}) (Set.Ioi (0 : ℝ)) := by
  have h_meas : Measurable (fun t : ℝ => μ.real {ω | X ω > t}) :=
    measurable_tail_real X
  have h_nn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      fun t : ℝ => μ.real {ω | X ω > t} :=
    .of_forall (fun _ => ENNReal.toReal_nonneg)
  refine ⟨h_meas.aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal h_nn_ae]
  have h_lint_eq : ∫⁻ t in Set.Ioi (0:ℝ),
      ENNReal.ofReal (μ.real {ω | X ω > t}) ∂volume
      = ∫⁻ t in Set.Ioi (0:ℝ), μ {ω | t < X ω} ∂volume := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    show ENNReal.ofReal (μ {ω | X ω > t}).toReal = μ {ω | t < X ω}
    have h_lt : μ {ω | t < X ω} < ⊤ := hX.measure_gt_lt_top ht
    rw [ENNReal.ofReal_toReal h_lt.ne]
  rw [h_lint_eq]
  have key := lintegral_eq_lintegral_meas_lt μ hX_nn hX.aemeasurable
  rw [← key]
  exact Integrable.lintegral_lt_top hX

/-- **Tail-integrability of `(t ↦ μ.real {X > t})²` on `Ioi 0`** for an
    integrable nonneg `X` under a probability measure `μ`.  Bounded by
    the linear version since `μ.real ≤ 1` on a probability space. -/
theorem integrableOn_measureReal_lt_sq_Ioi
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (hX_nn : 0 ≤ᵐ[μ] X) :
    IntegrableOn (fun t : ℝ => (μ.real {ω | X ω > t}) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have h_lin := integrableOn_measureReal_lt_Ioi hX hX_nn
  refine h_lin.mono' ?_ ?_
  · exact ((measurable_tail_real X).pow_const 2).aestronglyMeasurable.restrict
  · refine .of_forall (fun t => ?_)
    have h_nn : 0 ≤ μ.real {ω | X ω > t} := ENNReal.toReal_nonneg
    have h_le_one : μ.real {ω | X ω > t} ≤ 1 := by
      rw [measureReal_def]
      have h1 : μ {ω | X ω > t} ≤ 1 := prob_le_one
      have h2 := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (by simp : (1 : ENNReal) ≠ ⊤)).mpr h1
      simpa using h2
    have h_sq_nn : 0 ≤ μ.real {ω | X ω > t} ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h_sq_nn, sq]
    exact mul_le_of_le_one_right h_nn h_le_one

/-! ### Main theorem. -/

/-- **MAD layer-cake identity** (paper-style, in `Ioi 0` form).
    For an integrable RV `X : Ω → ℝ` with mean `m` under a probability
    measure `μ`,
        `𝔼|X − m| = 2 · ∫_{t > 0} ℙ(X > m + t) dt`. -/
theorem mad_eq_two_tail_integral
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (m : ℝ)
    (h_mean : (∫ ω, X ω ∂μ) = m) :
    ∫ ω, |X ω - m| ∂μ
      = 2 * ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω > m + t} := by
  -- Step 1: |X - m| = (X-m)⁺ + (m-X)⁺ pointwise.
  have h_pointwise : (fun ω => |X ω - m|)
      = (fun ω => max (X ω - m) 0 + max (m - X ω) 0) := by
    funext ω; exact abs_sub_eq_max_add_max _ _
  rw [h_pointwise]
  -- Step 2: integrability of both parts.
  have hX_sub : Integrable (fun ω => X ω - m) μ := hX.sub (integrable_const _)
  have hm_sub : Integrable (fun ω => m - X ω) μ := (integrable_const _).sub hX
  have h_pos : Integrable (fun ω => max (X ω - m) 0) μ := hX_sub.pos_part
  have h_neg : Integrable (fun ω => max (m - X ω) 0) μ := hm_sub.pos_part
  -- Step 3: linearity.
  rw [integral_add h_pos h_neg]
  -- Step 4: symmetry — replace `∫ (m − X)⁺` with `∫ (X − m)⁺`.
  rw [← integral_pos_part_eq_neg_part hX m h_mean]
  -- Step 5: layer cake for the positive part.
  rw [integral_pos_part_eq_tail_integral hX m]
  ring

end TailOptionPricing.MadLayerCake
