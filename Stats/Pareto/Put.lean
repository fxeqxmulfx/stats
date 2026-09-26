/-
  Strong-Pareto core: Result 3 (put pricing) and density normalisation from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.Put — put pricing and density normalisation.

  Result 3 (Eq. 7, corrected): `putIntegrand`, `putRaw`, `putRaw_eq`,
  `putRaw_ratio`.  Density normalisation `λ` and the normalised
  `putPrice` follow.

  See `Stats/Pareto.lean` for the umbrella module.
-/
import Stats.Pareto.Basic

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Result 3.  Put pricing.

    Negative return `r := (S₀ − S)/S₀` is Pareto with index `α` and Karamata
    constant `l`; the un-normalized PDF of `S = (1 − r)S₀` is
        f̃_S(S) = α (l·S₀)^α / (S₀ − S)^(α+1),     S < (1 − l)S₀.
    The put price for strike `K ∈ (0, (1 − l)S₀]` (up to the normalising
    constant `λ`, which cancels in any ratio) is
        P(K) = ∫₀^K (K − S) f̃_S(S) dS.

    NB.  Eq. (7) in the paper has *two* typos.  Direct numerical integration
    with `S₀ = 2, α = 2, l = 0.1, K = 1` gives `0.01`; the printed formula
    yields `−0.02`.  Corrected formula uses `(S₀ − K)^(1 − α)` (positive base)
    and `S₀^(−α)` (correct exponent). -/

/-- Un-normalized put-price integrand `(K − S) · f̃_S(S)`. -/
noncomputable def putIntegrand (l α S₀ K S : ℝ) : ℝ :=
  (K - S) * (α * (l * S₀) ^ α / (S₀ - S) ^ (α + 1))

/-- Un-normalized put-price integral on `[0, K]`. -/
noncomputable def putRaw (l α S₀ K : ℝ) : ℝ :=
  ∫ S in (0:ℝ)..K, putIntegrand l α S₀ K S

/-- Antiderivative of `putIntegrand` on the open set where `S < S₀`. -/
private noncomputable def putAntideriv (l α S₀ K S : ℝ) : ℝ :=
  (l * S₀) ^ α * (K - S₀) * (S₀ - S) ^ (-α) +
    α * (l * S₀) ^ α * (S₀ - S) ^ (1 - α) / (α - 1)

private lemma hasDerivAt_putAntideriv {l α S₀ K S : ℝ} (hα : 1 < α)
    (hS₀_S : 0 < S₀ - S) :
    HasDerivAt (putAntideriv l α S₀ K) (putIntegrand l α S₀ K S) S := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hα_ne : (α : ℝ) ≠ 0 := by linarith
  have hS₀_S_ne : (S₀ - S) ≠ 0 := hS₀_S.ne'
  have h_base : HasDerivAt (fun S : ℝ => S₀ - S) (-1) S := by
    simpa using (hasDerivAt_id S).const_sub S₀
  have h_neg_α : HasDerivAt (fun S : ℝ => (S₀ - S) ^ (-α))
      (α * (S₀ - S) ^ (-α - 1)) S := by
    have := h_base.rpow_const (p := -α) (Or.inl hS₀_S_ne)
    convert this using 1
    rw [show (-α - 1 : ℝ) = (-α) - 1 from rfl]
    ring
  have h_one_α : HasDerivAt (fun S : ℝ => (S₀ - S) ^ (1 - α))
      ((α - 1) * (S₀ - S) ^ (-α)) S := by
    have := h_base.rpow_const (p := 1 - α) (Or.inl hS₀_S_ne)
    convert this using 1
    rw [show (1 - α - 1 : ℝ) = -α from by ring]
    ring
  have h_sum := (h_neg_α.const_mul ((l * S₀) ^ α * (K - S₀))).add
                  ((h_one_α.const_mul (α * (l * S₀) ^ α)).div_const (α - 1))
  convert h_sum using 1
  unfold putIntegrand
  have hpow_neg : (S₀ - S) ^ (-α - 1) = ((S₀ - S) ^ (α + 1))⁻¹ := by
    rw [show (-α - 1 : ℝ) = -(α + 1) from by ring, Real.rpow_neg hS₀_S.le]
  have hpow_neg_α : (S₀ - S) ^ (-α) = ((S₀ - S) ^ (α + 1))⁻¹ * (S₀ - S) := by
    rw [show (-α : ℝ) = -(α + 1) + 1 from by ring,
        Real.rpow_add hS₀_S, Real.rpow_one, Real.rpow_neg hS₀_S.le]
  rw [hpow_neg, hpow_neg_α]
  have hpow_pos : 0 < (S₀ - S) ^ (α + 1) := Real.rpow_pos_of_pos hS₀_S _
  have hpow_ne : (S₀ - S) ^ (α + 1) ≠ 0 := hpow_pos.ne'
  field_simp
  ring

private lemma continuousOn_putIntegrand {l α S₀ K : ℝ} (hK_lt_S₀ : K < S₀) :
    ContinuousOn (fun S => putIntegrand l α S₀ K S) (Set.Icc 0 K) := by
  unfold putIntegrand
  have h_pos : ∀ S ∈ Set.Icc (0:ℝ) K, 0 < S₀ - S :=
    fun S hS => by linarith [hS.2]
  have h_cont_base : ContinuousOn (fun S : ℝ => S₀ - S) (Set.Icc 0 K) := by fun_prop
  refine ContinuousOn.mul (by fun_prop) ?_
  refine ContinuousOn.div (by fun_prop) ?_ ?_
  · exact h_cont_base.rpow_const (fun S hS => Or.inl (h_pos S hS).ne')
  · intro S hS
    exact (Real.rpow_pos_of_pos (h_pos S hS) _).ne'

/-- **Result 3, Eq. (7), corrected.** Closed form of the (un-normalized) put
    integral. -/
theorem putRaw_eq {l α S₀ K : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK_pos : 0 < K) (hK_lt : K ≤ (1 - l) * S₀) :
    putRaw l α S₀ K =
      (l * S₀) ^ α / (α - 1) *
        ((S₀ - K) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K + S₀)) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hα_ne : (α : ℝ) ≠ 0 := by linarith
  have hS₀_ne : (S₀ : ℝ) ≠ 0 := hS₀.ne'
  have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  have hK_lt_S₀ : K < S₀ := by nlinarith
  have hS₀mK_pos : 0 < S₀ - K := sub_pos.mpr hK_lt_S₀
  have hS₀mK_ne : (S₀ - K) ≠ 0 := hS₀mK_pos.ne'
  have h_S₀mS_pos : ∀ S ∈ Set.uIcc (0:ℝ) K, 0 < S₀ - S := by
    intro S hS
    rw [Set.uIcc_of_le hK_pos.le] at hS
    linarith [hS.2]
  have hF_deriv : ∀ S ∈ Set.uIcc (0:ℝ) K,
      HasDerivAt (putAntideriv l α S₀ K) (putIntegrand l α S₀ K S) S :=
    fun S hS => hasDerivAt_putAntideriv hα (h_S₀mS_pos S hS)
  have hF_int : IntervalIntegrable (putIntegrand l α S₀ K) volume 0 K :=
    (continuousOn_putIntegrand hK_lt_S₀).intervalIntegrable_of_Icc hK_pos.le
  have hFTC : ∫ S in (0:ℝ)..K, putIntegrand l α S₀ K S =
      putAntideriv l α S₀ K K - putAntideriv l α S₀ K 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hF_int
  unfold putRaw
  rw [hFTC]
  unfold putAntideriv
  have h₁ : (S₀ - K) ^ (1 - α) = (S₀ - K) * (S₀ - K) ^ (-α) := by
    rw [show (1 - α : ℝ) = 1 + -α from by ring, Real.rpow_add hS₀mK_pos,
        Real.rpow_one]
  have h₂ : S₀ ^ (1 - α) = S₀ * S₀ ^ (-α) := by
    rw [show (1 - α : ℝ) = 1 + -α from by ring, Real.rpow_add hS₀, Real.rpow_one]
  have h_pow_S₀mK_neg : (S₀ - K) ^ (-α) ≠ 0 := (Real.rpow_pos_of_pos hS₀mK_pos _).ne'
  have h_pow_S₀_neg : S₀ ^ (-α) ≠ 0 := (Real.rpow_pos_of_pos hS₀ _).ne'
  simp only [sub_zero]
  rw [h₁, h₂]
  field_simp
  ring

/-- **Result 3, Eq. (7), corrected.** Relative put pricing: the ratio depends
    only on `α` and `S₀`, not on `l` or the normalising constant. -/
theorem putRaw_ratio {l α S₀ K₁ K₂ : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK₁_pos : 0 < K₁) (hK₂_pos : 0 < K₂)
    (hK₁_lt : K₁ ≤ (1 - l) * S₀) (hK₂_lt : K₂ ≤ (1 - l) * S₀) :
    putRaw l α S₀ K₂ * ((S₀ - K₁) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K₁ + S₀))
      = putRaw l α S₀ K₁ * ((S₀ - K₂) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K₂ + S₀)) := by
  rw [putRaw_eq hα hl hS₀ hK₁_pos hK₁_lt, putRaw_eq hα hl hS₀ hK₂_pos hK₂_lt]
  ring

/-! ### Density normalisation `λ` and the normalised put price.

    The un-normalised density `f̃_S(S) = α(l·S₀)^α / (S₀ − S)^(α+1)` integrates to
    `1 − l^α` over `[0, (1 − l)S₀]`.  Hence the proper normalisation is
    `λ = 1 / (1 − l^α)`, and the (true) put price is
        `P(K) = λ · putRaw(K)`.
    The normalisation cancels in `putRaw_ratio`, so this section is mostly
    "completeness". -/

/-- Total mass of the un-normalised put-side density on `[0, (1−l)S₀]`. -/
noncomputable def densityMass (l α S₀ : ℝ) : ℝ :=
  ∫ S in (0:ℝ)..(1-l)*S₀, α * (l * S₀) ^ α / (S₀ - S) ^ (α + 1)

/-- **Total mass identity.**  The un-normalised density integrates to `1 − l^α`. -/
theorem densityMass_eq {l α S₀ : ℝ} (hα : 1 < α) (hl : 0 < l) (hl_lt : l < 1)
    (hS₀ : 0 < S₀) :
    densityMass l α S₀ = 1 - l ^ α := by
  unfold densityMass
  have h_lt : 0 < (1-l)*S₀ := mul_pos (by linarith) hS₀
  have h_lt_S₀ : (1-l)*S₀ < S₀ := by nlinarith
  have h_lS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  -- Antiderivative `F(S) := (l·S₀)^α · (S₀ − S)^(−α)`.
  set F : ℝ → ℝ := fun S => (l * S₀) ^ α * (S₀ - S) ^ (-α) with hF_def
  have hF_deriv : ∀ S ∈ Set.uIcc (0:ℝ) ((1-l)*S₀),
      HasDerivAt F (α * (l * S₀) ^ α / (S₀ - S) ^ (α + 1)) S := by
    intro S hS
    rw [Set.uIcc_of_le h_lt.le] at hS
    have hS₀_S : 0 < S₀ - S := by linarith [hS.2, h_lt_S₀]
    have hS₀_S_ne : S₀ - S ≠ 0 := hS₀_S.ne'
    have h_base : HasDerivAt (fun S : ℝ => S₀ - S) (-1) S := by
      simpa using (hasDerivAt_id S).const_sub S₀
    have h_pow : HasDerivAt (fun S : ℝ => (S₀ - S) ^ (-α))
        (α * (S₀ - S) ^ (-α - 1)) S := by
      have := h_base.rpow_const (p := -α) (Or.inl hS₀_S_ne)
      convert this using 1; ring
    have h_F : HasDerivAt F ((l*S₀)^α * (α * (S₀-S)^(-α-1))) S :=
      h_pow.const_mul _
    convert h_F using 1
    rw [show ((-α - 1) : ℝ) = -(α + 1) from by ring, Real.rpow_neg hS₀_S.le]
    field_simp
  have hF_int : IntervalIntegrable
      (fun S => α * (l * S₀) ^ α / (S₀ - S) ^ (α + 1)) volume 0 ((1-l)*S₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_lt.le]
    intro S hS
    have hS₀_S : 0 < S₀ - S := by linarith [hS.2, h_lt_S₀]
    refine ContinuousAt.continuousWithinAt ?_
    apply ContinuousAt.div
    · fun_prop
    · exact ContinuousAt.rpow_const (by fun_prop) (Or.inl hS₀_S.ne')
    · exact (Real.rpow_pos_of_pos hS₀_S _).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hF_int]
  show (l * S₀) ^ α * (S₀ - (1-l)*S₀) ^ (-α) -
       (l * S₀) ^ α * (S₀ - 0) ^ (-α) = 1 - l ^ α
  rw [show (S₀ - (1-l)*S₀ : ℝ) = l*S₀ from by ring,
      show (S₀ - 0 : ℝ) = S₀ from by ring,
      show (l*S₀)^α * (l*S₀)^(-α) = 1 from by
        rw [← Real.rpow_add h_lS₀_pos]; simp [Real.rpow_zero],
      show (l*S₀)^α * S₀^(-α) = l^α from by
        rw [Real.rpow_neg hS₀.le, Real.mul_rpow hl.le hS₀.le]
        field_simp]

/-- The proper normalisation constant: `λ = 1 / (1 − l^α)`. -/
noncomputable def putNormConst (l α : ℝ) : ℝ := (1 - l ^ α)⁻¹

/-- **Normalised put price** `P(K) = λ · putRaw(K)`. -/
noncomputable def putPrice (l α S₀ K : ℝ) : ℝ :=
  putNormConst l α * putRaw l α S₀ K

/-- **Closed form of the normalised put price.** -/
theorem putPrice_eq {l α S₀ K : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK_pos : 0 < K) (hK_lt : K ≤ (1 - l) * S₀) :
    putPrice l α S₀ K =
      (l * S₀) ^ α / ((α - 1) * (1 - l ^ α)) *
        ((S₀ - K) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K + S₀)) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_pos : 0 < (1-l)*S₀ := lt_of_lt_of_le hK_pos hK_lt
  have hl_lt_one : l < 1 := by nlinarith [h_pos, hS₀]
  have hlα_lt_one : l ^ α < 1 :=
    Real.rpow_lt_one hl.le hl_lt_one (by linarith)
  have h_one_lα_ne : (1 - l ^ α : ℝ) ≠ 0 := by linarith
  unfold putPrice putNormConst
  rw [putRaw_eq hα hl hS₀ hK_pos hK_lt]
  field_simp


end TailOptionPricing
