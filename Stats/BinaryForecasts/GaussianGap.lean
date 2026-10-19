module

/-
  Corrected actual Gaussian payoff-gap sensitivity for arXiv:1907.11162v3,
  Definition 5 and Remark 1 / Eq. 8. The threshold factor K is retained.
  Derivatives, strict convexity and a two-scale Jensen inequality follow
  for the actual normalized Gaussian scale family and its density gap.
-/
public import Stats.BinaryForecasts.GaussianScale
public import Stats.BinaryForecasts.SigmaCounterexample
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

-- Chain-rule steps also used privately in SigmaSensitivity.lean.
private theorem gaussianScaleRatio_hasDerivAt {K σ : ℝ} (hσ : σ ≠ 0) :
    HasDerivAt (fun s : ℝ => K / s) (-K / σ ^ 2) σ := by
  convert (hasDerivAt_inv hσ).const_mul K using 1
  · funext s
    change K / s = K * s⁻¹
    exact div_eq_mul_inv _ _
  · ring

private theorem gaussianScalePDF_hasDerivAt {K σ : ℝ} (hσ : σ ≠ 0) :
    HasDerivAt (fun s : ℝ => gaussianPDFReal 0 1 (K / s))
      (K ^ 2 / σ ^ 3 * gaussianPDFReal 0 1 (K / σ)) σ := by
  have h := (gaussianPDFReal_std_hasDerivAt (K / σ)).comp σ
    (gaussianScaleRatio_hasDerivAt hσ)
  convert h using 1
  · rfl
  · field_simp

private theorem gaussianGapClosed_hasDerivAt {K σ : ℝ} (hσ : σ ≠ 0) :
    HasDerivAt (fun s : ℝ => s * gaussianPDFReal 0 1 (K / s) -
      K * (1 - stdNormalCdf (K / s))) (gaussianPDFReal 0 1 (K / σ)) σ := by
  have hA := (hasDerivAt_id σ).mul (gaussianScalePDF_hasDerivAt (K := K) hσ)
  have hB := ((stdNormalCdf_hasDerivAt (K / σ)).comp σ
    (gaussianScaleRatio_hasDerivAt hσ)).const_sub 1
  convert hA.sub (hB.const_mul K) using 1
  · rfl
  · dsimp only [id]
    field_simp
    ring

/-- Correct first scale derivative of the actual Definition 5 gap;
Eq. 8 omitted the threshold K from its tail-probability term. -/
theorem gaussianPayoffGap_hasDerivAt {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (gaussianPayoffGap K) (gaussianPDFReal 0 1 (K / σ)) σ := by
  apply (gaussianGapClosed_hasDerivAt (K := K) hσ.ne').congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hσ] with s hs
  exact gaussianPayoffGap_eq_closed hs K

/-- Correct second scale derivative of the actual gap, replacing the
printed A-B sensitivity by Definition 5's A-K*B (Remark 1 / Eq. 8). -/
theorem gaussianPayoffGap_deriv_hasDerivAt {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (deriv (gaussianPayoffGap K))
      (K ^ 2 / σ ^ 3 * gaussianPDFReal 0 1 (K / σ)) σ := by
  apply (gaussianScalePDF_hasDerivAt (K := K) hσ.ne').congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hσ] with s hs
  exact (gaussianPayoffGap_hasDerivAt (K := K) hs).deriv

/-- The corrected actual Gaussian gap has strictly positive second
scale derivative on the source's positive threshold and scale domain. -/
theorem gaussianPayoffGap_secondDeriv_pos {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) :
    0 < deriv (deriv (gaussianPayoffGap K)) σ := by
  rw [(gaussianPayoffGap_deriv_hasDerivAt (K := K) hσ).deriv]
  exact mul_pos (div_pos (pow_pos hK 2) (pow_pos hσ 3))
    (gaussianPDFReal_pos 0 1 _ one_ne_zero)

/-- Actual payoff discrepancy increases strictly with positive Gaussian
scale, for every fixed finite threshold (Remark 1's Gaussian case). -/
theorem gaussianPayoffGap_strictMonoOn (K : ℝ) :
    StrictMonoOn (gaussianPayoffGap K) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro σ hσ
    exact (gaussianPayoffGap_hasDerivAt (K := K) hσ).continuousAt.continuousWithinAt
  · intro σ hσ
    rw [interior_Ioi] at hσ
    rw [(gaussianPayoffGap_hasDerivAt (K := K) hσ).deriv]
    exact gaussianPDFReal_pos 0 1 _ one_ne_zero

/-- Strict convexity of the actual Gaussian gap in positive scale for
positive threshold, supplying the corrected Gaussian Jensen step. -/
theorem gaussianPayoffGap_strictConvexOn {K : ℝ} (hK : 0 < K) :
    StrictConvexOn ℝ (Ioi 0) (gaussianPayoffGap K) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi _)
  · intro σ hσ
    exact (gaussianPayoffGap_hasDerivAt (K := K) hσ).continuousAt.continuousWithinAt
  · intro σ hσ
    rw [interior_Ioi] at hσ
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      gaussianPayoffGap_secondDeriv_pos hK hσ

/-- Correct two-scale Jensen inequality for actual Gaussian payoff gaps
(Remark 1). Both scales are positive, distinct and equally weighted. -/
theorem gaussianPayoffGap_midpoint_lt {K a b : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    gaussianPayoffGap K ((a + b) / 2) <
      (gaussianPayoffGap K a + gaussianPayoffGap K b) / 2 := by
  have h := (gaussianPayoffGap_strictConvexOn hK).2 ha hb hab
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have he : (a + b) / 2 = (1 / 2 : ℝ) * a + (1 / 2) * b := by ring
  have hf : (gaussianPayoffGap K a + gaussianPayoffGap K b) / 2 =
      (1 / 2 : ℝ) * gaussianPayoffGap K a + (1 / 2) * gaussianPayoffGap K b := by ring
  rw [← he, ← hf] at h
  exact h

/-- Correct first derivative of the paper's original density I1-I2,
with its Definition 5 threshold factor retained (Remark 1). -/
theorem gaussianDensityPayoffGap_hasDerivAt {K σ : ℝ} (hK : 0 ≤ K) (hσ : 0 < σ) :
    HasDerivAt (fun s : ℝ => I1 id (gaussianPDF_σ s) K - I2 id (gaussianPDF_σ s) K)
      (gaussianPDFReal 0 1 (K / σ)) σ := by
  apply (gaussianPayoffGap_hasDerivAt (K := K) hσ).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hσ] with s hs
  exact gaussianDensityPayoffGap_eq_actual hs hK

/-- Correct second derivative of the original written density gap,
identified with the actual law before differentiation (Remark 1 / Eq. 8). -/
theorem gaussianDensityPayoffGap_deriv_hasDerivAt {K σ : ℝ} (hK : 0 ≤ K) (hσ : 0 < σ) :
    HasDerivAt (deriv (fun s : ℝ => I1 id (gaussianPDF_σ s) K - I2 id (gaussianPDF_σ s) K))
      (K ^ 2 / σ ^ 3 * gaussianPDFReal 0 1 (K / σ)) σ := by
  apply (gaussianScalePDF_hasDerivAt (K := K) hσ.ne').congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hσ] with s hs
  exact (gaussianDensityPayoffGap_hasDerivAt hK hs).deriv

example : HasDerivAt (gaussianPayoffGap 3) (gaussianPDFReal 0 1 (3 / 5)) 5 :=
  gaussianPayoffGap_hasDerivAt (by norm_num)

example : HasDerivAt (deriv (gaussianPayoffGap 3))
    ((9 / 125 : ℝ) * gaussianPDFReal 0 1 (3 / 5)) 5 := by
  have h := gaussianPayoffGap_deriv_hasDerivAt (K := 3) (σ := 5) (by norm_num)
  norm_num at h
  exact h

example : 0 < deriv (deriv (gaussianPayoffGap 3)) 5 :=
  gaussianPayoffGap_secondDeriv_pos (by norm_num) (by norm_num)

example : StrictConvexOn ℝ (Ioi 0) (gaussianPayoffGap 3) :=
  gaussianPayoffGap_strictConvexOn (by norm_num)

example : gaussianPayoffGap 3 5 < (gaussianPayoffGap 3 3 + gaussianPayoffGap 3 7) / 2 := by
  have h := gaussianPayoffGap_midpoint_lt (K := 3) (a := 3) (b := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : HasDerivAt (fun s : ℝ => I1 id (gaussianPDF_σ s) 3 - I2 id (gaussianPDF_σ s) 3)
    (gaussianPDFReal 0 1 (3 / 5)) 5 :=
  gaussianDensityPayoffGap_hasDerivAt (by norm_num) (by norm_num)

example : HasDerivAt
    (deriv (fun s : ℝ => I1 id (gaussianPDF_σ s) 3 - I2 id (gaussianPDF_σ s) 3))
    ((9 / 125 : ℝ) * gaussianPDFReal 0 1 (3 / 5)) 5 := by
  have h := gaussianDensityPayoffGap_deriv_hasDerivAt (K := 3) (σ := 5)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

-- The source's printed sensitivity and the corrected actual gap have opposite signs here.
example : (Real.exp (-(3 : ℝ) ^ 2 / (2 * 5 ^ 2)) *
    ((3 - 1) * 3 ^ 3 - (3 - 2) * 3 * 5 ^ 2) / (Real.sqrt (2 * Real.pi) * 5 ^ 5) < 0) ∧
    0 < deriv (deriv (gaussianPayoffGap 3)) 5 :=
  ⟨gaussianEq8_negative_at_three_five, gaussianPayoffGap_secondDeriv_pos (by norm_num) (by norm_num)⟩

#print axioms gaussianDensityPayoffGap_deriv_hasDerivAt
#print axioms gaussianPayoffGap_hasDerivAt
#print axioms gaussianPayoffGap_deriv_hasDerivAt
#print axioms gaussianPayoffGap_secondDeriv_pos
#print axioms gaussianPayoffGap_strictConvexOn
#print axioms gaussianPayoffGap_midpoint_lt

end TailOptionPricing
