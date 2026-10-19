module

/-
  Corrected equality characterization and strict payoff gap for actual laws.
  Source: arXiv:1907.11162v3, Definition 5. The fixed-density pointwise
  converse needs restrictions: under an a.e. one-sided payoff bound,
  equality characterizes an a.e. constant payoff on the measured tail.
-/
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual payoff gap as the expected excess above the threshold payoff
(arXiv:1907.11162v3, Definition 5). Tail integrability makes the subtraction valid. -/
theorem tailPayoff_gap_eq_integral (ν : Measure ℝ) [IsFiniteMeasure ν] {g : ℝ → ℝ} {K : ℝ}
    (hg : IntegrableOn g (Ioi K) ν) :
    (∫ x in Ioi K, g x ∂ν) - g K * ν.real (Ioi K) =
      ∫ x in Ioi K, g x - g K ∂ν := by
  rw [integral_sub hg (integrable_const _), setIntegral_const, smul_eq_mul, mul_comm]

/-- Corrected fixed-law converse to Definition 5 of arXiv:1907.11162v3.
Under a one-sided a.e. payoff bound, equality holds exactly when the
payoff equals its threshold value a.e. under the restricted tail law.
This does not assert pointwise constancy outside the measure support. -/
theorem tailPayoff_eq_binary_iff_ae_eq (ν : Measure ℝ) [IsFiniteMeasure ν] {g : ℝ → ℝ} {K : ℝ}
    (hg : IntegrableOn g (Ioi K) ν)
    (hmono : ∀ᵐ x ∂ν.restrict (Ioi K), g K ≤ g x) :
    (∫ x in Ioi K, g x ∂ν) = g K * ν.real (Ioi K) ↔
      ∀ᵐ x ∂ν.restrict (Ioi K), g x = g K := by
  have hd : Integrable (fun x => g x - g K) (ν.restrict (Ioi K)) :=
    hg.sub (integrable_const _)
  have hn : 0 ≤ᵐ[ν.restrict (Ioi K)] (fun x => g x - g K) :=
    hmono.mono (fun x hx => sub_nonneg.mpr hx)
  constructor
  · intro he
    have hz : (∫ x in Ioi K, g x - g K ∂ν) = 0 := by
      rw [← tailPayoff_gap_eq_integral ν hg, he, sub_self]
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hd).mp hz
    filter_upwards [hzero] with x hx
    exact sub_eq_zero.mp hx
  · intro he
    rw [integral_congr_ae he, setIntegral_const, smul_eq_mul, mul_comm]

/-- A strict payoff excess on a tail of positive actual probability
gives a strict actual expectation gap (arXiv:1907.11162v3, Definition 5).
The tail-mass condition rules out a vacuous empty tail. -/
theorem tailPayoff_strict_gap (ν : Measure ℝ) [IsFiniteMeasure ν] {g : ℝ → ℝ} {K : ℝ}
    (hg : IntegrableOn g (Ioi K) ν) (hprob : 0 < ν.real (Ioi K))
    (hstrict : ∀ᵐ x ∂ν.restrict (Ioi K), g K < g x) :
    g K * ν.real (Ioi K) < ∫ x in Ioi K, g x ∂ν := by
  have hmono := hstrict.mono (fun x hx => hx.le)
  have hn : 0 ≤ᵐ[ν.restrict (Ioi K)] (fun x => g x - g K) :=
    hmono.mono (fun x hx => sub_nonneg.mpr hx)
  have hge := integral_nonneg_of_ae hn
  rw [← tailPayoff_gap_eq_integral ν hg] at hge
  have hne : (∫ x in Ioi K, g x ∂ν) ≠ g K * ν.real (Ioi K) := by
    intro he
    have hae := (tailPayoff_eq_binary_iff_ae_eq ν hg hmono).mp he
    have hf : ∀ᵐ x ∂ν.restrict (Ioi K), False := by
      filter_upwards [hae, hstrict] with x he hs
      exact hs.ne' he
    have hz : ν (Ioi K) = 0 := by
      simpa only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] using ae_iff.mp hf
    have hr : ν.real (Ioi K) = 0 := by rw [measureReal_def, hz, ENNReal.toReal_zero]
    exact hprob.ne' hr
  exact lt_of_le_of_ne (sub_nonneg.mp hge) (Ne.symm hne)

/-- General strict-gap criterion under the one-sided payoff bound.
The actual excess expectation is strictly positive exactly when the
measured tail contains a positive-probability set of strict payoff excess
(arXiv:1907.11162v3, Definition 5 correction). -/
theorem tailPayoff_strict_gap_iff (ν : Measure ℝ) [IsFiniteMeasure ν] {g : ℝ → ℝ} {K : ℝ}
    (hg : IntegrableOn g (Ioi K) ν)
    (hmono : ∀ᵐ x ∂ν.restrict (Ioi K), g K ≤ g x) :
    g K * ν.real (Ioi K) < ∫ x in Ioi K, g x ∂ν ↔
      0 < (ν.restrict (Ioi K)).real {x | g K < g x} := by
  have hd : Integrable (fun x => g x - g K) (ν.restrict (Ioi K)) :=
    hg.sub (integrable_const _)
  have hn : 0 ≤ᵐ[ν.restrict (Ioi K)] (fun x => g x - g K) :=
    hmono.mono (fun x hx => sub_nonneg.mpr hx)
  rw [← sub_pos, tailPayoff_gap_eq_integral ν hg, integral_pos_iff_support_of_nonneg_ae hn hd]
  have he : Function.support (fun x => g x - g K) =ᵐ[ν.restrict (Ioi K)]
      {x | g K < g x} := by
    filter_upwards [hmono] with x hx
    change (g x - g K ≠ 0) = (g K < g x)
    apply propext
    constructor
    · intro he
      exact lt_of_le_of_ne hx (Ne.symm (sub_ne_zero.mp he))
    · intro he
      exact sub_ne_zero.mpr he.ne'
  rw [measure_congr he]
  change (0 < (ν.restrict (Ioi K)) {x | g K < g x}) ↔
    0 < ((ν.restrict (Ioi K)) {x | g K < g x}).toReal
  exact ⟨fun h => ENNReal.toReal_pos h.ne' (by finiteness),
    fun h => (ENNReal.toReal_pos_iff.mp h).1⟩

end TailOptionPricing
