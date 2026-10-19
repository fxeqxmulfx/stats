module

/-
  Actual log-factor moments in the iid precision model,
  arXiv:1912.00277v2, Section V, Eqs. lerrorn–lerrornapprox.
  Mean-zero signed errors have negative mean logarithms. The exact
  mean and variance below provide the corrected CLT centering and
  Gaussian variance; they are integrals of the actual probability law.
-/
public import Stats.EpistemicUncertainty.PrecisionErrors
public import Mathlib.Probability.IdentDistrib

@[expose] public section

open Real MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual expectation of the log factor under the normalized signed
error law (Section V); no mean-zero-log approximation is assumed. -/
theorem epistemicErrorLaw_log_mean (ε : ℝ) :
    (∫ e : ℝ, Real.log (1 + e) ∂epistemicErrorLaw ε) =
      (Real.log (1 + ε) + Real.log (1 - ε)) / 2 := by
  rw [epistemicErrorLaw, equalMixture_integral (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp only [integral_dirac, ← sub_eq_add_neg]

/-- Actual variance of the log factor for the source's signed iid
errors. This differs from the error variance epsilon squared. -/
theorem epistemicErrorLaw_log_variance (ε : ℝ) :
    variance (fun e : ℝ => Real.log (1 + e)) (epistemicErrorLaw ε) =
      ((Real.log (1 + ε) - Real.log (1 - ε)) / 2) ^ 2 := by
  have hm : AEMeasurable (fun e : ℝ => Real.log (1 + e)) (epistemicErrorLaw ε) := by fun_prop
  rw [variance_eq_integral hm, epistemicErrorLaw_log_mean]
  rw [epistemicErrorLaw, equalMixture_integral (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp only [integral_dirac, ← sub_eq_add_neg]
  ring

/-- The same actual log-factor mean on the single infinite iid sample
space used for the precision process (Section V). -/
theorem epistemicErrorVariable_log_mean (ε : ℝ) (i : ℕ) :
    (∫ ω : ℕ → Bool, Real.log (1 + epistemicErrorVariable ε i ω) ∂epistemicInfiniteSignLaw) =
      (Real.log (1 + ε) + Real.log (1 - ε)) / 2 := by
  have hm : Measurable (fun e : ℝ => Real.log (1 + e)) := by fun_prop
  exact ((epistemicErrorVariable_hasLaw ε i).integral_comp hm.aestronglyMeasurable).trans
    (epistemicErrorLaw_log_mean ε)

/-- Actual log-factor variance on the iid process, transferred by its
whole error law rather than by a supplied moment certificate. -/
theorem epistemicErrorVariable_log_variance (ε : ℝ) (i : ℕ) :
    variance (fun ω : ℕ → Bool => Real.log (1 + epistemicErrorVariable ε i ω))
      epistemicInfiniteSignLaw = ((Real.log (1 + ε) - Real.log (1 - ε)) / 2) ^ 2 := by
  have hm : Measurable (fun e : ℝ => Real.log (1 + e)) := by fun_prop
  have hi := (epistemicErrorVariable_hasLaw ε i).identDistrib (HasLaw.id (μ := epistemicErrorLaw ε))
  exact (hi.comp hm).variance_eq.trans (epistemicErrorLaw_log_variance ε)

/-- Section V's missing log centering: on the positive-factor domain,
the actual mean log increment is log(1-epsilon squared)/2. -/
theorem epistemicErrorVariable_log_mean_eq {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (i : ℕ) :
    (∫ ω : ℕ → Bool, Real.log (1 + epistemicErrorVariable ε i ω) ∂epistemicInfiniteSignLaw) =
      Real.log (1 - ε ^ 2) / 2 := by
  rw [epistemicErrorVariable_log_mean]
  have hp : 0 < 1 + ε := by linarith
  have hn : 0 < 1 - ε := by linarith
  have he : (1 + ε) * (1 - ε) = 1 - ε ^ 2 := by ring
  rw [← Real.log_mul hp.ne' hn.ne', he]

/-- Every nonzero signed error in (0,1), however small, creates a
strictly negative actual mean log factor. This is the missing drift
in Section V's proposed zero-centered Gaussian approximation. -/
theorem epistemicErrorVariable_log_mean_neg {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) (i : ℕ) :
    (∫ ω : ℕ → Bool, Real.log (1 + epistemicErrorVariable ε i ω) ∂epistemicInfiniteSignLaw) < 0 := by
  rw [epistemicErrorVariable_log_mean_eq hε₀.le hε₁]
  have hp : 0 < 1 - ε ^ 2 := by nlinarith
  have hu : 1 - ε ^ 2 < 1 := by nlinarith [sq_pos_of_pos hε₀]
  exact div_neg_of_neg_of_pos (Real.log_neg hp hu) (by norm_num)

/-- The corrected log-factor CLT has a genuinely positive Gaussian
variance for every nonzero admissible signed error (Section V). -/
theorem epistemicErrorVariable_log_variance_pos {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (i : ℕ) :
    0 < variance (fun ω : ℕ → Bool => Real.log (1 + epistemicErrorVariable ε i ω))
      epistemicInfiniteSignLaw := by
  rw [epistemicErrorVariable_log_variance]
  have hd : 0 < Real.log (1 + ε) - Real.log (1 - ε) :=
    sub_pos.mpr (Real.log_lt_log (by linarith) (by linarith))
  exact sq_pos_of_pos (div_pos hd (by norm_num))

example (i : ℕ) :
    (∫ ω : ℕ → Bool, Real.log (1 + epistemicErrorVariable (1 / 100) i ω)
      ∂epistemicInfiniteSignLaw) = Real.log (1 - (1 / 100 : ℝ) ^ 2) / 2 :=
  epistemicErrorVariable_log_mean_eq (by norm_num) (by norm_num) i

example (i : ℕ) :
    (∫ ω : ℕ → Bool, Real.log (1 + epistemicErrorVariable (1 / 100) i ω)
      ∂epistemicInfiniteSignLaw) < 0 :=
  epistemicErrorVariable_log_mean_neg (by norm_num) (by norm_num) i

example (i : ℕ) : 0 < variance
    (fun ω : ℕ → Bool => Real.log (1 + epistemicErrorVariable (1 / 100) i ω))
    epistemicInfiniteSignLaw :=
  epistemicErrorVariable_log_variance_pos (by norm_num) (by norm_num) i

#print axioms epistemicErrorVariable_log_mean
#print axioms epistemicErrorVariable_log_variance
#print axioms epistemicErrorVariable_log_mean_neg
#print axioms epistemicErrorVariable_log_variance_pos

end TailOptionPricing
