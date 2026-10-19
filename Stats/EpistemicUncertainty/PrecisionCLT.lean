module

/-
  Corrected iid log-precision CLT, arXiv:1912.00277v2, Section V,
  following Eq. lerrornapprox. The printed uncentered Gaussian
  approximation is false. Here iid errors bounded uniformly away
  from -1 give square-integrable log factors. The ACTUAL product is
  centered by its log-factor mean, normalized by sqrt(n), and shown
  to converge in distribution to a genuine Gaussian with the actual
  log-factor variance. No log-linearization is used.
-/
public import Stats.EpistemicUncertainty.PrecisionErrors
public import Stats.EpistemicUncertainty.PrecisionLaw
public import Stats.EpistemicUncertainty.LogErrorMoments
public import Stats.EpistemicUncertainty
public import Mathlib.Probability.CentralLimitTheorem

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset Filter Topology

namespace TailOptionPricing

/-- A uniform signed-error radius below one bounds the actual log
factor, providing the moment assumption absent from Section V. -/
theorem epistemic_log_factor_abs_le {e r : ℝ} (hr : r < 1) (he : |e| ≤ r) :
    |Real.log (1 + e)| ≤ |Real.log (1 - r)| + |Real.log (1 + r)| := by
  obtain ⟨hl, hu⟩ := abs_le.mp he
  have hp : 0 < 1 + e := by linarith
  have hlo := Real.log_le_log (show 0 < 1 - r by linarith) (show 1 - r ≤ 1 + e by linarith)
  have hhi := Real.log_le_log hp (show 1 + e ≤ 1 + r by linarith)
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (1 - r)), abs_nonneg (Real.log (1 + r))]
  · linarith [le_abs_self (Real.log (1 + r)), abs_nonneg (Real.log (1 - r))]

/-- Section V with an explicit uniform bound: log factors are genuinely
in L2, derived from the error distribution rather than assumed moments. -/
theorem epistemic_log_factor_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Ω → ℝ) {r : ℝ}
    (hm : AEMeasurable E P) (hr : r < 1) (hb : ∀ᵐ ω ∂P, |E ω| ≤ r) :
    MemLp (fun ω => Real.log (1 + E ω)) 2 P := by
  have hlog : AEMeasurable (fun ω => Real.log (1 + E ω)) P := by fun_prop
  apply MemLp.of_bound hlog.aestronglyMeasurable
    (|Real.log (1 - r)| + |Real.log (1 + r)|)
  filter_upwards [hb] with ω hω
  exact epistemic_log_factor_abs_le hr hω

/-- Corrected Section V CLT for the actual precision product. Add iid
errors and a uniform bound |E_i| <= r < 1, derive log-factor L2, and
center by E[log(1+E_0)] rather than E[E_0]. After sqrt(n) normalization
the limit has the ACTUAL log-factor variance. The source's mean-zero
error assumption is unnecessary for this correctly centered result. -/
theorem epistemic_log_precision_CLT {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ℕ → Ω → ℝ) (lamHat : ℝ) {r : ℝ}
    (hLam : 0 < lamHat) (hr : r < 1) (hb : ∀ i, ∀ᵐ ω ∂P, |E i ω| ≤ r)
    (hi : iIndepFun E P) (hid : ∀ i, IdentDistrib (E i) (E 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
        (Real.log (lamHat * ∏ i ∈ Finset.range n, (1 + E i ω)) - Real.log lamHat -
          n * ∫ ω, Real.log (1 + E 0 ω) ∂P))
      atTop id (fun _ => P)
      (gaussianReal 0 (variance (fun ω => Real.log (1 + E 0 ω)) P).toNNReal) := by
  have hm : Measurable (fun e : ℝ => Real.log (1 + e)) := by fun_prop
  have hl2 := epistemic_log_factor_memLp P (E 0) (hid 0).aemeasurable_fst hr (hb 0)
  have hli : iIndepFun (fun i ω => Real.log (1 + E i ω)) P :=
    hi.comp (fun _ => fun e : ℝ => Real.log (1 + e)) (fun _ => hm)
  have hlid (i : ℕ) : IdentDistrib (fun ω => Real.log (1 + E i ω))
      (fun ω => Real.log (1 + E 0 ω)) P P := (hid i).comp hm
  have ht := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := P) (X := fun i ω => Real.log (1 + E i ω))
    (Y := id) (P' := gaussianReal 0 (variance (fun ω => Real.log (1 + E 0 ω)) P).toNNReal)
    HasLaw.id hl2 hli hlid
  have hp : ∀ᵐ ω ∂P, ∀ i : ℕ, 0 < 1 + E i ω := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hb i] with ω hω
    have he := (abs_le.mp hω).1
    linarith
  refine ht.congr (fun n => ?_) Filter.EventuallyEq.rfl
  filter_upwards [hp] with ω hω
  rw [log_multiplicative_error lamHat (fun i => E i ω) hLam (fun i _ => hω i)]
  ring

/-- The corrected CLT for the same actual signed iid precision process
that refutes the source's uncentered approximation. Its exact negative
centering is n*log(1-epsilon squared)/2; its Gaussian variance is the
proved actual log-factor variance, which is positive on this domain. -/
theorem epistemic_signed_log_precision_CLT (lamHat : ℝ) {ε : ℝ}
    (hLam : 0 < lamHat) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
        (Real.log (epistemicPrecisionVariable n lamHat ε ω) - Real.log lamHat -
          n * (Real.log (1 - ε ^ 2) / 2)))
      atTop id (fun _ => epistemicInfiniteSignLaw)
      (gaussianReal 0 (((Real.log (1 + ε) - Real.log (1 - ε)) / 2) ^ 2).toNNReal) := by
  have hb (i : ℕ) : ∀ᵐ ω ∂epistemicInfiniteSignLaw,
      |epistemicErrorVariable ε i ω| ≤ ε :=
    Filter.Eventually.of_forall (fun ω => by rw [epistemicErrorVariable_abs, abs_of_nonneg hε₀.le])
  have hid (i : ℕ) := (epistemicErrorVariable_hasLaw ε i).identDistrib
    (epistemicErrorVariable_hasLaw ε 0)
  have ht := epistemic_log_precision_CLT epistemicInfiniteSignLaw
    (epistemicErrorVariable ε) lamHat hLam hε₁ hb
    (epistemicErrorVariable_independent ε) hid
  have heq (n : ℕ) (ω : ℕ → Bool) : epistemicPrecisionVariable n lamHat ε ω =
      lamHat * ∏ i ∈ Finset.range n, (1 + epistemicErrorVariable ε i ω) := by
    unfold epistemicPrecisionVariable
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 + epistemicErrorVariable ε i ω) n]
  simpa only [heq,
    epistemicErrorVariable_log_mean_eq hε₀.le hε₁, epistemicErrorVariable_log_variance] using ht

/-- A genuine corrected lognormal limit for Section V: exponentiating
the CENTERED, sqrt(n)-normalized log precision converges to the
exponential of the Gaussian limit. The unnormalized precision is not
asserted to have a fixed lognormal limit. -/
theorem epistemic_signed_precision_normalized_lognormal_CLT (lamHat : ℝ) {ε : ℝ}
    (hLam : 0 < lamHat) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.exp ((√(n : ℝ))⁻¹ *
        (Real.log (epistemicPrecisionVariable n lamHat ε ω) - Real.log lamHat -
          n * (Real.log (1 - ε ^ 2) / 2))))
      atTop Real.exp (fun _ => epistemicInfiniteSignLaw)
      (gaussianReal 0 (((Real.log (1 + ε) - Real.log (1 - ε)) / 2) ^ 2).toNNReal) :=
  (epistemic_signed_log_precision_CLT lamHat hLam hε₀ hε₁).continuous_comp
    (g := Real.exp) Real.continuous_exp

example : |Real.log (1 - (1 / 100 : ℝ))| ≤
    |Real.log (1 - 1 / 100)| + |Real.log (1 + 1 / 100)| := by
  simpa only [neg_div, sub_eq_add_neg] using epistemic_log_factor_abs_le
    (e := (-1 / 100 : ℝ)) (r := (1 / 100 : ℝ)) (by norm_num) (by norm_num)

example : MemLp (fun ω => Real.log (1 + epistemicErrorVariable (1 / 100) 0 ω))
    2 epistemicInfiniteSignLaw := by
  apply epistemic_log_factor_memLp _ _
    (epistemicErrorVariable_hasLaw (1 / 100) 0).aemeasurable
    (r := (1 / 100 : ℝ)) (by norm_num)
  exact Filter.Eventually.of_forall (fun ω => by rw [epistemicErrorVariable_abs]; norm_num)

/-- A genuine nondegenerate mean-zero iid source model satisfying all
corrected CLT assumptions, on the previously constructed infinite space. -/
example : TendstoInDistribution
    (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      (Real.log (1 * ∏ i ∈ Finset.range n, (1 + epistemicErrorVariable (1 / 100) i ω)) -
        Real.log 1 - n * ∫ ω, Real.log (1 + epistemicErrorVariable (1 / 100) 0 ω)
          ∂epistemicInfiniteSignLaw))
    atTop id (fun _ => epistemicInfiniteSignLaw)
    (gaussianReal 0 (variance (fun ω => Real.log (1 + epistemicErrorVariable (1 / 100) 0 ω))
      epistemicInfiniteSignLaw).toNNReal) := by
  apply epistemic_log_precision_CLT _ _ _ (r := (1 / 100 : ℝ))
    (by norm_num) (by norm_num)
  · intro i
    exact Filter.Eventually.of_forall (fun ω => by rw [epistemicErrorVariable_abs]; norm_num)
  · exact epistemicErrorVariable_independent _
  · intro i
    exact (epistemicErrorVariable_hasLaw (1 / 100) i).identDistrib
      (epistemicErrorVariable_hasLaw (1 / 100) 0)

example : TendstoInDistribution
    (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      (Real.log (epistemicPrecisionVariable n 2 (1 / 100) ω) - Real.log 2 -
        n * (Real.log (1 - (1 / 100 : ℝ) ^ 2) / 2)))
    atTop id (fun _ => epistemicInfiniteSignLaw)
    (gaussianReal 0 (((Real.log (1 + (1 / 100 : ℝ)) - Real.log (1 - 1 / 100)) / 2) ^ 2).toNNReal) :=
  epistemic_signed_log_precision_CLT _ (by norm_num) (by norm_num) (by norm_num)

example : TendstoInDistribution
    (fun (n : ℕ) ω => Real.exp ((√(n : ℝ))⁻¹ *
      (Real.log (epistemicPrecisionVariable n 2 (1 / 100) ω) - Real.log 2 -
        n * (Real.log (1 - (1 / 100 : ℝ) ^ 2) / 2))))
    atTop Real.exp (fun _ => epistemicInfiniteSignLaw)
    (gaussianReal 0 (((Real.log (1 + (1 / 100 : ℝ)) - Real.log (1 - 1 / 100)) / 2) ^ 2).toNNReal) :=
  epistemic_signed_precision_normalized_lognormal_CLT _ (by norm_num) (by norm_num) (by norm_num)

#print axioms epistemic_log_factor_memLp
#print axioms epistemic_log_precision_CLT
#print axioms epistemic_signed_log_precision_CLT
#print axioms epistemic_signed_precision_normalized_lognormal_CLT

end TailOptionPricing
