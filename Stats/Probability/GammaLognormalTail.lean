module

/-
  Actual Gamma/lognormal tail domination, arXiv:1912.00277v2, Section VI.
  The proved hazards tend to the positive Gamma rate and zero. Their
  gap makes an exponentially weighted ratio of the actual survival
  probabilities eventually decreasing, proving that the ratio tends
  to zero. No coefficient-of-variation match or ordering is assumed.
-/
public import Stats.Probability.GammaHazard
public import Stats.Probability.LognormalHazard
public import Stats.BlackScholes.CallPrice.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

open LognormalMeasure

namespace LognormalMeasure

/-- The actual lognormal survival derivative on its positive domain.
The existing Black--Scholes pushforward at spot one is precisely the
canonical lognormalReal law (Section VI's hazard calculation). -/
theorem lognormalReal_survival_hasDerivAt {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => (lognormalReal m v).real (Ioi y))
      (-gaussianPDFReal m v (Real.log x) / x) x := by
  have he : survivalLN 1 m v = fun y => (lognormalReal m v).real (Ioi y) := by
    funext y
    simp only [survivalLN, lognormalLaw, lognormalReal, one_mul]
  have h := survivalLN_hasDerivAt (S₀ := 1) (μ := m) (by norm_num) hv hx
  rw [he, div_one] at h
  exact h

end LognormalMeasure

/-- Both actual populations have positive right survival at every
positive threshold, so their ratio is a genuine positive quantity. -/
theorem gamma_lognormal_tail_ratio_pos {a r m x : ℝ} {v : NNReal}
    (ha : 0 < a) (hr : 0 < r) (hv : v ≠ 0) (hx : 0 < x) :
    0 < (gammaMeasure a r).real (Ioi x) / (lognormalReal m v).real (Ioi x) :=
  div_pos (gammaMeasure_survival_pos ha hr hx) (lognormalReal_survival_pos hv hx)

/-- The derivative of the actual survival ratio is the ratio times
the lognormal-minus-Gamma hazard. Both denominator positivity and
survival derivatives have been proved for the population measures. -/
theorem gamma_lognormal_tail_ratio_hasDerivAt {a r m x : ℝ} {v : NNReal}
    (ha : 0 < a) (hr : 0 < r) (hv : v ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun y => (gammaMeasure a r).real (Ioi y) /
      (lognormalReal m v).real (Ioi y))
      ((lognormalHazard m v x - gammaHazard a r x) *
        ((gammaMeasure a r).real (Ioi x) / (lognormalReal m v).real (Ioi x))) x := by
  have hg := lognormalReal_survival_pos (m := m) hv hx
  have hf := gammaMeasure_survival_pos ha hr hx
  convert (gammaMeasure_survival_hasDerivAt ha hr hx).fun_div
    (lognormalReal_survival_hasDerivAt hv hx) hg.ne' using 1
  rw [gammaHazard, lognormalHazard_eq m v hx]
  field_simp [hg.ne', hf.ne', hx.ne']
  ring

/-- Every proper Gamma right tail is asymptotically negligible beside
every nondegenerate lognormal right tail (Section VI). The proof uses
actual survival probabilities, not just the numerical hazard limits. -/
theorem gamma_lognormal_tail_ratio_tendsto_zero {a r m : ℝ} {v : NNReal}
    (ha : 0 < a) (hr : 0 < r) (hv : v ≠ 0) :
    Tendsto (fun x => (gammaMeasure a r).real (Ioi x) /
      (lognormalReal m v).real (Ioi x)) atTop (𝓝 0) := by
  let q : ℝ → ℝ := fun x => (gammaMeasure a r).real (Ioi x) /
    (lognormalReal m v).real (Ioi x)
  let c : ℝ := r / 2
  have hc : 0 < c := half_pos hr
  have hq (x : ℝ) : 0 ≤ q x := div_nonneg measureReal_nonneg measureReal_nonneg
  have hgap : Tendsto (fun x => gammaHazard a r x - lognormalHazard m v x) atTop (𝓝 r) := by
    simpa only [sub_zero] using
      (gammaHazard_tendsto_rate ha hr).sub (lognormalHazard_tendsto_zero m hv)
  have hcsmall : c < r := by dsimp [c]; linarith
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hgap.eventually (lt_mem_nhds hcsmall))
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; have := le_max_right B 0; linarith
  have hBb : B < b := by dsimp [b]; have := le_max_left B 0; linarith
  let w : ℝ → ℝ := fun x => Real.exp (c * x) * q x
  have hw (x : ℝ) (hx : b < x) : HasDerivAt w
      (Real.exp (c * x) * (c - (gammaHazard a r x - lognormalHazard m v x)) * q x) x := by
    have hi : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul c
    convert hi.exp.fun_mul
      (gamma_lognormal_tail_ratio_hasDerivAt ha hr hv (hb.trans hx)) using 1
    dsimp [w, q]
    ring
  have hm : AntitoneOn w (Ioi b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x => Real.exp (c * x) *
        (c - (gammaHazard a r x - lognormalHazard m v x)) * q x) (convex_Ioi b)
    · exact fun x hx => (hw x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hw x (by simpa only [interior_Ioi, mem_Ioi] using hx)).hasDerivWithinAt
    · intro x hx
      have hxb : b < x := by simpa only [interior_Ioi, mem_Ioi] using hx
      have hcx : c < gammaHazard a r x - lognormalHazard m v x := hB x (hBb.le.trans hxb.le)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hcx.le)) (hq x)
  have hu : ∀ᶠ x in atTop, q x ≤ w (b + 1) * Real.exp (-(c * x)) := by
    filter_upwards [eventually_ge_atTop (b + 1)] with x hx
    have hwle := hm (show b + 1 ∈ Ioi b by simp)
      (show x ∈ Ioi b from lt_of_lt_of_le (by linarith : b < b + 1) hx) hx
    change Real.exp (c * x) * q x ≤ w (b + 1) at hwle
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hwle)
  have he : Tendsto (fun x : ℝ => Real.exp (-(c * x))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, mul_comm] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hc)
  exact squeeze_zero' (Eventually.of_forall hq) hu
    (by simpa only [mul_zero] using he.const_mul (w (b + 1)))

/-- In particular, the source's right-tail domination is an eventual
strict inequality between actual tail probabilities, for arbitrary
positive Gamma parameters and nondegenerate lognormal parameters. -/
theorem eventually_gamma_survival_lt_lognormal {a r m : ℝ} {v : NNReal}
    (ha : 0 < a) (hr : 0 < r) (hv : v ≠ 0) :
    ∀ᶠ x in atTop, (gammaMeasure a r).real (Ioi x) < (lognormalReal m v).real (Ioi x) := by
  have h := (gamma_lognormal_tail_ratio_tendsto_zero (m := m) ha hr hv).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hh hx
  exact (div_lt_one (lognormalReal_survival_pos hv hx)).mp hh

example : HasDerivAt (fun y => (lognormalReal 0 1).real (Ioi y))
    (-gaussianPDFReal 0 1 (Real.log 1) / 1) 1 :=
  lognormalReal_survival_hasDerivAt (by norm_num) (by norm_num)

example : 0 < (gammaMeasure 2 3).real (Ioi 1) / (lognormalReal 0 1).real (Ioi 1) :=
  gamma_lognormal_tail_ratio_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : HasDerivAt (fun y => (gammaMeasure 2 3).real (Ioi y) /
    (lognormalReal 0 1).real (Ioi y))
    ((lognormalHazard 0 1 1 - gammaHazard 2 3 1) *
      ((gammaMeasure 2 3).real (Ioi 1) / (lognormalReal 0 1).real (Ioi 1))) 1 :=
  gamma_lognormal_tail_ratio_hasDerivAt (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun x => (gammaMeasure 2 3).real (Ioi x) /
    (lognormalReal 0 1).real (Ioi x)) atTop (𝓝 0) :=
  gamma_lognormal_tail_ratio_tendsto_zero (by norm_num) (by norm_num) (by norm_num)

example : ∀ᶠ x in atTop, (gammaMeasure 2 3).real (Ioi x) < (lognormalReal 0 1).real (Ioi x) :=
  eventually_gamma_survival_lt_lognormal (by norm_num) (by norm_num) (by norm_num)

#print axioms LognormalMeasure.lognormalReal_survival_hasDerivAt
#print axioms gamma_lognormal_tail_ratio_pos
#print axioms gamma_lognormal_tail_ratio_hasDerivAt
#print axioms gamma_lognormal_tail_ratio_tendsto_zero
#print axioms eventually_gamma_survival_lt_lognormal

end TailOptionPricing
