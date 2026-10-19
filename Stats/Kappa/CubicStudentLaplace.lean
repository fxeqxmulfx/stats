module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.CubicStudentLaplace — Laplace asymptotic for `Γ(n+1, n)`.

  Discharges `incompleteGamma_laplace_asymptotic` (the axiom referenced in
  `CubicStudentAsymptotic.lean`):
      `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)` as `n → ∞`.

  Strategy (Loulakis-style + DCT):
  1.  Change of variable `t = n + u·√n` transforms the integral to
        `Γ(n+1, n) = √n · n^n · e^{-n} · ∫_0^∞ (1 + u/√n)^n · e^{-u·√n} du`.
  2.  Pointwise: `(1 + u/√n)^n · e^{-u·√n} → e^{-u²/2}` as `n → ∞`.
  3.  Dominator: `(1 + u/√n)^n · e^{-u·√n} ≤ e^{1 − u/4}` for `u ≥ 0`, `n ≥ 1`.
  4.  Dominator integrable on `Ioi 0`.
  5.  Lebesgue DCT: `∫_0^∞ (1 + u/√n)^n · e^{-u·√n} du → ∫_0^∞ e^{-u²/2} du
      = √(π/2)`.
-/
public import Stats.Kappa.CubicStudent
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing.CubicStudentLaplace

/-! ### The post-substitution integrand `G n u := (1 + u/√n)^n · e^{-u·√n}`. -/

/-- Integrand of the Laplace-substituted incomplete Gamma. -/
noncomputable def G (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u / Real.sqrt n) ^ n * Real.exp (-(u * Real.sqrt n))

/-! ### Sharp log bound `log(1+x) ≤ x − x²/(2(1+x))`. -/

/-- Sharp upper bound on `log(1+x)`:  for `x ≥ 0`,
    `log(1 + x) ≤ x − x²/(2(1+x))`.

    Proof: let `f(t) := t − t²/(2(1+t)) − log(1+t)`.  Then `f(0) = 0` and
    `f'(t) = t²/(2(1+t)²) ≥ 0` on `(0, ∞)`, so `f` is monotone on `[0,∞)`. -/
private lemma log_one_add_le_sub_sq_div (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x^2 / (2 * (1 + x)) := by
  set f : ℝ → ℝ := fun t => t - t^2 / (2 * (1 + t)) - Real.log (1 + t) with hf_def
  -- f'(t) = t²/(2(1+t)²)
  have hf_deriv : ∀ t ∈ Ioi (0:ℝ), HasDerivAt f (t^2 / (2 * (1 + t)^2)) t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have h1t_pos : 0 < 1 + t := by linarith
    have h1t_ne : (1 + t) ≠ 0 := h1t_pos.ne'
    have h21t_pos : 0 < 2 * (1 + t) := by positivity
    have h21t_ne : (2 : ℝ) * (1 + t) ≠ 0 := h21t_pos.ne'
    have hd1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have hd2 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using hd1.const_add (1 : ℝ)
    have hd_log : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      have h := (Real.hasDerivAt_log h1t_ne).comp t hd2
      convert h using 1 <;> simp [Function.comp_def]
    have hd_sq : HasDerivAt (fun s : ℝ => s^2) (2 * t) t := by
      have := hd1.pow 2
      convert this using 1 ; simp
    have hd_2_1t : HasDerivAt (fun s : ℝ => 2 * (1 + s)) (2 : ℝ) t := by
      have := hd2.const_mul (2 : ℝ)
      simpa using this
    -- Quotient rule: d/dt[t²/(2(1+t))]
    have hd_quot :
        HasDerivAt (fun s : ℝ => s^2 / (2 * (1 + s)))
          ((2 * t * (2 * (1 + t)) - t^2 * 2) / (2 * (1 + t))^2) t :=
      hd_sq.div hd_2_1t h21t_ne
    -- Simplify the derivative target
    have h_simp :
        (2 * t * (2 * (1 + t)) - t^2 * 2) / (2 * (1 + t))^2
        = (2 * t + t^2) / (2 * (1 + t)^2) := by
      field_simp; ring
    rw [h_simp] at hd_quot
    -- Combine: f' = 1 - (2t + t²)/(2(1+t)²) - 1/(1+t)
    have hf_combine := (hd1.sub hd_quot).sub hd_log
    -- Simplify result
    have h_target :
        1 - (2 * t + t^2) / (2 * (1 + t)^2) - 1 / (1 + t)
        = t^2 / (2 * (1 + t)^2) := by
      field_simp; ring
    rw [h_target] at hf_combine
    exact hf_combine
  -- f is monotone on Ici 0
  have h_mono : MonotoneOn f (Ici (0:ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · -- ContinuousOn
      have hpos_1t : ∀ t ∈ Ici (0:ℝ), (0:ℝ) < 1 + t := fun t ht => by
        have : (0:ℝ) ≤ t := ht; linarith
      have hcont_1t : ContinuousOn (fun t : ℝ => 1 + t) (Ici (0:ℝ)) :=
        continuousOn_const.add continuousOn_id
      refine ContinuousOn.sub ?_ ?_
      · refine ContinuousOn.sub continuousOn_id ?_
        refine ContinuousOn.div ?_ ?_ (fun t ht => ?_)
        · exact continuousOn_id.pow 2
        · exact continuousOn_const.mul hcont_1t
        · have := hpos_1t t ht
          have : (0:ℝ) < 2 * (1 + t) := by positivity
          exact this.ne'
      · refine ContinuousOn.log hcont_1t (fun t ht => (hpos_1t t ht).ne')
    · -- HasDerivWithinAt
      rw [interior_Ici]
      intro t ht
      exact (hf_deriv t ht).hasDerivWithinAt
    · -- non-neg derivative
      rw [interior_Ici]
      intro t ht
      have ht_pos : 0 < t := ht
      have h1t_pos : 0 < 1 + t := by linarith
      positivity
  -- Conclude
  have hf0 : f 0 = 0 := by
    show (0:ℝ) - 0^2 / (2 * (1+0)) - Real.log (1 + 0) = 0
    simp [Real.log_one]
  have h_le : f 0 ≤ f x := h_mono self_mem_Ici hx hx
  rw [hf0] at h_le
  -- f x ≥ 0 means x - x²/(2(1+x)) - log(1+x) ≥ 0 ⟹ log(1+x) ≤ x - x²/(2(1+x))
  have : (0:ℝ) ≤ x - x^2 / (2 * (1 + x)) - Real.log (1 + x) := h_le
  linarith

/-! ### Step C: Pointwise convergence `G n u → e^{−u²/2}`. -/

/-- **Pointwise convergence.**  For `u ≥ 0`,
        `(1 + u/√n)^n · e^{-u√n} → e^{-u²/2}` as `n → ∞`.

    Proof:  rewrite as `exp(n·log(1+u/√n) − u·√n)`; sandwich the exponent
    between `-u²/(u/√n + 2)` (using `2x/(x+2) ≤ log(1+x)`) and
    `-u²/(2(1+u/√n))` (using `log(1+x) ≤ x − x²/(2(1+x))`).  Both sides
    tend to `-u²/2`. -/
private lemma G_tendsto_pointwise (u : ℝ) (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => G n u) atTop (𝓝 (Real.exp (-(u^2/2)))) := by
  by_cases hu0 : u = 0
  · -- u = 0 case: G n 0 = 1 = exp(0)
    subst hu0
    have h_target : Real.exp (-((0:ℝ)^2/2)) = 1 := by simp
    rw [h_target]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with n _hn
    show (1:ℝ) = G n 0
    simp [G]
  have hu0' : u ≠ 0 := hu0
  clear hu0
  have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0')
  -- u/√n → 0
  have h_sqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_u_div_sqrt : Tendsto (fun n : ℕ => u / Real.sqrt n) atTop (𝓝 0) := by
    have h_inv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      h_sqrt_atTop.inv_tendsto_atTop
    have h_mul : Tendsto (fun n : ℕ => u * (Real.sqrt n)⁻¹) atTop (𝓝 (u * 0)) :=
      tendsto_const_nhds.mul h_inv
    rw [mul_zero] at h_mul
    refine h_mul.congr ?_
    intro n
    rw [div_eq_mul_inv]
  -- Define the exponent E n := n · log(1+u/√n) − u·√n
  set E : ℕ → ℝ := fun n => (n : ℝ) * Real.log (1 + u / Real.sqrt n) - u * Real.sqrt n with hE_def
  -- Step A: G n u = exp(E n) eventually (for n ≥ 1)
  have h_G_eq_exp_E : ∀ᶠ n in atTop, G n u = Real.exp (E n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have h1v_pos : 0 < 1 + u / Real.sqrt n := by positivity
    unfold G
    rw [show (1 + u / Real.sqrt n) ^ n =
            Real.exp ((n : ℝ) * Real.log (1 + u / Real.sqrt n)) from by
          rw [Real.exp_nat_mul, Real.exp_log h1v_pos]]
    rw [← Real.exp_add]
    refine congrArg Real.exp ?_
    show (n:ℝ) * Real.log (1 + u / Real.sqrt n) + -(u * Real.sqrt n) = E n
    rw [hE_def]
    show (n:ℝ) * Real.log (1 + u / Real.sqrt n) + -(u * Real.sqrt n) =
         (n:ℝ) * Real.log (1 + u / Real.sqrt n) - u * Real.sqrt n
    ring
  -- Step B: Lower bound `L n := -u²/(u/√n + 2) ≤ E n` for n ≥ 1
  have h_L_le_E : ∀ᶠ (n : ℕ) in atTop, -(u^2 / (u / Real.sqrt (n : ℝ) + 2)) ≤ E n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn_real_pos : (0 : ℝ) < n := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_real_pos
    have hs_ne : Real.sqrt (n : ℝ) ≠ 0 := hs_pos.ne'
    have hv_nn : 0 ≤ u / Real.sqrt (n : ℝ) := div_nonneg hu hs_pos.le
    have hs_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn_real_pos.le
    have h_log_lb := Real.le_log_one_add_of_nonneg hv_nn
    have h_n_mul := mul_le_mul_of_nonneg_left h_log_lb hn_real_pos.le
    have h_us_p2_pos : 0 < u / Real.sqrt (n : ℝ) + 2 := by linarith
    have h_us_p2_ne : (u / Real.sqrt (n : ℝ) + 2 : ℝ) ≠ 0 := h_us_p2_pos.ne'
    have h_n_over_s : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
      have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := by rw [← sq]; exact hs_sq
      field_simp; linarith [hss]
    have h_nv_eq : (n : ℝ) * (u / Real.sqrt (n : ℝ)) = u * Real.sqrt (n : ℝ) := by
      rw [show (n : ℝ) * (u / Real.sqrt (n : ℝ)) = u * ((n : ℝ) / Real.sqrt (n : ℝ))
            from by ring]
      rw [h_n_over_s]
    have h_simp : (n : ℝ) * (2 * (u / Real.sqrt (n : ℝ)) / (u / Real.sqrt (n : ℝ) + 2)) =
                  2 * u * Real.sqrt (n : ℝ) / (u / Real.sqrt (n : ℝ) + 2) := by
      rw [show (n : ℝ) * (2 * (u / Real.sqrt (n : ℝ)) / (u / Real.sqrt (n : ℝ) + 2))
            = (2 * ((n : ℝ) * (u / Real.sqrt (n : ℝ)))) / (u / Real.sqrt (n : ℝ) + 2)
            from by ring]
      rw [h_nv_eq]; ring
    rw [h_simp] at h_n_mul
    have h_eq2 : 2 * u * Real.sqrt (n : ℝ) / (u / Real.sqrt (n : ℝ) + 2) =
                 u * Real.sqrt (n : ℝ) - u^2 / (u / Real.sqrt (n : ℝ) + 2) := by
      field_simp; ring
    rw [h_eq2] at h_n_mul
    show -(u^2 / (u / Real.sqrt (n : ℝ) + 2)) ≤ E n
    show -(u^2 / (u / Real.sqrt (n : ℝ) + 2)) ≤
         (n : ℝ) * Real.log (1 + u / Real.sqrt (n : ℝ)) - u * Real.sqrt (n : ℝ)
    linarith
  -- Step C: Upper bound `E n ≤ U n := -u²/(2(1+u/√n))` for n ≥ 1
  have h_E_le_U : ∀ᶠ (n : ℕ) in atTop, E n ≤ -(u^2 / (2 * (1 + u / Real.sqrt (n : ℝ)))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn_real_pos : (0 : ℝ) < n := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hn_ne : (n : ℝ) ≠ 0 := hn_real_pos.ne'
    have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_real_pos
    have hs_ne : Real.sqrt (n : ℝ) ≠ 0 := hs_pos.ne'
    have hv_nn : 0 ≤ u / Real.sqrt (n : ℝ) := div_nonneg hu hs_pos.le
    have hs_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn_real_pos.le
    have h1v_pos : 0 < 1 + u / Real.sqrt (n : ℝ) := by linarith
    have h_log_ub := log_one_add_le_sub_sq_div (u / Real.sqrt (n : ℝ)) hv_nn
    have h_n_mul := mul_le_mul_of_nonneg_left h_log_ub hn_real_pos.le
    have h_n_over_s : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
      have hss : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := by rw [← sq]; exact hs_sq
      field_simp; linarith [hss]
    have h_nv : (n : ℝ) * (u / Real.sqrt (n : ℝ)) = u * Real.sqrt (n : ℝ) := by
      rw [show (n : ℝ) * (u / Real.sqrt (n : ℝ)) = u * ((n : ℝ) / Real.sqrt (n : ℝ))
            from by ring]
      rw [h_n_over_s]
    have h_nv2 : (n : ℝ) * (u / Real.sqrt (n : ℝ))^2 = u^2 := by
      rw [show (u / Real.sqrt (n : ℝ))^2 = u^2 / Real.sqrt (n : ℝ) ^ 2 from by ring]
      rw [hs_sq]; field_simp
    have h_simp : (n : ℝ) *
        (u / Real.sqrt (n : ℝ) - (u / Real.sqrt (n : ℝ))^2 / (2 * (1 + u / Real.sqrt (n : ℝ)))) =
        u * Real.sqrt (n : ℝ) - u^2 / (2 * (1 + u / Real.sqrt (n : ℝ))) := by
      rw [mul_sub, h_nv]
      congr 1
      rw [show (n:ℝ) * ((u / Real.sqrt (n : ℝ))^2 / (2 * (1 + u / Real.sqrt (n : ℝ)))) =
              ((n:ℝ) * (u / Real.sqrt (n : ℝ))^2) / (2 * (1 + u / Real.sqrt (n : ℝ)))
              from by ring]
      rw [h_nv2]
    rw [h_simp] at h_n_mul
    show E n ≤ -(u^2 / (2 * (1 + u / Real.sqrt (n : ℝ))))
    show (n : ℝ) * Real.log (1 + u / Real.sqrt (n : ℝ)) - u * Real.sqrt (n : ℝ)
         ≤ -(u^2 / (2 * (1 + u / Real.sqrt (n : ℝ))))
    linarith
  -- Step D: Lower & upper bounds tend to -u²/2.
  have h_L_tendsto :
      Tendsto (fun n : ℕ => -(u^2 / (u / Real.sqrt n + 2))) atTop (𝓝 (-(u^2/2))) := by
    have h_vp2 : Tendsto (fun n : ℕ => u / Real.sqrt n + 2) atTop (𝓝 2) := by
      have := h_u_div_sqrt.add_const 2
      simpa using this
    have h_div : Tendsto (fun n : ℕ => u^2 / (u / Real.sqrt n + 2)) atTop (𝓝 (u^2 / 2)) :=
      tendsto_const_nhds.div h_vp2 (by norm_num)
    exact h_div.neg
  have h_U_tendsto :
      Tendsto (fun n : ℕ => -(u^2 / (2 * (1 + u / Real.sqrt n)))) atTop (𝓝 (-(u^2/2))) := by
    have h_1pv : Tendsto (fun n : ℕ => 1 + u / Real.sqrt n) atTop (𝓝 1) := by
      have := h_u_div_sqrt.const_add 1
      simpa using this
    have h_2pv : Tendsto (fun n : ℕ => 2 * (1 + u / Real.sqrt n)) atTop (𝓝 2) := by
      have := h_1pv.const_mul 2
      simpa using this
    have h_div : Tendsto (fun n : ℕ => u^2 / (2 * (1 + u / Real.sqrt n))) atTop (𝓝 (u^2 / 2)) :=
      tendsto_const_nhds.div h_2pv (by norm_num)
    exact h_div.neg
  -- Step E: Sandwich gives E n → -u²/2.
  have h_E_tendsto : Tendsto E atTop (𝓝 (-(u^2/2))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h_L_tendsto h_U_tendsto h_L_le_E h_E_le_U
  -- Step F: G n u = exp(E n) → exp(-u²/2) by continuity.
  have h_exp_tendsto : Tendsto (fun n : ℕ => Real.exp (E n)) atTop (𝓝 (Real.exp (-(u^2/2)))) :=
    (Real.continuous_exp.tendsto _).comp h_E_tendsto
  exact h_exp_tendsto.congr' (h_G_eq_exp_E.mono (fun n hn => hn.symm))

/-! ### Step B: Pointwise dominator `G n u ≤ e^{1 − u/4}`. -/

/-- **Dominator inequality.**  For `n ≥ 1`, `u ≥ 0`,
        `(1 + u/√n)^n · e^{-u√n} ≤ e^{1 − u/4}`.

    Proof:  let `s = √n ≥ 1`, `v = u/s ≥ 0`.  By the sharp log bound,
        `n · log(1 + v) ≤ n·v − n·v²/(2(1+v)) = u·s − u²/(2(1+v))`.
    Hence `n·log(1+v) − u·s ≤ −u²/(2(1+u/s))`.
    Case `u ≤ s`:  `1+u/s ≤ 2`, so `-u²/(2(1+u/s)) ≤ -u²/4 ≤ 1 - u/4`
    (since `u² - u + 4 ≥ 0`).
    Case `u > s`:  `1+u/s ≤ 2u/s`, so `-u²/(2(1+u/s)) ≤ -u·s/4 ≤ -u/4 ≤ 1 - u/4`. -/
private lemma G_le_bound {n : ℕ} (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    G n u ≤ Real.exp (1 - u / 4) := by
  unfold G
  set s : ℝ := Real.sqrt n with hs_def
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs_ge_one : 1 ≤ s := by
    rw [hs_def]
    have h := Real.sqrt_le_sqrt hn_real
    rwa [Real.sqrt_one] at h
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_ge_one
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_sq : s ^ 2 = n := by
    rw [hs_def, Real.sq_sqrt (by exact_mod_cast Nat.zero_le n : (0 : ℝ) ≤ n)]
  have hv_nn : 0 ≤ u / s := div_nonneg hu hs_pos.le
  have h1v_pos : 0 < 1 + u / s := by linarith
  -- Rewrite `(1 + u/s)^n = exp(n · log(1 + u/s))` and combine with exp(-u·s).
  have h1v_pow : (1 + u / s) ^ n = Real.exp ((n : ℝ) * Real.log (1 + u / s)) := by
    rw [Real.exp_nat_mul, Real.exp_log h1v_pos]
  rw [h1v_pow, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  -- Reduce to: n · log(1+u/s) - u·s ≤ 1 - u/4.
  -- Step A: log(1+u/s) ≤ u/s - (u/s)²/(2(1+u/s))
  have h_log_bound := log_one_add_le_sub_sq_div (u / s) hv_nn
  have hn_pos_real : (0 : ℝ) < n := by
    have : 0 < (n : ℕ) := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    exact_mod_cast this
  -- Identities using s² = n: n/s = s, n · (u/s) = u·s, n · (u/s)² = u²
  have h_n_div_s : (n : ℝ) / s = s := by
    have hss : s * s = n := by rw [← sq]; exact hs_sq
    field_simp
    linarith [hss]
  have h_nv : (n : ℝ) * (u / s) = u * s := by
    rw [mul_div_assoc', mul_comm (n : ℝ) u, mul_div_assoc, h_n_div_s]
  have h_nv2 : (n : ℝ) * (u / s) ^ 2 = u ^ 2 := by
    have h1 : (u / s) ^ 2 = u^2 / s^2 := by ring
    rw [h1, hs_sq]
    field_simp
  -- Multiply log bound by n.
  have h_mul := mul_le_mul_of_nonneg_left h_log_bound hn_pos_real.le
  rw [mul_sub, h_nv] at h_mul
  have h_2v_ne : (2 * (1 + u / s) : ℝ) ≠ 0 := by
    have : 0 < 2 * (1 + u / s) := by linarith
    exact this.ne'
  have h_div_eq : (n : ℝ) * ((u / s) ^ 2 / (2 * (1 + u / s))) =
                  u^2 / (2 * (1 + u / s)) := by
    rw [show (n : ℝ) * ((u/s)^2 / (2*(1+u/s))) =
            ((n:ℝ) * (u/s)^2) / (2*(1+u/s)) from by ring, h_nv2]
  rw [h_div_eq] at h_mul
  -- Now: n · log(1+u/s) - u·s ≤ -u²/(2(1+u/s))
  have h_rearrange :
      (n : ℝ) * Real.log (1 + u / s) - u * s ≤ -(u^2 / (2 * (1 + u / s))) := by
    linarith
  -- Show -u²/(2(1+u/s)) ≤ 1 - u/4
  have h_bound : -(u^2 / (2 * (1 + u / s))) ≤ 1 - u / 4 := by
    have h_2v_pos : 0 < 2 * (1 + u / s) := by linarith
    rcases le_or_gt u s with h_us | h_us
    · -- Case A: u ≤ s
      have h_2v_le_4 : 2 * (1 + u / s) ≤ 4 := by
        have : u / s ≤ 1 := (div_le_one hs_pos).mpr h_us
        linarith
      have h_u2_lb : u^2 / 4 ≤ u^2 / (2 * (1 + u / s)) := by
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) h_2v_pos]
        nlinarith [sq_nonneg u]
      -- -u²/(2(1+u/s)) ≤ -u²/4 ≤ 1 - u/4
      have h1 : -(u^2 / (2 * (1 + u / s))) ≤ -(u^2 / 4) := by linarith
      have h2 : -(u^2 / 4) ≤ 1 - u / 4 := by nlinarith [sq_nonneg (u - 1/2)]
      linarith
    · -- Case B: u > s
      have hu_pos : 0 < u := lt_of_lt_of_le hs_pos h_us.le
      have hus_ge_1 : 1 ≤ u / s := by
        rw [le_div_iff₀ hs_pos]; linarith
      have h_2v_le : 2 * (1 + u / s) ≤ 4 * (u / s) := by linarith
      have h_4us_pos : 0 < 4 * (u / s) := by
        have : 0 < u / s := div_pos hu_pos hs_pos
        linarith
      have h_u2_lb : u^2 / (4 * (u / s)) ≤ u^2 / (2 * (1 + u / s)) := by
        rw [div_le_div_iff₀ h_4us_pos h_2v_pos]
        nlinarith [sq_nonneg u]
      have h_div_eq2 : u^2 / (4 * (u / s)) = u * s / 4 := by
        have hu_ne : u ≠ 0 := hu_pos.ne'
        field_simp
      rw [h_div_eq2] at h_u2_lb
      have h_us_ge : u / 4 ≤ u * s / 4 := by
        have : u ≤ u * s := by nlinarith
        linarith
      linarith
  linarith

/-! ### Step D: Dominator integrability on `Ioi 0`. -/

/-- The dominator `e^{1 − u/4}` is integrable on `Ioi 0`. -/
private lemma bound_integrable :
    IntegrableOn (fun u : ℝ => Real.exp (1 - u / 4)) (Ioi (0:ℝ)) := by
  have h_eq : (fun u : ℝ => Real.exp (1 - u / 4)) =
              fun u => Real.exp 1 * Real.exp (-(1/4) * u) := by
    funext u
    rw [← Real.exp_add]
    congr 1; ring
  rw [h_eq]
  exact (exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1/4)).const_mul (Real.exp 1)

/-- The integrand `G n u` is non-negative for `u ≥ 0`, `n ≥ 1`. -/
private lemma G_nonneg {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ G n u := by
  have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold G
  have h1v : (0:ℝ) ≤ 1 + u / Real.sqrt n := by
    have : (0:ℝ) ≤ u / Real.sqrt n := div_nonneg hu hs_pos.le
    linarith
  exact mul_nonneg (pow_nonneg h1v n) (Real.exp_pos _).le

/-- `G n` is integrable on `Ioi 0` (for `n ≥ 1`), by domination by `e^{1 − u/4}`. -/
private lemma G_integrable {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (G n) (Ioi (0:ℝ)) := by
  refine Integrable.mono' bound_integrable ?_ ?_
  · -- AEStronglyMeasurable G_n on Ioi 0
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.pow ?_ n
      apply ContinuousOn.add continuousOn_const
      exact continuousOn_id.div continuousOn_const (fun _ _ => hs_pos.ne')
    · refine Continuous.continuousOn ?_
      exact Real.continuous_exp.comp (continuous_neg.comp (continuous_id.mul continuous_const))
  · -- Pointwise bound on Ioi 0
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_pos : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg hn hu_pos.le)]
    exact G_le_bound hn u hu_pos.le

/-! ### Step E: Change of variable `Γ(n+1, n) = √n · n^n · e^{-n} · ∫₀^∞ G n`. -/

/-- **Change of variable.**  For `n ≥ 1`:
        `incompleteGamma (n+1, n) = √n · n^n · e^{-n} · ∫₀^∞ (1 + u/√n)^n · e^{-u·√n} du`.

    Substitution `t = n + u·√n` (Jacobian `√n`) on `Ici 0`, `f '' Ici 0 = Ici n`. -/
private lemma incompleteGamma_change_of_variable {n : ℕ} (hn : 1 ≤ n) :
    incompleteGamma ((n : ℝ) + 1) (n : ℝ) =
      Real.sqrt n * (n : ℝ)^n * Real.exp (-(n : ℝ)) * ∫ u in Ioi (0:ℝ), G n u := by
  set s : ℝ := Real.sqrt n with hs_def
  have hn_real_pos : (0 : ℝ) < n := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hn_real_pos
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_sq : s^2 = n := Real.sq_sqrt hn_real_pos.le
  -- The substitution function f u := n + u·s.
  set f : ℝ → ℝ := fun u => (n : ℝ) + u * s with hf_def
  -- Step 1: incompleteGamma (n+1) n = ∫ t in Ioi n, t^n · e^(-t)  [convert rpow to natural pow]
  have h_rpow_eq : incompleteGamma ((n : ℝ) + 1) (n : ℝ) =
      ∫ t in Ioi (n : ℝ), t^n * Real.exp (-t) := by
    unfold incompleteGamma
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht_pos : 0 < t := lt_of_lt_of_le hn_real_pos (le_of_lt ht)
    show t ^ ((n : ℝ) + 1 - 1) * Real.exp (-t) = t^n * Real.exp (-t)
    congr 1
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [h_rpow_eq]
  -- Step 2: f is injective on Ici 0 with derivative s, image = Ici n.
  have h_f_deriv : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f s (Ici (0:ℝ)) x := fun x _hx => by
    have h1 : HasDerivAt f s x := by
      have := ((hasDerivAt_id x).mul_const s).const_add (n : ℝ)
      simpa [hf_def] using this
    exact h1.hasDerivWithinAt
  have h_f_inj : Set.InjOn f (Ici (0:ℝ)) := by
    intro u _ v _ huv
    have h1 : u * s = v * s := by
      have : (n : ℝ) + u * s = (n : ℝ) + v * s := huv
      linarith
    exact mul_right_cancel₀ hs_ne h1
  have h_f_image : f '' Ici 0 = Ici (n : ℝ) := by
    ext t
    simp only [Set.mem_image, Set.mem_Ici]
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hu, rfl⟩
      have : (0:ℝ) ≤ u * s := mul_nonneg hu hs_pos.le
      show (n:ℝ) ≤ (n:ℝ) + u * s
      linarith
    · intro ht
      refine ⟨(t - n) / s, ?_, ?_⟩
      · exact div_nonneg (by linarith) hs_pos.le
      · show (n:ℝ) + ((t - n) / s) * s = t
        field_simp; ring
  -- Step 3: apply image change of variable
  have h_subst :=
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ici h_f_deriv h_f_inj
      (fun t : ℝ => t^n * Real.exp (-t))
  rw [h_f_image] at h_subst
  -- h_subst : ∫ t in Ici n, t^n · e^(-t) = ∫ u in Ici 0, |s| • ((n+u·s)^n · e^(-(n+u·s)))
  rw [show (∫ t in Ioi (n:ℝ), t^n * Real.exp (-t))
        = ∫ t in Ici (n:ℝ), t^n * Real.exp (-t)
        from (integral_Ici_eq_integral_Ioi).symm]
  rw [h_subst]
  -- Simplify |s| = s on the RHS
  rw [abs_of_pos hs_pos]
  -- Convert Ici 0 → Ioi 0 on the RHS
  rw [show (∫ u in Ici (0:ℝ), s • (f u ^ n * Real.exp (-(f u))))
        = ∫ u in Ioi (0:ℝ), s • (f u ^ n * Real.exp (-(f u)))
        from integral_Ici_eq_integral_Ioi]
  -- Pull s out
  rw [integral_smul]
  -- RHS: s · ∫ u in Ioi 0, (n + u·s)^n · e^(-(n+u·s))
  -- Goal: s · ∫ u in Ioi 0, (n+u·s)^n · e^(-(n+u·s))
  --     = √n · n^n · e^(-n) · ∫ u in Ioi 0, G n u
  -- where G n u = (1 + u/√n)^n · e^(-u·√n)
  -- and (n + u·s)^n = n^n · (1 + u/s)^n, e^(-(n+u·s)) = e^(-n) · e^(-u·s)
  have h_rewrite : ∀ u : ℝ, 0 < u →
      f u ^ n * Real.exp (-(f u)) = (n:ℝ)^n * Real.exp (-(n:ℝ)) * G n u := by
    intro u hu
    have h_factor : f u = (n : ℝ) * (1 + u / s) := by
      show (n:ℝ) + u * s = (n:ℝ) * (1 + u / s)
      have : (n : ℝ) * (1 + u / s) = (n:ℝ) + (n:ℝ) * u / s := by ring
      rw [this]
      have h_ns : (n : ℝ) / s = s := by
        have : s * s = n := by rw [← sq]; exact hs_sq
        field_simp; linarith [this]
      rw [show (n:ℝ) * u / s = ((n:ℝ)/s) * u from by ring, h_ns]
      ring
    have h_pow : f u ^ n = (n : ℝ)^n * (1 + u / s)^n := by
      rw [h_factor, mul_pow]
    have h_exp_neg : Real.exp (-(f u)) = Real.exp (-(n:ℝ)) * Real.exp (-(u * s)) := by
      rw [← Real.exp_add]
      congr 1
      show -((n:ℝ) + u * s) = -(n:ℝ) + -(u * s)
      ring
    rw [h_pow, h_exp_neg]
    show (n:ℝ)^n * (1 + u/s)^n * (Real.exp (-(n:ℝ)) * Real.exp (-(u * s))) =
         (n:ℝ)^n * Real.exp (-(n:ℝ)) * G n u
    unfold G
    show (n:ℝ)^n * (1 + u/s)^n * (Real.exp (-(n:ℝ)) * Real.exp (-(u * s))) =
         (n:ℝ)^n * Real.exp (-(n:ℝ)) * ((1 + u/Real.sqrt n)^n * Real.exp (-(u * Real.sqrt n)))
    rw [← hs_def]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => h_rewrite u (hu : (0:ℝ) < u))]
  -- Now: s · ∫ u in Ioi 0, (n^n · e^(-n) · G n u) = √n · n^n · e^(-n) · ∫ u in Ioi 0, G n u
  rw [integral_const_mul]
  rw [smul_eq_mul]
  ring

/-- The Gaussian integral on the positive half-line. -/
theorem integral_exp_neg_half_sq_Ioi :
    ∫ u in Ioi (0:ℝ), Real.exp (-(u^2/2)) = Real.sqrt (Real.pi / 2) := by
  have h := integral_gaussian_Ioi (1/2 : ℝ)
  -- `integral_gaussian_Ioi b : ∫ x in Ioi 0, exp (-b * x^2) = √(π/b)/2`.
  -- With b = 1/2 : ∫ x in Ioi 0, exp(-x²/2) = √(π/(1/2))/2 = √(2π)/2 = √(π/2).
  have h1 : Real.sqrt (Real.pi / (1/2)) / 2 = Real.sqrt (Real.pi / 2) := by
    rw [show Real.pi / (1/2) = 4 * (Real.pi / 2) from by ring]
    rw [show (4 : ℝ) = 2^2 from by norm_num]
    rw [Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [← h1, ← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _hu
  show Real.exp (-(u^2/2)) = Real.exp (-(1/2) * u^2)
  congr 1; ring

/-! ### Step F: DCT — `∫ G n → √(π/2)`. -/

/-- **DCT step.**  `∫_{Ioi 0} G n → ∫_{Ioi 0} e^{-u²/2} = √(π/2)` as `n → ∞`. -/
private lemma G_integral_tendsto :
    Tendsto (fun n : ℕ => ∫ u in Ioi (0:ℝ), G n u) atTop
      (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h_target :
      Tendsto (fun n : ℕ => ∫ u in Ioi (0:ℝ), G n u) atTop
        (𝓝 (∫ u in Ioi (0:ℝ), Real.exp (-(u^2/2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => Real.exp (1 - u/4)) ?_ ?_ bound_integrable ?_
    · -- AEStronglyMeasurable G n on Ioi 0 (eventually for n ≥ 1)
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.pow ?_ n
        apply ContinuousOn.add continuousOn_const
        exact continuousOn_id.div continuousOn_const (fun _ _ => hs_pos.ne')
      · refine Continuous.continuousOn ?_
        exact Real.continuous_exp.comp (continuous_neg.comp (continuous_id.mul continuous_const))
    · -- Pointwise bound ‖G n u‖ ≤ exp(1 - u/4) for n ≥ 1, u ∈ Ioi 0
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu_pos : 0 < u := hu
      rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg hn hu_pos.le)]
      exact G_le_bound hn u hu_pos.le
    · -- Pointwise convergence G n u → exp(-u²/2) for u ∈ Ioi 0
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      exact G_tendsto_pointwise u hu.le
  rw [integral_exp_neg_half_sq_Ioi] at h_target
  exact h_target

/-! ### Step G: Main theorem (the axiom). -/

/-- **Laplace asymptotic for `Γ(n+1, n)`.**  Discharges the axiom
    `incompleteGamma_laplace_asymptotic` in `CubicStudentAsymptotic.lean`:
        `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)` as `n → ∞`. -/
theorem incompleteGamma_laplace_asymptotic_thm :
    Tendsto (fun n : ℕ =>
        Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n /
          Real.sqrt n)
      atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  refine G_integral_tendsto.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  -- Goal: ∫ u in Ioi 0, G n u = e^n · n^(-n) · Γ(n+1, n) / √n
  have h_cv := incompleteGamma_change_of_variable hn
  have hn_real_pos : (0 : ℝ) < n := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_real_pos
  have h_exp_pos : 0 < Real.exp (n : ℝ) := Real.exp_pos _
  have h_npown_pos : 0 < (n : ℝ)^n := pow_pos hn_real_pos n
  have hs_ne : Real.sqrt (n : ℝ) ≠ 0 := hs_pos.ne'
  have hexp_ne : Real.exp (n : ℝ) ≠ 0 := h_exp_pos.ne'
  have hnpow_ne : ((n:ℝ)^n : ℝ) ≠ 0 := h_npown_pos.ne'
  -- Convert n^(-(n:ℝ)) (rpow) to ((n:ℝ)^n)⁻¹ (natural pow inverse)
  have h_rpow_inv : (n : ℝ)^(-(n : ℝ)) = ((n:ℝ)^n)⁻¹ := by
    rw [Real.rpow_neg hn_real_pos.le, Real.rpow_natCast]
  rw [h_cv, h_rpow_inv, Real.exp_neg]
  field_simp

end TailOptionPricing.CubicStudentLaplace
