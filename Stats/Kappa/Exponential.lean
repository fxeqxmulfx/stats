module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.Exponential — exponential / Gamma closed form and asymptotic.

  For iid `X_i ∼ Exponential(λ)`, the partial sum `S_n` is
  `Gamma(n, λ)`-distributed.  The MAD admits the closed form (Eq. 15)
      `M(n) = 2 · e^(−n) · n^n / (λ · Γ(n))`,
  and substituting into the abstract κ definition gives Eq. 16.
  Stirling-based asymptotic (Appendix C):
      `lim_{n → ∞} log(n) · κ_{1, n} = 4 − 2 · log(2π)`.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Probability.Distributions.Gamma
public import Stats.Kappa.Basic

@[expose] public section

open Real Set Filter Topology

namespace TailOptionPricing

/-! ## Exponential / Gamma closed form (Eq. 15, 16).

    For iid `X_i ∼ Exponential(λ)` (density `λ · e^(−λx)` on `[0, ∞)`),
    the partial sum `S_n` is Gamma-distributed with density
    `λ^n · z^(n−1) · e^(−λz) / Γ(n)`.  The MAD of `S_n` admits the
    closed form (Eq. 15)
        M(n) = 2 · e^(−n) · n^n / (λ · Γ(n)).
    Substituting into Eq. 1 yields the closed-form `κ_{1,n}`
    (Eq. 16). -/

/-- **Gamma-sum density (paper Eq. 14).**  Density of `S_n ∼ Gamma(n, λ)`,
    the partial sum of `n` iid `Exponential(λ)` summands:
        f_{S_n}(z) := λ^n · z^(n−1) · e^(−λz) / (n−1)!   for z ≥ 0,
    and `0` for `z < 0`.  Mathlib's `ProbabilityTheory.gammaPDFReal n λ`
    is the same function (`gammaSumDensity_eq_gammaPDFReal` below);
    using `(n-1)!` makes the integer-shape special case verbatim from
    the paper. -/
noncomputable def gammaSumDensity (lam : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  if 0 ≤ z then
    lam ^ n * z ^ (n - 1) * Real.exp (-(lam * z)) /
      ((n - 1).factorial : ℝ)
  else 0

/-- **Identification with Mathlib's `gammaPDFReal`.**  For `n ≥ 1` and
    `0 ≤ z`, the paper's integer-shape `gammaSumDensity λ n z` equals
    Mathlib's `gammaPDFReal n λ z` — the standard Gamma density with
    shape `n` and rate `λ`.  This bridges the paper's Eq. 14 with
    Mathlib's probability-theory infrastructure. -/
theorem gammaSumDensity_eq_gammaPDFReal {lam : ℝ} {n : ℕ}
    (hn : 1 ≤ n) {z : ℝ} (hz : 0 ≤ z) :
    gammaSumDensity lam n z = ProbabilityTheory.gammaPDFReal (n:ℝ) lam z := by
  unfold gammaSumDensity ProbabilityTheory.gammaPDFReal
  rw [ite_eq_left hz, ite_eq_left hz]
  -- Step 1: rewrite `Γ(n) = (n-1)!` using `Real.Gamma_nat_eq_factorial`.
  have h_cast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have : (n - 1 : ℕ) + 1 = n := by omega
    exact_mod_cast this
  have h_gamma_eq : Real.Gamma (n : ℝ) = ((n - 1).factorial : ℝ) := by
    have h := Real.Gamma_nat_eq_factorial (n - 1)
    rw [← h_cast]
    exact_mod_cast h
  -- Step 2: rpow ↔ npow conversions for `lam^n` and `z^(n-1)`.
  have h_lam_pow : lam ^ (n : ℝ) = lam ^ n := by
    rw [← Real.rpow_natCast lam n]
  have h_z_pow : z ^ ((n : ℝ) - 1) = z ^ (n - 1) := by
    have h_exp_eq : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
      have : (n - 1 : ℕ) + 1 = n := by omega
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast this
      linarith
    rw [h_exp_eq, ← Real.rpow_natCast z (n - 1)]
  rw [h_gamma_eq, h_lam_pow, h_z_pow]
  ring

/-- **Exponential / Gamma sum-MAD (paper Eq. 15).**  The mean absolute
    deviation of `S_n ∼ Gamma(n, λ)` at its mean `n/λ` is
        `M(n) := 2 · e^(−n) · n^n / (λ · Γ(n))`.
    Definition; derivation from the Gamma density (which is an
    incomplete-Gamma evaluation) is taken from the paper. -/
noncomputable def expSumMAD (lam : ℝ) (n : ℕ) : ℝ :=
  2 * Real.exp (-(n:ℝ)) * (n:ℝ) ^ (n:ℕ) / (lam * Real.Gamma n)

/-- **Exponential κ closed form (paper Eq. 16).**  For the Gamma sum
    with `n ≥ 2`,
        κ(1, n) = 2 − log(n) / (n · log(n) − n − log(Γ(n)) + 1).

    Derived by substituting `expSumMAD` into the abstract `kappa`
    definition. -/
theorem kappa_exponential {lam : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hn : 2 ≤ n) :
    kappa (expSumMAD lam) 1 n
      = 2 - Real.log n /
          ((n:ℝ) * Real.log n - (n:ℝ) - Real.log (Real.Gamma n) + 1) := by
  have hn_gt_one : 1 < n := by omega
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn_gt_one
  have hn_real_pos : (0:ℝ) < (n:ℝ) := by linarith
  have hΓ_one : Real.Gamma ((1:ℕ):ℝ) = 1 := by norm_num
  have hΓn_pos : 0 < Real.Gamma n := Real.Gamma_pos_of_pos hn_real_pos
  have hΓn_ne : Real.Gamma n ≠ 0 := hΓn_pos.ne'
  -- Pointwise expansion of expSumMAD at 1 and at n.
  have hM1 : expSumMAD lam 1 = 2 * Real.exp (-1) / lam := by
    unfold expSumMAD
    rw [hΓ_one]
    have : (((1:ℕ):ℝ) : ℝ) ^ (1:ℕ) = 1 := by norm_num
    rw [this, show (-(((1:ℕ):ℝ))) = -1 from by norm_num]
    field_simp
  have hM1_pos : 0 < expSumMAD lam 1 := by
    rw [hM1]; positivity
  -- log(Mn) - log(M1):
  have h_log_diff : Real.log (expSumMAD lam n) - Real.log (expSumMAD lam 1)
      = (n:ℝ) * Real.log n - (n:ℝ) - Real.log (Real.Gamma n) + 1 := by
    have hlam_ne : lam ≠ 0 := hlam.ne'
    have h_logMn : Real.log (expSumMAD lam n)
        = Real.log 2 + (-(n:ℝ)) + (n:ℝ) * Real.log n
          - Real.log lam - Real.log (Real.Gamma n) := by
      unfold expSumMAD
      have h_npow_pos : 0 < (n:ℝ) ^ (n:ℕ) := pow_pos hn_real_pos n
      have h_exp_pos : 0 < Real.exp (-(n:ℝ)) := Real.exp_pos _
      have h_lamΓ_pos : 0 < lam * Real.Gamma n := mul_pos hlam hΓn_pos
      rw [Real.log_div (by positivity) h_lamΓ_pos.ne',
          Real.log_mul (by positivity) h_npow_pos.ne',
          Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_pos _).ne',
          Real.log_mul hlam_ne hΓn_ne,
          Real.log_exp, Real.log_pow]
      ring
    have h_logM1 : Real.log (expSumMAD lam 1) = Real.log 2 - 1 - Real.log lam := by
      rw [hM1, Real.log_div (by positivity) hlam.ne',
          Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_pos _).ne',
          Real.log_exp]
      ring
    rw [h_logMn, h_logM1]
    ring
  unfold kappa
  rw [h_log_diff,
      show Real.log ((1:ℕ):ℝ) = 0 from by simp]
  ring

/-! ### Exponential κ asymptotic (paper Appendix C).

    Stirling-based asymptotic of the closed-form `kappa_exponential`:
        `lim_{n → ∞} log(n) · κ(1, n) = 4 − 2 · log(2π)`.

    Direct algebraic consequence of `Stirling.tendsto_stirlingSeq_sqrt_pi`,
    transported through `Γ(n) = (n − 1)!`.

    Proof outline:
    * Stage 1 — `log n! − n·log n + n − ½·log n → ½·log(2π)`
      (from `log stirlingSeq → log √π = ½·log π`, plus `½·log 2`).
    * Stage 2 — `log Γ(n) − n·log n + n + ½·log n → ½·log(2π)`
      (via `Γ(n) = (n − 1)!` shift; pick up cancelling `n·log(1+1/n) − 1`).
    * Stage 3 — `(n·log n − n − log Γ(n) + 1) − ½·log n → 1 − ½·log(2π)`.
    * Stage 4 — `log(n) · κ(1, n) → 4 − 2·log(2π)` via algebraic limit. -/

/-- **Stirling for `log n!`** (auxiliary form).
        `log n! − n·log n + n − ½·log n → ½·log(2π)` as `n → ∞`.
    Direct corollary of `Stirling.tendsto_stirlingSeq_sqrt_pi`. -/
private theorem tendsto_log_factorial_stirling :
    Tendsto
      (fun n : ℕ =>
        Real.log ((n.factorial : ℝ)) - (n : ℝ) * Real.log n + (n : ℝ)
          - Real.log n / 2)
      atTop (𝓝 (Real.log (2 * Real.pi) / 2)) := by
  -- Step 1: log ∘ stirlingSeq → log √π = log π / 2.
  have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_log_sqrt : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 :=
    Real.log_sqrt Real.pi_pos.le
  have h_logStirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log Real.pi / 2)) := by
    rw [← h_log_sqrt]
    exact (Real.continuousAt_log h_sqrt_pi_pos.ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  -- Step 2: shift by log 2 / 2, limit becomes log(2π)/2.
  have h_shift :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2)
        atTop (𝓝 (Real.log (2 * Real.pi) / 2)) := by
    have h_add := h_logStirling.add (tendsto_const_nhds (x := Real.log 2 / 2))
    have h_eq :
        Real.log Real.pi / 2 + Real.log 2 / 2 = Real.log (2 * Real.pi) / 2 := by
      rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_pos.ne']
      ring
    rw [h_eq] at h_add
    exact h_add
  -- Step 3: rewrite via `Stirling.log_stirlingSeq_formula`.
  refine h_shift.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : 0 < n := hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn_pos
  -- `log (stirlingSeq n) = log n! - (1/2) log(2n) - n · log(n/e)`.
  rw [Stirling.log_stirlingSeq_formula n]
  have h_log_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hn_real_pos.ne'
  have h_log_n_div_e : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div hn_real_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [h_log_2n, h_log_n_div_e]
  ring

/-- **Stirling for `log Γ(n)`** (auxiliary form).
        `log Γ(n) − n·log n + n + ½·log n → ½·log(2π)` as `n → ∞`.
    Obtained from `tendsto_log_factorial_stirling` by the shift
    `Γ(n + 1) = n!`, with correction `n·log(1 + 1/n) → 1`. -/
private theorem tendsto_log_Gamma_stirling :
    Tendsto
      (fun n : ℕ =>
        Real.log (Real.Gamma (n : ℝ)) - (n : ℝ) * Real.log n + (n : ℝ)
          + Real.log n / 2)
      atTop (𝓝 (Real.log (2 * Real.pi) / 2)) := by
  -- Shift n → m+1; prove the m-indexed version.
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  -- Step A: `m · log(1 + 1/m) → 1`.
  have h_m_log : Tendsto (fun m : ℕ => (m : ℝ) * Real.log (1 + 1/(m : ℝ)))
      atTop (𝓝 1) := by
    have h_real := Real.tendsto_mul_log_one_add_div_atTop (1 : ℝ)
    exact h_real.comp tendsto_natCast_atTop_atTop
  -- Step B: `log(1 + 1/m) → 0`.
  have h_log_one : Tendsto (fun m : ℕ => Real.log (1 + 1/(m : ℝ)))
      atTop (𝓝 0) := by
    have h_inv : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 0) := by
      simp_rw [one_div]; exact tendsto_inv_atTop_nhds_zero_nat
    have h_one_plus : Tendsto (fun m : ℕ => 1 + 1/(m : ℝ)) atTop (𝓝 1) := by
      have := h_inv.const_add 1; simpa using this
    have h_log_one_eq : Real.log 1 = 0 := Real.log_one
    rw [← h_log_one_eq]
    exact (Real.continuousAt_log one_ne_zero).tendsto.comp h_one_plus
  -- Step C: difference `g(m+1) − f(m) = −m·log(1+1/m) + 1 − ½·log(1+1/m) → 0`.
  have h_diff : Tendsto
      (fun m : ℕ => -((m : ℝ) * Real.log (1 + 1/(m : ℝ))) + 1
        - Real.log (1 + 1/(m : ℝ)) / 2) atTop (𝓝 0) := by
    have h1 := h_m_log.neg.add_const 1
    have h2 := h_log_one.div_const 2
    have h_sub := h1.sub h2
    convert h_sub using 1
    norm_num
  -- Step D: combine with Stage 1.
  have h_combined := tendsto_log_factorial_stirling.add h_diff
  -- The limit is log(2π)/2 + 0 = log(2π)/2.
  have h_limit_eq : Real.log (2 * Real.pi) / 2 + 0 = Real.log (2 * Real.pi) / 2 := by
    ring
  rw [← h_limit_eq]
  refine h_combined.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm_pos : 0 < m := hm
  have hm_real_pos : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr hm_pos
  have hm_real_ne : (m:ℝ) ≠ 0 := hm_real_pos.ne'
  -- log Γ(↑(m+1)) = log m!
  have h_gamma_eq : Real.log (Real.Gamma ((m + 1 : ℕ) : ℝ))
      = Real.log ((m.factorial : ℝ)) := by
    have h_cast : ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h_cast]
    rw [Real.Gamma_nat_eq_factorial m]
  -- log(m+1) = log m + log(1 + 1/m)
  have h_log_succ : Real.log (((m + 1 : ℕ) : ℝ))
      = Real.log m + Real.log (1 + 1/(m:ℝ)) := by
    have h_factor : ((m + 1 : ℕ) : ℝ) = (m:ℝ) * (1 + 1/(m:ℝ)) := by
      push_cast; field_simp
    rw [h_factor, Real.log_mul hm_real_ne (by positivity)]
  rw [h_gamma_eq, h_log_succ]
  push_cast
  ring

/-- **Stirling for the exponential-κ denominator.**
        `(n·log n − n − log Γ(n) + 1) − ½·log n → 1 − ½·log(2π)` as `n → ∞`.
    Direct shift of `tendsto_log_Gamma_stirling`. -/
private theorem tendsto_kappa_exp_denom_minus_half_log :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) * Real.log n - (n : ℝ) - Real.log (Real.Gamma (n : ℝ)) + 1)
          - Real.log n / 2)
      atTop (𝓝 (1 - Real.log (2 * Real.pi) / 2)) := by
  have h := tendsto_log_Gamma_stirling
  have h_neg_add := (h.neg).const_add 1
  -- h_neg_add : Tendsto (fun n => 1 + -(log Γ(n) − n·log n + n + (1/2) log n))
  --              atTop (𝓝 (1 + -(log(2π)/2))).
  convert h_neg_add using 1
  funext n; ring

/-- **Exponential κ asymptotic (paper Appendix C).**  Limit of
    `log(n) · κ_{1, n}` for the exponential / Gamma sum:
        `lim_{n → ∞} log(n) · κ_{1, n} = 4 − 2 · log(2π)`.

    Direct Stirling-based asymptotic from `tendsto_kappa_exp_denom_minus_half_log`:
    setting `D(n) := n·log n − n − log Γ(n) + 1` and `c(n) := D(n) − log n / 2`,
    Stage 3 gives `c(n) → 1 − log(2π)/2`.  Then for n ≥ 2,
        `log(n) · κ(1, n) = 2 c(n) · (log n / D(n))`,
    and `log n / D(n) = 1/(½ + c(n)/log n) → 2`, so the limit is
    `2 · (1 − log(2π)/2) · 2 = 4 − 2 log(2π)`. -/
theorem kappa_exponential_asymptotic {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => Real.log n * kappa (expSumMAD lam) 1 n)
      atTop (𝓝 (4 - 2 * Real.log (2 * Real.pi))) := by
  -- log(n) → ∞.
  have h_log_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- D, c, c_inf abbreviations.
  set c_inf : ℝ := 1 - Real.log (2 * Real.pi) / 2 with hc_inf_def
  set D : ℕ → ℝ := fun n =>
    (n : ℝ) * Real.log n - (n : ℝ) - Real.log (Real.Gamma (n : ℝ)) + 1
    with hD_def
  set c : ℕ → ℝ := fun n => D n - Real.log n / 2 with hc_def
  -- Stage 3: c → c_inf.
  have h_c : Tendsto c atTop (𝓝 c_inf) := tendsto_kappa_exp_denom_minus_half_log
  -- log(n)/2 → ∞.
  have h_log_half_atTop : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
    h_log_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2)
  -- D(n) = log(n)/2 + c(n), so D → ∞.
  have h_D_eq : D = (fun n : ℕ => Real.log n / 2 + c n) := by
    funext n; show D n = Real.log n / 2 + (D n - Real.log n / 2); ring
  have h_D_atTop : Tendsto D atTop atTop := by
    rw [h_D_eq]
    exact h_log_half_atTop.atTop_add h_c
  -- D(n) > 0 eventually.
  have h_D_pos : ∀ᶠ n in atTop, 0 < D n := h_D_atTop.eventually_gt_atTop 0
  -- c(n) / log(n) → 0.
  have h_c_div_log : Tendsto (fun n : ℕ => c n / Real.log n) atTop (𝓝 0) :=
    h_c.div_atTop h_log_atTop
  -- 1/2 + c(n)/log(n) → 1/2.
  have h_denom : Tendsto (fun n : ℕ => (1:ℝ)/2 + c n / Real.log n)
      atTop (𝓝 ((1:ℝ)/2)) := by
    have := h_c_div_log.const_add ((1:ℝ)/2)
    simpa using this
  -- 1 / (1/2 + c(n)/log(n)) → 2.
  have h_inv : Tendsto (fun n : ℕ => 1 / ((1:ℝ)/2 + c n / Real.log n))
      atTop (𝓝 2) := by
    have h_one : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h_div := h_one.div h_denom (by norm_num : (1:ℝ)/2 ≠ 0)
    -- h_div : Tendsto ((fun _ => 1) / (fun n => 1/2 + ...)) atTop (𝓝 (1/(1/2)))
    have h_eq : (1:ℝ) / (1/2) = 2 := by norm_num
    have h_div' : Tendsto (fun n : ℕ => 1 / ((1:ℝ)/2 + c n / Real.log n))
        atTop (𝓝 ((1:ℝ) / (1/2))) := h_div
    rw [h_eq] at h_div'
    exact h_div'
  -- 2 c(n) · (1/(1/2 + c(n)/log(n))) → 2 c_inf · 2.
  have h_prod : Tendsto
      (fun n : ℕ => 2 * c n * (1 / ((1:ℝ)/2 + c n / Real.log n)))
      atTop (𝓝 (2 * c_inf * 2)) :=
    (h_c.const_mul 2).mul h_inv
  -- Simplify limit: 2 c_inf · 2 = 4 - 2 log(2π).
  have h_limit_eq : 2 * c_inf * 2 = 4 - 2 * Real.log (2 * Real.pi) := by
    rw [hc_inf_def]; ring
  rw [← h_limit_eq]
  -- Final step: show log(n) · κ = 2 c(n) · (1/(1/2 + c/log)) eventually.
  refine h_prod.congr' ?_
  filter_upwards [eventually_ge_atTop 2, eventually_gt_atTop 1, h_D_pos]
    with n hn₂ hn_gt hD_pos
  rw [kappa_exponential hlam hn₂]
  have hn_gt_one : 1 < n := hn_gt
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn_gt_one
  have h_log_pos : 0 < Real.log n := Real.log_pos hn_real_gt_one
  have h_log_ne : Real.log n ≠ 0 := h_log_pos.ne'
  have hD_ne : D n ≠ 0 := hD_pos.ne'
  -- c(n) = D(n) - log(n)/2.
  have hc_unfold : c n = D n - Real.log n / 2 := rfl
  -- 1/2 + c(n)/log(n) = D(n)/log(n).
  have h_denom_eq : (1:ℝ)/2 + c n / Real.log n = D n / Real.log n := by
    rw [hc_unfold]; field_simp; ring
  rw [h_denom_eq]
  -- The identity: 2 · (D(n) - log(n)/2) · (1/(D(n)/log(n))) = log(n) · (2 - log(n)/D(n)).
  rw [hc_unfold]
  -- Fold the unfolded form back to `D n`.
  show 2 * (D n - Real.log n / 2) * (1 / (D n / Real.log n)) =
    Real.log n * (2 - Real.log n / D n)
  field_simp

end TailOptionPricing
