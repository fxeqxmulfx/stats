module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.PoissonCDF — Poisson CDF at the mean → 1/2.

  Formalises the standard fact
      `lim_{n → ∞} e^{-n} · Σ_{m=0}^{n-1} n^m / m! = 1/2`,
  i.e. `P(X_n < n) → 1/2` where `X_n ~ Poisson(n)`.  Equivalent (up to
  the `m = n` term, which we show vanishes) to
      `lim_{n → ∞} e^{-n} · Σ_{m=0}^n n^m / m! = 1/2`.

  Resolves `todo3.md` C.3 (Poisson CLT alternative path).

  ### Proof strategy (route (b): direct Laplace asymptotic, leveraging C.1)

  Three pieces of existing infrastructure feed in:

  1. **Loulakis identity** (`incompleteGamma_loulakis`, proved in
     `Stats.Kappa.CubicStudent`) —
         `Γ(n+1, n) = n! · e^{-n} · Σ_{k=0}^n n^k/k!`.
     Subtracting the `k = n` term yields
         `e^{-n} · Σ_{k=0}^{n-1} n^k/k! = Γ(n+1,n)/n! - n^n · e^{-n}/n!`.

  2. **Stirling** (Mathlib's `Stirling.tendsto_stirlingSeq_sqrt_pi`) —
         `n! / (√(2n) · (n/e)^n) → √π`,
     which we rearrange to
         `√n · n^n · e^{-n} / n! → 1/√(2π)`.

  3. **Laplace asymptotic for `Γ(n+1, n)`**
     (`incompleteGamma_laplace_asymptotic_thm`, proved in
     `Stats.Kappa.CubicStudentLaplace`) —
         `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)`.

  Combining 2 and 3 by `Tendsto.mul`:
      `Γ(n+1, n) / n! = (Γ(n+1, n) / (n^n e^{-n} √n)) · (√n · n^n · e^{-n} / n!)
                     → √(π/2) · 1/√(2π) = 1/2`.
  And `n^n · e^{-n} / n! = (√n · n^n · e^{-n} / n!) · (1/√n) → 1/√(2π) · 0 = 0`.

  Subtracting via Loulakis:
      `e^{-n} · Σ_{k=0}^{n-1} n^k/k! → 1/2 − 0 = 1/2`. ∎

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Stats.Kappa.CubicStudent
public import Stats.Kappa.CubicStudentLaplace
public import Mathlib.Analysis.SpecialFunctions.Stirling

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing.PoissonCDF

/-! ### Step A — Stirling-rearranged form

`√n · n^n · e^{-n} / n! → 1/√(2π)`.

Direct algebraic rearrangement of Mathlib's
`Stirling.tendsto_stirlingSeq_sqrt_pi`, namely
`n! / (√(2n) · (n/e)^n) → √π`.

The intermediate step `(n / exp 1)^n = n^n · exp(−n)` uses
`Real.exp_nat_mul` (rewriting `(exp 1)^n = exp n`). -/

/-- Identity `(n / e)^n = n^n · e^{-n}`. -/
private lemma pow_n_div_exp_one (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n = (n : ℝ)^n * Real.exp (-(n:ℝ)) := by
  rw [div_pow]
  have h_exp : (Real.exp 1) ^ n = Real.exp (n : ℝ) := by
    have := Real.exp_nat_mul (1 : ℝ) n
    rw [mul_one] at this
    exact this.symm
  rw [h_exp]
  rw [div_eq_mul_inv, ← Real.exp_neg]

/-- Identity `√(2n) = √2 · √n` for `n : ℕ`. -/
private lemma sqrt_two_mul_n (n : ℕ) :
    Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt n :=
  Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (n : ℝ)

/-- **Stirling-rearranged limit** —
    `√n · n^n · e^{-n} / n! → 1/√(2π)` as `n → ∞`. -/
theorem tendsto_stirling_rearranged :
    Tendsto (fun n : ℕ =>
        Real.sqrt n * (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ))
      atTop (𝓝 (1 / Real.sqrt (2 * Real.pi))) := by
  have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_sqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := h_sqrt_pi_pos.ne'
  have h_sqrt_2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h_sqrt_2_ne : Real.sqrt 2 ≠ 0 := h_sqrt_2_pos.ne'
  -- 1/stirlingSeq → 1/√π
  have h_inv :
      Tendsto (fun n : ℕ => (Stirling.stirlingSeq n)⁻¹) atTop
        (𝓝 (Real.sqrt Real.pi)⁻¹) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.inv₀ h_sqrt_pi_ne
  -- Multiply by 1/√2: (1/stirlingSeq) · (1/√2) → 1/(√π · √2) = 1/√(2π)
  have h_target :
      (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / Real.sqrt (2 * Real.pi) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) Real.pi]
    rw [one_div, mul_inv_rev, mul_comm]
  have h_scaled :
      Tendsto (fun n : ℕ => (Stirling.stirlingSeq n)⁻¹ * (Real.sqrt 2)⁻¹)
        atTop (𝓝 (1 / Real.sqrt (2 * Real.pi))) := by
    rw [← h_target]
    exact h_inv.mul_const _
  -- Show pointwise equality for n ≥ 1.
  refine h_scaled.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : 0 < n := hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n:ℝ) ≠ 0 := hn_real_pos.ne'
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have h_sqrt_n_ne : Real.sqrt n ≠ 0 := h_sqrt_n_pos.ne'
  have h_pow_pos : (0:ℝ) < (n:ℝ)^n := pow_pos hn_real_pos n
  have h_pow_ne : ((n:ℝ)^n) ≠ 0 := h_pow_pos.ne'
  have h_exp_pos : (0:ℝ) < Real.exp (n:ℝ) := Real.exp_pos _
  have h_exp_ne : Real.exp (n:ℝ) ≠ 0 := h_exp_pos.ne'
  have h_expneg_ne : Real.exp (-(n:ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have h_fact_pos : (0:ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  have h_fact_ne : (n.factorial : ℝ) ≠ 0 := h_fact_pos.ne'
  -- stirlingSeq n = n! / (√(2n) · (n/e)^n)
  show (Stirling.stirlingSeq n)⁻¹ * (Real.sqrt 2)⁻¹
      = Real.sqrt n * (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ)
  unfold Stirling.stirlingSeq
  rw [pow_n_div_exp_one, sqrt_two_mul_n]
  -- Goal:
  --   (n! / (√2 · √n · (n^n · exp(-n))))⁻¹ · (√2)⁻¹
  --     = √n · n^n · exp(-n) / n!
  have h_denom_ne : Real.sqrt 2 * Real.sqrt n * ((n:ℝ)^n * Real.exp (-(n:ℝ))) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero h_sqrt_2_ne h_sqrt_n_ne)
      (mul_ne_zero h_pow_ne h_expneg_ne)
  field_simp

/-! ### Step B — `Γ(n+1, n) / n! → 1/2`

Product of Step A and the Laplace asymptotic
`incompleteGamma_laplace_asymptotic_thm` (C.1).

`Γ(n+1, n) / n! = (e^n · n^{-n} · Γ(n+1,n) / √n) · (√n · n^n · e^{-n} / n!)
              → √(π/2) · 1/√(2π) = 1/2`. -/

/-- Algebraic identity `√(π/2) · (1/√(2π)) = 1/2`. -/
private lemma sqrt_pi_half_div_sqrt_two_pi :
    Real.sqrt (Real.pi / 2) * (1 / Real.sqrt (2 * Real.pi)) = 1 / 2 := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_nn : (0:ℝ) ≤ Real.pi := h_pi_pos.le
  have h_sqrt_2_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h_sqrt_2_ne : Real.sqrt 2 ≠ 0 := h_sqrt_2_pos.ne'
  have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr h_pi_pos
  have h_sqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := h_sqrt_pi_pos.ne'
  have h_sqrt_2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  -- √(π/2) = √π / √2;  √(2π) = √2 · √π.
  rw [Real.sqrt_div h_pi_nn, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp
  linarith [h_sqrt_2_sq]

/-- **Γ(n+1, n) / n! → 1/2.**  Combines C.1
    (`incompleteGamma_laplace_asymptotic_thm`,
    `Stats.Kappa.CubicStudentLaplace`) with Step A
    (`tendsto_stirling_rearranged`):
        `Γ(n+1, n) / n! = (Γ(n+1, n) / (n^n · e^{-n} · √n))
                          · (√n · n^n · e^{-n} / n!)
                       → √(π/2) · 1/√(2π) = 1/2`. -/
theorem tendsto_incompleteGamma_div_factorial :
    Tendsto (fun n : ℕ => incompleteGamma (n + 1) n / (n.factorial : ℝ))
      atTop (𝓝 (1/2)) := by
  -- (Γ(n+1,n) / (n^n · e^{-n} · √n)) — derived from C.1 via algebra.
  have h_C1 := TailOptionPricing.CubicStudentLaplace.incompleteGamma_laplace_asymptotic_thm
  -- C.1's form: e^n · n^(-(n:ℝ)) · Γ(n+1, n) / √n → √(π/2)
  -- We multiply by `tendsto_stirling_rearranged`:
  --   √n · n^n · e^{-n} / n! → 1/√(2π)
  -- Product → √(π/2) · 1/√(2π) = 1/2 (by sqrt_pi_half_div_sqrt_two_pi).
  have h_prod := h_C1.mul tendsto_stirling_rearranged
  -- Massage the limit.
  rw [sqrt_pi_half_div_sqrt_two_pi] at h_prod
  -- Show the product equals `Γ(n+1,n) / n!` pointwise (for n ≥ 1).
  refine h_prod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : 0 < n := hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n:ℝ) ≠ 0 := hn_real_pos.ne'
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have h_sqrt_n_ne : Real.sqrt n ≠ 0 := h_sqrt_n_pos.ne'
  have h_pow_pos : (0:ℝ) < (n:ℝ)^n := pow_pos hn_real_pos n
  have h_pow_ne : ((n:ℝ)^n) ≠ 0 := h_pow_pos.ne'
  have h_exp_pos : (0:ℝ) < Real.exp (n:ℝ) := Real.exp_pos _
  have h_exp_ne : Real.exp (n:ℝ) ≠ 0 := h_exp_pos.ne'
  have h_expneg_ne : Real.exp (-(n:ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have h_fact_pos : (0:ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  have h_fact_ne : (n.factorial : ℝ) ≠ 0 := h_fact_pos.ne'
  -- Goal: (e^n · n^(-n:ℝ) · Γ(n+1,n) / √n) · (√n · n^n · e^(-n) / n!)
  --       = Γ(n+1,n) / n!
  -- Convert n^(-(n:ℝ)) to (n^n)⁻¹.
  have h_rpow_inv : (n : ℝ)^(-(n:ℝ)) = ((n:ℝ)^n)⁻¹ := by
    rw [Real.rpow_neg hn_real_pos.le, Real.rpow_natCast]
  have h_exp_cancel : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  show Real.exp n * (n:ℝ)^(-(n:ℝ)) * incompleteGamma (n + 1) n / Real.sqrt n
        * (Real.sqrt n * (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ))
      = incompleteGamma (n + 1) n / (n.factorial:ℝ)
  rw [h_rpow_inv]
  -- Rewrite expression to expose `Real.exp n * Real.exp (-n) = 1`.
  set G : ℝ := incompleteGamma ((n:ℝ) + 1) (n:ℝ) with hG
  show Real.exp n * ((n:ℝ)^n)⁻¹ * G / Real.sqrt n
        * (Real.sqrt n * (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ))
      = G / (n.factorial:ℝ)
  field_simp
  linear_combination G * h_exp_cancel

/-! ### Step C — `n^n · e^{-n} / n! → 0`

Direct from Step A by multiplying by `(√n)⁻¹ → 0`. -/

/-- `(√n)⁻¹ → 0` as `n → ∞` along `ℕ`. -/
private lemma tendsto_inv_sqrt_nat :
    Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
  have h_sqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h_sqrt

/-- **`n^n · e^{-n} / n! → 0`.**  Multiplying Step A by `1/√n → 0`. -/
theorem tendsto_pow_exp_div_factorial :
    Tendsto (fun n : ℕ => (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ))
      atTop (𝓝 0) := by
  -- Product of `√n · n^n · e^{-n} / n!` (→ 1/√(2π)) and `(√n)⁻¹` (→ 0)
  have h_prod := tendsto_stirling_rearranged.mul tendsto_inv_sqrt_nat
  rw [mul_zero] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : 0 < n := hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn_pos
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  have h_sqrt_n_ne : Real.sqrt n ≠ 0 := h_sqrt_n_pos.ne'
  have h_fact_pos : (0:ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  have h_fact_ne : (n.factorial : ℝ) ≠ 0 := h_fact_pos.ne'
  show Real.sqrt n * (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ) * (Real.sqrt n)⁻¹
      = (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial:ℝ)
  field_simp

/-! ### Step D — combine via Loulakis

The Loulakis identity (`incompleteGamma_loulakis`, proved in
`Stats.Kappa.CubicStudent`) gives
    `Γ(n+1, n) = n! · e^{-n} · Σ_{k ∈ range(n+1)} n^k/k!`.

Subtracting the `k = n` term from the sum via `Finset.sum_range_succ`:
    `e^{-n} · Σ_{k ∈ range n} n^k/k!
      = Γ(n+1, n)/n! − n^n · e^{-n}/n!`.

Both sides → `1/2 − 0 = 1/2`. -/

/-- **Poisson CDF at the mean tends to 1/2** (todo3.md C.3, route (b)).

    The truncated Poisson sum
    `e^{-n} · Σ_{m=0}^{n-1} n^m / m!` is exactly
    `P(Poisson(n) ≤ n - 1)`.  Stirling + the Laplace asymptotic for
    `Γ(n+1, n)` (C.1) imply this tends to `1/2` as `n → ∞`. -/
theorem poisson_cdf_at_mean_tendsto_half :
    Tendsto (fun n : ℕ =>
        Real.exp (-(n:ℝ)) *
          ∑ k ∈ Finset.range n, (n:ℝ)^k / (k.factorial:ℝ))
      atTop (𝓝 (1/2)) := by
  -- The combined limit `Γ(n+1, n)/n! − n^n · e^{-n}/n!` → 1/2 − 0 = 1/2.
  have h_diff :
      Tendsto (fun n : ℕ =>
          incompleteGamma (n + 1) n / (n.factorial : ℝ)
            - (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial : ℝ))
        atTop (𝓝 (1/2 - 0)) :=
    tendsto_incompleteGamma_div_factorial.sub tendsto_pow_exp_div_factorial
  rw [sub_zero] at h_diff
  refine h_diff.congr' ?_
  filter_upwards [Filter.univ_mem] with n _
  -- Loulakis: Γ(n+1, n) = n! · e^{-n} · Σ_{k ∈ range(n+1)} n^k/k!
  have h_loulakis := incompleteGamma_loulakis n
  -- Split the sum over range(n+1) into range n plus the last term n^n/n!.
  have h_split :
      ∑ k ∈ Finset.range (n + 1), (n:ℝ)^k / (k.factorial:ℝ)
        = ∑ k ∈ Finset.range n, (n:ℝ)^k / (k.factorial:ℝ)
            + (n:ℝ)^n / (n.factorial:ℝ) :=
    Finset.sum_range_succ _ _
  have h_fact_pos : (0:ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  have h_fact_ne : (n.factorial : ℝ) ≠ 0 := h_fact_pos.ne'
  -- Show pointwise equality.
  show incompleteGamma (n + 1) n / (n.factorial : ℝ)
          - (n:ℝ)^n * Real.exp (-(n:ℝ)) / (n.factorial : ℝ)
      = Real.exp (-(n:ℝ)) *
          ∑ k ∈ Finset.range n, (n:ℝ)^k / (k.factorial:ℝ)
  rw [h_loulakis, h_split]
  field_simp
  ring

end TailOptionPricing.PoissonCDF
