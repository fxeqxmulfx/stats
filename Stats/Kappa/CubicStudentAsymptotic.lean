module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.CubicStudentAsymptotic — Stirling/Laplace asymptotic.

  Stirling/Laplace-based asymptotic of `kappa_cubicStudent`:
      `lim_{n → ∞} log(n) · κ_{1, n} = log(π²/4) = 2·log(π/2)`.

  Note on the paper's stated value: paper Appendix A
  (`arXiv:1802.05495v3`, page 8) states the limit as `π²/4`, but
  that is a typo — taking the `log` is missing.  The correct limit
  is `log(π²/4) ≈ 0.903`, derived here.

  Built on the proved theorem
      `incompleteGamma_laplace_asymptotic`
  (Loulakis-style Laplace asymptotic for `Γ(n+1, n)`). Its DCT-based
  proof is in `Stats/Kappa/CubicStudentLaplace.lean`.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Stats.Kappa.CubicStudent
public import Stats.Kappa.CubicStudentLaplace

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing

/-! ### Cubic Student κ asymptotic (paper Appendix A, Loulakis).

    Stirling/Laplace-based asymptotic of `kappa_cubicStudent`:
        `lim_{n → ∞} log(n) · κ_{1, n} = log(π²/4) = 2·log(π/2)`.

    **Note on the paper's stated value.**  Paper Appendix A
    (`arXiv:1802.05495v3`, page 8) states the limit as `π²/4`, but
    that is a typo — taking the `log` is missing.  The correct limit
    is `log(π²/4) ≈ 0.903`, which we derive here.

    Proof outline:
    1. **Laplace asymptotic** — substitution `t = n + u·√n` in
       `Γ(n+1, n) = ∫_n^∞ t^n · e^{-t} dt` transforms the integral to
       `√n · n^n · e^{-n} · ∫_0^∞ (1 + u/√n)^n · e^{-u·√n} du`.  Pointwise
       `(1 + u/√n)^n · e^{-u·√n} → e^{-u²/2}` as `n → ∞`, with dominator
       `e^{1 − u/4}` (integrable on `[0, ∞)`).  DCT yields
       `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)`, i.e.
       `e^n · n^{-n} · Γ(n+1, n) / √n → √(π/2)`.

    2. **Log form** — taking log of both sides (positive eventually):
       `log(e^n · n^{-n} · Γ(n+1, n)) − (1/2)·log(n) → (1/2)·log(π/2)`,
       and the `− 1` in the κ formula is asymptotically negligible
       (since the antecedent → ∞).

    3. **κ-limit** — the algebraic identity
       `log(n) · κ(1, n) = 2c(n) · log(n)/D(n)`,
       with `D(n) := log(e^n n^{-n} Γ(n+1,n) − 1)` and `c(n) := D(n) − log(n)/2 → log(π/2)/2`,
       combined with `log(n)/D(n) → 2`, yields
       `log(n) · κ(1, n) → 2 · (log(π/2)/2) · 2 = 2 · log(π/2) = log(π²/4)`.

    Step 1 uses `incompleteGamma_laplace_asymptotic`, proved by
    dominated convergence in `Stats/Kappa/CubicStudentLaplace.lean`. -/

/-- **Laplace asymptotic for the upper incomplete Gamma at the saddle
    point** (paper Appendix A / Loulakis).

    `Γ(n+1, n) = ∫_n^∞ t^n e^{-t} dt` admits the Laplace asymptotic
        `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)` as `n → ∞`,
    or equivalently
        `e^n · n^{-n} · Γ(n+1, n) / √n → √(π/2)`.

    Standard derivation (Loulakis):  substitute `t = n + u·√n`,
    `dt = √n du`, range `u ∈ [0, ∞)`:
      `Γ(n+1, n) = √n · n^n · e^{-n} · ∫_0^∞ (1 + u/√n)^n · e^{-u√n} du`.
    Pointwise, `(1 + u/√n)^n · e^{-u√n} → e^{-u²/2}` (Taylor on `log`).
    Dominator: `(1 + u/√n)^n · e^{-u√n} ≤ e^{1 − u/4}` (from `log(1+x) ≤ x − x²/(2(1+x))`).
    By DCT,  `∫ → ∫_0^∞ e^{-u²/2} du = √(π/2)`.

    Discharged in `Stats.Kappa.CubicStudentLaplace`. -/
theorem incompleteGamma_laplace_asymptotic :
    Tendsto (fun n : ℕ =>
        Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n /
          Real.sqrt n)
      atTop (𝓝 (Real.sqrt (Real.pi / 2))) :=
  CubicStudentLaplace.incompleteGamma_laplace_asymptotic_thm

/-- **Stage 2: log form of the Laplace asymptotic.**
        `log(e^n · n^{-n} · Γ(n+1, n)) − (1/2)·log(n) → (1/2)·log(π/2)`. -/
private theorem tendsto_log_incompleteGamma_minus_half_log :
    Tendsto (fun n : ℕ =>
        Real.log
          (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n)
          - Real.log n / 2)
      atTop (𝓝 (Real.log (Real.pi / 2) / 2)) := by
  have h_laplace := incompleteGamma_laplace_asymptotic
  have h_target_pos : (0:ℝ) < Real.sqrt (Real.pi / 2) :=
    Real.sqrt_pos.mpr (by positivity)
  -- Step A: log(X/√n) → log √(π/2) = (1/2) log(π/2).
  have h_log_quot : Tendsto (fun n : ℕ =>
        Real.log
          (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n /
            Real.sqrt n))
      atTop (𝓝 (Real.log (Real.pi / 2) / 2)) := by
    have h := (Real.continuousAt_log h_target_pos.ne').tendsto.comp h_laplace
    simp only [Function.comp_def] at h
    rw [show Real.log (Real.sqrt (Real.pi / 2)) = Real.log (Real.pi / 2) / 2 from
        Real.log_sqrt (by positivity)] at h
    exact h
  -- Step B: eventually X/√n > 0.
  have h_event_pos : ∀ᶠ n : ℕ in atTop,
      0 < Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n /
            Real.sqrt n :=
    h_laplace.eventually (IsOpen.mem_nhds isOpen_Ioi h_target_pos)
  -- Step C: pointwise rewrite log(X/√n) = log(X) - (1/2) log(n).
  refine h_log_quot.congr' ?_
  filter_upwards [eventually_ge_atTop 1, h_event_pos] with n hn h_pos
  have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
  have h_sqrt_n_ne : Real.sqrt (n:ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hn_real_pos).ne'
  have h_X_ne :
      Real.exp ↑n * (↑n : ℝ)^(-(↑n:ℝ)) * incompleteGamma (↑n+1) ↑n ≠ 0 :=
    (div_ne_zero_iff.mp h_pos.ne').1
  rw [Real.log_div h_X_ne h_sqrt_n_ne, Real.log_sqrt hn_real_pos.le]

/-- **Stage 2b: same asymptotic for `... − 1`.**  The `− 1` is
    asymptotically negligible (subtracted from a quantity going to ∞). -/
private theorem tendsto_log_incompleteGamma_sub_one_minus_half_log :
    Tendsto (fun n : ℕ =>
        Real.log
          (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n - 1)
          - Real.log n / 2)
      atTop (𝓝 (Real.log (Real.pi / 2) / 2)) := by
  have h_laplace := incompleteGamma_laplace_asymptotic
  have h_target_pos : (0:ℝ) < Real.sqrt (Real.pi / 2) :=
    Real.sqrt_pos.mpr (by positivity)
  -- X / √n → √(π/2) > 0, and √n → ∞, so X → ∞.
  have h_sqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) atTop atTop := by
    have h_nat : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    exact Real.tendsto_sqrt_atTop.comp h_nat
  -- X = (X/√n) · √n. X/√n → √(π/2) > 0, √n → ∞ ⇒ X → ∞.
  have h_X_atTop : Tendsto (fun n : ℕ =>
      Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n)
      atTop atTop := by
    have h_prod := Filter.Tendsto.pos_mul_atTop h_target_pos h_laplace h_sqrt_atTop
    refine h_prod.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
    have h_sqrt_n_ne : Real.sqrt (n:ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr hn_real_pos).ne'
    field_simp
  -- 1/X → 0.
  have h_inv_X_tendsto :
      Tendsto (fun n : ℕ =>
        (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n)⁻¹)
        atTop (𝓝 0) := h_X_atTop.inv_tendsto_atTop
  -- 1 - 1/X → 1.
  have h_one_sub : Tendsto (fun n : ℕ =>
      1 - (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n)⁻¹)
      atTop (𝓝 1) := by
    have := h_inv_X_tendsto.const_sub 1
    simpa using this
  -- log(1 - 1/X) → log 1 = 0.
  have h_log_one_sub : Tendsto (fun n : ℕ =>
      Real.log (1 - (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
        incompleteGamma (n + 1) n)⁻¹))
      atTop (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp h_one_sub
    simp only [Function.comp_def, Real.log_one] at h
    exact h
  -- log(X - 1) = log(X · (1 - 1/X)) = log(X) + log(1 - 1/X).
  -- So log(X - 1) - log(n)/2 = (log(X) - log(n)/2) + log(1 - 1/X).
  have h_combined := tendsto_log_incompleteGamma_minus_half_log.add h_log_one_sub
  -- limit: log(π/2)/2 + 0 = log(π/2)/2.
  have h_limit : Real.log (Real.pi / 2) / 2 + 0 = Real.log (Real.pi / 2) / 2 := by
    ring
  rw [← h_limit]
  refine h_combined.congr' ?_
  -- Eventually X > 1 so that log(X - 1), log(X), 1 - 1/X are all valid.
  have h_X_gt_one : ∀ᶠ n : ℕ in atTop,
      1 < Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n :=
    h_X_atTop.eventually_gt_atTop 1
  filter_upwards [h_X_gt_one] with n hX_gt_one
  have hX_pos : 0 < Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n :=
    lt_trans zero_lt_one hX_gt_one
  have hX_ne : Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n ≠ 0 :=
    hX_pos.ne'
  have hX_sub_pos : 0 < Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
      incompleteGamma (n + 1) n - 1 := by linarith
  have hX_sub_ne : Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
      incompleteGamma (n + 1) n - 1 ≠ 0 := hX_sub_pos.ne'
  have h_one_sub_pos :
      0 < 1 - (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
        incompleteGamma (n + 1) n)⁻¹ := by
    have h_inv_lt_one : (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
        incompleteGamma (n + 1) n)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right; exact hX_gt_one
    linarith
  have h_one_sub_ne : 1 - (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
      incompleteGamma (n + 1) n)⁻¹ ≠ 0 := h_one_sub_pos.ne'
  -- log(X - 1) = log(X · (1 - 1/X))
  have h_factor : Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
      incompleteGamma (n + 1) n - 1 =
        Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n *
          (1 - (Real.exp n * (n : ℝ) ^ (-(n : ℝ)) *
            incompleteGamma (n + 1) n)⁻¹) := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ hX_ne]
  rw [h_factor, Real.log_mul hX_ne h_one_sub_ne]
  ring

/-- **Cubic Student κ asymptotic.**  `lim_{n → ∞} log(n) · κ_{1, n} =
    log(π²/4)`.  Algebraic limit derivation from
    `tendsto_log_incompleteGamma_sub_one_minus_half_log` (Stage 2b),
    structurally identical to `kappa_exponential_asymptotic` (Stage 4).

    *Note*: paper Appendix A claims the limit as `π²/4`, but this is a
    typo (missing `log`).  The correct asymptotic, derivable from the
    Laplace asymptotic on `Γ(n+1, n)`, is `log(π²/4) = 2·log(π/2)`.
    Uses the proved `incompleteGamma_laplace_asymptotic` theorem. -/
theorem kappa_cubicStudent_asymptotic :
    Tendsto (fun n : ℕ => Real.log n * kappa cubicStudentSumMAD 1 n)
      atTop (𝓝 (Real.log (Real.pi ^ 2 / 4))) := by
  -- log(n) → ∞.
  have h_log_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Abbreviations.
  set X : ℕ → ℝ := fun n =>
    Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n with hX_def
  set c_inf : ℝ := Real.log (Real.pi / 2) / 2 with hc_inf_def
  set D : ℕ → ℝ := fun n => Real.log (X n - 1) with hD_def
  set c : ℕ → ℝ := fun n => D n - Real.log n / 2 with hc_def
  -- Stage 2b: c → c_inf.
  have h_c : Tendsto c atTop (𝓝 c_inf) :=
    tendsto_log_incompleteGamma_sub_one_minus_half_log
  -- log(n)/2 → ∞.
  have h_log_half_atTop : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
    h_log_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2)
  -- D(n) = log(n)/2 + c(n) → ∞.
  have h_D_eq : D = (fun n : ℕ => Real.log n / 2 + c n) := by
    funext n; show D n = Real.log n / 2 + (D n - Real.log n / 2); ring
  have h_D_atTop : Tendsto D atTop atTop := by
    rw [h_D_eq]
    exact h_log_half_atTop.atTop_add h_c
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
    have h_eq : (1:ℝ) / (1/2) = 2 := by norm_num
    have h_div' : Tendsto (fun n : ℕ => 1 / ((1:ℝ)/2 + c n / Real.log n))
        atTop (𝓝 ((1:ℝ) / (1/2))) := h_div
    rw [h_eq] at h_div'
    exact h_div'
  -- 2 c(n) · (1 / (1/2 + c(n)/log(n))) → 2 c_inf · 2.
  have h_prod : Tendsto
      (fun n : ℕ => 2 * c n * (1 / ((1:ℝ)/2 + c n / Real.log n)))
      atTop (𝓝 (2 * c_inf * 2)) :=
    (h_c.const_mul 2).mul h_inv
  -- Simplify limit: 2 c_inf · 2 = 4 c_inf = 2 log(π/2) = log(π²/4).
  have h_limit_eq : 2 * c_inf * 2 = Real.log (Real.pi ^ 2 / 4) := by
    rw [hc_inf_def,
        show (Real.pi ^ 2 / 4 : ℝ) = (Real.pi / 2) ^ 2 from by ring,
        Real.log_pow]
    push_cast
    ring
  rw [← h_limit_eq]
  -- log(n) · κ = 2 c(n) · (1/(1/2 + c/log)) eventually.
  refine h_prod.congr' ?_
  -- Need n ≥ 2 (for kappa_cubicStudent), X(n) - 1 > 0 (for log), D(n) > 0.
  have h_event_X_pos : ∀ᶠ n : ℕ in atTop, 0 < X n - 1 := by
    have h_X_atTop : Tendsto X atTop atTop := by
      have h_laplace := incompleteGamma_laplace_asymptotic
      have h_target_pos : (0:ℝ) < Real.sqrt (Real.pi / 2) :=
        Real.sqrt_pos.mpr (by positivity)
      have h_sqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have h_prod_aux := Filter.Tendsto.pos_mul_atTop h_target_pos h_laplace h_sqrt_atTop
      refine h_prod_aux.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn_real_pos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
      have h_sqrt_n_ne : Real.sqrt (n:ℝ) ≠ 0 :=
        (Real.sqrt_pos.mpr hn_real_pos).ne'
      show _ = X n
      rw [hX_def]
      field_simp
    have h_X_gt_one := h_X_atTop.eventually_gt_atTop 1
    filter_upwards [h_X_gt_one] with n h; linarith
  filter_upwards [eventually_ge_atTop 2, eventually_gt_atTop 1, h_D_pos, h_event_X_pos]
    with n hn₂ hn_gt hD_pos hX_sub_pos
  rw [kappa_cubicStudent hn₂ hX_sub_pos]
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn_gt
  have h_log_pos : 0 < Real.log n := Real.log_pos hn_real_gt_one
  have h_log_ne : Real.log n ≠ 0 := h_log_pos.ne'
  have hD_ne : D n ≠ 0 := hD_pos.ne'
  have hc_unfold : c n = D n - Real.log n / 2 := rfl
  have h_denom_eq : (1:ℝ)/2 + c n / Real.log n = D n / Real.log n := by
    rw [hc_unfold]; field_simp; ring
  rw [h_denom_eq]
  rw [hc_unfold]
  show 2 * (D n - Real.log n / 2) * (1 / (D n / Real.log n)) =
    Real.log n * (2 - Real.log n / D n)
  field_simp


end TailOptionPricing
