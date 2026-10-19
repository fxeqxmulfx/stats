module

/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.MLE — confidence intervals for the tail-index MLE (Item 7).

  Scalar estimator expressions, a Pareto-tail/logarithm identity and
  candidate asymptotic variance/interval formulas. The iid estimator law,
  Fisher-information calculation, estimator CLT and interval coverage
  are not constructed here.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
public import Stats.Pareto

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 7 — Confidence intervals for the tail-index MLE.

    For iid samples `X_1, …, X_n` from strong Pareto(`l`, `α`) with
    known `l`, the maximum-likelihood estimator of `α` is
        α̂_n := n / Σᵢ log(X_i / l).
    The transformed sample `Y_i := log(X_i / l)` is iid Exponential(α),
    so the sufficient statistic `S_n := Σ Y_i ~ Gamma(n, α)` has
    `E[S_n] = n / α`, `Var(S_n) = n / α²`.  In the inverse-MLE form,
        E[1 / α̂_n] = E[S_n / n] = 1 / α,
    `α̂` is asymptotically unbiased, and by the delta method has
    asymptotic variance `α² / n`.

    These statements motivate the formulas. The code below proves scalar
    reciprocal identities and a pointwise power/log transformation, then
    bounds supplied variance and interval expressions. It does not define
    an observed iid sample or prove its transformed law, estimator moments,
    a delta-method limit or confidence-interval coverage. -/

/-- **Pareto MLE (inverse form):** `1/α̂ = (1/n) · Σ log(X_i / l)`.
    Encoded for an abstract sum-of-logs `S` and sample size `n`. -/
noncomputable def paretoMLE_inv (S : ℝ) (n : ℕ) : ℝ := S / n

/-- **Pareto MLE:** `α̂ = n / Σ log(X_i / l)`. -/
noncomputable def paretoMLE (S : ℝ) (n : ℕ) : ℝ := (n : ℝ) / S

/-- **MLE inverse-relation.**  The MLE is the reciprocal of its
    inverse form: `α̂ · α̂_inv = 1`, when the sufficient statistic
    `S = Σ log(X_i / l) ≠ 0` and `n > 0`. -/
theorem paretoMLE_mul_inv {S : ℝ} {n : ℕ}
    (hS : S ≠ 0) (hn : n ≠ 0) :
    paretoMLE S n * paretoMLE_inv S n = 1 := by
  unfold paretoMLE paretoMLE_inv
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- **Exponential transformation of a strong-Pareto variate.**  Under
    `X ~ Pareto(l, α)`, the transformed variable `Y := log(X / l)` has
    the property `P(Y > t) = e^{-α·t}`, i.e. `Y ~ Exp(α)`.

    Pointwise version (no measure theory): for `x ≥ l > 0`,
        `survival l α x = exp(-α · log(x / l))`. -/
theorem survival_eq_exp_neg_α_log_ratio {l α x : ℝ} (hl : 0 < l) (hx : 0 < x) :
    survival l α x = Real.exp (-(α * Real.log (x / l))) := by
  unfold survival
  have h_ratio_pos : 0 < l / x := div_pos hl hx
  have h_ratio_pos' : 0 < x / l := div_pos hx hl
  rw [show (l / x) = (x / l)⁻¹ from by rw [inv_div]]
  rw [Real.inv_rpow h_ratio_pos'.le, ← Real.rpow_neg h_ratio_pos'.le]
  rw [show ((x / l) ^ (-α) : ℝ) = Real.exp (Real.log ((x / l) ^ (-α))) from
        (Real.exp_log (Real.rpow_pos_of_pos h_ratio_pos' _)).symm]
  congr 1
  rw [Real.log_rpow h_ratio_pos']
  ring

/-- **Identity for the inverse MLE on a deterministic anchor.**  When
    the sufficient statistic equals its expected value `n / α`, the
    MLE recovers the true tail index exactly. -/
theorem paretoMLE_at_expected {α : ℝ} {n : ℕ} (hα_pos : 0 < α) (hn : n ≠ 0) :
    paretoMLE ((n : ℝ) / α) n = α := by
  unfold paretoMLE
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- **Asymptotic variance of the Pareto MLE.**  Under iid Pareto
    sampling of size `n`, the variance of `α̂_n` is `α² / n` to leading
    order — the inverse Fisher information evaluated at the true `α`.

    This is a symbolic candidate expression. No estimator CLT or actual
    variance identification is proved here, and it is not asserted to
    bound the finite-sample variance. -/
noncomputable def paretoMLE_asymptoticVariance (α : ℝ) (n : ℕ) : ℝ :=
  α ^ 2 / n

/-- The candidate variance expression is positive for `α > 0` and `n > 0`. -/
theorem paretoMLE_asymptoticVariance_pos {α : ℝ} {n : ℕ}
    (hα_pos : 0 < α) (hn : 0 < n) :
    0 < paretoMLE_asymptoticVariance α n := by
  unfold paretoMLE_asymptoticVariance
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  positivity

/-- The supplied asymptotic-variance expression scales as `1/n` for
every real `α` and positive `n`. This algebra does not prove that an
actual estimator's variance or asymptotic variance equals that expression. -/
theorem paretoMLE_asymptoticVariance_scaling {α : ℝ} {n : ℕ}
    (hn : 0 < n) :
    paretoMLE_asymptoticVariance α n * n = α ^ 2 := by
  unfold paretoMLE_asymptoticVariance
  have hn_ne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

/-- **Confidence-interval half-width** for `α̂_n` at level `1 − γ`
    (with critical value `z_γ` from the standard normal):
        `z_γ · √(α² / n) = z_γ · α / √n`.

    Used as the asymptotic CI: `α̂_n ± paretoCIBound z α n`. -/
noncomputable def paretoCIBound (z α : ℝ) (n : ℕ) : ℝ :=
  z * α / Real.sqrt n

/-- **CI bound is non-negative** when the critical value and tail
    index are non-negative. -/
theorem paretoCIBound_nonneg {z α : ℝ} {n : ℕ}
    (hz : 0 ≤ z) (hα : 0 ≤ α) :
    0 ≤ paretoCIBound z α n := by
  unfold paretoCIBound
  apply div_nonneg
  · exact mul_nonneg hz hα
  · exact Real.sqrt_nonneg _

/-- **CI bound's square equals the asymptotic variance times `z²`.**
    Confirms the "halfwidth-from-variance" identity:
        `(z · α / √n)² = z² · (α² / n) = z² · asymptoticVariance`. -/
theorem paretoCIBound_sq {z α : ℝ} {n : ℕ} (hn : 0 < n) :
    paretoCIBound z α n ^ 2 = z ^ 2 * paretoMLE_asymptoticVariance α n := by
  unfold paretoCIBound paretoMLE_asymptoticVariance
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h_sqrt_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn_pos.le
  rw [div_pow]
  rw [h_sqrt_sq, mul_pow]
  ring

/-- **CI bound scales as `1 / √n`.**  Halving the sample width inflates
    the confidence interval by `√2`.  Standard parametric rate
    statement. -/
theorem paretoCIBound_scaling {z α : ℝ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) :
    paretoCIBound z α n * Real.sqrt n = paretoCIBound z α m * Real.sqrt m := by
  unfold paretoCIBound
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h_sqrt_n_ne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
  have h_sqrt_m_ne : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm_pos).ne'
  field_simp

/-- **Algebraic derivative of `paretoMLE` in the sufficient statistic.**
Since `paretoMLE S n = n / S`, the derivative with respect to `S` is
`-n / S²`.  Foundation for the data-side chain rule (A3b). -/
theorem paretoMLE_hasDerivAt {S : ℝ} {n : ℕ}
    (hS : S ≠ 0) (hn : 0 < n) :
    HasDerivAt (fun S' => paretoMLE S' n) (-(n : ℝ) / S^2) S := by
  have h_inv : HasDerivAt (fun S' : ℝ => S'⁻¹) (-(S^2)⁻¹) S := by
    simpa [sq] using (hasDerivAt_inv hS)
  have h := h_inv.const_mul ((n : ℝ))
  have hfun : (fun S' : ℝ => paretoMLE S' n) = (fun S' : ℝ => (n : ℝ) * S'⁻¹) := by
    funext S'; simp [paretoMLE, div_eq_mul_inv]
  have hval : (n : ℝ) * -(S^2)⁻¹ = -(n : ℝ) / S^2 := by field_simp
  rw [hfun, ← hval]
  exact h

/-- **Data-side sufficient statistic for the Pareto MLE.**
`S(xs) := Σ log(xs i / l)`.  The MLE is then `paretoMLE (S(xs)) n = n / S(xs)`. -/
noncomputable def paretoLogSumStat {n : ℕ} (l : ℝ) (xs : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (xs i / l)

/-- **Per-point influence of the Pareto MLE (data-side chain rule).**
Differentiating the MLE with respect to the value at coordinate `j`
(holding the others fixed), and evaluating at `xs j`, yields the
closed-form per-point influence:

  `∂α̂/∂(xs j) = -α̂² / (n · xs j)`

where `α̂ = paretoMLE (paretoLogSumStat l xs) n`.  This is the
C-score used in the three-score bad-point detector — closed-form,
not a numerical TracIn approximation. -/
theorem paretoMLE_data_hasDerivAt
    {n : ℕ} {l : ℝ} {xs : Fin n → ℝ} {j : Fin n}
    (hl : 0 < l) (hxs_pos : ∀ i, 0 < xs i) (hn : 0 < n)
    (hS_ne : paretoLogSumStat l xs ≠ 0) :
    HasDerivAt
      (fun t : ℝ => paretoMLE (paretoLogSumStat l (Function.update xs j t)) n)
      (-(paretoMLE (paretoLogSumStat l xs) n)^2 / (n * xs j)) (xs j) := by
  -- Notation.
  set S : ℝ := paretoLogSumStat l xs with hS_def
  have hxs_j_pos : 0 < xs j := hxs_pos j
  have hxs_j_ne : xs j ≠ 0 := hxs_j_pos.ne'
  have hn_pos_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_r.ne'
  -- Step 1: derivative of the sufficient statistic in coordinate `j`.
  have h_S_deriv :
      HasDerivAt (fun t : ℝ => paretoLogSumStat l (Function.update xs j t))
        (1 / xs j) (xs j) := by
    -- Per-summand derivative: 1/xs j if i = j else 0.
    have h_each : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun t : ℝ => Real.log ((Function.update xs j t) i / l))
          (if i = j then 1 / xs j else 0) (xs j) := by
      intro i _
      by_cases hij : i = j
      · subst hij
        -- (Function.update xs i t) i = t, so the function is t ↦ log (t / l).
        have h_eq :
            (fun t : ℝ => Real.log ((Function.update xs i t) i / l))
              = (fun t : ℝ => Real.log (t / l)) := by
          funext t
          simp [Function.update_self]
        rw [h_eq, ite_eq_left rfl]
        -- Derivative of t ↦ log (t / l) at xs i is 1 / xs i.
        have h_div : HasDerivAt (fun t : ℝ => t / l) (1 / l) (xs i) := by
          simpa [one_div] using (hasDerivAt_id (xs i)).div_const l
        have h_pos : 0 < xs i / l := div_pos (hxs_pos i) hl
        -- Use HasDerivAt.log: (hf : HasDerivAt f f' x) (hx : f x ≠ 0)
        --   ⇒ HasDerivAt (fun y => log (f y)) (f' / f x) x
        have h_log_div :
            HasDerivAt (fun t : ℝ => Real.log (t / l))
              ((1 / l) / (xs i / l)) (xs i) := h_div.log h_pos.ne'
        -- (1/l) / (xs i / l) = 1 / xs i.
        have h_simp : (1 / l) / (xs i / l) = 1 / xs i := by
          have hl_ne : l ≠ 0 := hl.ne'
          field_simp
        rw [← h_simp]
        exact h_log_div
      · -- (Function.update xs j t) i = xs i, constant in t.
        have h_eq :
            (fun t : ℝ => Real.log ((Function.update xs j t) i / l))
              = (fun _ : ℝ => Real.log (xs i / l)) := by
          funext t
          rw [Function.update_of_ne hij]
        rw [h_eq, ite_eq_right hij]
        exact hasDerivAt_const _ _
    -- Sum the derivatives.
    have h_sum := HasDerivAt.fun_sum h_each
    -- Simplify the resulting sum-of-ites.
    have h_sum_eq :
        (∑ i : Fin n, if i = j then (1 : ℝ) / xs j else 0) = 1 / xs j := by
      rw [Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℝ) / xs j)]
      simp
    -- Rewrite the LHS sum to match paretoLogSumStat.
    have h_LHS :
        (fun y : ℝ => ∑ i : Fin n, Real.log ((Function.update xs j y) i / l))
          = (fun t : ℝ => paretoLogSumStat l (Function.update xs j t)) := by
      funext t; rfl
    rw [← h_LHS, ← h_sum_eq]
    exact h_sum
  -- Step 2: chain rule with paretoMLE_hasDerivAt at S.
  -- Note: g(xs j) = paretoLogSumStat l (Function.update xs j (xs j))
  --              = paretoLogSumStat l xs = S, via Function.update_eq_self.
  have h_update_self : Function.update xs j (xs j) = xs :=
    Function.update_eq_self j xs
  have h_g_at :
      paretoLogSumStat l (Function.update xs j (xs j)) = S := by
    rw [h_update_self]
  -- HasDerivAt (paretoMLE · n) (-(n:ℝ)/S^2) at S.
  have h_f_deriv :
      HasDerivAt (fun S' : ℝ => paretoMLE S' n) (-(n : ℝ) / S^2) S :=
    paretoMLE_hasDerivAt hS_ne hn
  -- Reframe h_f_deriv as having base point `g (xs j)`.
  have h_f_deriv' :
      HasDerivAt (fun S' : ℝ => paretoMLE S' n) (-(n : ℝ) / S^2)
        (paretoLogSumStat l (Function.update xs j (xs j))) := by
    rw [h_g_at]; exact h_f_deriv
  -- Compose: derivative is (-(n:ℝ)/S^2) * (1 / xs j).
  have h_comp :
      HasDerivAt
        (fun t : ℝ => paretoMLE (paretoLogSumStat l (Function.update xs j t)) n)
        ((-(n : ℝ) / S^2) * (1 / xs j)) (xs j) :=
    h_f_deriv'.comp (xs j) h_S_deriv
  -- Step 3: simplify (-(n:ℝ)/S^2) * (1/xs j) = -(paretoMLE S n)^2 / (n * xs j).
  have h_target :
      (-(n : ℝ) / S^2) * (1 / xs j)
        = -(paretoMLE S n)^2 / ((n : ℝ) * xs j) := by
    unfold paretoMLE
    field_simp
  rw [h_target] at h_comp
  exact h_comp

/-- **Joint Pareto MLE matrix-influence (Fréchet derivative across `k`
coordinates).**  Lifting `paretoMLE_hasDerivAt` componentwise via the
canonical projection structure on `Fin k → ℝ`: each coordinate is
independently differentiable, with its single-coordinate derivative
`-n / (S j)²`, and the joint Fréchet derivative is the diagonal map. -/
theorem paretoMLE_joint_hasFDerivAt
    {k n : ℕ} {S : Fin k → ℝ}
    (hS : ∀ j, S j ≠ 0) (hn : 0 < n) :
    HasFDerivAt
      (fun S' : Fin k → ℝ => fun j => paretoMLE (S' j) n)
      (ContinuousLinearMap.pi
        (fun j => (-(n : ℝ) / (S j)^2) • (ContinuousLinearMap.proj j :
          (Fin k → ℝ) →L[ℝ] ℝ)))
      S := by
  refine hasFDerivAt_pi.mpr fun j => ?_
  have h_deriv : HasDerivAt (fun t : ℝ => paretoMLE t n) (-(n : ℝ) / (S j)^2) (S j) :=
    paretoMLE_hasDerivAt (hS j) hn
  have h_proj : HasFDerivAt (fun S' : Fin k → ℝ => S' j) (ContinuousLinearMap.proj j) S :=
    (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).hasFDerivAt
  exact h_deriv.comp_hasFDerivAt S h_proj

end TailOptionPricing
