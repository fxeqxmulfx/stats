/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.Bernoulli — paper Appendix A.

  Cumulant-generating function of the Bernoulli, its derivatives,
  and the corresponding cumulants κ_3, κ_4.

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
import Stats.BinaryForecasts.CharacteristicScale

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ## Bernoulli cumulants (paper Appendix A).

    For `X ∼ Bernoulli(p)`, the cumulant generating function is
        ψ(t) := log E[e^(tX)] = log(1 − p + p · e^t).
    Its first two derivatives at `0` give the first two cumulants:
        κ_1 = ψ'(0) = p,        κ_2 = ψ''(0) = p · (1 − p).
    For an iid sum of `N` Bernoulli's, cumulants scale by `N`, so the
    average `(1/N) Σ X_i` has cumulants `κ_k/N^{k−1}` → CLT-rate
    `O(1/√N)` for the standardised sum.

    We formalise the cumulant-generating-function derivative
    computations; the moment-finiteness of `P^(p)(n)` follows from
    boundedness `|X − 𝟙| ≤ 1`. -/

/-- **Bernoulli cumulant generating function (CGF).**
        `ψ(p, t) := log(1 − p + p · exp(t))`. -/
noncomputable def bernoulliCGF (p t : ℝ) : ℝ :=
  Real.log (1 - p + p * Real.exp t)

/-- **CGF positivity:** for any `p ∈ [0, 1]` and `t ∈ ℝ`, the inner
    expression `1 − p + p·exp(t)` is strictly positive (a convex
    combination of `1` and `e^t > 0`).  Required for `log`. -/
theorem bernoulliCGF_inner_pos {p t : ℝ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    0 < 1 - p + p * Real.exp t := by
  have h_exp_pos : 0 < Real.exp t := Real.exp_pos _
  rcases eq_or_lt_of_le hp_lb with hp_zero | hp_pos
  · rw [← hp_zero]; norm_num
  · have h_term : 0 < p * Real.exp t := mul_pos hp_pos h_exp_pos
    have h_one_sub_p_nn : 0 ≤ 1 - p := by linarith
    linarith

/-- **First Bernoulli cumulant**: `ψ'(p, 0) = p`.  The derivative
    of `log(1 − p + p · e^t)` with respect to `t` at `t = 0` equals
    `p · e^0 / (1 − p + p · e^0) = p / 1 = p`. -/
theorem bernoulliCGF_hasDerivAt_zero (p : ℝ) :
    HasDerivAt (bernoulliCGF p) p 0 := by
  -- Step 1: derivative of the inner function `1 − p + p · e^t`.
  have h_inner : HasDerivAt (fun t : ℝ => 1 - p + p * Real.exp t)
      (p * Real.exp 0) 0 := by
    have h_exp : HasDerivAt Real.exp (Real.exp 0) 0 := Real.hasDerivAt_exp 0
    have h := h_exp.const_mul p
    simpa using h.const_add (1 - p)
  -- Step 2: inner value at 0 is positive ⇒ can take log.
  have h_inner_pos : 0 < 1 - p + p * Real.exp 0 := by
    rw [Real.exp_zero]; linarith
  have h_inner_ne : (fun t : ℝ => 1 - p + p * Real.exp t) 0 ≠ 0 := by
    exact h_inner_pos.ne'
  -- Step 3: chain with log.
  have h_log := (Real.hasDerivAt_log h_inner_ne).comp 0 h_inner
  -- h_log : HasDerivAt (log ∘ inner) ((1 - p + p·exp 0)⁻¹ · (p · exp 0)) 0
  convert h_log using 1
  · rfl
  · simp only [Real.exp_zero, mul_one]
    show p = (1 - p + p)⁻¹ * p
    rw [show (1 - p + p : ℝ) = 1 from by ring, inv_one, one_mul]

/-- **Bernoulli CGF at zero is zero**: `ψ(p, 0) = log(1) = 0`. -/
theorem bernoulliCGF_zero {p : ℝ} :
    bernoulliCGF p 0 = 0 := by
  unfold bernoulliCGF
  rw [Real.exp_zero, show (1 - p + p * 1 : ℝ) = 1 from by ring, Real.log_one]

/-- **First cumulant `κ_1 = p`** (paper Appendix A).  Direct value
    of `ψ'(0) = p`.  Records the cumulant-derivative identity at zero. -/
theorem bernoulli_kappa1 (p : ℝ) :
    deriv (bernoulliCGF p) 0 = p :=
  (bernoulliCGF_hasDerivAt_zero p).deriv

/-- **First-derivative function of the Bernoulli CGF**: for `p ∈ [0, 1]`,
        ψ'(t) = p · exp(t) / (1 − p + p · exp(t)).
    Pointwise `HasDerivAt`, valid for *any* real `t` (the denominator
    is strictly positive). -/
theorem bernoulliCGF_hasDerivAt {p t : ℝ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (bernoulliCGF p)
      (p * Real.exp t / (1 - p + p * Real.exp t)) t := by
  have h_inner : HasDerivAt (fun s : ℝ => 1 - p + p * Real.exp s)
      (p * Real.exp t) t := by
    have h_exp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have h := h_exp.const_mul p
    simpa using h.const_add (1 - p)
  have h_inner_pos : 0 < 1 - p + p * Real.exp t :=
    bernoulliCGF_inner_pos hp_lb hp_ub
  have h_inner_ne : (fun s : ℝ => 1 - p + p * Real.exp s) t ≠ 0 := by
    exact h_inner_pos.ne'
  have h_log := (Real.hasDerivAt_log h_inner_ne).comp t h_inner
  convert h_log using 1
  · rfl
  · show p * Real.exp t / (1 - p + p * Real.exp t)
        = ((fun s : ℝ => 1 - p + p * Real.exp s) t)⁻¹ * (p * Real.exp t)
    simp only
    rw [div_eq_mul_inv, mul_comm]

/-- **Second cumulant `κ_2 = p(1 − p)`** (paper Appendix A).  Computed
    as the derivative-of-the-derivative of the Bernoulli CGF at zero.

    Algebra:  let `N(t) := p · e^t`, `M(t) := 1 − p + p · e^t`.  Then
    `ψ'(t) = N(t)/M(t)` with `N' = N`, `M' = N`.  Quotient rule:
        ψ''(t) = (N'·M − N·M') / M² = (N·M − N²)/M² = N·(1 − p)/M
                (using `M − N = 1 − p`).
    At t = 0: `N(0) = p`, `M(0) = 1`, so `ψ''(0) = p · (1 − p)`. -/
theorem bernoulli_kappa2 {p : ℝ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (fun t : ℝ => p * Real.exp t / (1 - p + p * Real.exp t))
      (p * (1 - p)) 0 := by
  have h_inner : HasDerivAt (fun s : ℝ => 1 - p + p * Real.exp s)
      (p * Real.exp 0) 0 := by
    have h_exp : HasDerivAt Real.exp (Real.exp 0) 0 := Real.hasDerivAt_exp 0
    have h := h_exp.const_mul p
    simpa using h.const_add (1 - p)
  have h_inner_pos : 0 < 1 - p + p * Real.exp 0 :=
    bernoulliCGF_inner_pos hp_lb hp_ub
  have h_inner_ne : (fun s : ℝ => 1 - p + p * Real.exp s) 0 ≠ 0 := by
    exact h_inner_pos.ne'
  have h_num : HasDerivAt (fun s : ℝ => p * Real.exp s)
      (p * Real.exp 0) 0 := by
    have h_exp : HasDerivAt Real.exp (Real.exp 0) 0 := Real.hasDerivAt_exp 0
    exact h_exp.const_mul p
  -- Quotient rule.
  have h_div := h_num.div h_inner h_inner_ne
  convert h_div using 1
  -- Goal: p(1-p) = (p·e^0·M(0) − p·e^0·M'(0))/M(0)² simplified.
  show p * (1 - p) =
    (p * Real.exp 0 * ((fun s : ℝ => 1 - p + p * Real.exp s) 0)
      - p * Real.exp 0 * (p * Real.exp 0)) /
    ((fun s : ℝ => 1 - p + p * Real.exp s) 0) ^ 2
  simp only [Real.exp_zero, mul_one]
  rw [show (1 - p + p : ℝ) = 1 from by ring]
  ring

/-- **Second-derivative function of the Bernoulli CGF.**  By a quick
    quotient-rule calculation,
        ψ''(t) = (1 − p) · p · e^t / (1 − p + p·e^t)².
    At `t = 0` this equals `κ_2 = p · (1 − p)` (consistency check with
    `bernoulli_kappa2`). -/
noncomputable def bernoulliCGF_secondDeriv (p t : ℝ) : ℝ :=
  (1 - p) * p * Real.exp t / (1 - p + p * Real.exp t) ^ 2

/-- **Third cumulant `κ_3 = p · (1 − p) · (1 − 2 · p)`** (paper
    Appendix A).  Computed as the derivative of `ψ''(t)` at `t = 0`.

    Algebra:  let `N(t) := (1 − p)·p·e^t` and
    `D(t) := (1 − p + p·e^t)²`.  Then `N'(0) = (1 − p)·p`,
    `D'(0) = 2 · 1 · p = 2p`, `N(0) = (1 − p)p`, `D(0) = 1`, so the
    quotient rule gives
        ψ'''(0) = (N'(0)·D(0) − N(0)·D'(0)) / D(0)²
                = ((1 − p)p − (1 − p)p·2p) / 1
                = p · (1 − p) · (1 − 2·p).  ✓ -/
theorem bernoulli_kappa3 {p : ℝ} (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (bernoulliCGF_secondDeriv p)
      (p * (1 - p) * (1 - 2 * p)) 0 := by
  have h_num : HasDerivAt (fun t : ℝ => (1 - p) * p * Real.exp t)
      ((1 - p) * p * Real.exp 0) 0 :=
    (Real.hasDerivAt_exp 0).const_mul ((1 - p) * p)
  have h_inner : HasDerivAt (fun s : ℝ => 1 - p + p * Real.exp s)
      (p * Real.exp 0) 0 := by
    have h := (Real.hasDerivAt_exp 0).const_mul p
    simpa using h.const_add (1 - p)
  have h_inner_pos : 0 < 1 - p + p * Real.exp 0 :=
    bernoulliCGF_inner_pos hp_lb hp_ub
  have h_inner_ne : (fun s : ℝ => 1 - p + p * Real.exp s) 0 ≠ 0 := by
    exact h_inner_pos.ne'
  have h_den : HasDerivAt (fun t : ℝ => (1 - p + p * Real.exp t) ^ 2)
      (2 * (1 - p + p * Real.exp 0) * (p * Real.exp 0)) 0 := by
    have h := h_inner.pow 2
    convert h using 1; ring
  have h_den_ne : (fun s : ℝ => (1 - p + p * Real.exp s) ^ 2) 0 ≠ 0 := by
    show (1 - p + p * Real.exp 0) ^ 2 ≠ 0
    exact pow_ne_zero 2 h_inner_ne
  have h_div := h_num.div h_den h_den_ne
  unfold bernoulliCGF_secondDeriv
  convert h_div using 1
  simp only [Real.exp_zero, mul_one]
  rw [show (1 - p + p : ℝ) = 1 from by ring]
  ring

/-- **Third-derivative function of the Bernoulli CGF.**  Quotient-rule
    derivative of `bernoulliCGF_secondDeriv`:
        ψ'''(t) = (1 − p)·p·e^t · (1 − p − p·e^t) / (1 − p + p·e^t)³.
    At `t = 0` reduces to `κ_3 = p · (1 − p) · (1 − 2 · p)` (consistency
    check with `bernoulli_kappa3`); its `t`-derivative at zero gives
    the fourth cumulant `κ_4` (`bernoulli_kappa4` below). -/
noncomputable def bernoulliCGF_thirdDeriv (p t : ℝ) : ℝ :=
  (1 - p) * p * Real.exp t * (1 - p - p * Real.exp t) /
    (1 - p + p * Real.exp t) ^ 3

/-- **Fourth cumulant `κ_4 = p·(1−p)·(1 − 6·p·(1−p))`** (paper
    Appendix A).  Computed as the `t`-derivative of `ψ'''(t)` at
    `t = 0`.

    Algebra:  let `A(t) := (1 − p)·p·e^t`, `B(t) := 1 − p − p·e^t`,
    `D(t) := (1 − p + p·e^t)³`.  Then `A' = A`, `B'(t) = −p·e^t`, and
    `D'(t) = 3·(1 − p + p·e^t)² · p·e^t`.  At `t = 0`:
      `A(0) = (1−p)p`, `B(0) = 1 − 2p`, `B'(0) = −p`, `D(0) = 1`,
      `D'(0) = 3p`.
    Quotient rule on `A·B / D`:
        ψ''''(0) = [(A·(B+B'))(0)·D(0) − A(0)·B(0)·D'(0)] / D(0)²
                = (1−p)p·(1 − 3p) · 1 − (1−p)p·(1−2p)·3p
                = p·(1−p) · [(1 − 3p) − 3p(1 − 2p)]
                = p·(1−p) · (1 − 6p + 6p²)
                = p·(1−p) · (1 − 6·p·(1−p)).  ✓ -/
theorem bernoulli_kappa4 {p : ℝ} (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (bernoulliCGF_thirdDeriv p)
      (p * (1 - p) * (1 - 6 * p * (1 - p))) 0 := by
  -- A(t) = (1-p)·p·e^t. A'(t) = (1-p)·p·e^t.
  have h_A : HasDerivAt (fun t : ℝ => (1 - p) * p * Real.exp t)
      ((1 - p) * p * Real.exp 0) 0 :=
    (Real.hasDerivAt_exp 0).const_mul ((1 - p) * p)
  -- p·e^t: derivative is p·e^t.
  have h_pe : HasDerivAt (fun t : ℝ => p * Real.exp t)
      (p * Real.exp 0) 0 := (Real.hasDerivAt_exp 0).const_mul p
  -- B(t) = (1-p) - p·e^t. B'(t) = -(p·e^t).
  have h_B : HasDerivAt (fun t : ℝ => 1 - p - p * Real.exp t)
      (-(p * Real.exp 0)) 0 := h_pe.const_sub (1 - p)
  -- Inner inner: (1 - p + p·e^t).
  have h_inner : HasDerivAt (fun s : ℝ => 1 - p + p * Real.exp s)
      (p * Real.exp 0) 0 := h_pe.const_add (1 - p)
  have h_inner_pos : 0 < 1 - p + p * Real.exp 0 :=
    bernoulliCGF_inner_pos hp_lb hp_ub
  have h_inner_ne : (fun s : ℝ => 1 - p + p * Real.exp s) 0 ≠ 0 := by
    exact h_inner_pos.ne'
  -- N(t) = A(t) · B(t) by product rule.
  have h_num : HasDerivAt
      (fun t : ℝ => (1 - p) * p * Real.exp t * (1 - p - p * Real.exp t))
      ((1 - p) * p * Real.exp 0 * (1 - p - p * Real.exp 0)
        + (1 - p) * p * Real.exp 0 * (-(p * Real.exp 0))) 0 :=
    h_A.mul h_B
  -- D(t) = (1 - p + p·e^t)^3.
  have h_den : HasDerivAt (fun t : ℝ => (1 - p + p * Real.exp t) ^ 3)
      (3 * (1 - p + p * Real.exp 0) ^ 2 * (p * Real.exp 0)) 0 := by
    have h := h_inner.pow 3
    convert h using 1
  have h_den_ne : (fun s : ℝ => (1 - p + p * Real.exp s) ^ 3) 0 ≠ 0 := by
    show (1 - p + p * Real.exp 0) ^ 3 ≠ 0
    exact pow_ne_zero 3 h_inner_ne
  have h_div := h_num.div h_den h_den_ne
  unfold bernoulliCGF_thirdDeriv
  convert h_div using 1
  simp only [Real.exp_zero, mul_one]
  rw [show (1 - p + p : ℝ) = 1 from by ring]
  ring


end TailOptionPricing
