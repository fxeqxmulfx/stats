module

/-
  Branching epistemic uncertainty and thickness of tails.
    Taleb & Cirillo, arXiv:1912.00277v2 (Dec 2019).

  Formal scope: finite binomial-weighted scale moments, a candidate
  kurtosis expression and its inequalities, finite decaying-error
  products, and log-additivity for positive multiplicative factors.

  The scale-moment identities are
    E[σ_n²] = σ² · (1 + ε²)^n,
    E[σ_n⁴] = σ⁴ · (1 + 6ε² + ε⁴)^n,
  where E here abbreviates the explicitly defined weighted finite sum.
  The candidate raw kurtosis is strictly greater than 3 when n ≥ 1,
  σ ≠ 0 and ε ≠ 0.

  A Gaussian-mixture law, its outcome moments, divergence limits,
  a CLT and the Normal-Gamma compound-law theorem are not constructed
  here. Higher kurtosis alone does not establish a power-law tail.
  See REVIEW.md, EU-01–EU-34, for paper correspondence and missing work.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Stats.Pareto

@[expose] public section

open Real Set Filter Topology Finset

namespace TailOptionPricing

/-! ## Section III — Constant error rate.

    A perturbation tree of depth `n`: at each layer the dispersion is
    multiplied by either `(1 + ε)` or `(1 − ε)` with equal probability.
    After `n` layers, `σ_n = σ · (1 + ε)^j · (1 − ε)^(n − j)` with
    probability `C(n, j) / 2^n`, `j ∈ {0, …, n}`.

    Equivalently, `σ_n = σ · ∏_{i=1}^n B_i` where `B_i ∈ {1+ε, 1−ε}`
    iid uniform.  We compute the binomial-weighted moments of `σ_n`
    in closed form. -/

/-- **Per-layer moment factor** (paper's algebra).  The average of
    `(1 + ε)^k` and `(1 − ε)^k`:
        `M_k(ε) := ((1 + ε)^k + (1 − ε)^k) / 2`.
    Specialises to `M_2(ε) = 1 + ε²` and `M_4(ε) = 1 + 6ε² + ε⁴`. -/
noncomputable def epistemicMomentFactor (k : ℕ) (ε : ℝ) : ℝ :=
  ((1 + ε)^k + (1 - ε)^k) / 2

/-- **Second moment factor:** `M_2(ε) = 1 + ε²`. -/
theorem epistemicMomentFactor_two (ε : ℝ) :
    epistemicMomentFactor 2 ε = 1 + ε^2 := by
  unfold epistemicMomentFactor; ring

/-- **Fourth moment factor:** `M_4(ε) = 1 + 6ε² + ε⁴`. -/
theorem epistemicMomentFactor_four (ε : ℝ) :
    epistemicMomentFactor 4 ε = 1 + 6 * ε^2 + ε^4 := by
  unfold epistemicMomentFactor; ring

/-- **Binomial-weighted `k`-th moment of `σ_n`** under `n` layers of
    ±ε perturbation:
        E[σ_n^k] := (1/2^n) · Σ_{j=0}^n C(n,j) · (σ·(1+ε)^j·(1−ε)^(n−j))^k. -/
noncomputable def epistemicSigmaMoment (n k : ℕ) (σ ε : ℝ) : ℝ :=
  ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1),
    (Nat.choose n j : ℝ) * (σ * (1 + ε)^j * (1 - ε)^(n - j))^k

/-- **Closed form (paper Eq. 2 / 3 algebra).**  After `n` layers, the
    `k`-th raw moment of `σ_n` admits the closed form
        E[σ_n^k] = σ^k · M_k(ε)^n.
    Proof: binomial theorem applied to `(a + b)^n` with
    `a := (1 + ε)^k`, `b := (1 − ε)^k`. -/
theorem epistemicSigmaMoment_eq (n k : ℕ) (σ ε : ℝ) :
    epistemicSigmaMoment n k σ ε
      = σ^k * (epistemicMomentFactor k ε)^n := by
  unfold epistemicSigmaMoment epistemicMomentFactor
  -- Rewrite each summand: σ^k · C(n,j) · ((1+ε)^k)^j · ((1-ε)^k)^(n-j),
  -- then `Σ C(n,j) · a^j · b^(n-j) = (a+b)^n` by the binomial theorem.
  trans (((2 ^ n : ℕ) : ℝ)⁻¹ *
      (σ^k * ((1 + ε)^k + (1 - ε)^k)^n))
  · -- Reorder summands and pull σ^k.
    congr 1
    trans (∑ j ∈ Finset.range (n + 1),
        σ^k * (((1 + ε)^k)^j * ((1 - ε)^k)^(n - j) * (Nat.choose n j : ℝ)))
    · apply Finset.sum_congr rfl
      intros j _
      have h1 : ((1 + ε)^j)^k = ((1 + ε)^k)^j := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h2 : ((1 - ε)^(n - j))^k = ((1 - ε)^k)^(n - j) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [mul_pow, mul_pow, h1, h2]
      ring
    · rw [← Finset.mul_sum]
      rw [show ∑ j ∈ Finset.range (n + 1),
            ((1 + ε)^k)^j * ((1 - ε)^k)^(n - j) * (Nat.choose n j : ℝ)
          = ((1 + ε)^k + (1 - ε)^k)^n from (add_pow _ _ _).symm]
  · -- Combine 2^(-n) with ((1+ε)^k + (1-ε)^k)^n.
    have h_pow_nat : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ)^n := by push_cast; rfl
    rw [h_pow_nat, show (((1 + ε)^k + (1 - ε)^k) / 2)^n
          = ((1 + ε)^k + (1 - ε)^k)^n / 2^n from by rw [div_pow]]
    field_simp

/-- **Weighted scale second moment (paper Eq. 2 ingredient):**
        E[σ_n²] = σ² · (1 + ε²)^n.
    Direct corollary of `epistemicSigmaMoment_eq` at `k = 2`.
    Identifying this with an outcome variance needs a mixture-law bridge. -/
theorem epistemicVariance_eq (n : ℕ) (σ ε : ℝ) :
    epistemicSigmaMoment n 2 σ ε = σ^2 * (1 + ε^2)^n := by
  rw [epistemicSigmaMoment_eq, epistemicMomentFactor_two]

/-- **Fourth moment of `σ_n` (paper Eq. 3 specialisation):**
        E[σ_n^4] = σ^4 · (1 + 6ε² + ε^4)^n. -/
theorem epistemicSigmaFourthMoment_eq (n : ℕ) (σ ε : ℝ) :
    epistemicSigmaMoment n 4 σ ε = σ^4 * (1 + 6 * ε^2 + ε^4)^n := by
  rw [epistemicSigmaMoment_eq, epistemicMomentFactor_four]

/-! ### Kurtosis formula and the tail-thickening inequality. -/

/-- **Candidate raw kurtosis expression.** The factor 3 is motivated
    by a centered Gaussian conditional fourth moment. This definition
    does not itself construct a mixture or prove its moment identities. -/
noncomputable def epistemicKurtosis (n : ℕ) (σ ε : ℝ) : ℝ :=
  3 * epistemicSigmaMoment n 4 σ ε / (epistemicSigmaMoment n 2 σ ε)^2

/-- **Kurtosis closed form (paper Section III).**  For `σ ≠ 0`,
        Kurt(X) = 3 · (1 + 6ε² + ε^4)^n / (1 + ε²)^{2n}.
    Direct algebra from `epistemicVariance_eq` and
    `epistemicSigmaFourthMoment_eq`. -/
theorem epistemicKurtosis_eq (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicKurtosis n σ ε
      = 3 * (1 + 6 * ε^2 + ε^4)^n / (1 + ε^2)^(2 * n) := by
  unfold epistemicKurtosis
  rw [epistemicVariance_eq, epistemicSigmaFourthMoment_eq]
  have h_one_eps_pos : (0 : ℝ) < 1 + ε^2 := by nlinarith [sq_nonneg ε]
  have h_one_eps_pow_pos : 0 < (1 + ε^2 : ℝ)^n := pow_pos h_one_eps_pos n
  have hσ4 : σ^4 ≠ 0 := pow_ne_zero 4 hσ
  have h_one_eps_pow2n_pos : 0 < (1 + ε^2 : ℝ)^(2 * n) := pow_pos h_one_eps_pos _
  -- (σ² · (1+ε²)^n)² = σ^4 · (1+ε²)^{2n}.
  have h_sq_expand : (σ^2 * (1 + ε^2)^n)^2 = σ^4 * (1 + ε^2)^(2 * n) := by
    have h_pow_n_sq : ((1 + ε^2 : ℝ)^n)^2 = (1 + ε^2)^(2 * n) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [mul_pow, h_pow_n_sq]
    ring
  rw [h_sq_expand]
  field_simp

/-- **Tail-thickening kernel: `M_4(ε) ≥ M_2(ε)²`.**  Algebraic
    inequality `1 + 6ε² + ε⁴ ≥ (1 + ε²)²`, with strict inequality for
    `ε ≠ 0`.  Equivalent to `4ε² ≥ 0`. -/
theorem epistemicMomentFactor_four_ge_two_sq (ε : ℝ) :
    (1 + ε^2)^2 ≤ 1 + 6 * ε^2 + ε^4 := by
  nlinarith [sq_nonneg ε, sq_nonneg (ε^2)]

/-- **Strict tail-thickening** for `ε ≠ 0`: `M_4(ε) > M_2(ε)²`. -/
theorem epistemicMomentFactor_four_strict {ε : ℝ} (hε : ε ≠ 0) :
    (1 + ε^2)^2 < 1 + 6 * ε^2 + ε^4 := by
  have hε_sq_pos : 0 < ε^2 := by positivity
  nlinarith [hε_sq_pos]

/-- **Kurtosis ≥ 3 (fat-tail signature, paper claim).**  For any `n`
    and `σ ≠ 0`, the epistemic kurtosis satisfies
        Kurt(X) ≥ 3
    with equality iff `ε = 0` (no uncertainty) or `n = 0` (no layers).
    Strict inequality for any `ε ≠ 0` and `n ≥ 1` — the headline
    "uncertainty thickens tails" result. -/
theorem epistemicKurtosis_ge_three (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    3 ≤ epistemicKurtosis n σ ε := by
  rw [epistemicKurtosis_eq n σ ε hσ]
  have h_one_eps_pos : (0 : ℝ) < 1 + ε^2 := by nlinarith [sq_nonneg ε]
  have h_one_eps_pow_pos : 0 < (1 + ε^2 : ℝ)^(2 * n) := pow_pos h_one_eps_pos _
  rw [le_div_iff₀ h_one_eps_pow_pos]
  have h_rewrite : (1 + ε^2 : ℝ)^(2 * n) = ((1 + ε^2)^2)^n := by
    rw [← pow_mul, Nat.mul_comm]
  rw [h_rewrite]
  rw [show (3 : ℝ) * ((1 + ε^2)^2)^n = 3 * ((1 + ε^2)^2)^n from rfl]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (by positivity)
      (epistemicMomentFactor_four_ge_two_sq ε) n
  · norm_num

/-- **Excess kurtosis (paper convention).**  In some conventions
    "kurtosis" denotes the *excess* `Kurt − 3` (which vanishes for the
    Gaussian).  The paper's Section III states the kurtosis as
        `3 · ((1 + 6ε² + ε⁴)^n / (1 + ε²)^{2n} − 1)`,
    matching this convention.  Our `epistemicKurtosis` uses the *raw*
    convention (3 for Gaussian).  Translation: -/
noncomputable def epistemicExcessKurtosis (n : ℕ) (σ ε : ℝ) : ℝ :=
  epistemicKurtosis n σ ε - 3

/-- **Excess kurtosis closed form (paper convention, Section III).**
        ExcessKurt(X) = 3 · ((1 + 6ε² + ε⁴)^n / (1 + ε²)^{2n} − 1).
    Direct subtraction `Kurt − 3` from `epistemicKurtosis_eq`. -/
theorem epistemicExcessKurtosis_eq (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicExcessKurtosis n σ ε
      = 3 * ((1 + 6 * ε^2 + ε^4)^n / (1 + ε^2)^(2 * n) - 1) := by
  unfold epistemicExcessKurtosis
  rw [epistemicKurtosis_eq n σ ε hσ]
  ring

/-- **Excess kurtosis ≥ 0** (paper Section III claim, in paper's
    naming).  Direct corollary of `epistemicKurtosis_ge_three`. -/
theorem epistemicExcessKurtosis_nonneg (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    0 ≤ epistemicExcessKurtosis n σ ε := by
  unfold epistemicExcessKurtosis
  linarith [epistemicKurtosis_ge_three n σ ε hσ]

/-- **Strict candidate kurtosis > 3 for nonzero uncertainty.**
    Requires `n ≥ 1`, `ε ≠ 0`, and `σ ≠ 0`. This scalar inequality
    does not establish regular variation of a mixture tail. -/
theorem epistemicKurtosis_gt_three {n : ℕ} {σ ε : ℝ}
    (hn : 1 ≤ n) (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    3 < epistemicKurtosis n σ ε := by
  rw [epistemicKurtosis_eq n σ ε hσ]
  have h_one_eps_pos : (0 : ℝ) < 1 + ε^2 := by nlinarith [sq_nonneg ε]
  have h_one_eps_pow_pos : 0 < (1 + ε^2 : ℝ)^(2 * n) := pow_pos h_one_eps_pos _
  rw [lt_div_iff₀ h_one_eps_pow_pos]
  have h_rewrite : (1 + ε^2 : ℝ)^(2 * n) = ((1 + ε^2)^2)^n := by
    rw [← pow_mul, Nat.mul_comm]
  rw [h_rewrite]
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 3)
  have hn_pos : 0 < n := hn
  exact pow_lt_pow_left₀ (epistemicMomentFactor_four_strict hε)
    (by positivity) hn_pos.ne'

/-! ## Section IV — Decaying error rates (paper Eq. 5).

    Take `ε_i = κ^(i-1) · ε_1` for some `κ ∈ [0, 1]`.  At layer `i` the
    error term has variance `σ²(ε_i) = κ^{2(i-1)} · σ²(ε_1)`, so the
    cumulative variance contribution multiplies as
        Var(X) = σ² · ∏_{i=0}^{n-1} (1 + ε_1² · κ^{2i}).
    The right-hand side is the truncated `q`-Pochhammer symbol
    `[-ε_1²; κ²]_n`. -/

/-- **Decaying-error variance (paper Eq. 5):**
        σ² · ∏_{i=0}^{n-1} (1 + ε_1² · κ^{2i}). -/
noncomputable def decayingErrorVariance (n : ℕ) (σ ε₁ κ : ℝ) : ℝ :=
  σ^2 * ∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i))

/-- **Each factor is at least 1.**  Therefore the product is at least
    `σ²` — the variance only grows under decaying-error layering. -/
theorem decayingErrorVariance_ge_base (n : ℕ) (σ ε₁ κ : ℝ) (hσ : 0 ≤ σ^2) :
    σ^2 ≤ decayingErrorVariance n σ ε₁ κ := by
  unfold decayingErrorVariance
  have h_factor_ge : ∀ i ∈ Finset.range n, 1 ≤ 1 + ε₁^2 * κ^(2 * i) := by
    intros i _
    have h_eps_sq_nn : 0 ≤ ε₁^2 := sq_nonneg _
    have h_kappa_pow_nn : 0 ≤ κ^(2 * i) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg κ) i
    linarith [mul_nonneg h_eps_sq_nn h_kappa_pow_nn]
  have h_prod_ge : 1 ≤ ∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i)) := by
    have h_aux : (∏ _i ∈ Finset.range n, (1 : ℝ))
        ≤ ∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i)) := by
      apply Finset.prod_le_prod₀
      · intros i _; exact zero_le_one
      · intros i hi; exact h_factor_ge i hi
    simpa using h_aux
  calc σ^2 = σ^2 * 1 := by ring
    _ ≤ σ^2 * ∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i)) :=
        mul_le_mul_of_nonneg_left h_prod_ge hσ

/-- **Monotonicity in `n`** (each additional layer multiplies by a
    factor ≥ 1).  Variance only grows with depth. -/
theorem decayingErrorVariance_mono (σ ε₁ κ : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (hσ : 0 ≤ σ^2) :
    decayingErrorVariance n σ ε₁ κ ≤ decayingErrorVariance m σ ε₁ κ := by
  unfold decayingErrorVariance
  apply mul_le_mul_of_nonneg_left _ hσ
  have h_factor_nn : ∀ i, 0 ≤ 1 + ε₁^2 * κ^(2 * i) := by
    intros i
    have h_eps_sq_nn : 0 ≤ ε₁^2 := sq_nonneg _
    have h_kappa_pow_nn : 0 ≤ κ^(2 * i) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg κ) i
    linarith [mul_nonneg h_eps_sq_nn h_kappa_pow_nn]
  have h_factor_ge_one : ∀ i, 1 ≤ 1 + ε₁^2 * κ^(2 * i) := by
    intros i
    have h_eps_sq_nn : 0 ≤ ε₁^2 := sq_nonneg _
    have h_kappa_pow_nn : 0 ≤ κ^(2 * i) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg κ) i
    linarith [mul_nonneg h_eps_sq_nn h_kappa_pow_nn]
  -- Split the larger product.
  have h_split : ∏ i ∈ Finset.range m, (1 + ε₁^2 * κ^(2 * i))
      = (∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i))) *
        (∏ i ∈ Finset.Ico n m, (1 + ε₁^2 * κ^(2 * i))) := by
    rw [show Finset.range m = Finset.range n ∪ Finset.Ico n m from by
          ext k; simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega]
    rw [Finset.prod_union]
    rw [Finset.disjoint_left]
    intros a ha hb
    simp [Finset.mem_range, Finset.mem_Ico] at ha hb
    omega
  rw [h_split]
  have h_tail_ge_one : 1 ≤ ∏ i ∈ Finset.Ico n m, (1 + ε₁^2 * κ^(2 * i)) := by
    have h_aux : (∏ _i ∈ Finset.Ico n m, (1 : ℝ))
        ≤ ∏ i ∈ Finset.Ico n m, (1 + ε₁^2 * κ^(2 * i)) := by
      apply Finset.prod_le_prod₀
      · intros i _; exact zero_le_one
      · intros i _; exact h_factor_ge_one i
    simpa using h_aux
  have h_prod_nn : 0 ≤ ∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i)) :=
    Finset.prod_nonneg (fun i _ => h_factor_nn i)
  calc ∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i))
      = (∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i))) * 1 := by ring
    _ ≤ (∏ i ∈ Finset.range n, (1 + ε₁^2 * κ^(2 * i))) *
          (∏ i ∈ Finset.Ico n m, (1 + ε₁^2 * κ^(2 * i))) :=
        mul_le_mul_of_nonneg_left h_tail_ge_one h_prod_nn

/-! ## Section V — Log-additivity of multiplicative errors.

    Eq. 10:  `λ = λ̂ · ∏_{i=1}^n (1 + ε_i)`.
    Eq. 11:  `log λ = log λ̂ + Σ_{i=1}^n log(1 + ε_i)`.
    Only the finite log-additivity identity is proved here. A CLT for
    the log factors needs a probability model, moment hypotheses,
    centering and normalization; it is not established by this identity. -/

/-- **Log-additivity of the multiplicative composition (paper Eq. 11).**
    `log(λ̂ · ∏ (1 + ε_i)) = log λ̂ + Σ log(1 + ε_i)`,
    under the positivity hypothesis `1 + ε_i > 0`. -/
theorem log_multiplicative_error {n : ℕ} (lamHat : ℝ) (ε : ℕ → ℝ)
    (hLam : 0 < lamHat) (hε : ∀ i ∈ Finset.range n, 0 < 1 + ε i) :
    Real.log (lamHat * ∏ i ∈ Finset.range n, (1 + ε i))
      = Real.log lamHat + ∑ i ∈ Finset.range n, Real.log (1 + ε i) := by
  have h_prod_pos : 0 < ∏ i ∈ Finset.range n, (1 + ε i) :=
    Finset.prod_pos (fun i hi => hε i hi)
  rw [Real.log_mul hLam.ne' h_prod_pos.ne']
  congr 1
  exact Real.log_prod (fun i hi => (hε i hi).ne')

/-- **Upper bound `log(1 + ε) ≤ ε` (paper Eq. 12, upper side).**
    Standard `log(1 + x) ≤ x` for `x > -1`, derived from
    `1 + x ≤ exp(x)`. This one-sided estimate does not control the
    absolute remainder or justify the accumulated CLT linearization. -/
theorem log_one_add_le_self {ε : ℝ} (hε : -1 < ε) :
    Real.log (1 + ε) ≤ ε := by
  have h_pos : 0 < 1 + ε := by linarith
  have h_exp_ge : 1 + ε ≤ Real.exp ε := by
    have := Real.add_one_le_exp ε
    linarith
  have h_log_mono : Real.log (1 + ε) ≤ Real.log (Real.exp ε) :=
    Real.log_le_log h_pos h_exp_ge
  rwa [Real.log_exp] at h_log_mono

end TailOptionPricing
