/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.CubicStudent — Cubic Student T (α = 3) closed form and Loulakis identity.

  For iid `X_i` with the cubic Student PDF
      `p(x) = 6√3 / (π · (x² + 3)²)`     (paper Eq. 8),
  the sum `S_n` has MAD (Eq. 10)
      `M(n) = 2√3/π · (e^n · n^(−n) · Γ(n+1, n) − 1)`,
  where `Γ(a, z)` is the upper incomplete-Gamma.  This module
  formalises the closed form (Eq. 9) plus the algebraic Loulakis
  identity (Appendix A)
      `Γ(n+1, n) = n! · e^(-n) · Σ_{m=0}^n n^m/m!`.

  The Stirling/Laplace asymptotic of `kappa_cubicStudent`
  (`log(n) · κ_{1, n} → log(π²/4)`) lives in
  `Stats.Kappa.CubicStudentAsymptotic`.

  See `Stats/Kappa.lean` for the umbrella module.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Stats.Kappa.Basic

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing


/-! ## Cubic Student T (α = 3) closed form (paper Eq. 9, 10).

    For iid `X_i` distributed with the cubic Student PDF
        p(x) = 6√3 / (π · (x² + 3)²)   (paper Eq. 8),
    the sum `S_n` has MAD (Eq. 10)
        M(n) = 2√3/π · (e^n · n^(−n) · Γ(n+1, n) − 1)   for `n ≥ 2`,
    where `Γ(a, z)` is the upper incomplete-Gamma function
        Γ(a, z) := ∫_z^∞ t^(a−1) · e^(−t) dt.
    Substituting into Eq. 1 yields the closed-form `κ_{1,n}` (Eq. 9). -/

/-- **Cubic Student T PDF (paper Eq. 8).**  The density
        p(x) := 6√3 / (π · (x² + 3)²),   x ∈ ℝ,
    of the cubic Student distribution — a Student-t with 3 degrees of
    freedom, rescaled so that its variance is `3` and its tail index
    is the integer `α = 3`.  Definitional content only; the MAD of
    the iid sum is the `cubicStudentSumMAD` below. -/
noncomputable def cubicStudentDensity (x : ℝ) : ℝ :=
  6 * Real.sqrt 3 / (Real.pi * (x ^ 2 + 3) ^ 2)

/-- The cubic Student density is strictly positive everywhere. -/
theorem cubicStudentDensity_pos (x : ℝ) : 0 < cubicStudentDensity x := by
  unfold cubicStudentDensity
  have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 < Real.pi := Real.pi_pos
  have h3 : 0 < x ^ 2 + 3 := by positivity
  positivity

/-- The cubic Student density is symmetric about `0`. -/
theorem cubicStudentDensity_neg (x : ℝ) :
    cubicStudentDensity (-x) = cubicStudentDensity x := by
  unfold cubicStudentDensity
  congr 2
  ring

/-- **Upper incomplete Gamma** `Γ(a, z) := ∫_z^∞ t^(a−1) · e^(−t) dt`.
    Local definition; Mathlib has the complete `Real.Gamma` but no
    upper-incomplete version. -/
noncomputable def incompleteGamma (a z : ℝ) : ℝ :=
  ∫ t in Set.Ioi z, t ^ (a - 1) * Real.exp (-t)

/-- **Cubic Student T sum-MAD (paper Eq. 10).**  For `n ≥ 2`,
        `cubicStudentSumMAD n := 2·√3/π · (e^n · n^(−n) · Γ(n+1, n) − 1)`.

    At `n = 1` the formula is `2√3/π`, the MAD of the cubic Student
    itself.  Definition follows the paper directly; deriving from the
    underlying PDF (Eq. 8) is research-scale (Fourier inversion of the
    characteristic function `(1 + √3|ω|)^n · e^(−n√3|ω|)`). -/
noncomputable def cubicStudentSumMAD (n : ℕ) : ℝ :=
  if n = 1 then 2 * Real.sqrt 3 / Real.pi
  else 2 * Real.sqrt 3 / Real.pi *
    (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1)

/-- **Cubic Student MAD at the unit baseline.**  By construction
    `cubicStudentSumMAD 1 = 2√3/π`, matching the paper's Eq. 10 for
    `n = 1`. -/
theorem cubicStudentSumMAD_one : cubicStudentSumMAD 1 = 2 * Real.sqrt 3 / Real.pi := by
  unfold cubicStudentSumMAD; simp

/-- **Cubic Student MAD for `n ≥ 2`** in unfolded form. -/
theorem cubicStudentSumMAD_succ {n : ℕ} (hn : 2 ≤ n) :
    cubicStudentSumMAD n = 2 * Real.sqrt 3 / Real.pi *
      (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1) := by
  have hn_ne : n ≠ 1 := by omega
  unfold cubicStudentSumMAD
  simp [hn_ne]

/-! ### Loulakis identity for the upper incomplete Gamma (Appendix A).

Algebraic identity underlying the paper's Eq. 10 derivation:
    `Γ(n+1, n) = n! · e^(-n) · Σ_{m=0}^n n^m / m!`,    n ∈ ℕ.

The proof exhibits the explicit antiderivative
    `F_n(t) := -e^(-t) · Σ_{k=0}^n (n!/k!) · t^k`
of `t ↦ t^n · e^(-t)` and applies FTC on `(n, ∞)`, noting
`F_n(t) → 0` as `t → ∞` by exponential decay. -/

/-- Polynomial appearing in the Loulakis identity:
    `loulakisPoly n t := Σ_{k=0}^n (n!/k!) · t^k`. -/
private noncomputable def loulakisPoly (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((n.factorial : ℝ) / k.factorial) * t ^ k

/-- Antiderivative of `t ↦ t^n · e^(-t)` used to prove the Loulakis
    identity:  `loulakisAntideriv n t := -e^(-t) · loulakisPoly n t`. -/
private noncomputable def loulakisAntideriv (n : ℕ) (t : ℝ) : ℝ :=
  -Real.exp (-t) * loulakisPoly n t

private lemma loulakisPoly_zero_eq (t : ℝ) : loulakisPoly 0 t = 1 := by
  simp [loulakisPoly]

private lemma loulakisPoly_succ (n : ℕ) (t : ℝ) :
    loulakisPoly (n + 1) t = ((n : ℝ) + 1) * loulakisPoly n t + t ^ (n + 1) := by
  unfold loulakisPoly
  rw [Finset.sum_range_succ]
  have h_inner : ∑ k ∈ Finset.range (n + 1),
        (((n + 1).factorial : ℝ) / k.factorial) * t ^ k
      = ((n : ℝ) + 1) *
        ∑ k ∈ Finset.range (n + 1), ((n.factorial : ℝ) / k.factorial) * t ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros k _
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have h_last : (((n + 1).factorial : ℝ) / ((n + 1).factorial : ℝ)) * t ^ (n + 1)
      = t ^ (n + 1) := by
    have : ((((n + 1).factorial : ℕ) : ℝ) / ((n + 1).factorial : ℝ)) = 1 :=
      div_self (Nat.cast_ne_zero.mpr (n + 1).factorial_ne_zero)
    rw [this, one_mul]
  rw [h_inner, h_last]

private lemma loulakisAntideriv_zero_eq (t : ℝ) :
    loulakisAntideriv 0 t = -Real.exp (-t) := by
  unfold loulakisAntideriv
  rw [loulakisPoly_zero_eq, mul_one]

private lemma loulakisAntideriv_succ (n : ℕ) (t : ℝ) :
    loulakisAntideriv (n + 1) t =
      ((n : ℝ) + 1) * loulakisAntideriv n t - Real.exp (-t) * t ^ (n + 1) := by
  unfold loulakisAntideriv
  rw [loulakisPoly_succ]
  ring

private lemma hasDerivAt_exp_neg' (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  have h : HasDerivAt (fun s : ℝ => -s) (-(1 : ℝ)) t := (hasDerivAt_id t).neg
  have := h.exp
  simp only [mul_neg, mul_one] at this
  exact this

private lemma loulakisAntideriv_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (loulakisAntideriv n) (t ^ n * Real.exp (-t)) t := by
  induction n with
  | zero =>
    have h_neg_exp : HasDerivAt (fun s : ℝ => -Real.exp (-s)) (Real.exp (-t)) t := by
      have := (hasDerivAt_exp_neg' t).neg
      simpa using this
    have heq : loulakisAntideriv 0 = fun s : ℝ => -Real.exp (-s) := by
      funext s; exact loulakisAntideriv_zero_eq s
    rw [heq]
    simpa [pow_zero, one_mul] using h_neg_exp
  | succ n ih =>
    have heq : loulakisAntideriv (n + 1) =
        fun s : ℝ =>
          ((n : ℝ) + 1) * loulakisAntideriv n s - Real.exp (-s) * s ^ (n + 1) := by
      funext s; exact loulakisAntideriv_succ n s
    rw [heq]
    have h_first : HasDerivAt (fun s => ((n : ℝ) + 1) * loulakisAntideriv n s)
        (((n : ℝ) + 1) * (t ^ n * Real.exp (-t))) t :=
      ih.const_mul ((n : ℝ) + 1)
    have h_pow : HasDerivAt (fun s : ℝ => s ^ (n + 1))
        (((n + 1 : ℕ) : ℝ) * t ^ ((n + 1) - 1)) t := hasDerivAt_pow (n + 1) t
    have h_pow' : HasDerivAt (fun s : ℝ => s ^ (n + 1))
        (((n : ℝ) + 1) * t ^ n) t := by
      have : ((n + 1 : ℕ) : ℝ) * t ^ ((n + 1) - 1) = ((n : ℝ) + 1) * t ^ n := by
        push_cast; rfl
      rw [this] at h_pow
      exact h_pow
    have h_second : HasDerivAt (fun s => Real.exp (-s) * s ^ (n + 1))
        (-Real.exp (-t) * t ^ (n + 1) + Real.exp (-t) * (((n : ℝ) + 1) * t ^ n)) t :=
      (hasDerivAt_exp_neg' t).mul h_pow'
    have h_combined := h_first.sub h_second
    convert h_combined using 1
    have : t ^ (n + 1) = t * t ^ n := by rw [pow_succ, mul_comm]
    rw [this]
    ring

private lemma loulakisAntideriv_tendsto_zero (n : ℕ) :
    Tendsto (loulakisAntideriv n) atTop (𝓝 0) := by
  have heq : (loulakisAntideriv n) = fun t : ℝ =>
      -∑ k ∈ Finset.range (n + 1),
        ((n.factorial : ℝ) / k.factorial) * (t ^ k * Real.exp (-t)) := by
    funext t
    unfold loulakisAntideriv loulakisPoly
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros k _
    ring
  rw [heq]
  have h_sum : Tendsto
      (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
        ((n.factorial : ℝ) / k.factorial) * (t ^ k * Real.exp (-t)))
      atTop (𝓝 (∑ _k ∈ Finset.range (n + 1), (0 : ℝ))) := by
    apply tendsto_finset_sum
    intros k _
    have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul
      ((n.factorial : ℝ) / k.factorial)
    simpa using h
  have h_zero : (∑ _k ∈ Finset.range (n + 1), (0 : ℝ)) = 0 := by simp
  rw [h_zero] at h_sum
  have h_neg := h_sum.neg
  rw [neg_zero] at h_neg
  exact h_neg

private lemma integrableOn_pow_mul_exp_neg_Ioi (n : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t)) (Set.Ioi z) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := loulakisAntideriv n) (l := 0)
  · exact (loulakisAntideriv_hasDerivAt n z).continuousAt.continuousWithinAt
  · intros t _; exact loulakisAntideriv_hasDerivAt n t
  · intros t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hz ht)
    exact mul_nonneg (pow_nonneg ht0 n) (Real.exp_pos _).le
  · exact loulakisAntideriv_tendsto_zero n

private lemma integral_Ioi_pow_mul_exp_neg (n : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    ∫ t in Set.Ioi z, t ^ n * Real.exp (-t)
      = Real.exp (-z) * loulakisPoly n z := by
  have h_int := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := loulakisAntideriv n)
    (f' := fun t : ℝ => t ^ n * Real.exp (-t))
    (m := (0 : ℝ))
    (a := z)
    ((loulakisAntideriv_hasDerivAt n z).continuousAt.continuousWithinAt)
    (fun x _ => loulakisAntideriv_hasDerivAt n x)
    (integrableOn_pow_mul_exp_neg_Ioi n z hz)
    (loulakisAntideriv_tendsto_zero n)
  rw [h_int]
  unfold loulakisAntideriv
  ring

/-- **Loulakis identity for the upper incomplete Gamma** (paper Appendix A).
    For every `n ∈ ℕ`,
        `Γ(n+1, n) = n! · e^(-n) · Σ_{m=0}^n n^m / m!`.
    Closed-form algebraic evaluation of the integral defining
    `incompleteGamma`, obtained by exhibiting the explicit
    polynomial-times-exponential antiderivative. -/
theorem incompleteGamma_loulakis (n : ℕ) :
    incompleteGamma (n + 1) n
      = (n.factorial : ℝ) * Real.exp (-(n : ℝ)) *
          ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k.factorial : ℝ) := by
  -- Step 1: rewrite `Γ(n+1, n)` to `∫ t in Ioi n, t^n · e^(-t)`.
  have h_rpow : ∀ t ∈ Set.Ioi (n : ℝ),
      t ^ (((n : ℝ) + 1) - 1) * Real.exp (-t) = t ^ n * Real.exp (-t) := by
    intros t ht
    have ht_pos : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht
    have : ((n : ℝ) + 1) - 1 = (n : ℝ) := by ring
    rw [this]
    rw [show (t : ℝ) ^ (n : ℝ) = t ^ n from
      by exact_mod_cast Real.rpow_natCast t n]
  have h_integral : incompleteGamma ((n : ℝ) + 1) n
      = ∫ t in Set.Ioi (n : ℝ), t ^ n * Real.exp (-t) := by
    unfold incompleteGamma
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    exact h_rpow
  rw [h_integral, integral_Ioi_pow_mul_exp_neg n n (Nat.cast_nonneg n)]
  -- Step 2: rearrange the Σ.
  unfold loulakisPoly
  have h_terms : ∀ k, ((n.factorial : ℝ) / (k.factorial : ℝ)) * (n : ℝ) ^ k =
      (n.factorial : ℝ) * ((n : ℝ) ^ k / (k.factorial : ℝ)) := by
    intro k
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
  simp only [h_terms]
  rw [← Finset.mul_sum]
  ring

/-- **Cubic Student sum-MAD in Loulakis form** (paper Eq. 10, Appendix A).
    For `n ≥ 2`,
        `cubicStudentSumMAD n = (2 √3 · n!) / (π · n^n) · Σ_{m=0}^{n−1} n^m/m!`.
    Direct corollary of `incompleteGamma_loulakis` substituted into
    `cubicStudentSumMAD_succ`, separating the `m = n` term of the
    Loulakis sum (whose value is `n^n/n!`) which cancels the leading
    `-1` in `cubicStudentSumMAD_succ`. -/
theorem cubicStudentSumMAD_loulakis_form {n : ℕ} (hn : 2 ≤ n) :
    cubicStudentSumMAD n
      = (2 * Real.sqrt 3 * (n.factorial : ℝ)) / (Real.pi * (n : ℝ) ^ n) *
          ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k.factorial : ℝ) := by
  have hn_pos : 0 < n := by omega
  have hn_pos_R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_ne_R : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  have h_pow_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn_pos_R n
  have h_pow_ne : ((n : ℝ) ^ n) ≠ 0 := h_pow_pos.ne'
  have h_fact_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_ne : Real.pi ≠ 0 := h_pi_pos.ne'
  have h_npow_neg : ((n : ℝ) ^ (-(n : ℝ))) = ((n : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg hn_pos_R.le, Real.rpow_natCast]
  have h_exp_cancel : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- Abbreviate the sum to keep `ring` happy.
  set S : ℝ := ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k.factorial : ℝ) with hS
  rw [cubicStudentSumMAD_succ hn, incompleteGamma_loulakis n,
      Finset.sum_range_succ, ← hS, h_npow_neg]
  -- Goal now: 2√3/π · (e^n · (n^n)⁻¹ · (n! · e^(-n) · (S + n^n/n!)) - 1)
  --        = (2√3 · n!) / (π · n^n) · S
  -- Rewrite the inner expression algebraically.
  have h_inner : Real.exp (n : ℝ) * ((n : ℝ) ^ n)⁻¹ *
        ((n.factorial : ℝ) * Real.exp (-(n : ℝ)) *
          (S + (n : ℝ) ^ n / (n.factorial : ℝ))) - 1
      = (n.factorial : ℝ) / ((n : ℝ) ^ n) * S := by
    have h_reorder :
        Real.exp (n : ℝ) * ((n : ℝ) ^ n)⁻¹ *
          ((n.factorial : ℝ) * Real.exp (-(n : ℝ)) *
            (S + (n : ℝ) ^ n / (n.factorial : ℝ)))
        = (Real.exp (n : ℝ) * Real.exp (-(n : ℝ))) *
          ((n.factorial : ℝ) * ((n : ℝ) ^ n)⁻¹ *
            (S + (n : ℝ) ^ n / (n.factorial : ℝ))) := by ring
    rw [h_reorder, h_exp_cancel, one_mul]
    field_simp
    ring
  rw [h_inner]
  field_simp

/-- **Cubic Student κ closed form (paper Eq. 9).**  Provided the
    incomplete-Gamma evaluation gives a positive `cubicStudentSumMAD n`
    for the chosen `n`, the κ-metric is
        κ(1, n) = 2 − log(n) / log(e^n · n^(−n) · Γ(n+1, n) − 1).

    Algebraic specialisation of `kappa_eq_ratio` to the closed-form MAD.
    Positivity hypothesis `0 < e^n · n^(−n) · Γ(n+1, n) − 1` is the
    paper's implicit assumption (verified numerically for `n ≥ 2`). -/
theorem kappa_cubicStudent {n : ℕ} (hn : 2 ≤ n)
    (h_pos : 0 < Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1) :
    kappa cubicStudentSumMAD 1 n = 2 - Real.log n /
      Real.log (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1) := by
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_base_pos : 0 < 2 * Real.sqrt 3 / Real.pi := by positivity
  have hM1 : cubicStudentSumMAD 1 = 2 * Real.sqrt 3 / Real.pi := cubicStudentSumMAD_one
  have hMn : cubicStudentSumMAD n = (2 * Real.sqrt 3 / Real.pi) *
        (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1) :=
    cubicStudentSumMAD_succ hn
  have hM1_pos : 0 < cubicStudentSumMAD 1 := by rw [hM1]; exact h_base_pos
  have hMn_pos : 0 < cubicStudentSumMAD n := by
    rw [hMn]; exact mul_pos h_base_pos h_pos
  -- log(Mn) - log(M1) = log(...)
  have h_log_diff : Real.log (cubicStudentSumMAD n) - Real.log (cubicStudentSumMAD 1)
      = Real.log (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1) := by
    rw [hMn, hM1, Real.log_mul h_base_pos.ne' h_pos.ne']
    ring
  unfold kappa
  rw [h_log_diff,
      show Real.log ((1:ℕ):ℝ) = 0 from by simp]
  ring


end TailOptionPricing
