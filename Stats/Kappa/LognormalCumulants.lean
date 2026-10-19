module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LognormalCumulants — closed-form lognormal cumulants
  (paper Appendix B).

  A nondegenerate lognormal mgf is not finite on any open interval
  around `0`, so the analytic derivative-of-log-mgf definition does
  not apply. This module works directly
  from the closed-form (non-central) moments
      m_k(μ, σ) = exp(k·μ + k²·σ²/2)
  of `X ~ LogNormal(μ, σ²)` (taken as definitional here), defines
  cumulant expressions via the
  moment-cumulant relations, and cumulants of the iid sum
  `S_n = X_1 + ⋯ + X_n` by additivity (`K_i(S_n) = n · K_i(X_1)`).

  Theorems delivered (paper Appendix B):

  * `lognormalCumulant_one`, `_two`, `_three`, `_four` — closed forms.
  * `lognormalSkewness`, `lognormalKurtosis` — closed forms.
  * `lognormal_kappa_tendsto_zero_as_sigma_to_zero`,
    `lognormal_kappa_tendsto_zero_as_n_to_infty` — limits of the
    cumulant proxy (excess kurtosis), which vanishes for Gaussian
    (where κ = 0).

  These proxy limits do not prove the corresponding limits of the
  MAD-based κ_{1,n}. The genuine large-σ MAD limit is established
  separately in `Stats/Kappa/LoulakisLognormal.lean`; the small-σ
  and large-n MAD limits still need their probability bridges.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Stats.Kappa.Basic

@[expose] public section

open Real Filter Topology

namespace TailOptionPricing

/-! ## Exponential power helpers. -/

private lemma exp_pow_two (a : ℝ) : (Real.exp a)^2 = Real.exp (2 * a) := by
  rw [← Real.exp_nat_mul]; norm_cast

private lemma exp_pow_three (a : ℝ) : (Real.exp a)^3 = Real.exp (3 * a) := by
  rw [← Real.exp_nat_mul]; norm_cast

private lemma exp_pow_four (a : ℝ) : (Real.exp a)^4 = Real.exp (4 * a) := by
  rw [← Real.exp_nat_mul]; norm_cast

/-! ## Lognormal moments. -/

/-- Non-central moment `m_k` of `X ~ LogNormal(μ, σ²)`:
    `E[X^k] = exp(k·μ + k²·σ²/2)`.  Definitional here. -/
noncomputable def lognormalMoment (k : ℕ) (μ σ : ℝ) : ℝ :=
  Real.exp ((k : ℝ) * μ + (k : ℝ)^2 * σ^2 / 2)

lemma lognormalMoment_one (μ σ : ℝ) :
    lognormalMoment 1 μ σ = Real.exp (μ + σ^2 / 2) := by
  unfold lognormalMoment; congr 1; push_cast; ring

lemma lognormalMoment_two (μ σ : ℝ) :
    lognormalMoment 2 μ σ = Real.exp (2 * μ + 2 * σ^2) := by
  unfold lognormalMoment; congr 1; push_cast; ring

lemma lognormalMoment_three (μ σ : ℝ) :
    lognormalMoment 3 μ σ = Real.exp (3 * μ + 9 * σ^2 / 2) := by
  unfold lognormalMoment; congr 1; push_cast; ring

lemma lognormalMoment_four (μ σ : ℝ) :
    lognormalMoment 4 μ σ = Real.exp (4 * μ + 8 * σ^2) := by
  unfold lognormalMoment; congr 1; push_cast; ring

/-! ## Single-X cumulants via moment-cumulant relations. -/

/-- `K_1(X) := m_1`. -/
noncomputable def lognormalCumulantOne_single (μ σ : ℝ) : ℝ :=
  lognormalMoment 1 μ σ

/-- `K_2(X) := m_2 − m_1²`. -/
noncomputable def lognormalCumulantTwo_single (μ σ : ℝ) : ℝ :=
  lognormalMoment 2 μ σ - (lognormalMoment 1 μ σ)^2

/-- `K_3(X) := m_3 − 3 m_1 m_2 + 2 m_1³`. -/
noncomputable def lognormalCumulantThree_single (μ σ : ℝ) : ℝ :=
  lognormalMoment 3 μ σ
    - 3 * lognormalMoment 1 μ σ * lognormalMoment 2 μ σ
    + 2 * (lognormalMoment 1 μ σ)^3

/-- `K_4(X) := m_4 − 4 m_1 m_3 − 3 m_2² + 12 m_1² m_2 − 6 m_1⁴`. -/
noncomputable def lognormalCumulantFour_single (μ σ : ℝ) : ℝ :=
  lognormalMoment 4 μ σ
    - 4 * lognormalMoment 1 μ σ * lognormalMoment 3 μ σ
    - 3 * (lognormalMoment 2 μ σ)^2
    + 12 * (lognormalMoment 1 μ σ)^2 * lognormalMoment 2 μ σ
    - 6 * (lognormalMoment 1 μ σ)^4

/-! ## iid-sum cumulants (additivity baked in). -/

/-- `K_1^n` of the lognormal iid sum: `n · K_1(X_1)`. -/
noncomputable def lognormalCumulantSum_one (n : ℕ) (μ σ : ℝ) : ℝ :=
  (n : ℝ) * lognormalCumulantOne_single μ σ

/-- `K_2^n`. -/
noncomputable def lognormalCumulantSum_two (n : ℕ) (μ σ : ℝ) : ℝ :=
  (n : ℝ) * lognormalCumulantTwo_single μ σ

/-- `K_3^n`. -/
noncomputable def lognormalCumulantSum_three (n : ℕ) (μ σ : ℝ) : ℝ :=
  (n : ℝ) * lognormalCumulantThree_single μ σ

/-- `K_4^n`. -/
noncomputable def lognormalCumulantSum_four (n : ℕ) (μ σ : ℝ) : ℝ :=
  (n : ℝ) * lognormalCumulantFour_single μ σ

/-! ## Closed-form cumulant identities (paper Appendix B). -/

/-- **`K_1^n` closed form.**  `K_1^n = n · e^(μ + σ²/2)`. -/
theorem lognormalCumulant_one (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_one n μ σ = (n : ℝ) * Real.exp (μ + σ^2 / 2) := by
  unfold lognormalCumulantSum_one lognormalCumulantOne_single
  rw [lognormalMoment_one]

/-- **`K_2^n` closed form.**  `K_2^n = n · (e^(σ²) − 1) · e^(2μ + σ²)`. -/
theorem lognormalCumulant_two (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_two n μ σ
      = (n : ℝ) * (Real.exp (σ^2) - 1) * Real.exp (2 * μ + σ^2) := by
  unfold lognormalCumulantSum_two lognormalCumulantTwo_single
  rw [lognormalMoment_one, lognormalMoment_two]
  -- `m_1² = e^(2μ + σ²)`
  have h_sq : (Real.exp (μ + σ^2 / 2))^2 = Real.exp (2 * μ + σ^2) := by
    rw [exp_pow_two]; congr 1; ring
  -- `m_2 = e^(2μ + σ²) · e^(σ²)`
  have h_m2 : Real.exp (2 * μ + 2 * σ^2) = Real.exp (2 * μ + σ^2) * Real.exp (σ^2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h_sq, h_m2]; ring

/-- **`K_3^n` closed form.**
    `K_3^n = n · (e^(σ²) − 1)² · (e^(σ²) + 2) · e^(3μ + 3σ²/2)`. -/
theorem lognormalCumulant_three (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_three n μ σ
      = (n : ℝ) * (Real.exp (σ^2) - 1)^2 * (Real.exp (σ^2) + 2)
          * Real.exp (3 * μ + 3 * σ^2 / 2) := by
  unfold lognormalCumulantSum_three lognormalCumulantThree_single
  rw [lognormalMoment_one, lognormalMoment_two, lognormalMoment_three]
  -- Factor each term over `u := e^(3μ + 3σ²/2)`, with `v := e^(σ²)`:
  --   m_3 = u · v^3,  m_1·m_2 = u · v,  m_1^3 = u.
  set v := Real.exp (σ^2) with hv
  set u := Real.exp (3 * μ + 3 * σ^2 / 2) with hu
  have h_m3 : Real.exp (3 * μ + 9 * σ^2 / 2) = u * v^3 := by
    rw [hu, hv, exp_pow_three, ← Real.exp_add]; congr 1; ring
  have h_m1m2 :
      Real.exp (μ + σ^2/2) * Real.exp (2 * μ + 2 * σ^2) = u * v := by
    rw [hu, hv, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h_m1cube : (Real.exp (μ + σ^2/2))^3 = u := by
    rw [exp_pow_three, hu]; congr 1; ring
  rw [h_m3, h_m1cube]
  rw [show (3:ℝ) * Real.exp (μ + σ^2/2) * Real.exp (2 * μ + 2 * σ^2)
        = 3 * (Real.exp (μ + σ^2/2) * Real.exp (2 * μ + 2 * σ^2)) from by ring,
      h_m1m2]
  -- LHS = n · (u v^3 − 3 u v + 2 u);  RHS = n · (v − 1)² · (v + 2) · u.
  -- Polynomial identity: v^3 − 3 v + 2 = (v − 1)² · (v + 2).
  ring

/-- **`K_4^n` closed form.**
    `K_4^n = n · e^(4μ + 2σ²) · (e^(σ²) − 1)²
              · (e^(4σ²) + 2 e^(3σ²) + 3 e^(2σ²) − 6)`. -/
theorem lognormalCumulant_four (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_four n μ σ
      = (n : ℝ) * Real.exp (4 * μ + 2 * σ^2) * (Real.exp (σ^2) - 1)^2
          * (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
             + 3 * Real.exp (2 * σ^2) - 6) := by
  unfold lognormalCumulantSum_four lognormalCumulantFour_single
  rw [lognormalMoment_one, lognormalMoment_two, lognormalMoment_three,
      lognormalMoment_four]
  set v := Real.exp (σ^2) with hv
  set u := Real.exp (4 * μ + 2 * σ^2) with hu
  -- Express each non-central moment product in `u, v`:
  --   m_4 = u · v^6,  m_1·m_3 = u · v^3,  m_2^2 = u · v^2,
  --   m_1^2·m_2 = u · v,  m_1^4 = u.
  have h_m4 : Real.exp (4 * μ + 8 * σ^2) = u * v^6 := by
    rw [hu, hv, show v^6 = v^2 * v^4 from by ring, exp_pow_two, exp_pow_four,
        ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h_m1m3 :
      Real.exp (μ + σ^2/2) * Real.exp (3 * μ + 9 * σ^2/2) = u * v^3 := by
    rw [hu, hv, exp_pow_three, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h_m2sq : (Real.exp (2 * μ + 2 * σ^2))^2 = u * v^2 := by
    rw [hu, hv, exp_pow_two, exp_pow_two, ← Real.exp_add]; congr 1; ring
  have h_m12m2 :
      (Real.exp (μ + σ^2/2))^2 * Real.exp (2 * μ + 2 * σ^2) = u * v := by
    rw [hu, hv, exp_pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h_m1pow4 : (Real.exp (μ + σ^2/2))^4 = u := by
    rw [hu, exp_pow_four]; congr 1; ring
  -- Replace v-powers on the RHS to fold into v^k.
  have hv2 : Real.exp (2 * σ^2) = v^2 := by rw [hv]; exact (exp_pow_two _).symm
  have hv3 : Real.exp (3 * σ^2) = v^3 := by rw [hv]; exact (exp_pow_three _).symm
  have hv4 : Real.exp (4 * σ^2) = v^4 := by rw [hv]; exact (exp_pow_four _).symm
  rw [h_m4, h_m1pow4, hv2, hv3, hv4]
  rw [show (4:ℝ) * Real.exp (μ + σ^2/2) * Real.exp (3 * μ + 9 * σ^2/2)
        = 4 * (Real.exp (μ + σ^2/2) * Real.exp (3 * μ + 9 * σ^2/2)) from by ring,
      h_m1m3, h_m2sq]
  rw [show (12:ℝ) * (Real.exp (μ + σ^2/2))^2 * Real.exp (2 * μ + 2 * σ^2)
        = 12 * ((Real.exp (μ + σ^2/2))^2 * Real.exp (2 * μ + 2 * σ^2)) from by ring,
      h_m12m2]
  -- Polynomial identity in `v`:
  --   v^6 − 4 v^3 − 3 v^2 + 12 v − 6 = (v − 1)² (v^4 + 2 v^3 + 3 v² − 6).
  ring

/-! ## Skewness and kurtosis of the iid sum. -/

/-- Skewness of `S_n` defined via cumulants: `K_3^n / (K_2^n)^(3/2)`. -/
noncomputable def lognormalSkewnessSum (n : ℕ) (μ σ : ℝ) : ℝ :=
  lognormalCumulantSum_three n μ σ / (lognormalCumulantSum_two n μ σ) ^ ((3:ℝ)/2)

/-- Kurtosis of `S_n` defined via cumulants: `3 + K_4^n / (K_2^n)^2`. -/
noncomputable def lognormalKurtosisSum (n : ℕ) (μ σ : ℝ) : ℝ :=
  3 + lognormalCumulantSum_four n μ σ / (lognormalCumulantSum_two n μ σ) ^ 2

/-- **Lognormal skewness (paper Appendix B).**
    `Skew(S_n) = √(e^(σ²) − 1) · (e^(σ²) + 2) / √n`.
    Equivalently the paper's
    `√(e^(σ²) − 1) · (e^(σ²) + 2) · e^((2μ + σ²)/2 − μ − σ²/2) / √n`
    (the exponential factor evaluates to 1). -/
theorem lognormalSkewness (n : ℕ) (μ σ : ℝ) (hn : 0 < n) (hσ : σ ≠ 0) :
    lognormalSkewnessSum n μ σ
      = Real.sqrt (Real.exp (σ^2) - 1) * (Real.exp (σ^2) + 2) / Real.sqrt n := by
  unfold lognormalSkewnessSum
  rw [lognormalCumulant_three n μ σ, lognormalCumulant_two n μ σ]
  set v := Real.exp (σ^2) with hv
  set w := Real.exp (3 * μ + 3 * σ^2 / 2) with hw
  set e2 := Real.exp (2 * μ + σ^2) with he2
  have hv_pos : 0 < v := Real.exp_pos _
  have hw_pos : 0 < w := Real.exp_pos _
  have he2_pos : 0 < e2 := Real.exp_pos _
  have hσ_sq_pos : 0 < σ^2 := by positivity
  have hv_gt_one : 1 < v := by
    rw [hv]; exact Real.one_lt_exp_iff.mpr hσ_sq_pos
  have hv_sub_pos : 0 < v - 1 := by linarith
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  -- e2^(3/2) = w
  have h_e2_pow : e2 ^ ((3:ℝ)/2) = w := by
    rw [he2, hw, ← Real.exp_mul]; congr 1; ring
  -- (K_2^n)^(3/2) = n^(3/2) · (v-1)^(3/2) · w
  have h_K2n_pow :
      ((n:ℝ) * (v - 1) * e2) ^ ((3:ℝ)/2)
        = (n:ℝ) ^ ((3:ℝ)/2) * (v - 1) ^ ((3:ℝ)/2) * w := by
    rw [Real.mul_rpow (by positivity) he2_pos.le,
        Real.mul_rpow hn_pos.le hv_sub_pos.le, h_e2_pow]
  rw [h_K2n_pow]
  -- After rewrites: goal is
  --   (n · (v-1)² · (v+2) · w) / (n^(3/2) · (v-1)^(3/2) · w)
  --     = √(v-1) · (v+2) / √n
  -- Identify √ with ^(1/2):
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  -- Split `(v-1)² = (v-1)^(1/2) · (v-1)^(3/2)` and `n^(3/2) = n · n^(1/2)`:
  have h_v_split :
      (v - 1) ^ 2 = (v - 1) ^ ((1:ℝ)/2) * (v - 1) ^ ((3:ℝ)/2) := by
    have h1 : (v - 1) ^ (2:ℝ) = (v - 1) ^ 2 :=
      Real.rpow_natCast (v - 1) 2
    rw [← h1, ← Real.rpow_add hv_sub_pos]
    congr 1; norm_num
  have h_n_split : (n:ℝ) ^ ((3:ℝ)/2) = (n:ℝ) * (n:ℝ) ^ ((1:ℝ)/2) := by
    rw [show ((3:ℝ)/2) = (1:ℝ) + 1/2 from by norm_num,
        Real.rpow_add hn_pos, Real.rpow_one]
  rw [h_v_split, h_n_split]
  -- Goal:
  --   (n · ((v-1)^(1/2) · (v-1)^(3/2)) · (v+2) · w)
  --     / ((n · n^(1/2)) · (v-1)^(3/2) · w)
  --     = (v-1)^(1/2) · (v+2) / n^(1/2)
  -- Cancel n, (v-1)^(3/2), w; field_simp + ring.
  have hn_ne : (n:ℝ) ≠ 0 := hn_pos.ne'
  have hw_ne : w ≠ 0 := hw_pos.ne'
  have h_v32_ne : (v - 1) ^ ((3:ℝ)/2) ≠ 0 := (Real.rpow_pos_of_pos hv_sub_pos _).ne'
  have h_n12_ne : (n:ℝ) ^ ((1:ℝ)/2) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
  field_simp

/-- **Lognormal kurtosis (paper Appendix B).**
    `Kurt(S_n) = 3 + (e^(2σ²) · (e^(σ²) · (e^(σ²) + 2) + 3) − 6) / n`.
    Equivalent expansion:
    `Kurt(S_n) = 3 + (e^(4σ²) + 2 e^(3σ²) + 3 e^(2σ²) − 6) / n`. -/
theorem lognormalKurtosis (n : ℕ) (μ σ : ℝ) (hn : 0 < n) (hσ : σ ≠ 0) :
    lognormalKurtosisSum n μ σ
      = 3 + (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
             + 3 * Real.exp (2 * σ^2) - 6) / (n : ℝ) := by
  unfold lognormalKurtosisSum
  rw [lognormalCumulant_four n μ σ, lognormalCumulant_two n μ σ]
  set v := Real.exp (σ^2) with hv
  set e2 := Real.exp (2 * μ + σ^2) with he2
  set e42 := Real.exp (4 * μ + 2 * σ^2) with he42
  have hv_pos : 0 < v := Real.exp_pos _
  have he2_pos : 0 < e2 := Real.exp_pos _
  have he42_pos : 0 < e42 := Real.exp_pos _
  have hσ_sq_pos : 0 < σ^2 := by positivity
  have hv_gt_one : 1 < v := by
    rw [hv]; exact Real.one_lt_exp_iff.mpr hσ_sq_pos
  have hv_sub_pos : 0 < v - 1 := by linarith
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_e2sq : e2 ^ 2 = e42 := by
    rw [he2, he42, exp_pow_two]; congr 1; ring
  have h_K2sq :
      ((n:ℝ) * (v - 1) * e2) ^ 2 = (n:ℝ)^2 * (v - 1)^2 * e42 := by
    rw [show ((n:ℝ) * (v - 1) * e2) ^ 2
          = (n:ℝ)^2 * (v - 1)^2 * e2^2 from by ring, h_e2sq]
  rw [h_K2sq]
  have hn_ne : (n:ℝ) ≠ 0 := hn_pos.ne'
  have hv_sub_sq_ne : (v - 1)^2 ≠ 0 := pow_ne_zero _ hv_sub_pos.ne'
  have he42_ne : e42 ≠ 0 := he42_pos.ne'
  field_simp

/-! ## Cumulant proxy for κ (excess kurtosis) and its limits.

    This module uses the cumulant-expansion proxy: the excess-kurtosis
    expression of the iid sum. It vanishes at the Gaussian reference.
    The small-σ and large-n proxy limits below do not identify this
    expression with the MAD-based κ or prove its corresponding limits. -/

/-- Cumulant-expansion proxy for `κ_{1, n}` of the lognormal iid sum:
    excess kurtosis, equal to zero for the Gaussian limit. -/
noncomputable def lognormalKappaProxy (n : ℕ) (μ σ : ℝ) : ℝ :=
  lognormalKurtosisSum n μ σ - 3

/-- The kappa proxy as a continuous closed form valid for all σ.  This
    extends `lognormalKurtosis` (which is stated for `σ ≠ 0`) to all
    `σ ∈ ℝ` — the expression
    `(e^(4σ²) + 2 e^(3σ²) + 3 e^(2σ²) − 6) / n` evaluates to `0` at
    `σ = 0` and is continuous. -/
lemma lognormalKappaProxy_closed_form (n : ℕ) (μ σ : ℝ) (hn : 0 < n) :
    lognormalKappaProxy n μ σ
      = (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
         + 3 * Real.exp (2 * σ^2) - 6) / (n : ℝ) := by
  unfold lognormalKappaProxy lognormalKurtosisSum
  rw [lognormalCumulant_four n μ σ, lognormalCumulant_two n μ σ]
  set v := Real.exp (σ^2) with hv
  set e2 := Real.exp (2 * μ + σ^2) with he2
  set e42 := Real.exp (4 * μ + 2 * σ^2) with he42
  have he2_pos : 0 < e2 := Real.exp_pos _
  have he42_pos : 0 < e42 := Real.exp_pos _
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_e2sq : e2 ^ 2 = e42 := by
    rw [he2, he42, exp_pow_two]; congr 1; ring
  have h_K2sq :
      ((n:ℝ) * (v - 1) * e2) ^ 2 = (n:ℝ)^2 * (v - 1)^2 * e42 := by
    rw [show ((n:ℝ) * (v - 1) * e2) ^ 2
          = (n:ℝ)^2 * (v - 1)^2 * e2^2 from by ring, h_e2sq]
  rw [h_K2sq]
  -- Goal: 3 + n · e42 · (v-1)² · (v^4 + 2 v^3 + 3 v² − 6) / (n² · (v-1)² · e42) − 3
  --      = (v^4 + 2 v^3 + 3 v² − 6) / n
  -- where v^k = e^(kσ²).
  have hn_ne : (n:ℝ) ≠ 0 := hn_pos.ne'
  have he42_ne : e42 ≠ 0 := he42_pos.ne'
  -- Trickier: when σ = 0, v = 1, so (v-1)² = 0 and we cannot cancel.
  -- BUT the numerator polynomial vanishes at v = 1: it has (v-1)² as a factor
  -- (as established in `lognormalCumulant_four`).  Use that factorisation
  -- to cancel symbolically.
  -- Specifically, e^(4σ²) + 2 e^(3σ²) + 3 e^(2σ²) - 6 = (v-1)² · Q(v) where
  --   Q(v) = (v^4 + 2 v^3 + 3 v² − 6) / (v-1)²  ... not algebraic.
  -- Actually the identity we proved: K_4 = e42 · (v-1)² · (v^4 + ...) where
  -- v^4 + 2 v^3 + 3 v² − 6 is the *raw* polynomial, NOT divided by (v-1)².
  -- So if v = 1, K_4 = 0 (since (v-1)² = 0), and the proxy is 0/0 — actually
  -- 0/0 should give 0 here once we cancel formally. The trouble is that
  -- (v-1)² appears in both num and denom.
  -- Solution: combine the factor (v-1)² in the numerator (from K_4 closed form)
  -- with the (v-1)² in the denominator. Then no issue when v = 1.
  rw [show Real.exp (4 * σ^2) = v^4 from by rw [hv, exp_pow_four],
      show Real.exp (3 * σ^2) = v^3 from by rw [hv, exp_pow_three],
      show Real.exp (2 * σ^2) = v^2 from by rw [hv, exp_pow_two]]
  rcases eq_or_ne (v - 1) 0 with hv1 | hv1
  · -- v = 1, i.e. σ = 0 (or σ² = 0). Both sides vanish.
    have h_v_eq : v = 1 := by linarith
    rw [h_v_eq]
    -- Both sides: 3 + n · e42 · 0 · (...) / (n² · 0 · e42) − 3, and
    -- (1 + 2 + 3 − 6) / n = 0. The LHS has 0/0, but Lean treats x/0 = 0.
    simp [pow_two]
    ring
  · -- v ≠ 1: legitimate cancellation.
    have hv_sub_sq_ne : (v - 1)^2 ≠ 0 := pow_ne_zero _ hv1
    field_simp
    ring

/-- **`κ_{1, n} → 0` as `σ → 0`** (paper Appendix B; cumulant-expansion
    formulation).  The excess-kurtosis proxy `lognormalKappaProxy n μ σ`
    tends to `0` as `σ → 0` for any fixed `n ≥ 1`.  Heuristic: a low-σ
    lognormal converges to a Gaussian (`κ = 0`).  Algebraic via the
    continuity of `Real.exp` at `0`. -/
theorem lognormal_kappa_tendsto_zero_as_sigma_to_zero
    (n : ℕ) (μ : ℝ) (hn : 0 < n) :
    Tendsto (fun σ => lognormalKappaProxy n μ σ) (𝓝 0) (𝓝 0) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  -- Rewrite using the closed form.
  have h_eq : (fun σ => lognormalKappaProxy n μ σ)
      = (fun σ => (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
                   + 3 * Real.exp (2 * σ^2) - 6) / (n : ℝ)) := by
    funext σ
    exact lognormalKappaProxy_closed_form n μ σ hn
  rw [h_eq]
  -- As σ → 0, each exp(k σ²) → exp 0 = 1; numerator → 1 + 2 + 3 − 6 = 0;
  -- ratio → 0/n = 0.
  have h_cont : Continuous (fun σ : ℝ =>
      (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
       + 3 * Real.exp (2 * σ^2) - 6) / (n : ℝ)) := by
    fun_prop
  have h_val : ((Real.exp (4 * (0:ℝ)^2) + 2 * Real.exp (3 * (0:ℝ)^2)
                 + 3 * Real.exp (2 * (0:ℝ)^2) - 6) / (n : ℝ)) = 0 := by
    have hz : (0:ℝ)^2 = 0 := by norm_num
    rw [hz, mul_zero, mul_zero, mul_zero, Real.exp_zero]
    norm_num
  have h_tendsto := h_cont.tendsto 0
  rw [h_val] at h_tendsto
  exact h_tendsto

/-- **`κ_{1, n} → 0` as `n → ∞`** (paper Appendix B).  The
    excess-kurtosis proxy tends to `0` along `atTop` for any fixed
    `μ, σ` (`σ ≠ 0` hypothesis is paper convention; the proof goes
    through for all σ).

    The paper frames this as a CLT-convergence signature, but the
    closed form `lognormalKappaProxy_closed_form` already exhibits
    `lognormalKappaProxy n μ σ = C(σ) / n` for `n ≥ 1`, with
        `C(σ) := e^(4σ²) + 2·e^(3σ²) + 3·e^(2σ²) − 6`.
    The limit is then elementary `Tendsto (C / ·) atTop (𝓝 0)` — no
    CLT machinery required. -/
theorem lognormal_kappa_tendsto_zero_as_n_to_infty
    (μ σ : ℝ) (_hσ : σ ≠ 0) :
    Tendsto (fun n : ℕ => lognormalKappaProxy n μ σ) atTop (𝓝 0) := by
  set C : ℝ :=
    Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2) + 3 * Real.exp (2 * σ^2) - 6
    with hC
  -- `C/n → 0` as `n → ∞` along `ℕ`.
  have h_inv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h_decay : Tendsto (fun n : ℕ => C * (1 / n)) atTop (𝓝 (C * 0)) :=
    h_inv.const_mul C
  rw [mul_zero] at h_decay
  -- For `n ≥ 1`, `lognormalKappaProxy n μ σ = C * (1/n)`.
  refine h_decay.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  show C * (1 / n) = lognormalKappaProxy n μ σ
  rw [lognormalKappaProxy_closed_form n μ σ hn, ← hC]
  have hn_ne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

end TailOptionPricing
