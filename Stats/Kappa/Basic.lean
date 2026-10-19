module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.Basic — abstract κ framework and decompositions.

  This submodule contains:

    1. Abstract κ-definition and ratio identity.
    2. Stable-basin invariance: `M(n) = c · n^(1/ᾱ)` ⇒ `κ(n₀, n) = 2 − ᾱ`.
    3. Effective stable index `ᾱ` (paper Eq. 5), square-root and linear
       reference curves (`ᾱ = 2`, `ᾱ = 1`).
    4. The paper's sample-size power expression `n_ν` (Eq. 7).
    5. κ additive decomposition (paper Eq. 2): telescoping the
       partial log-ratios.

  The input `M` is a supplied real function. Identifying it with the actual
  MAD of an iid sum is a separate probability theorem. In particular, the
  linear reference curve is not a finite MAD for a Cauchy law: that law
  lacks the finite mean required by the paper's Definition 1.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Stats.Pareto
public import Stats.Theorem1

@[expose] public section

open Real Set Filter Topology

namespace TailOptionPricing

/-! ## Abstract κ-metric. -/

/-- **Abstract κ expression** from Taleb, arXiv:1802.05495v3, Definition 1.
    For a supplied function `M : ℕ → ℝ`, the expression at base
    `n₀` and horizon `n` is
        κ(n₀, n) := 2 − log(n / n₀) / log(M(n) / M(n₀)).
    Encoded via `log(a) − log(b) = log(a/b)` for `a, b > 0` to keep the
    division explicit at the syntactic level. Its probability interpretation
    requires `M` to be the genuine MAD of an iid partial sum. Lean's total
    logarithm and division also give values outside the paper's domain. -/
noncomputable def kappa (M : ℕ → ℝ) (n₀ n : ℕ) : ℝ :=
  2 - (Real.log n - Real.log n₀) / (Real.log (M n) - Real.log (M n₀))

/-- **κ-metric in ratio form** (paper Eq. 1 verbatim).  When `n₀, n > 0`
    and `M(n₀), M(n) > 0`, the κ-metric equals the ratio form
        2 − log(n / n₀) / log(M(n) / M(n₀)). -/
theorem kappa_eq_ratio {M : ℕ → ℝ} {n₀ n : ℕ}
    (hn₀ : 0 < n₀) (hn : 0 < n)
    (hM₀ : 0 < M n₀) (hMn : 0 < M n) :
    kappa M n₀ n = 2 - Real.log ((n:ℝ)/(n₀:ℝ)) / Real.log ((M n)/(M n₀)) := by
  unfold kappa
  have hn₀_pos : (0:ℝ) < n₀ := Nat.cast_pos.mpr hn₀
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.log_div hn_pos.ne' hn₀_pos.ne', Real.log_div hMn.ne' hM₀.ne']

/-! ## Stable-basin invariance: `M(n) = c · n^(1/ᾱ)` ⇒ `κ = 2 − ᾱ`. -/

/-- **Power-curve identity**, corresponding to Taleb, arXiv:1802.05495v3,
    subsection "Equivalence for stable distributions". If a supplied function
    satisfies
        `M(n) = c · n^(1/ᾱ)`
    for `c > 0` and `ᾱ > 0`, then `κ(n₀, n) = 2 − ᾱ` for every
    `n > n₀ ≥ 1`. This proves an algebraic identity under `hM_form`;
    deriving that hypothesis from an actual distribution remains separate.
    A finite-mean stable-law interpretation requires index greater than 1,
    despite the paper including the boundary index 1 in this subsection. -/
theorem kappa_stable_invariance {M : ℕ → ℝ} {c ᾱ : ℝ}
    (hc : 0 < c) (hᾱ : 0 < ᾱ)
    (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ) ^ ((1:ℝ) / ᾱ))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 2 - ᾱ := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h_lt
  have hn₀_pos : (0:ℝ) < n₀ := Nat.cast_pos.mpr hn₀
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hn₀_lt_n : (n₀:ℝ) < n := by exact_mod_cast h_lt
  have hᾱ_ne : ᾱ ≠ 0 := hᾱ.ne'
  have h_inv_ᾱ_pos : 0 < 1 / ᾱ := by positivity
  -- Closed forms:
  have hMn₀ : M n₀ = c * (n₀:ℝ) ^ ((1:ℝ) / ᾱ) := hM_form n₀ hn₀
  have hMn : M n = c * (n:ℝ) ^ ((1:ℝ) / ᾱ) := hM_form n hn
  -- Positivity:
  have hp₀ : 0 < (n₀:ℝ) ^ ((1:ℝ) / ᾱ) := Real.rpow_pos_of_pos hn₀_pos _
  have hp_n : 0 < (n:ℝ) ^ ((1:ℝ) / ᾱ) := Real.rpow_pos_of_pos hn_pos _
  have hMn₀_pos : 0 < M n₀ := by rw [hMn₀]; positivity
  have hMn_pos : 0 < M n := by rw [hMn]; positivity
  -- log(M n / M n₀) = (1/ᾱ) · log(n/n₀):
  have h_log_M : Real.log (M n) - Real.log (M n₀)
      = (1 / ᾱ) * (Real.log n - Real.log n₀) := by
    rw [hMn, hMn₀,
        Real.log_mul hc.ne' hp_n.ne', Real.log_mul hc.ne' hp₀.ne',
        Real.log_rpow hn_pos, Real.log_rpow hn₀_pos]
    ring
  -- The ratio collapses to ᾱ:
  have h_log_n_diff_ne : Real.log n - Real.log n₀ ≠ 0 := by
    have h_log_lt : Real.log n₀ < Real.log n :=
      Real.log_lt_log hn₀_pos hn₀_lt_n
    linarith
  unfold kappa
  rw [h_log_M]
  field_simp

/-! ### Effective stable index `ᾱ` (paper Eq. 5).

    The κ-stable invariance above is stated in terms of an *effective*
    stable index `ᾱ > 0`.  Paper Eq. 5 *defines* `ᾱ` by clipping the
    raw stable index `α` at 2:
        ᾱ := α · 𝟙_{α<2} + 2 · 𝟙_{α≥2}.
    This definition records the proposed clipped index only. A
    domain-of-attraction theorem, a CLT or a limit for an actual sum's
    MAD does not follow from clipping; see REVIEW.md, K-05 and K-07. -/

/-- **Effective stable index (paper Eq. 5).**  Piecewise:
        ᾱ(α) := α   if α < 2,
        ᾱ(α) := 2   if α ≥ 2. -/
noncomputable def stableAlphaBar (α : ℝ) : ℝ :=
  if α < 2 then α else 2

/-- `stableAlphaBar α = α` in the proper stable regime `α < 2`. -/
theorem stableAlphaBar_of_lt {α : ℝ} (h : α < 2) : stableAlphaBar α = α := by
  unfold stableAlphaBar; rw [ite_eq_left h]

/-- `stableAlphaBar α = 2` in the Gaussian basin `α ≥ 2`. -/
theorem stableAlphaBar_of_ge {α : ℝ} (h : 2 ≤ α) : stableAlphaBar α = 2 := by
  unfold stableAlphaBar; rw [ite_eq_right (not_lt.mpr h)]

/-- `stableAlphaBar` is bounded above by `2`. -/
theorem stableAlphaBar_le_two (α : ℝ) : stableAlphaBar α ≤ 2 := by
  unfold stableAlphaBar
  split_ifs with h
  · linarith
  · exact le_refl 2

/-- `stableAlphaBar` is strictly positive for any `α > 0`. -/
theorem stableAlphaBar_pos {α : ℝ} (hα : 0 < α) : 0 < stableAlphaBar α := by
  unfold stableAlphaBar
  split_ifs with h
  · exact hα
  · norm_num

/-- **Stable κ via `ᾱ` (paper Eq. 5 + Eq. 6).**  Combining the clip
    `ᾱ = stableAlphaBar α` with `kappa_stable_invariance` yields the
    bridge `κ(n₀, n) = 2 − ᾱ(α)` directly from a raw stable index `α`,
    provided the MAD scales as `c · n^(1/ᾱ(α))`.  Specialisations:
    `α < 2 → κ = 2 − α`; `α ≥ 2 → κ = 0`. -/
theorem kappa_stable_invariance_alphaBar {M : ℕ → ℝ} {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ) ^ ((1:ℝ) / stableAlphaBar α))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 2 - stableAlphaBar α :=
  kappa_stable_invariance hc (stableAlphaBar_pos hα) hM_form hn₀ h_lt

/-- **Square-root reference curve (ᾱ = 2).** Taleb, arXiv:1802.05495v3,
    subsection "Equivalence for stable distributions". Under the supplied
    identity `M(n) = c · √n`, the abstract κ expression is zero.
    The MAD law for actual Gaussian iid sums is not established here. -/
theorem kappa_gaussian {M : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hM_form : ∀ k : ℕ, 0 < k → M k = c * Real.sqrt k)
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 0 := by
  -- Recast `√k = k^(1/2)` for k > 0.
  have hM_form' : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ) ^ ((1:ℝ) / 2) := by
    intro k hk
    rw [hM_form k hk]
    rw [Real.sqrt_eq_rpow]
  have h := kappa_stable_invariance (c := c) (ᾱ := 2) hc (by norm_num)
    hM_form' hn₀ h_lt
  linarith

/-- **Linear reference curve (ᾱ = 1).** Taleb, arXiv:1802.05495v3,
    subsection "Equivalence for stable distributions", includes index 1.
    This theorem only proves that `M(n) = c · n` gives abstract κ equal to 1.
    Its historical name does not identify `M` with a Cauchy MAD: a Cauchy
    law lacks the finite mean required by the paper's Definition 1. -/
theorem kappa_cauchy {M : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 1 := by
  have hM_form' : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ) ^ ((1:ℝ) / 1) := by
    intro k hk
    rw [hM_form k hk]
    have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
    rw [show ((1:ℝ) / 1) = 1 from by norm_num, Real.rpow_one]
  have h := kappa_stable_invariance (c := c) (ᾱ := 1) hc (by norm_num)
    hM_form' hn₀ h_lt
  linarith

/-! ## The paper's sample-size power expression.

    Taleb, arXiv:1802.05495v3, subsection "Practical significance for sample
    sufficiency", display `simpleequiv`, proposes `n_ν = n_g^(1/(1 − κ_g))`.
    The actual criterion in display `md` compares mean absolute deviations
    of sample means at positive integer sizes. The algebra below does not
    identify this power expression with that minimum or bound its error. -/

/-- **The proposed sample-size power expression**, Taleb,
    arXiv:1802.05495v3, display `simpleequiv`:
        `n_ν := n_g ^ (1 / (1 − κ_g))`.
    This is a real-valued formula on supplied parameters. Its connection to
    the positive-integer minimum `n_min` requires a separate justification.
    At `κ_g = 1`, Lean's total division gives exponent zero and value one;
    this is outside the intended `κ_g < 1` regime. -/
noncomputable def n_nu (n_g : ℕ) (κ_g : ℝ) : ℝ :=
  (n_g : ℝ) ^ ((1:ℝ) / (1 - κ_g))

/-- **The sample-size expression at κ = 0** equals its baseline.
    This algebraic identity concerns Taleb's display `simpleequiv`
    (arXiv:1802.05495v3); it does not identify a probability law. -/
theorem n_nu_gaussian (n_g : ℕ) :
    n_nu n_g 0 = (n_g : ℝ) := by
  unfold n_nu
  rw [sub_zero, div_one, Real.rpow_one]

/-- **`n_nu` grows as a fixed power of `n_g` for a fixed tail index.**  For any
    `0 < κ_g < 1`, the exponent `1/(1 − κ_g) > 1`, so `n_ν > n_g`
    (more summands needed than for the Gaussian baseline). -/
theorem n_nu_gt_n_g {n_g : ℕ} {κ_g : ℝ}
    (hn_g : 1 < n_g) (hκ_pos : 0 < κ_g) (hκ_lt : κ_g < 1) :
    (n_g : ℝ) < n_nu n_g κ_g := by
  unfold n_nu
  have hn_g_gt_one : (1:ℝ) < n_g := by exact_mod_cast hn_g
  have h_exp_pos : 0 < 1 - κ_g := by linarith
  have h_exp_gt_one : 1 < 1 / (1 - κ_g) := by
    rw [lt_div_iff₀ h_exp_pos]; linarith
  have h := (Real.rpow_lt_rpow_left_iff hn_g_gt_one).mpr h_exp_gt_one
  calc (n_g : ℝ) = (n_g : ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
    _ < (n_g : ℝ) ^ (1 / (1 - κ_g)) := h

/-! ### Bidirectional Eq. 7 (paper Section III-B).

    Companion to `n_nu`.  The Eq. 7 relation `n_ν = n_g^(1/(1−κ))` is
    *algebraically invertible*: raising both sides to the `(1−κ)` power
    recovers `n_g = n_ν^(1−κ)`.  This gives a literal inverse function
    `n_g_of_n_nu`, packaged with the round-trip identity
    `n_g_of_n_nu (n_nu n_g κ) κ = n_g`.

    The paper's "bidirectional" reading swaps the roles of `n_g` and
    `n_ν` and replaces the exponent `(1−κ)` by `1/(1−κ_ν)`, where
    `κ_ν` is the κ-value at the alternative anchor.  Algebraically the
    two forms are equivalent iff `(1−κ_g)(1−κ_ν) = 1`.  This dual is
    captured in `n_nu_bidirectional`. -/

/-- **Algebraic inverse of `n_nu`.**  Given a target sample size `n_ν`
    and the κ-parameter `κ_g`, the Gaussian-equivalent sample size is
        `n_g_of_n_nu n_ν κ_g := n_ν ^ (1 − κ_g)`.
    Round-trip with `n_nu` recovers the original `n_g` (see
    `n_g_of_n_nu_n_nu`). -/
noncomputable def n_g_of_n_nu (n_ν : ℝ) (κ_g : ℝ) : ℝ :=
  n_ν ^ (1 - κ_g)

/-- **Round-trip identity (n_nu inverse).** For every `n_g : ℕ` and `κ_g ≠ 1`,
    applying `n_g_of_n_nu` to `n_nu n_g κ_g` recovers `n_g`. -/
theorem n_g_of_n_nu_n_nu {n_g : ℕ} {κ_g : ℝ}
    (hκ : κ_g ≠ 1) :
    n_g_of_n_nu (n_nu n_g κ_g) κ_g = (n_g : ℝ) := by
  unfold n_g_of_n_nu n_nu
  have hn_g_nn : (0:ℝ) ≤ n_g := Nat.cast_nonneg _
  have h_sub_ne : (1 - κ_g) ≠ 0 := sub_ne_zero.mpr (Ne.symm hκ)
  rw [← Real.rpow_mul hn_g_nn, div_mul_cancel₀ _ h_sub_ne, Real.rpow_one]

/-- **Reverse round-trip.**  `n_nu` recovers `n_ν` from `n_g_of_n_nu n_ν κ_g`
    (for positive real `n_ν` and `κ_g ≠ 1`).  Together with
    `n_g_of_n_nu_n_nu`, this exhibits `n_nu` and `n_g_of_n_nu` as a pair
    of algebraic inverses on the punctured `κ ≠ 1` axis. -/
theorem n_nu_n_g_of_n_nu {n_ν : ℝ} {κ_g : ℝ}
    (hn_ν : 0 ≤ n_ν) (hκ : κ_g ≠ 1) :
    (n_g_of_n_nu n_ν κ_g) ^ ((1:ℝ) / (1 - κ_g)) = n_ν := by
  unfold n_g_of_n_nu
  have h_sub_ne : (1 - κ_g) ≠ 0 := sub_ne_zero.mpr (Ne.symm hκ)
  rw [← Real.rpow_mul hn_ν, mul_one_div, div_self h_sub_ne, Real.rpow_one]

/-- **Bidirectional Eq. 7 (paper form).**  The two paper-form Eq. 7
    statements
        `n_ν = n_g^(1/(1−κ_g))`   and   `n_g = n_ν^(1/(1−κ_ν))`
    are *equivalent* exactly when the κ-pair satisfies the dual relation
        `(1 − κ_g)(1 − κ_ν) = 1`,
    i.e. `κ_ν = −κ_g/(1 − κ_g)`.  In the stable basin where κ is
    anchor-invariant this collapses to `κ = 0` (Gaussian), confirming
    that the paper's bidirectional reading captures the pre-asymptotic
    rebasing of κ between the `n_g` and `n_ν` anchors. -/
theorem n_nu_bidirectional {n_g n_ν : ℝ} {κ_g κ_ν : ℝ}
    (hn_g : 0 ≤ n_g) (hn_ν : 0 ≤ n_ν)
    (hκ_g : κ_g < 1) (hκ_ν : κ_ν < 1)
    (h_dual : (1 - κ_g) * (1 - κ_ν) = 1) :
    n_ν = n_g ^ ((1:ℝ) / (1 - κ_g)) ↔ n_g = n_ν ^ ((1:ℝ) / (1 - κ_ν)) := by
  have h_pos_g : 0 < 1 - κ_g := by linarith
  have h_pos_ν : 0 < 1 - κ_ν := by linarith
  have h_prod : (1 / (1 - κ_g)) * (1 / (1 - κ_ν)) = 1 := by
    rw [one_div, one_div, ← mul_inv, h_dual, inv_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, ← Real.rpow_mul hn_g, h_prod, Real.rpow_one]
  · rw [h, ← Real.rpow_mul hn_ν, mul_comm, h_prod, Real.rpow_one]

/-! ## Minimum sample size sufficiency (paper Section III-B).

    The paper introduces `n_min` as the *smallest* sample size `n_ν`
    needed for the ν-distribution's sample-mean MAD to match (be at
    least as concentrated as) the Gaussian baseline's at sample size
    `n_g`:
        n_min := inf {n_ν ∈ ℕ : 0 < n_ν ∧ E[|S_ν,n_ν − m_p|]/n_ν
                                ≤ E[|S_g,n_g − m_g|]/n_g}.
    Under the stable approximation, `n_min` is well-approximated by
    `n_nu` (paper Eq. 7); the linkage is captured by
    `n_min_le_of_witness`, which provides an upper bound on `n_min`
    from any sample size satisfying the condition. -/

/-- **Sample-mean MAD.**  For an MAD oracle `M : ℕ → ℝ` (the MAD of the
    iid partial sum), the **sample-mean MAD** at sample size `n` is the
    per-summand deviation
        `sampleMeanMAD M n := M(n) / n`,
    i.e. `E[|S_n − E[S_n]|]/n = E[|S_n/n − E[S_n/n]|]`. -/
noncomputable def sampleMeanMAD (M : ℕ → ℝ) (n : ℕ) : ℝ :=
  M n / (n : ℝ)

/-- **Minimum sample size sufficiency (paper Section III-B).**  Given
    target-distribution MAD oracle `M_ν` and Gaussian baseline `M_g`
    at sample size `n_g`, the minimum number of target summands for
    sample-mean MAD concentration to match the Gaussian's is
        `n_min := inf {n_ν ∈ ℕ : 0 < n_ν ∧ M_ν(n_ν)/n_ν ≤ M_g(n_g)/n_g}`.
    Zero is excluded from the candidate set. The result is `0` only
    when no positive candidate exists. A probabilistic interpretation
    also requires a positive reference size and actual MAD oracles. -/
noncomputable def n_min (M_ν M_g : ℕ → ℝ) (n_g : ℕ) : ℕ :=
  sInf {n_ν : ℕ | 0 < n_ν ∧ sampleMeanMAD M_ν n_ν ≤ sampleMeanMAD M_g n_g}

/-- **n_min upper bound by witness.**  Any sample size `n_ν` that
    satisfies the sample-mean MAD condition is an upper bound on
    `n_min`.  This is the operational handle for linking `n_min` to
    `n_nu`: producing any explicit witness (e.g. from the stable
    approximation) bounds `n_min` above. -/
theorem n_min_le_of_witness {M_ν M_g : ℕ → ℝ} {n_g n_ν : ℕ}
    (hn : 0 < n_ν)
    (h : sampleMeanMAD M_ν n_ν ≤ sampleMeanMAD M_g n_g) :
    n_min M_ν M_g n_g ≤ n_ν := by
  unfold n_min
  exact Nat.sInf_le ⟨hn, h⟩

/-- **n_min is realised when the witness set is nonempty.**  If any
    sample size `k` satisfies the sample-mean MAD condition, then
    `n_min M_ν M_g n_g` itself satisfies the condition — i.e. the
    infimum is attained at a natural number.  This is the operational
    converse of `n_min_le_of_witness`. -/
theorem n_min_mem {M_ν M_g : ℕ → ℝ} {n_g : ℕ}
    (h_witness : ∃ k, 0 < k ∧ sampleMeanMAD M_ν k ≤ sampleMeanMAD M_g n_g) :
    0 < n_min M_ν M_g n_g ∧
      sampleMeanMAD M_ν (n_min M_ν M_g n_g) ≤ sampleMeanMAD M_g n_g := by
  unfold n_min
  exact Nat.sInf_mem h_witness

/-- A nonempty set of admissible positive sample sizes has a positive minimum. -/
theorem n_min_pos {M_ν M_g : ℕ → ℝ} {n_g : ℕ}
    (h_witness : ∃ k, 0 < k ∧ sampleMeanMAD M_ν k ≤ sampleMeanMAD M_g n_g) :
    0 < n_min M_ν M_g n_g := (n_min_mem h_witness).1

/-- The zero sentinel occurs exactly when no positive sample size suffices. -/
theorem n_min_eq_zero_iff {M_ν M_g : ℕ → ℝ} {n_g : ℕ} :
    n_min M_ν M_g n_g = 0 ↔
      ¬ ∃ k, 0 < k ∧ sampleMeanMAD M_ν k ≤ sampleMeanMAD M_g n_g := by
  constructor
  · intro hzero hw
    have hpos := n_min_pos hw
    omega
  · intro hnone
    unfold n_min
    have hempty : {k : ℕ | 0 < k ∧ sampleMeanMAD M_ν k ≤ sampleMeanMAD M_g n_g} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hk => hnone ⟨k, hk⟩
    rw [hempty]
    exact Nat.sInf_empty

/-! ## κ additive decomposition (paper Eq. 2).

    The κ-metric admits a telescoping representation in terms of
    consecutive "local" κ-rates:
        κ(n₀, n) = 2 − log(n/n₀) / Σ_{i=n₀}^{n-1} log((i+1)/i) / (2 − κ(i, i+1)).
    Convenient for analyzing the *running* κ as `n` grows.  Direct
    consequence of the chain identity
        log(M(n)/M(n₀)) = Σ log(M(i+1)/M(i)). -/

/-- **Helper: telescoping sum of consecutive log-MAD ratios.**  For any
    `M : ℕ → ℝ` with `M k > 0` on the considered range, the chain
    identity
        log(M(n)) − log(M(n₀)) = Σ_{i=n₀}^{n-1} (log(M(i+1)) − log(M(i)))
    holds by telescoping.  Algebraic shell for the κ-decomposition. -/
theorem log_MAD_telescope {M : ℕ → ℝ} {n₀ n : ℕ} (h_le : n₀ ≤ n) :
    Real.log (M n) - Real.log (M n₀)
      = ∑ i ∈ Finset.range (n - n₀),
          (Real.log (M (n₀ + i + 1)) - Real.log (M (n₀ + i))) := by
  induction n, h_le using Nat.le_induction with
  | base => simp
  | succ k _ ih =>
    have h_succ_eq : k + 1 - n₀ = (k - n₀) + 1 := by omega
    rw [h_succ_eq, Finset.sum_range_succ]
    have h_idx : n₀ + (k - n₀) = k := by omega
    rw [h_idx]
    linarith [ih]

/-- **κ additive decomposition (paper Eq. 2, post-substitution form).**
    The expression telescopes for any `M : ℕ → ℝ` and `n₀ ≤ n`, including
    zero endpoints under Lean's total logarithm and division conventions:
        κ(n₀, n) = 2 − log(n/n₀) /
                   Σ_{i=0}^{n−n₀−1} (log(M(n₀+i+1)) − log(M(n₀+i))).

    Its probabilistic κ interpretation needs positive sample sizes and
    actual nondegenerate MADs. For valid parameters it analyzes running κ,
    decomposed into
    per-step contributions.  Equivalent to Eq. 2 of the paper after
    rewriting each local term via the per-step κ; see
    `kappa_decomposition_local` for the literal Eq. 2 form. -/
theorem kappa_decomposition {M : ℕ → ℝ} {n₀ n : ℕ}
    (h_le : n₀ ≤ n) :
    kappa M n₀ n
      = 2 - (Real.log n - Real.log n₀) /
          (∑ i ∈ Finset.range (n - n₀),
              (Real.log (M (n₀ + i + 1)) - Real.log (M (n₀ + i)))) := by
  unfold kappa
  rw [log_MAD_telescope (M := M) h_le]

/-- **κ additive decomposition (paper Eq. 2, literal form via per-step κ's).**
    The telescoping representation re-expressed using local κ-rates
    `κ(i, i+1)`:
        κ(n₀, n) = 2 − log(n/n₀) /
                   Σ_{i=0}^{n−n₀−1} log((n₀+i+1)/(n₀+i)) / (2 − κ(M, n₀+i, n₀+i+1)).

    This is Eq. 2 verbatim.  Reduces to `kappa_decomposition` by the
    pointwise identity
        `log((i+1)/i) / (2 − κ(M, i, i+1)) = log(M(i+1)) − log(M(i))`,
    which follows directly from the κ-definition. -/
theorem kappa_decomposition_local {M : ℕ → ℝ} {n₀ n : ℕ}
    (hn₀ : 0 < n₀) (h_le : n₀ ≤ n)
    (h_log_ne : ∀ i, n₀ ≤ i → i < n →
        Real.log (M (i + 1)) - Real.log (M i) ≠ 0) :
    kappa M n₀ n
      = 2 - (Real.log n - Real.log n₀) /
          (∑ i ∈ Finset.range (n - n₀),
              (Real.log ((n₀ + i + 1 : ℕ) : ℝ) - Real.log ((n₀ + i : ℕ) : ℝ)) /
                (2 - kappa M (n₀ + i) (n₀ + i + 1))) := by
  rw [kappa_decomposition h_le]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hi_idx : n₀ + i < n := by omega
  have h_local_ne := h_log_ne (n₀ + i) (Nat.le_add_right _ _) hi_idx
  -- The natural-number log diff is also nonzero (n₀ ≥ 1, so n₀ + i + 1 > n₀ + i ≥ 1).
  have hn₀i_pos : 0 < n₀ + i := by omega
  have hn₀i_real_pos : (0:ℝ) < ((n₀ + i : ℕ) : ℝ) := by exact_mod_cast hn₀i_pos
  have h_succ_lt : ((n₀ + i : ℕ) : ℝ) < ((n₀ + i + 1 : ℕ) : ℝ) := by
    have : (n₀ + i : ℕ) < (n₀ + i + 1 : ℕ) := by omega
    exact_mod_cast this
  have h_log_nat_diff_pos : 0 < Real.log ((n₀ + i + 1 : ℕ) : ℝ) - Real.log ((n₀ + i : ℕ) : ℝ) := by
    have := Real.log_lt_log hn₀i_real_pos h_succ_lt
    linarith
  have h_log_nat_diff_ne :
      Real.log ((n₀ + i + 1 : ℕ) : ℝ) - Real.log ((n₀ + i : ℕ) : ℝ) ≠ 0 :=
    h_log_nat_diff_pos.ne'
  -- Per-step κ:  2 − κ(i, i+1) = (log(i+1) − log(i)) / (log M(i+1) − log M(i)).
  have h_step : 2 - kappa M (n₀ + i) (n₀ + i + 1)
      = (Real.log ((n₀ + i + 1 : ℕ) : ℝ) - Real.log ((n₀ + i : ℕ) : ℝ)) /
          (Real.log (M (n₀ + i + 1)) - Real.log (M (n₀ + i))) := by
    unfold kappa; ring
  rw [h_step]
  -- log((i+1)/i) / ((log((i+1)/i)) / (log M(i+1) − log M(i)))
  --   = log M(i+1) − log M(i).
  field_simp


end TailOptionPricing
