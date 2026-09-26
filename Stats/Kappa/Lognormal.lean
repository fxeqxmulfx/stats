/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.Lognormal — Loulakis lognormal bound.

  Loulakis' argument for the lognormal under subexponentiality:
  "as `σ → ∞`, `M(n)/M(1) ≥ n`, while at the same time
  `M(n)/M(1) ≤ n`, so `M(n) = n · M(1)` in the limit", giving
  `κ_{1,n} = 1`.  This module captures the *implication* — given
  the bound, derive κ — abstractly without reproducing the
  subexponentiality proof.

  Theorems delivered (paper Section IV-B):

  * `kappa_upper_bound_subadditive` — universal `κ ≤ 1` from iid
    triangle-inequality sub-additivity.
  * `kappa_loulakis_lower_bound` — subexp lower bound ⇒ `κ ≥ 1`.
  * `kappa_loulakis_eq_one` — exact saturation `κ = 1` at the
    Loulakis limit.
  * `lognormal_M_ratio_le_n` — explicit MAD-ratio form of the
    universal upper bound (paper Section IV-B, todo B.2.1).
  * `lognormal_M_ratio_ge_n_subexp` — explicit MAD-ratio form of
    the Loulakis lower bound under subexponentiality (todo B.2.2).
  * `kappa_lognormal_tendsto_one` — squeeze: along a parametric
    family with `M(σ, n)/M(σ, 1) → n`, `κ_{1, n} → 1` (todo B.2.3).

  See `Stats/Kappa.lean` for the umbrella module.
-/
import Stats.Kappa.Basic

open Real Set Filter Topology

namespace TailOptionPricing

/-! ## Loulakis' lognormal bound (paper Section IV-B).

    Loulakis' argument for the lognormal under subexponentiality:
    "as `σ → ∞`, `M(n)/M(1) ≥ n`, while at the same time
    `M(n)/M(1) ≤ n`, so `M(n) = n · M(1)` in the limit", giving
    `κ_{1,n} = 1`.  We capture the *implication* — given the bound,
    derive κ — abstractly without reproducing the subexponentiality
    proof, which involves Hölder's inequality on a Gaussian
    transformation. -/

/-- **Universal κ ≤ 1 upper bound from iid sub-additivity.**  For an
    MAD oracle arising from an iid sum, the triangle inequality gives
    `M(n) ≤ n · M(1)`:
        `E[|S_n − n·E[X]|] = E[|Σ (X_i − E[X])|] ≤ Σ E[|X_i − E[X]|]
                          = n · M(1).`
    Under this sub-additivity bound (plus `M(1) < M(n)`, i.e. `M` is
    strictly growing — which holds for any non-degenerate iid sum),
    the κ-metric satisfies the universal upper bound `κ(1, n) ≤ 1`.

    Combined with Loulakis' lower bound at the lognormal limit, this
    pins down `κ ∈ (·, 1]` for every reasonable iid-sum MAD oracle,
    with `κ → 1` saturating the bound for the heaviest (subexponential)
    tails. -/
theorem kappa_upper_bound_subadditive {M : ℕ → ℝ} {n : ℕ}
    (hn : 1 < n) (hM1_pos : 0 < M 1) (hM_grow : M 1 < M n)
    (h_subadditive : M n ≤ (n:ℝ) * M 1) :
    kappa M 1 n ≤ 1 := by
  have hn_pos : 0 < n := by omega
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := by linarith
  have h_log_n_pos : 0 < Real.log n := Real.log_pos hn_real_gt_one
  have h_log_M_diff_pos : 0 < Real.log (M n) - Real.log (M 1) := by
    have h := Real.log_lt_log hM1_pos hM_grow
    linarith
  have h_nM1_pos : 0 < (n:ℝ) * M 1 := mul_pos hn_real_pos hM1_pos
  have h_log_M_le : Real.log (M n) ≤ Real.log ((n:ℝ) * M 1) := by
    have hMn_pos : 0 < M n := lt_trans hM1_pos hM_grow
    exact Real.log_le_log hMn_pos h_subadditive
  have h_log_split : Real.log ((n:ℝ) * M 1) = Real.log n + Real.log (M 1) :=
    Real.log_mul hn_real_pos.ne' hM1_pos.ne'
  have h_log_M_diff_le : Real.log (M n) - Real.log (M 1) ≤ Real.log n := by
    rw [h_log_split] at h_log_M_le; linarith
  -- κ ≤ 1 ⇔ log(n) / (log M(n) − log M(1)) ≥ 1 ⇔ log(n) ≥ log M(n) − log M(1).
  have h_ratio_ge_one :
      1 ≤ Real.log n / (Real.log (M n) - Real.log (M 1)) := by
    rw [le_div_iff₀ h_log_M_diff_pos, one_mul]
    exact h_log_M_diff_le
  unfold kappa
  rw [show Real.log ((1:ℕ):ℝ) = 0 from by simp, sub_zero]
  linarith

/-- **Loulakis' abstract lower bound.**  Given an MAD oracle `M` with
    `M(n) ≥ n · M(1)` and `M(1) > 0`, `M(n) > 0`, `n > 1`, the
    κ-metric is *at least* `1`:
        κ(1, n) ≥ 1.
    Specialising to `M(n) = n · M(1)` exactly gives `κ(1, n) = 1`,
    matching Loulakis' lognormal limit.  Direct algebraic consequence
    of monotonicity of `log`. -/
theorem kappa_loulakis_lower_bound {M : ℕ → ℝ} {n : ℕ}
    (hn : 1 < n) (hM1_pos : 0 < M 1)
    (h_bound : (n:ℝ) * M 1 ≤ M n) :
    1 ≤ kappa M 1 n := by
  have hn_pos : 0 < n := by omega
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := by linarith
  -- log(M n / M 1) ≥ log(n), so log diff ≥ log n > 0; ratio ≤ 1; κ ≥ 1.
  have h_log_n_pos : 0 < Real.log n := Real.log_pos hn_real_gt_one
  have h_nM1_pos : 0 < (n:ℝ) * M 1 := mul_pos hn_real_pos hM1_pos
  have h_log_ge : Real.log ((n:ℝ) * M 1) ≤ Real.log (M n) :=
    Real.log_le_log h_nM1_pos h_bound
  have h_log_split : Real.log ((n:ℝ) * M 1) = Real.log n + Real.log (M 1) :=
    Real.log_mul hn_real_pos.ne' hM1_pos.ne'
  have h_log_M_diff : Real.log n ≤ Real.log (M n) - Real.log (M 1) := by
    linarith
  have h_log_M_diff_pos : 0 < Real.log (M n) - Real.log (M 1) :=
    lt_of_lt_of_le h_log_n_pos h_log_M_diff
  have h_ratio_le_one :
      Real.log n / (Real.log (M n) - Real.log (M 1)) ≤ 1 := by
    rw [div_le_one h_log_M_diff_pos]
    exact h_log_M_diff
  unfold kappa
  rw [show Real.log ((1:ℕ):ℝ) = 0 from by simp, sub_zero]
  linarith

/-- **Loulakis exact equality (paper Section IV-B asymptote).**  When
    `M(n) = n · M(1)` exactly — Loulakis' lognormal limit — the
    κ-metric saturates at `1`. -/
theorem kappa_loulakis_eq_one {M : ℕ → ℝ} {n : ℕ}
    (hn : 1 < n) (hM1_pos : 0 < M 1)
    (h_eq : M n = (n:ℝ) * M 1) :
    kappa M 1 n = 1 := by
  -- Apply the (already-proven) Cauchy case with `c := M 1` after a recast.
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn_pos
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hMn_pos : 0 < M n := by rw [h_eq]; positivity
  have h_log_M_diff : Real.log (M n) - Real.log (M 1) = Real.log n := by
    rw [h_eq, Real.log_mul hn_real_pos.ne' hM1_pos.ne']; ring
  have h_log_n_pos : 0 < Real.log n := Real.log_pos hn_real_gt_one
  have h_log_n_ne : Real.log n ≠ 0 := h_log_n_pos.ne'
  unfold kappa
  rw [h_log_M_diff,
      show Real.log ((1:ℕ):ℝ) = 0 from by simp,
      sub_zero, div_self h_log_n_ne]
  ring

/-! ## Explicit MAD-ratio bounds for the lognormal (paper Section IV-B).

    The abstract `kappa_*` bounds above operate on the κ-metric directly.
    The paper's Section IV-B presents the same content at the *MAD-ratio*
    level: under iid sub-additivity, `M(n)/M(1) ≤ n`; under Loulakis
    subexponentiality, `M(n)/M(1) ≥ n`.  These two MAD-ratio bounds are
    the *origin* of the κ-bounds — the squeeze on the ratio gives the
    squeeze on κ.

    Stated here as theorems (rather than absorbed into the κ-bounds)
    because the paper, the Loulakis (2002) reference, and downstream
    proofs treat the MAD ratio as a separate object of study. -/

/-- **Universal MAD-ratio upper bound (paper Section IV-B, todo B.2.1).**
    For any MAD oracle `M : ℕ → ℝ` arising from an iid partial sum, the
    sub-additivity bound `M(n) ≤ n · M(1)` (triangle inequality on
    `E[|Σ (X_i − E[X])|]`) gives the ratio bound
        `M(n) / M(1) ≤ n`
    for `n > 0` and `M(1) > 0`.  Specialises to the lognormal by name —
    the iid sub-additivity hypothesis is automatic for any iid sum,
    including the lognormal sum addressed in Loulakis' argument. -/
theorem lognormal_M_ratio_le_n {M : ℕ → ℝ} {n : ℕ}
    (hM1_pos : 0 < M 1)
    (h_subadditive : M n ≤ (n:ℝ) * M 1) :
    M n / M 1 ≤ (n:ℝ) := by
  rw [div_le_iff₀ hM1_pos]
  linarith

/-- **Loulakis MAD-ratio lower bound (paper Section IV-B, todo B.2.2).**
    Under Loulakis' subexponentiality hypothesis `n · M(1) ≤ M(n)`
    (obtained for the lognormal via the subexponential tail bound
    `ℙ(S_n > t) ≥ n · ℙ(X_1 > t)` for `t → ∞`, integrated via layer-cake
    and Hölder's inequality — paper Section IV-B), the MAD ratio
    satisfies
        `n ≤ M(n) / M(1)`.
    The Loulakis-style hypothesis is taken as input: the lognormal
    discharge requires probability infrastructure beyond the scope of
    this κ-formalisation (Mathlib has no lognormal distribution as of
    v4.29.1 — see `Stats.Kappa.LognormalCumulants` for analogous
    primitive-form lognormal facts). -/
theorem lognormal_M_ratio_ge_n_subexp {M : ℕ → ℝ} {n : ℕ}
    (hM1_pos : 0 < M 1)
    (h_subexp : (n:ℝ) * M 1 ≤ M n) :
    (n:ℝ) ≤ M n / M 1 := by
  rw [le_div_iff₀ hM1_pos]
  linarith

/-! ## σ → ∞ squeeze: κ_{1, n} → 1 (paper Section IV-B, todo B.2.3).

    Combining the universal upper bound and the Loulakis lower bound,
    the lognormal MAD ratio converges to `n` as `σ → ∞`, and by
    continuity of the κ-formula the κ-metric converges to `1`.

    Formalised here at the abstract level: take any parametric family
    `M : ℝ → ℕ → ℝ` (`σ ↦ M_σ`) for which the MAD ratio `M_σ(n)/M_σ(1)`
    converges to `n` along `atTop`.  Then `κ_{1, n}(M_σ) → 1`.

    The lognormal interpretation: `σ` is the lognormal scale parameter,
    and the hypothesis `M_σ(n)/M_σ(1) → n` is the conclusion of the
    pinch between the upper bound `≤ n` (sub-additivity) and the lower
    bound `≥ n − o(1)` (Loulakis subexponentiality). -/

/-- **κ_{1, n} → 1 under MAD-ratio squeeze (paper Section IV-B,
    todo B.2.3).**  Given a parametric MAD-oracle family `M : ℝ → ℕ → ℝ`
    along `atTop` (the lognormal `σ → ∞` limit), if
        `M(σ, 1) > 0` and `M(σ, n)/M(σ, 1) → n`,
    then `kappa (M σ) 1 n → 1`.

    Direct corollary of the upper/lower MAD-ratio bounds: the squeeze
    on the ratio gives the squeeze on κ via continuity of
    `r ↦ 2 − log(n)/log(r)` at `r = n`. -/
theorem kappa_lognormal_tendsto_one {M : ℝ → ℕ → ℝ} {n : ℕ}
    (hn : 1 < n)
    (h_pos : ∀ᶠ σ in atTop, 0 < M σ 1)
    (h_ratio : Tendsto (fun σ => M σ n / M σ 1) atTop (𝓝 (n:ℝ))) :
    Tendsto (fun σ => kappa (M σ) 1 n) atTop (𝓝 1) := by
  have hn_real_gt_one : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn_real_pos : (0:ℝ) < (n:ℝ) := by linarith
  have h_log_n_pos : 0 < Real.log n := Real.log_pos hn_real_gt_one
  have h_log_n_ne : Real.log n ≠ 0 := h_log_n_pos.ne'
  -- Step 1: log of the ratio tends to log n.
  have h_log_ratio_tendsto :
      Tendsto (fun σ => Real.log (M σ n / M σ 1)) atTop (𝓝 (Real.log n)) := by
    have h_log_cont : ContinuousAt Real.log (n:ℝ) :=
      Real.continuousAt_log hn_real_pos.ne'
    exact h_log_cont.tendsto.comp h_ratio
  -- Step 2: kappa rewrites to `2 − log(n)/log(M σ n / M σ 1)` eventually.
  have h_ratio_pos : ∀ᶠ σ in atTop, 0 < M σ n / M σ 1 := by
    have h_half_lt_n : (n:ℝ) / 2 < (n:ℝ) := by
      have : (0:ℝ) < (n:ℝ) / 2 := by positivity
      linarith
    have h_eventually := h_ratio.eventually (eventually_gt_nhds h_half_lt_n)
    filter_upwards [h_eventually] with σ hσ
    have : (0:ℝ) < (n:ℝ) / 2 := by positivity
    linarith
  have h_kappa_eq : ∀ᶠ σ in atTop,
      kappa (M σ) 1 n
        = 2 - Real.log (n:ℝ) / Real.log (M σ n / M σ 1) := by
    filter_upwards [h_pos, h_ratio_pos] with σ hσM1 hσRatio
    have hσMn : 0 < M σ n := by
      have hh : 0 < M σ n / M σ 1 * M σ 1 := mul_pos hσRatio hσM1
      simpa [div_mul_cancel₀ _ hσM1.ne'] using hh
    have h_log_div : Real.log (M σ n / M σ 1)
        = Real.log (M σ n) - Real.log (M σ 1) :=
      Real.log_div hσMn.ne' hσM1.ne'
    have h_log_one_nat : Real.log ((1:ℕ):ℝ) = 0 := by
      rw [Nat.cast_one, Real.log_one]
    unfold kappa
    rw [h_log_one_nat, sub_zero, h_log_div]
  -- Step 3: limit of the ratio expression is 1.
  have h_ratio_tendsto :
      Tendsto (fun σ => Real.log (n:ℝ) / Real.log (M σ n / M σ 1))
        atTop (𝓝 1) := by
    have h_lim_div : Tendsto (fun σ => Real.log (n:ℝ) / Real.log (M σ n / M σ 1))
        atTop (𝓝 (Real.log (n:ℝ) / Real.log (n:ℝ))) :=
      Tendsto.div tendsto_const_nhds h_log_ratio_tendsto h_log_n_ne
    rwa [div_self h_log_n_ne] at h_lim_div
  have h_two_sub_tendsto :
      Tendsto (fun σ => 2 - Real.log (n:ℝ) / Real.log (M σ n / M σ 1))
        atTop (𝓝 (2 - 1)) :=
    tendsto_const_nhds.sub h_ratio_tendsto
  have h_two_sub_one : (2 : ℝ) - 1 = 1 := by norm_num
  rw [h_two_sub_one] at h_two_sub_tendsto
  exact h_two_sub_tendsto.congr' (h_kappa_eq.mono (fun _ h => h.symm))

end TailOptionPricing
