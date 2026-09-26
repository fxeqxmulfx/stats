/-
  Strong-Pareto core: mispricing signal and variance-swap breakdown from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.Mispricing — BS-vs-Pareto gap asymptotics and variance-swap breakdown.

  Contains:
    * `callPrice_gap_*` family: ratio/asymptotic behaviour of the
      Pareto call-price gap against a generic survival `f`.
    * `paretoDensity`, variance-swap non-integrability for `α ≤ 2`.

  See `Stats/Pareto.lean` for the umbrella module.
-/
import Stats.Pareto.AbstractCall

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Mispricing signal: BS-vs-Pareto gap asymptotics.

    Closed-form decay of `callPrice` is polynomial: `K^(1−α)`.  Any model
    with super-polynomial tail decay (e.g. lognormal Black–Scholes via
    Mills) is `o(callPrice)` at infinity, so the *relative* mispricing
    `gap(K) / callPrice(l, α, K) → −1` — Black–Scholes misses the entire
    Pareto tail in relative terms (paper Fig. 3).  In absolute terms the
    gap shrinks to zero from below.  The argument is purely
    asymptotic-algebraic, so we state it for an arbitrary `f : ℝ → ℝ`
    standing in for the "alternative" model price. -/

/-- **Pareto call-price decay.**  Under `α > 1`, `callPrice → 0` as
    `K → ∞`.  Closed-form decay rate is polynomial: `K^(1 − α)`. -/
theorem callPrice_tendsto_zero_atTop {l α : ℝ}
    (hα : 1 < α) (hl : 0 < l) :
    Tendsto (callPrice l α) atTop (𝓝 0) := by
  have hα1_pos : 0 < α - 1 := by linarith
  have h_pow : Tendsto (fun K : ℝ => K ^ (1 - α)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop hα1_pos
    have h_eq : (fun K : ℝ => K ^ (1 - α)) = (fun K : ℝ => K ^ (-(α - 1))) := by
      funext K; congr 1; ring
    rw [h_eq]; exact h
  have h_const_mul : Tendsto (fun K : ℝ => l ^ α * K ^ (1 - α)) atTop (𝓝 0) := by
    have := h_pow.const_mul (l ^ α); simpa using this
  have h_form : Tendsto (fun K : ℝ => l ^ α * K ^ (1 - α) / (α - 1)) atTop (𝓝 0) := by
    have := h_const_mul.div_const (α - 1); simpa using this
  apply h_form.congr'
  filter_upwards [eventually_ge_atTop l] with K hK
  exact (callPrice_eq hα hl hK).symm

/-- **Pareto call price is eventually strictly positive at infinity.**  All
    factors of the closed form `l^α · K^(1−α) / (α−1)` are positive once
    `K ≥ l`. -/
theorem callPrice_pos_atTop {l α : ℝ}
    (hα : 1 < α) (hl : 0 < l) :
    ∀ᶠ K in atTop, 0 < callPrice l α K := by
  filter_upwards [eventually_ge_atTop l] with K hK
  rw [callPrice_eq hα hl hK]
  have hα1_pos : 0 < α - 1 := by linarith
  have hKp : 0 < K := hl.trans_le hK
  have hKp_pow : 0 < K ^ (1 - α) := Real.rpow_pos_of_pos hKp _
  have hl_pow : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  positivity

/-- **Mispricing signal — relative gap.**  If a model price `f`
    decays faster than the strong-Pareto reference (`f K / C(K) → 0`),
    then the *relative* gap diverges to the worst-case value:
        `(f K − C(K)) / C(K) → −1`.
    Reading: in relative terms the alternative model misses the *entire*
    Pareto tail.  This is the paper's Fig. 3 mispricing signal. -/
theorem callPrice_gap_ratio_tendsto_neg_one {l α : ℝ} {f : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l)
    (h_f_o : Tendsto (fun K => f K / callPrice l α K) atTop (𝓝 0)) :
    Tendsto (fun K => (f K - callPrice l α K) / callPrice l α K)
      atTop (𝓝 (-1)) := by
  have h_pos := callPrice_pos_atTop hα hl
  have h_eq : (fun K => f K / callPrice l α K - 1) =ᶠ[atTop]
      fun K => (f K - callPrice l α K) / callPrice l α K := by
    filter_upwards [h_pos] with K hK
    rw [sub_div, div_self hK.ne']
  have h_diff : Tendsto (fun K => f K / callPrice l α K - 1) atTop (𝓝 (-1)) := by
    have := h_f_o.sub_const 1; simpa using this
  exact h_diff.congr' h_eq

/-- **Mispricing signal — absolute gap.**  If both `f` and `C` tend to
    zero (e.g. `f` is the Black–Scholes call which Mills-decays
    super-exponentially), then `f K − C(K) → 0`. -/
theorem callPrice_gap_tendsto_zero {l α : ℝ} {f : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l)
    (h_f : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun K => f K - callPrice l α K) atTop (𝓝 0) := by
  have h_C := callPrice_tendsto_zero_atTop hα hl
  have := h_f.sub h_C; simpa using this

/-- **Mispricing signal — sign of the gap.**  Under the relative-decay
    hypothesis `f K / C(K) → 0`, the gap is *eventually negative*:
    BS-style models systematically underprice the Pareto deep-OTM call. -/
theorem callPrice_gap_eventually_neg {l α : ℝ} {f : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l)
    (h_f_o : Tendsto (fun K => f K / callPrice l α K) atTop (𝓝 0)) :
    ∀ᶠ K in atTop, f K - callPrice l α K < 0 := by
  have h_pos := callPrice_pos_atTop hα hl
  have h_lt_one : ∀ᶠ K in atTop, f K / callPrice l α K < 1 :=
    h_f_o.eventually_lt_const (by norm_num : (0:ℝ) < 1)
  filter_upwards [h_pos, h_lt_one] with K hKpos hKlt
  rw [div_lt_iff₀ hKpos] at hKlt
  linarith

/-! ## Variance-swap breakdown: infinite second moment for `α ≤ 2`.

    Under the strong Pareto law on `[l, ∞)`, the `n`-th raw moment is
    finite iff `n < α`.  In particular `E[S²] = +∞` whenever `α ≤ 2`,
    so variance-swap pricing — and any second-moment-based payoff — is
    *not well-defined* under heavy Pareto tails.  The breakdown is the
    quantitative failure of BS-style replication for power-law markets.

    Replacement strategies (log-contract, capped variance, truncation)
    require finite-moment transformations of `S` and are out of scope
    here; this section establishes the ill-posedness side. -/

/-- **Sharp integrability iff for `s^k · survival(s)` on `(l, ∞)`.**
    Strengthening of `integrableOn_rpow_mul_survival` to a biconditional:
    `IntegrableOn (s^k · (l/s)^α) (l, ∞) ↔ k < α − 1`.  Equivalent
    form: the `(k+1)`-st raw moment of the strong Pareto law is finite
    iff `k + 1 < α`. -/
theorem rpow_mul_survival_integrableOn_iff {l k α : ℝ} (hl : 0 < l) :
    IntegrableOn (fun s : ℝ => s ^ k * survival l α s) (Ioi l) ↔ k < α - 1 := by
  have hl_pow_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  have h_pt : ∀ s ∈ Ioi l, s ^ k * survival l α s = l ^ α * s ^ (k - α) := by
    intro s hs
    have hs_pos : 0 < s := hl.trans hs
    unfold survival
    rw [Real.div_rpow hl.le hs_pos.le,
        show (k - α : ℝ) = k + -α from by ring,
        Real.rpow_add hs_pos, Real.rpow_neg hs_pos.le]
    field_simp
  refine ⟨fun h => ?_, integrableOn_rpow_mul_survival hl⟩
  have h1 : IntegrableOn (fun s : ℝ => l ^ α * s ^ (k - α)) (Ioi l) :=
    h.congr_fun h_pt measurableSet_Ioi
  have h2 : IntegrableOn (fun s : ℝ => s ^ (k - α)) (Ioi l) := by
    have hcm := h1.const_mul (l ^ α)⁻¹
    have h_eq : (fun s : ℝ => (l ^ α)⁻¹ * (l ^ α * s ^ (k - α)))
                = fun s => s ^ (k - α) := by
      funext s; rw [← mul_assoc, inv_mul_cancel₀ hl_pow_pos.ne', one_mul]
    rwa [h_eq] at hcm
  have h3 : (k - α : ℝ) < -1 := (integrableOn_Ioi_rpow_iff hl).mp h2
  linarith

/-- **Pareto density** on the support `[l, ∞)`:
        f_S(s) = α · l^α / s^(α+1).
    The strong-Pareto density that integrates to 1 on `Ioi l` and matches
    the Breeden–Litzenberger second derivative `d²C/dK²`. -/
noncomputable def paretoDensity (l α s : ℝ) : ℝ := α * l ^ α / s ^ (α + 1)

/-- **Variance breakdown (layer-cake form).**  For `α ≤ 2`, the layer-cake
    integrand of the second moment, `s · survival(s) = l^α · s^(1−α)`,
    is *not* integrable on `(l, ∞)`: equivalent to `E[S²] = +∞`.
    Variance-swap pricing under such heavy tails is ill-defined. -/
theorem variance_layerCake_not_integrable {l α : ℝ}
    (hα_le : α ≤ 2) (hl : 0 < l) :
    ¬ IntegrableOn (fun s => s * survival l α s) (Ioi l) volume := by
  intro h
  have h_eq : (fun s : ℝ => s ^ (1:ℝ) * survival l α s)
              = fun s => s * survival l α s := by
    funext s; rw [Real.rpow_one]
  have h' : IntegrableOn (fun s : ℝ => s ^ (1:ℝ) * survival l α s) (Ioi l) := by
    rw [h_eq]; exact h
  have := (rpow_mul_survival_integrableOn_iff (k := 1) (α := α) hl).mp h'
  linarith

/-- **Variance breakdown (density form).**  For `1 < α ≤ 2`, the
    second-moment integrand `s² · paretoDensity(s)` is not integrable
    on the support.  Density-form analogue of
    `variance_layerCake_not_integrable`. -/
theorem variance_density_not_integrable {l α : ℝ}
    (hα : 1 < α) (hα_le : α ≤ 2) (hl : 0 < l) :
    ¬ IntegrableOn (fun s => s ^ (2:ℝ) * paretoDensity l α s) (Ioi l) volume := by
  intro h
  have h_pt : ∀ s ∈ Ioi l,
      s ^ (2:ℝ) * paretoDensity l α s = α * (s * survival l α s) := by
    intro s hs
    have hs_pos : 0 < s := hl.trans hs
    unfold paretoDensity survival
    rw [Real.div_rpow hl.le hs_pos.le,
        show s ^ (α + 1) = s * s ^ α from by
          rw [show (α + 1 : ℝ) = 1 + α from by ring, Real.rpow_add hs_pos,
              Real.rpow_one],
        show s ^ (2:ℝ) = s * s from by
          rw [show (2:ℝ) = 1 + 1 from by ring, Real.rpow_add hs_pos,
              Real.rpow_one]]
    have hsα_pos : 0 < s ^ α := Real.rpow_pos_of_pos hs_pos _
    field_simp
  have h_int' : IntegrableOn (fun s : ℝ => α * (s * survival l α s)) (Ioi l) :=
    h.congr_fun h_pt measurableSet_Ioi
  have hα_ne : (α : ℝ) ≠ 0 := by linarith
  have h_int'' : IntegrableOn (fun s : ℝ => s * survival l α s) (Ioi l) := by
    have hcm := h_int'.const_mul α⁻¹
    have h_eq : (fun s : ℝ => α⁻¹ * (α * (s * survival l α s)))
                = fun s => s * survival l α s := by
      funext s; rw [← mul_assoc, inv_mul_cancel₀ hα_ne, one_mul]
    rwa [h_eq] at hcm
  exact variance_layerCake_not_integrable hα_le hl h_int''

/-- **Variance is finite for `α > 2`.**  Sharp converse: for tails lighter
    than the variance threshold, the second-moment integrand IS
    integrable.  Direct corollary of `rpow_mul_survival_integrableOn_iff`. -/
theorem variance_layerCake_integrable {l α : ℝ}
    (hα : 2 < α) (hl : 0 < l) :
    IntegrableOn (fun s => s * survival l α s) (Ioi l) volume := by
  have h := (rpow_mul_survival_integrableOn_iff (k := 1) (α := α) hl).mpr
              (by linarith)
  have h_eq : (fun s : ℝ => s ^ (1:ℝ) * survival l α s)
              = fun s => s * survival l α s := by
    funext s; rw [Real.rpow_one]
  rwa [h_eq] at h


end TailOptionPricing
