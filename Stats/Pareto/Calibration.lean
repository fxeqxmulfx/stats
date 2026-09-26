/-
  Strong-Pareto core: multi-anchor calibration and term structure from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.Calibration — multi-anchor calibration, term structure.

  Contains:
    * `alphaFromTwoAnchors`, `lFromTwoAnchors` — closed-form
      inversion of the two-anchor Pareto-parameter calibration.
    * `callPrice_param_inj` — parameter-identifiability of the
      Pareto family from two strike anchors.
    * Term structure under `α`-stable scaling
      (`stable_scaling_identity`).

  See `Stats/Pareto.lean` for the umbrella module.
-/
import Stats.Pareto.Basic
import Stats.Pareto.Returns
import Stats.Pareto.TailRisk

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Multi-anchor calibration: identifiability and two-anchor inversion.

    The single-anchor inversion `callPrice_invert` recovers `l` given a
    fixed `α`.  In practice both parameters are unknown.  Two distinct
    anchor strikes `K₁ ≠ K₂` overdetermine `(l, α)` via the closed
    forms; here we extract the explicit two-anchor recovery formulas:
        α = 1 + log(C₁/C₂) / log(K₂/K₁),
        l = ((α−1) · C₁ · K₁^(α−1))^(1/α),
    and prove the corresponding **identifiability** statement: the
    parameter map `(l, α) ↦ (callPrice l α K₁, callPrice l α K₂)` is
    injective on `(0, ∞) × (1, ∞)` for `K₁ < K₂`.  This is the
    foundation of any joint LS calibrator: with `N ≥ 2` consistent
    observations, `(l, α)` are uniquely recovered. -/

/-- **Two-anchor recovery of `α`** (closed form).  Inverts the
    Pareto-pricing ratio formula:
        α = 1 + log(C₁/C₂) / log(K₂/K₁). -/
noncomputable def alphaFromTwoAnchors (C₁ C₂ K₁ K₂ : ℝ) : ℝ :=
  1 + Real.log (C₁ / C₂) / Real.log (K₂ / K₁)

/-- **Two-anchor recovery of `α` is exact on Pareto data.**  Plugging
    consistent anchor calls `Cᵢ = callPrice(l, α, Kᵢ)` into
    `alphaFromTwoAnchors` returns `α` exactly. -/
theorem alphaFromTwoAnchors_eq {l α K₁ K₂ : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l ≤ K₁) (hK₂ : l ≤ K₂)
    (hK_lt : K₁ < K₂) :
    alphaFromTwoAnchors (callPrice l α K₁) (callPrice l α K₂) K₁ K₂ = α := by
  have hK₁_pos : 0 < K₁ := hl.trans_le hK₁
  have hK₂_pos : 0 < K₂ := hl.trans_le hK₂
  have hK_ratio_pos : 0 < K₂ / K₁ := div_pos hK₂_pos hK₁_pos
  have hK_ratio_gt_one : 1 < K₂ / K₁ := by
    rw [lt_div_iff₀ hK₁_pos]; linarith
  have hlog_pos : 0 < Real.log (K₂ / K₁) := Real.log_pos hK_ratio_gt_one
  have hlog_ne : Real.log (K₂ / K₁) ≠ 0 := hlog_pos.ne'
  have hl_pow_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have hC₁_pos : 0 < callPrice l α K₁ := by
    rw [callPrice_eq hα hl hK₁]
    have hK₁p : 0 < K₁ ^ (1 - α) := Real.rpow_pos_of_pos hK₁_pos _
    positivity
  have h_ratio := callPrice_ratio hα hl hK₁ hK₂
  have hK_pow_pos : 0 < (K₂ / K₁) ^ (1 - α) :=
    Real.rpow_pos_of_pos hK_ratio_pos _
  have h_C1_C2 : callPrice l α K₁ / callPrice l α K₂ = (K₂ / K₁) ^ (α - 1) := by
    rw [h_ratio,
        show (α - 1 : ℝ) = -(1 - α) from by ring,
        Real.rpow_neg hK_ratio_pos.le]
    field_simp
  have h_log : Real.log (callPrice l α K₁ / callPrice l α K₂)
              = (α - 1) * Real.log (K₂ / K₁) := by
    rw [h_C1_C2]; exact Real.log_rpow hK_ratio_pos (α - 1)
  unfold alphaFromTwoAnchors
  rw [h_log, mul_div_assoc, div_self hlog_ne, mul_one]
  ring

/-- **Two-anchor recovery of `l`** (composition with `callPrice_invert`).
    Given the recovered `α` from `alphaFromTwoAnchors`, the Karamata
    constant follows by single-anchor inversion. -/
noncomputable def lFromTwoAnchors (C₁ C₂ K₁ K₂ : ℝ) : ℝ :=
  let α := alphaFromTwoAnchors C₁ C₂ K₁ K₂
  ((α - 1) * C₁ * K₁ ^ (α - 1)) ^ ((1 : ℝ) / α)

/-- **Two-anchor recovery of `l` is exact on Pareto data.**  Plugging
    consistent anchor calls into `lFromTwoAnchors` returns `l` exactly. -/
theorem lFromTwoAnchors_eq {l α K₁ K₂ : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l ≤ K₁) (hK₂ : l ≤ K₂)
    (hK_lt : K₁ < K₂) :
    lFromTwoAnchors (callPrice l α K₁) (callPrice l α K₂) K₁ K₂ = l := by
  unfold lFromTwoAnchors
  rw [alphaFromTwoAnchors_eq hα hl hK₁ hK₂ hK_lt]
  exact (callPrice_invert hα hl hK₁ rfl).symm

/-- **Identifiability of strong-Pareto calibration.**  Distinct parameter
    pairs `(l, α)` produce distinct two-anchor profiles: any two anchor
    calls (at distinct strikes) uniquely determine `(l, α)`.  Foundation
    for joint LS calibration uniqueness. -/
theorem callPrice_param_inj {l₁ l₂ α₁ α₂ K₁ K₂ : ℝ}
    (hα₁ : 1 < α₁) (hα₂ : 1 < α₂) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hK₁₁ : l₁ ≤ K₁) (hK₁₂ : l₂ ≤ K₁) (hK₂₁ : l₁ ≤ K₂) (hK₂₂ : l₂ ≤ K₂)
    (hK_lt : K₁ < K₂)
    (h₁ : callPrice l₁ α₁ K₁ = callPrice l₂ α₂ K₁)
    (h₂ : callPrice l₁ α₁ K₂ = callPrice l₂ α₂ K₂) :
    l₁ = l₂ ∧ α₁ = α₂ := by
  have hα_eq : α₁ = α₂ := by
    have h_lhs : alphaFromTwoAnchors
        (callPrice l₁ α₁ K₁) (callPrice l₁ α₁ K₂) K₁ K₂ = α₁ :=
      alphaFromTwoAnchors_eq hα₁ hl₁ hK₁₁ hK₂₁ hK_lt
    have h_rhs : alphaFromTwoAnchors
        (callPrice l₂ α₂ K₁) (callPrice l₂ α₂ K₂) K₁ K₂ = α₂ :=
      alphaFromTwoAnchors_eq hα₂ hl₂ hK₁₂ hK₂₂ hK_lt
    rw [h₁, h₂] at h_lhs
    linarith [h_lhs.symm.trans h_rhs]
  refine ⟨?_, hα_eq⟩
  have hl₁_inv : l₁ = ((α₁ - 1) * callPrice l₁ α₁ K₁ * K₁ ^ (α₁ - 1)) ^ ((1:ℝ)/α₁) :=
    callPrice_invert hα₁ hl₁ hK₁₁ rfl
  have hl₂_inv : l₂ = ((α₂ - 1) * callPrice l₂ α₂ K₁ * K₁ ^ (α₂ - 1)) ^ ((1:ℝ)/α₂) :=
    callPrice_invert hα₂ hl₂ hK₁₂ rfl
  rw [hα_eq] at hl₁_inv h₁
  rw [hl₁_inv, hl₂_inv, h₁]

/-- **Continuity / sensitivity of the two-anchor `α`-recovery in the
    observed prices.**  On the open positive orthant of call prices,
    `(C₁, C₂) ↦ alphaFromTwoAnchors C₁ C₂ K₁ K₂` is continuous when the
    strikes are distinct (and positive).  Smooth dependence of the
    recovered tail index on observation noise.  Sensitivity bounds
    `∂α̂/∂C_i = ±(C_i · log(K₂/K₁))⁻¹` are read off from the closed
    form. -/
theorem alphaFromTwoAnchors_continuousOn {K₁ K₂ : ℝ}
    (hK₁_pos : 0 < K₁) (hK_lt : K₁ < K₂) :
    ContinuousOn (fun C : ℝ × ℝ => alphaFromTwoAnchors C.1 C.2 K₁ K₂)
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  have hK₂_pos : 0 < K₂ := hK₁_pos.trans hK_lt
  have hK_ratio_pos : 0 < K₂ / K₁ := div_pos hK₂_pos hK₁_pos
  have hK_ratio_gt_one : 1 < K₂ / K₁ := by
    rw [lt_div_iff₀ hK₁_pos]; linarith
  have hlog_ne : Real.log (K₂ / K₁) ≠ 0 := (Real.log_pos hK_ratio_gt_one).ne'
  unfold alphaFromTwoAnchors
  refine ContinuousOn.add continuousOn_const ?_
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.log ?_ ?_
  · refine ContinuousOn.div ?_ continuousOn_snd ?_
    · exact continuousOn_fst
    · intro x hx
      exact (hx.2 : 0 < x.2).ne'
  · intro x hx
    have h1_pos : 0 < x.1 := hx.1
    have h2_pos : 0 < x.2 := hx.2
    exact (div_pos h1_pos h2_pos).ne'

/-! ## Term structure under `α`-stable Pareto scaling.

    The paper's Result 2 fixes a single horizon.  Real markets need a
    *term structure*: how does `callPriceReturns(l, α, S₀, K)` scale with
    horizon `T` when the upside return `r_T` is `α`-stable?

    Stable-Pareto scaling: `l(T) = l₀ · T^(1/α)`, so
        `(l(T) · S₀)^α = l₀^α · S₀^α · T`.
    Substituting into the closed form gives
        `callPriceReturns(l(T), α, S₀, K) = T · l₀^α · S₀^α · (K − S₀)^(1−α) / (α − 1)`,
    *linear* in `T`.  Theta (`∂C/∂T`) is a positive constant; calendar
    spreads are linear in the horizon difference.

    This characterises the scaling claim in the todo: `α(T)` is constant
    but `l(T) ∝ T^(1/α)`. -/

/-- **Stable-Pareto scaling identity.**  Under `l(T) = l₀ · T^(1/α)`,
        `(l(T))^α = l₀^α · T`.
    The exponent absorption is the algebraic core of the linear-in-T
    pricing formula. -/
theorem stable_scaling_identity {l₀ α T : ℝ}
    (hα_pos : 0 < α) (hl₀ : 0 ≤ l₀) (hT : 0 ≤ T) :
    (l₀ * T ^ ((1:ℝ) / α)) ^ α = l₀ ^ α * T := by
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hT_pow_nn : 0 ≤ T ^ ((1:ℝ) / α) := Real.rpow_nonneg hT _
  rw [Real.mul_rpow hl₀ hT_pow_nn, ← Real.rpow_mul hT,
      show ((1:ℝ) / α * α) = 1 from by field_simp,
      Real.rpow_one]

/-- **Term-structure call price** under `α`-stable Pareto returns
    (`l(T) := l₀ · T^(1/α)`):
        `callPriceReturns_T l₀ α S₀ K T := callPriceReturns (l₀ · T^(1/α)) α S₀ K`. -/
noncomputable def callPriceReturns_T (l₀ α S₀ K T : ℝ) : ℝ :=
  callPriceReturns (l₀ * T ^ ((1:ℝ) / α)) α S₀ K

/-- **Linear-in-T closed form.**  Under stable scaling and the
    extension of the strike-feasibility condition `S₀(1 + l(T)) ≤ K`,
        `callPriceReturns_T(l₀, α, S₀, K, T) = T · l₀^α · S₀^α · (K − S₀)^(1−α) / (α − 1)`.
    The Pareto-returns call is *linear* in horizon. -/
theorem callPriceReturns_T_eq {l₀ α S₀ K T : ℝ}
    (hα : 1 < α) (hl₀ : 0 < l₀) (hS₀ : 0 < S₀) (hT : 0 < T)
    (hK : S₀ * (1 + l₀ * T ^ ((1:ℝ) / α)) ≤ K) :
    callPriceReturns_T l₀ α S₀ K T
      = T * l₀ ^ α * S₀ ^ α * (K - S₀) ^ (1 - α) / (α - 1) := by
  have hα_pos : 0 < α := by linarith
  have hT_pow_pos : 0 < T ^ ((1:ℝ) / α) := Real.rpow_pos_of_pos hT _
  have hl_T_pos : 0 < l₀ * T ^ ((1:ℝ) / α) := mul_pos hl₀ hT_pow_pos
  unfold callPriceReturns_T
  rw [callPriceReturns_eq hα hl_T_pos hS₀ hK]
  have h_scale : (l₀ * T ^ ((1:ℝ) / α) * S₀) ^ α = l₀ ^ α * T * S₀ ^ α := by
    rw [show l₀ * T ^ ((1:ℝ) / α) * S₀ = (l₀ * T ^ ((1:ℝ) / α)) * S₀ from rfl,
        Real.mul_rpow hl_T_pos.le hS₀.le,
        stable_scaling_identity hα_pos hl₀.le hT.le]
  rw [h_scale]
  ring

/-- **Theta — derivative of the term-structure call price w.r.t. `T`.**
    Under stable scaling, the Pareto-returns call price's `T`-derivative
    is the *constant*
        `∂C/∂T = l₀^α · S₀^α · (K − S₀)^(1−α) / (α − 1)`.
    Linearity in `T` is exactly the claim that theta is non-decaying. -/
theorem callPriceReturns_T_hasDerivAt {l₀ α S₀ K T : ℝ}
    (hα : 1 < α) (hl₀ : 0 < l₀) (hS₀ : 0 < S₀) (hT : 0 < T)
    (hK : S₀ * (1 + l₀ * T ^ ((1:ℝ) / α)) < K) :
    HasDerivAt (callPriceReturns_T l₀ α S₀ K)
      (l₀ ^ α * S₀ ^ α * (K - S₀) ^ (1 - α) / (α - 1)) T := by
  have hα_pos : 0 < α := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hT_pow_pos : 0 < T ^ ((1:ℝ) / α) := Real.rpow_pos_of_pos hT _
  -- Since the closed form holds in a neighbourhood of T, we differentiate
  -- the linear closed form `T · c` to get `c`.
  set c : ℝ := l₀ ^ α * S₀ ^ α * (K - S₀) ^ (1 - α) / (α - 1)
  have h_lin : HasDerivAt (fun T : ℝ => T * c) c T := by
    simpa using ((hasDerivAt_id T).mul_const c)
  -- Show callPriceReturns_T = (fun T => T · c) eventually around T.
  -- Need an open neighbourhood where the strike condition holds.
  have h_local_eq : (fun t : ℝ => callPriceReturns_T l₀ α S₀ K t) =ᶠ[𝓝 T]
      (fun t : ℝ => t * c) := by
    have h_cont_aux : ContinuousAt
        (fun t : ℝ => S₀ * (1 + l₀ * t ^ ((1:ℝ) / α))) T := by
      refine ContinuousAt.mul continuousAt_const ?_
      refine ContinuousAt.add continuousAt_const ?_
      refine ContinuousAt.mul continuousAt_const ?_
      exact ContinuousAt.rpow_const continuousAt_id (Or.inl hT.ne')
    have h_open : ∀ᶠ t in 𝓝 T, S₀ * (1 + l₀ * t ^ ((1:ℝ) / α)) < K := by
      have h_ev := h_cont_aux.eventually_lt_const hK
      exact h_ev
    have h_pos_T : ∀ᶠ t in 𝓝 T, (0:ℝ) < t :=
      eventually_gt_nhds hT
    filter_upwards [h_open, h_pos_T] with t h_t_strike h_t_pos
    show callPriceReturns_T l₀ α S₀ K t = t * c
    rw [callPriceReturns_T_eq hα hl₀ hS₀ h_t_pos h_t_strike.le]
    show t * l₀ ^ α * S₀ ^ α * (K - S₀) ^ (1 - α) / (α - 1)
        = t * (l₀ ^ α * S₀ ^ α * (K - S₀) ^ (1 - α) / (α - 1))
    ring
  exact h_lin.congr_of_eventuallyEq h_local_eq

/-- **Calendar spread is linear in horizon difference.**  For
    `0 < T₁ < T₂` both inside the strike-feasibility region, the
    calendar spread satisfies
        `C(T₂) − C(T₁) = (T₂ − T₁) · l₀^α · S₀^α · (K − S₀)^(1−α) / (α − 1)`.
    Direct corollary of linearity. -/
theorem callPriceReturns_T_calendarSpread {l₀ α S₀ K T₁ T₂ : ℝ}
    (hα : 1 < α) (hl₀ : 0 < l₀) (hS₀ : 0 < S₀) (hT₁ : 0 < T₁) (hT₁₂ : T₁ < T₂)
    (hK₁ : S₀ * (1 + l₀ * T₁ ^ ((1:ℝ) / α)) ≤ K)
    (hK₂ : S₀ * (1 + l₀ * T₂ ^ ((1:ℝ) / α)) ≤ K) :
    callPriceReturns_T l₀ α S₀ K T₂ - callPriceReturns_T l₀ α S₀ K T₁
      = (T₂ - T₁) * (l₀ ^ α * S₀ ^ α * (K - S₀) ^ (1 - α) / (α - 1)) := by
  have hT₂ : 0 < T₂ := hT₁.trans hT₁₂
  rw [callPriceReturns_T_eq hα hl₀ hS₀ hT₂ hK₂,
      callPriceReturns_T_eq hα hl₀ hS₀ hT₁ hK₁]
  ring

/-- **VaR term-structure scaling.**  Under `l(T) = l₀ · T^(1/α)`, the
    Pareto Value-at-Risk on the *upside-return* density at level `p`
    scales as `T^(1/α)`:
        `paretoVaR(l(T), α, p) = T^(1/α) · paretoVaR(l₀, α, p)`.
    Standard `α`-stable temporal scaling for a power-law tail. -/
theorem paretoVaR_T_scaling (l₀ α p T : ℝ) :
    paretoVaR (l₀ * T ^ ((1:ℝ) / α)) α p = T ^ ((1:ℝ) / α) * paretoVaR l₀ α p := by
  unfold paretoVaR; ring


end TailOptionPricing
