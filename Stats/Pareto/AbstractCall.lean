module

/-
  Strong-Pareto core: abstract call-price functional from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.AbstractCall — abstract call-price `callPrice_F` and Pareto envelope.

  The layer-cake call price `callPrice_F F K := ∫_K^∞ F(s) ds`
  for a generic survival function `F`, with monotonicity and the
  Pareto envelope (upper / lower bounds against the Pareto survival).

  See `Stats/Pareto.lean` for the umbrella module.
-/
public import Stats.Pareto.Basic

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Abstract call-price functional and the Pareto envelope.

    Lift the Pareto-specific `callPrice` to a functional
    `callPrice_F F K := ∫_K^∞ F` over an arbitrary survival `F`.
    The strong Pareto is recovered by `F = survival l α`, and the
    Breeden–Litzenberger / continuity machinery already in
    `Stats/Calculus.lean` (`hasDerivAt_integral_Ioi`,
    `continuousOn_integral_Ioi`) applies verbatim to `callPrice_F`.

    The **Pareto envelope** then drops out: any tail with
    `F(s) ≤ (l/s)^α` is priced no higher than the Pareto, turning the
    paper's `α`-lower-bound (Eq. 10) into an upper bound on the call
    price for an entire class of distributions, not a point estimate. -/

/-- **Abstract call-price functional:**
        callPrice_F F K := ∫_K^∞ F(s) ds.
    Recovers `callPrice l α` when `F = survival l α`. -/
noncomputable def callPrice_F (F : ℝ → ℝ) (K : ℝ) : ℝ :=
  ∫ s in Ioi K, F s

/-- `callPrice` is the Pareto specialisation of `callPrice_F`. -/
theorem callPrice_F_survival {l α K : ℝ} :
    callPrice_F (survival l α) K = callPrice l α K := rfl

/-- **Monotonicity of `callPrice_F` in the survival function:**
    `F ≤ G` on `(K, ∞)` ⟹ `callPrice_F F K ≤ callPrice_F G K`. -/
theorem callPrice_F_mono {F G : ℝ → ℝ} {K : ℝ}
    (hF_int : IntegrableOn F (Ioi K) volume)
    (hG_int : IntegrableOn G (Ioi K) volume)
    (h_le : ∀ s ∈ Ioi K, F s ≤ G s) :
    callPrice_F F K ≤ callPrice_F G K :=
  setIntegral_mono_on hF_int hG_int measurableSet_Ioi h_le

/-- **Pareto-survival integrability:** for `0 < l ≤ K` and `α > 1`, the
    Pareto survival `(l/s)^α` is integrable on `(K, ∞)`. -/
theorem survival_integrableOn_Ioi {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    IntegrableOn (survival l α) (Ioi K) volume := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hα_neg : -α < -1 := by linarith
  have h_target : IntegrableOn (fun s : ℝ => l ^ α * s ^ (-α)) (Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt hα_neg hK_pos).const_mul (l ^ α)
  refine h_target.congr_fun ?_ measurableSet_Ioi
  intro s hs
  have hs_pos : 0 < s := hK_pos.trans hs
  show l ^ α * s ^ (-α) = survival l α s
  unfold survival
  rw [Real.div_rpow hl.le hs_pos.le, Real.rpow_neg hs_pos.le, ← div_eq_mul_inv]

/-- **Pareto envelope (robust upper bound).**  For any integrable survival
    `F` on `(K, ∞)` bounded above by the strong-Pareto survival,
        F(s) ≤ (l/s)^α  ⟹  callPrice_F F K ≤ callPrice l α K.
    Sharpens Eq. (10) from a point estimate of `α` into a *class* statement:
    every distribution whose tail is dominated by `(l/s)^α` is priced no
    higher than the Pareto reference. -/
theorem callPrice_envelope_upper {l α K : ℝ} {F : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K)
    (hF_int : IntegrableOn F (Ioi K) volume)
    (hF_bound : ∀ s ∈ Ioi K, F s ≤ survival l α s) :
    callPrice_F F K ≤ callPrice l α K := by
  rw [show callPrice l α K = callPrice_F (survival l α) K from rfl]
  exact callPrice_F_mono hF_int (survival_integrableOn_Ioi hα hl hK) hF_bound

/-- **Pareto envelope (robust lower bound).**  Symmetric to
    `callPrice_envelope_upper`: any integrable survival `F` on `(K, ∞)`
    bounded *below* by the strong-Pareto survival is priced *at least* as
    high as the Pareto reference.
        F(s) ≥ (l/s)^α  ⟹  callPrice_F F K ≥ callPrice l α K.
    Combined with the upper envelope, sandwiched survivals
        (l₁/s)^α ≤ F(s) ≤ (l₂/s)^α
    pin `callPrice_F F K` between two Pareto reference levels. -/
theorem callPrice_envelope_lower {l α K : ℝ} {F : ℝ → ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K)
    (hF_int : IntegrableOn F (Ioi K) volume)
    (hF_bound : ∀ s ∈ Ioi K, survival l α s ≤ F s) :
    callPrice l α K ≤ callPrice_F F K := by
  rw [show callPrice l α K = callPrice_F (survival l α) K from rfl]
  exact callPrice_F_mono (survival_integrableOn_Ioi hα hl hK) hF_int hF_bound


end TailOptionPricing
