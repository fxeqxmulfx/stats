/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.ParetoSensitivity — paper Eq. 9 and Remarks 1–5.

  Contains:
    * Pareto sensitivity `∂²(I_1/I_2)/∂α² = 2K/(α-1)³` (Eq. 9).
    * Inseparability of probability (Remark 5): convex Jensen gap.

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
import Stats.BinaryForecasts.Conflation
import Stats.BinaryForecasts.Brier

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ## Pareto sensitivity (paper Eq. 9).

    For fixed `K > 0`, the conditional-mean function
        m(α) := α · K / (α − 1)
    (equivalently `E[X | X > K]` under Pareto) has second derivative
        m''(α) = 2 K / (α − 1)³.
    Positive and diverging as `α → 1⁺` — small perturbations in the
    tail index `α` produce large changes in the expected tail payoff,
    *with the sensitivity growing as the tails get heavier*.  Combined
    with Jensen's inequality (Remark 1), this means stochastic `α`
    increases the conflation discrepancy. -/

/-- **First derivative of the Pareto conditional mean in `α`:**
        d/dα [α K / (α − 1)] = −K / (α − 1)². -/
theorem paretoTailMean_hasDerivAt_alpha {α K : ℝ} (hα : 1 < α) :
    HasDerivAt (fun a => a * K / (a - 1)) (-K / (α - 1) ^ 2) α := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := by linarith
  have h_num : HasDerivAt (fun a : ℝ => a * K) (1 * K) α :=
    (hasDerivAt_id α).mul_const K
  have h_den : HasDerivAt (fun a : ℝ => a - 1) 1 α := by
    simpa using (hasDerivAt_id α).sub_const 1
  have h_den_ne : (fun a : ℝ => a - 1) α ≠ 0 := by simpa using hα1_ne
  have h_div := h_num.div h_den h_den_ne
  convert h_div using 1
  show (-K / (α - 1) ^ 2 : ℝ) = (1 * K * (α - 1) - α * K * 1) / (α - 1) ^ 2
  field_simp
  ring

/-- **Second derivative of the Pareto conditional mean in `α` (paper Eq. 9):**
        d²/dα² [α K / (α − 1)] = 2 K / (α − 1)³.
    Positive for any `K > 0` and `α > 1`; diverges as `α → 1⁺` — the
    fatter the tail, the more sensitive the expected payoff to small
    changes in `α`.  Direct calculation. -/
theorem paretoTailMean_hasDerivAt_alpha_second {α K : ℝ} (hα : 1 < α) :
    HasDerivAt (fun a : ℝ => -K / (a - 1) ^ 2) (2 * K / (α - 1) ^ 3) α := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := by linarith
  have hα1_sq_ne : (α - 1 : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hα1_ne
  have h_num : HasDerivAt (fun _ : ℝ => (-K : ℝ)) 0 α := hasDerivAt_const α (-K)
  have h_id : HasDerivAt (fun a : ℝ => a) 1 α := hasDerivAt_id α
  have h_sub : HasDerivAt (fun a : ℝ => a - 1) 1 α := by
    simpa using (hasDerivAt_id α).sub_const 1
  have h_sq : HasDerivAt (fun a : ℝ => (a - 1) ^ 2) (2 * (α - 1)) α := by
    have h := h_sub.pow 2
    convert h using 1; ring
  have h_sq_ne : (fun a : ℝ => (a - 1) ^ 2) α ≠ 0 := by simpa using hα1_sq_ne
  have h_div := h_num.div h_sq h_sq_ne
  convert h_div using 1
  show (2 * K / (α - 1) ^ 3 : ℝ) =
       (0 * (α - 1) ^ 2 - (-K) * (2 * (α - 1))) / ((α - 1) ^ 2) ^ 2
  have h_pow_eq : ((α - 1) ^ 2) ^ 2 = (α - 1) ^ 4 := by ring
  rw [h_pow_eq]
  have h_pow_split : (α - 1) ^ 4 = (α - 1) ^ 3 * (α - 1) := by ring
  rw [h_pow_split]
  field_simp
  ring

/-- **Sensitivity sign (paper Remark 1):** `∂²(I_1/I_2 · K) / ∂α² > 0`.
    The conditional mean's second derivative in `α` is strictly
    positive for any `K > 0` and `α > 1`.  By Jensen's inequality,
    under stochastic `α` (parameter uncertainty), `E[m(α)] > m(E[α])`,
    so the discrepancy `I_1 − I_2` grows under parameter uncertainty. -/
theorem paretoTailMean_secondDeriv_alpha_pos {α K : ℝ}
    (hα : 1 < α) (hK : 0 < K) :
    0 < 2 * K / (α - 1) ^ 3 := by
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_cube_pos : 0 < (α - 1) ^ 3 := by positivity
  positivity

/-- **Eq. 9 in literal `deriv^[2]` form.**  The iterated derivative
        `(d²/dα²) [α · K / (α − 1)] = 2 · K / (α − 1)³`
    is what the paper writes.  Combines `paretoTailMean_hasDerivAt_alpha`
    and `paretoTailMean_hasDerivAt_alpha_second` via the standard
    `HasDerivAt.deriv` chain.  Note: the inner `deriv` is computed
    only locally around `α` (via `EventuallyEq`), so the conclusion
    is on the second derivative evaluated at `α`. -/
theorem paretoTailMean_iteratedDeriv_two {α K : ℝ} (hα : 1 < α) :
    deriv (deriv (fun a : ℝ => a * K / (a - 1))) α = 2 * K / (α - 1) ^ 3 := by
  have h_local : deriv (fun a : ℝ => a * K / (a - 1)) =ᶠ[𝓝 α]
                 (fun a : ℝ => -K / (a - 1) ^ 2) := by
    -- First derivative agrees with `-K/(a-1)²` on a neighborhood of α.
    have h_open : ∀ᶠ a in 𝓝 α, 1 < a := eventually_gt_nhds hα
    filter_upwards [h_open] with a ha
    exact (paretoTailMean_hasDerivAt_alpha ha).deriv
  -- Replace deriv by the closed form, then differentiate it.
  rw [Filter.EventuallyEq.deriv_eq h_local]
  exact (paretoTailMean_hasDerivAt_alpha_second hα).deriv

/-! ## Inseparability of probability (paper Remark 5).

    The theorems below prove constant-payoff integral linearity,
    affine-payoff integral decomposition, and strict Jensen for two
    distinct points with a strictly convex payoff and positive weights.
    Non-affinity alone does not imply strict Jensen for every law.
    A general probability version also needs normalization and
    integrability; see REVIEW.md, BF-28. -/

/-- **Inseparability identity for constant payoff.**  When `g` is
    constant `c` on the integration domain, the conflation is *exact*:
        ∫_K^∞ c · f(x) dx = c · ∫_K^∞ f(x) dx.
    This is a sufficient equality case, by integral linearity. -/
theorem inseparability_const {f : ℝ → ℝ} {K c : ℝ} :
    ∫ x in Ioi K, c * f x = c * ∫ x in Ioi K, f x :=
  MeasureTheory.integral_const_mul c _

/-- **Inseparability gap is the linearity defect.**  For *affine* `g`
    `g(x) = a · x + b`, the conflation gap reduces to the
    expectation-vs-evaluation gap of the linear part:
        ∫_K^∞ (a·x + b) · f(x) dx
            = a · ∫_K^∞ x · f(x) dx + b · ∫_K^∞ f(x) dx.
    Direct integral linearity under the stated integrability assumptions. -/
theorem inseparability_affine_linearity {f : ℝ → ℝ} {K a b : ℝ}
    (hf_int : IntegrableOn f (Ioi K))
    (hxf_int : IntegrableOn (fun x : ℝ => x * f x) (Ioi K)) :
    ∫ x in Ioi K, (a * x + b) * f x
      = a * (∫ x in Ioi K, x * f x) + b * (∫ x in Ioi K, f x) := by
  have h_pt : (fun x : ℝ => (a * x + b) * f x)
      = fun x => a * (x * f x) + b * f x := by funext x; ring
  rw [h_pt]
  rw [MeasureTheory.integral_add (hxf_int.const_mul a) (hf_int.const_mul b)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **Strict Jensen (paper Eq. 17 / Remark 5).**  For a strictly convex
    payoff `g` on `ℝ` and any *two distinct* points `x ≠ y` with
    positive weights `(a, b)` summing to `1`:
        g(a·x + b·y) < a·g(x) + b·g(y),
    i.e., the expected payoff `a·g(x) + b·g(y)` strictly exceeds the
    payoff at the average `a·x + b·y`.  This is the two-point form of
    Jensen's inequality. A general discrete or measure-theoretic
    extension requires its own hypotheses and proof. -/
theorem inseparability_jensen_strict {g : ℝ → ℝ}
    (hg : StrictConvexOn ℝ Set.univ g) {x y a b : ℝ}
    (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    g (a * x + b * y) < a * g x + b * g y := by
  have h := hg.2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab
  simpa [smul_eq_mul] using h



end TailOptionPricing
