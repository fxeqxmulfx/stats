/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.Conflation — paper Definitions 5–6.

  Conflation `I_1` vs `I_2` (Definition 5), Gaussian closed form
  (Eq. 6), and the corrected probability `p*` (Definition 6).

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
import Stats.BinaryForecasts.CharacteristicScale

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ## Conflation `I_1` vs `I_2` (paper Definition 5).

    `I_1 := ∫_K^∞ g(x) f(x) dx` and `I_2 := g(K) · ∫_K^∞ f(x) dx`.
    The conflation becomes an identity *iff* `g` is constant above `K`.
    For the binary payoff `g = θ_K`, `g ≡ 1` on `(K, ∞)`, so `I_1 = I_2`.
    For continuous `g(x) = x`, the substitution introduces a
    multiplicative gap captured by `characteristicScale_pareto`. -/

/-- **Expected payoff above `K` (paper `I_1`).** -/
noncomputable def I1 (g f : ℝ → ℝ) (K : ℝ) : ℝ :=
  ∫ x in Ioi K, g x * f x

/-- **Binary substitution (paper `I_2`).** -/
noncomputable def I2 (g f : ℝ → ℝ) (K : ℝ) : ℝ :=
  g K * ∫ x in Ioi K, f x

/-- **Conflation identity for constant `g` above `K`.**  If `g` is
    a.e. equal to `g K` on `(K, ∞)`, then `I_1 = I_2`.  This is the
    paper's Definition 5 "iff" direction: substitution becomes an
    identity precisely under constant-`g`.  In particular, applies
    to the Heaviside `θ_K` (binary payoff). -/
theorem I1_eq_I2_of_constantOn {g f : ℝ → ℝ} {K : ℝ}
    (h_const : ∀ᵐ x ∂(volume.restrict (Ioi K)), g x = g K) :
    I1 g f K = I2 g f K := by
  unfold I1 I2
  have h_eq : (fun x => g x * f x) =ᵐ[volume.restrict (Ioi K)]
              (fun x => g K * f x) := by
    filter_upwards [h_const] with x hx
    rw [hx]
  rw [integral_congr_ae h_eq, MeasureTheory.integral_const_mul]

/-- **Heaviside binary payoff `θ_K(x) := 𝟙_{x ≥ K}`.**  Equals `1`
    everywhere on `(K, ∞)` (where the strict-vs-weak distinction is
    immaterial). -/
noncomputable def heaviside (K : ℝ) (x : ℝ) : ℝ :=
  if K ≤ x then 1 else 0

/-- **Heaviside conflation: `I_1(θ_K) = I_2(θ_K)`.**  For the binary
    payoff, the substitution is *exact* — the expected payoff coincides
    with the probability of exceeding `K`.  This is the special case
    where the "binary world" and the "continuous world" agree. -/
theorem I1_eq_I2_heaviside {f : ℝ → ℝ} {K : ℝ} :
    I1 (heaviside K) f K = I2 (heaviside K) f K := by
  apply I1_eq_I2_of_constantOn
  -- For x ∈ Ioi K we have K < x, hence K ≤ x ⇒ heaviside K x = 1.
  -- Likewise heaviside K K = 1 (since K ≤ K).
  have h_mem : ∀ᵐ x ∂(volume.restrict (Ioi K)), x ∈ Ioi K :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [h_mem] with x hx
  have hKx : K ≤ x := le_of_lt hx
  unfold heaviside
  simp [hKx]

/-- **`I_1` for the Pareto payoff `g(x) = x`.**  Reduces to the strong
    Pareto tail expectation `E[S; S > K] = paretoTailExpectation l α K`. -/
theorem I1_pareto_id_eq {l α K : ℝ}
    (_hα : 1 < α) (_hl : 0 < l) (_hK : l ≤ K) :
    I1 id (paretoDensity l α) K = paretoTailExpectation l α K := by
  unfold I1 paretoTailExpectation paretoDensity
  rfl

/-- **`I_2` for the Pareto payoff `g(x) = x`.**  Reduces to
    `K · ℙ(S > K) = K · survival l α K`. -/
theorem I2_pareto_id_eq {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    I2 id (paretoDensity l α) K = K * survival l α K := by
  unfold I2
  have hK_pos : 0 < K := hl.trans_le hK
  show K * ∫ x in Ioi K, paretoDensity l α x = K * survival l α K
  congr 1
  -- Reduce the integrand to a constant times an `rpow`.
  have hα_neg : -(α + 1) < -1 := by linarith
  have hα_pos : 0 < α := by linarith
  have hα_ne : α ≠ 0 := hα_pos.ne'
  have hK_α_pos : 0 < K ^ α := Real.rpow_pos_of_pos hK_pos _
  have hK_α_ne : K ^ α ≠ 0 := hK_α_pos.ne'
  have h_pt : ∀ x ∈ Ioi K, paretoDensity l α x = (α * l ^ α) * x ^ (-(α + 1)) := by
    intro x hx
    have hx_pos : 0 < x := hK_pos.trans hx
    unfold paretoDensity
    rw [Real.rpow_neg hx_pos.le]
    have hx_α1_pos : 0 < x ^ (α + 1) := Real.rpow_pos_of_pos hx_pos _
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt,
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt hα_neg hK_pos]
  -- Now: goal is `α · l^α · (-K^(-(α+1)+1)/(-(α+1)+1)) = survival l α K`.
  have h_exp_eq : (-(α + 1) + 1 : ℝ) = -α := by ring
  rw [h_exp_eq]
  -- α · l^α · (-K^(-α)/(-α)) = α · l^α · K^(-α)/α = l^α · K^(-α).
  have h_alg : α * l ^ α * (-K ^ (-α) / -α) = l ^ α * K ^ (-α) := by
    rw [neg_div_neg_eq]
    field_simp
  rw [h_alg]
  -- survival l α K = (l/K)^α = l^α · K^(-α).
  unfold survival
  rw [Real.div_rpow hl.le hK_pos.le, Real.rpow_neg hK_pos.le]
  field_simp

/-- **Pareto `I_1 / I_2` closed form (paper Eq. 7).**  For `g(x) = x`
    and the strong Pareto density with `α > 1`,
        I_1 / I_2 = α / (α − 1).
    Binary substitution underestimates the tail payoff by the
    multiplicative factor `α / (α − 1) > 1`; the gap diverges as
    `α → 1⁺` (the heavy-tail limit). -/
theorem pareto_I1_div_I2_eq {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    I1 id (paretoDensity l α) K / I2 id (paretoDensity l α) K = α / (α - 1) := by
  rw [I1_pareto_id_eq hα hl hK, I2_pareto_id_eq hα hl hK]
  exact characteristicScale_pareto hα hl hK

/-- **Theorem 1, Pareto / D_2 limit-form (paper Eq. 4).**  The
    Pareto-class `I_1 / I_2` ratio *tends* to the characteristic scale
    `α / (α − 1)` as `K → ∞`.  Since the ratio is the *pointwise*
    constant `α / (α − 1)` for every `K ≥ l` (see `pareto_I1_div_I2_eq`),
    the limit is trivial; this theorem records the explicit `Tendsto`
    statement that matches the paper's wording. -/
theorem pareto_I1_div_I2_tendsto {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    Tendsto (fun K : ℝ =>
        I1 id (paretoDensity l α) K / I2 id (paretoDensity l α) K)
      atTop (𝓝 (α / (α - 1))) := by
  -- For K ≥ l the ratio is constantly α/(α-1).
  have h_ev : (fun K : ℝ =>
      I1 id (paretoDensity l α) K / I2 id (paretoDensity l α) K) =ᶠ[atTop]
      (fun _ : ℝ => α / (α - 1)) := by
    filter_upwards [eventually_ge_atTop l] with K hK
    exact pareto_I1_div_I2_eq hα hl hK
  exact (tendsto_const_nhds.congr' h_ev.symm)

/-! ## Gaussian closed form (paper Eq. 6).

    For the standard Gaussian `φ(x) = (2π)^(-1/2) · e^(−x²/2)`,
        ∫_K^∞ x · φ(x) dx = φ(K) = e^(−K²/2) / √(2π).
    Standard one-sided Gaussian tail integral.  Direct FTC with
    antiderivative `−φ` (the derivative `(−φ)'(x) = x · φ(x)` is
    already formalised in `hasDerivAt_neg_gaussianPDFReal_std`). -/

/-- **Standard Gaussian tail integral (paper Eq. 6).**  For any
    threshold `K ≥ 0`,
        ∫_K^∞ x · φ(x) dx = φ(K),
    where `φ = gaussianPDFReal 0 1`.  FTC with antiderivative `−φ`.
    The non-negativity hypothesis `0 ≤ K` ensures the integrand is
    non-negative on `(K, ∞)`, which suffices for the FTC-style
    integrability argument. -/
theorem gaussian_I1_id_eq {K : ℝ} (hK : 0 ≤ K) :
    ∫ x in Ioi K, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 K := by
  have h_antideriv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -gaussianPDFReal 0 1 y)
      (x * gaussianPDFReal 0 1 x) x := hasDerivAt_neg_gaussianPDFReal_std
  have h_tendsto_neg : Tendsto (fun x : ℝ => -gaussianPDFReal 0 1 x)
      atTop (𝓝 0) := by
    simpa using tendsto_gaussianPDFReal_std_atTop.neg
  have h_nonneg : ∀ x ∈ Set.Ioi K, 0 ≤ x * gaussianPDFReal 0 1 x := by
    intro x hx
    have hx_pos : 0 ≤ x := le_of_lt (lt_of_le_of_lt hK hx)
    exact mul_nonneg hx_pos (gaussianPDFReal_nonneg 0 1 x)
  have h_int_xφ : IntegrableOn (fun x : ℝ => x * gaussianPDFReal 0 1 x)
      (Set.Ioi K) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg ?_ ?_ h_nonneg h_tendsto_neg
    · exact ((h_antideriv K).continuousAt).continuousWithinAt
    · intro x _; exact h_antideriv x
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => -gaussianPDFReal 0 1 y) (a := K) (m := 0)
    (f' := fun x => x * gaussianPDFReal 0 1 x)
    ((h_antideriv K).continuousAt.continuousWithinAt)
    (fun x _ => h_antideriv x) h_int_xφ h_tendsto_neg
  rw [hFTC]; ring

/-! ## Corrected probability `p*` (paper Definition 6).

    The "corrected probability" `p*` is the probability at which the
    conflation `I_1 = I_2` is *forced* to hold:
        p* := { p : I_1 = g(K) · p } = I_1 / g(K).
    For Pareto with `g(x) = x`:
        p* = paretoTailExpectation l α K / K = (α / (α − 1)) · ℙ(X > K),
    i.e., the binary probability of exceeding `K` must be inflated by
    the factor `α / (α − 1)` for the conflation to be consistent. -/

/-- **Corrected probability for Pareto with `g(x) = x` (paper Definition 6).**
        p* = (α / (α − 1)) · survival(l, α, K).
    Direct rescaling of the survival probability by the
    characteristic-scale factor.  Algebraic restatement of Eq. 7. -/
theorem correctedProbability_pareto {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K / K = (α / (α - 1)) * survival l α K := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hK_ne : K ≠ 0 := hK_pos.ne'
  have h_surv_pos : 0 < survival l α K := by unfold survival; positivity
  have h_surv_ne : survival l α K ≠ 0 := h_surv_pos.ne'
  have h := paretoTailExpectation_div_survival hα hl hK
  -- h : paretoTailExpectation / survival = α·K/(α-1)
  -- ⇒ paretoTailExpectation = (α·K/(α-1)) · survival
  -- ⇒ paretoTailExpectation / K = (α/(α-1)) · survival.
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := by linarith
  field_simp at h ⊢
  linarith [h]


end TailOptionPricing
