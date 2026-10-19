module

/-
  Karamata's Abelian theorem.

  ## Stats.RegularVariation.Abelian.Basic — `survivalSV`, `callPriceSV`, substitution identity.

  Defines `survivalSV`, `callPriceSV`, and the substitution identity
  underlying the Abelian theorem.  Establishes the strong-Pareto
  special case as a corollary.

  See `Stats/RegularVariation/Abelian.lean` for the umbrella.
-/
public import Stats.RegularVariation.Defs
public import Stats.RegularVariation.Representation
public import Stats.Pareto
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-- Slowly-varying generalisation of the strong-Pareto survival.
    `bF(s) = L(s) · s^(-α)`, with `L` slowly varying.  Strong Pareto is
    the special case `L = l^α` (a positive constant). -/
noncomputable def survivalSV (L : ℝ → ℝ) (α s : ℝ) : ℝ := L s * s ^ (-α)

/-- European call price under the slowly-varying survival, defined via the
    layer-cake representation `C(K) = ∫_K^∞ ℙ(S > s) ds`. -/
noncomputable def callPriceSV (L : ℝ → ℝ) (α K : ℝ) : ℝ :=
  ∫ s in Ioi K, survivalSV L α s

/-- **Strong Pareto is the special case `L ≡ l^α` (constant).**  Connects the
    new SV-survival call price to the strong-Pareto `callPrice` from
    `Stats.Pareto`. -/
theorem callPrice_eq_callPriceSV_const {l α K : ℝ} (hl : 0 < l) (hK_pos : 0 < K) :
    callPrice l α K = callPriceSV (fun _ => l ^ α) α K := by
  unfold callPrice callPriceSV survival survivalSV
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [Set.mem_Ioi] at hs
  have hs_pos : 0 < s := lt_of_lt_of_le hK_pos (le_of_lt hs)
  show (l / s) ^ α = l ^ α * s ^ (-α)
  rw [Real.div_rpow hl.le hs_pos.le, div_eq_mul_inv, ← Real.rpow_neg hs_pos.le]

/-! ### Substitution identity

    The change of variables `s = K · u` turns the tail integral into
        `K^(1-α) · ∫_1^∞ L(K · u) · u^(-α) du`,
    isolating the universal `K^(1-α)` scaling. -/

lemma callPriceSV_substitution
    {L : ℝ → ℝ} {α K : ℝ} (hK_pos : 0 < K) :
    callPriceSV L α K =
      K ^ (1 - α) * ∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α) := by
  have hK_ne : (K : ℝ) ≠ 0 := hK_pos.ne'
  unfold callPriceSV survivalSV
  -- Apply substitution s = K·x: ∫_K^∞ f = K · ∫_1^∞ f(K·)
  have h_subst :
      ∫ x in Ioi (1 : ℝ), L (K * x) * (K * x) ^ (-α) =
      K⁻¹ * ∫ s in Ioi K, L s * s ^ (-α) := by
    have h := integral_comp_mul_left_Ioi
      (fun s : ℝ => L s * s ^ (-α)) 1 hK_pos
    rw [show K * (1 : ℝ) = K from by ring] at h
    simpa [smul_eq_mul] using h
  -- Pull K^(-α) out of (K*x)^(-α).
  have h_pt : ∀ x ∈ Ioi (1 : ℝ),
      L (K * x) * (K * x) ^ (-α) = K ^ (-α) * (L (K * x) * x ^ (-α)) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one (le_of_lt hx)
    rw [Real.mul_rpow hK_pos.le hx_pos.le]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_pt] at h_subst
  rw [integral_const_mul] at h_subst
  -- h_subst : K^(-α) * (∫ x in Ioi 1, L(K*x) * x^(-α))
  --         = K⁻¹ * (∫ s in Ioi K, L(s) * s^(-α))
  -- Solve for ∫ s in Ioi K, L(s) * s^(-α):
  --       = K · K^(-α) * (∫ x in Ioi 1, L(K*x) * x^(-α))
  --       = K^(1-α) * (∫ x in Ioi 1, L(K*x) * x^(-α))
  have h_K_mul : K * (K⁻¹ * ∫ s in Ioi K, L s * s ^ (-α)) =
      ∫ s in Ioi K, L s * s ^ (-α) := by
    rw [← mul_assoc, mul_inv_cancel₀ hK_ne, one_mul]
  have h_K_pow : K * K ^ (-α) = K ^ (1 - α) := by
    rw [show (1 - α : ℝ) = 1 + (-α) from by ring,
        Real.rpow_add hK_pos, Real.rpow_one]
  calc ∫ s in Ioi K, L s * s ^ (-α)
      = K * (K⁻¹ * ∫ s in Ioi K, L s * s ^ (-α)) := h_K_mul.symm
    _ = K * (K ^ (-α) * ∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α)) := by rw [h_subst]
    _ = (K * K ^ (-α)) * ∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α) := by ring
    _ = K ^ (1 - α) * ∫ x in Ioi (1 : ℝ), L (K * x) * x ^ (-α) := by rw [h_K_pow]


end TailOptionPricing
