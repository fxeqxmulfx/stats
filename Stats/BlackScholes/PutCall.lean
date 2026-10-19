module

/-
  Black–Scholes put price + put–call parity.

  • General Gaussian MGF at `t = 1`: `∫ exp(x) ∂(𝒩(μ, v)) = exp(μ + v/2)`.
  • `putPriceBS` definition `E_Q[(K − S_T)⁺]`.
  • Put–call parity (general): `BSC − P = S₀·exp(μ + v/2) − K`.
  • BS put closed forms (general + risk-neutral).
-/
public import Stats.BlackScholes.CallPrice

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory MeasureTheory in
/-- **Gaussian MGF at `t = 1`.**  For any `μ : ℝ`, `v : ℝ≥0`,
        `∫ exp(x) ∂(𝒩(μ, v)) = exp(μ + v/2)`. -/
theorem integral_exp_gaussianReal {μ : ℝ} {v : ℝ≥0} :
    ∫ x, Real.exp x ∂(gaussianReal μ v) =
    Real.exp (μ + (v : ℝ) / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := μ) (v := v)) 1
  have h_arg : μ * 1 + (v : ℝ) * (1 : ℝ)^2 / 2 = μ + (v : ℝ) / 2 := by ring
  rw [h_arg] at h
  show ∫ x, Real.exp x ∂(gaussianReal μ v) = Real.exp (μ + (v : ℝ) / 2)
  have h_mgf : mgf id (gaussianReal μ v) 1 =
      ∫ x, Real.exp x ∂(gaussianReal μ v) := by
    unfold mgf
    simp [id]
  rw [← h_mgf]; exact h

open ProbabilityTheory MeasureTheory in
/-- **Lognormal put price at zero interest rates.**
    `P(K) = E[(K − S_T)⁺]` with `S_T = S₀ · exp(X)`, `X ∼ 𝒩(μ, v)`.
    The choice `μ = -v/2` is risk-neutral. -/
noncomputable def putPriceBS (S₀ μ : ℝ) (v : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ x, max (K - S₀ * Real.exp x) 0 ∂(gaussianReal μ v)

open ProbabilityTheory MeasureTheory in
/-- **Put–call parity** (general parametrisation).
        `BSC(K) − P(K) = S₀ · exp(μ + v/2) − K`,
    which is `S₀ · E[exp(X)] − K`.  For risk-neutral `μ = −v/2`, this is the
    classical `BSC − P = S₀ − K`. -/
theorem putCallParity_BS
    {S₀ μ K : ℝ} {v : ℝ≥0} :
    callPriceBS S₀ μ v K - putPriceBS S₀ μ v K =
    S₀ * Real.exp (μ + (v : ℝ) / 2) - K := by
  rw [callPriceBS_eq_expectation]
  unfold putPriceBS
  have h_int_exp : Integrable (fun x : ℝ => Real.exp x) (gaussianReal μ v) := by
    simpa using integrable_exp_mul_gaussianReal (μ := μ) (v := v) 1
  have h_int_S₀exp : Integrable (fun x : ℝ => S₀ * Real.exp x) (gaussianReal μ v) :=
    h_int_exp.const_mul S₀
  have h_int_const : Integrable (fun _ : ℝ => K) (gaussianReal μ v) :=
    integrable_const K
  have h_int_call : Integrable
      (fun x : ℝ => max (S₀ * Real.exp x - K) 0) (gaussianReal μ v) :=
    (h_int_S₀exp.sub h_int_const).pos_part
  have h_int_put : Integrable
      (fun x : ℝ => max (K - S₀ * Real.exp x) 0) (gaussianReal μ v) :=
    (h_int_const.sub h_int_S₀exp).pos_part
  rw [← MeasureTheory.integral_sub h_int_call h_int_put]
  have h_pointwise : ∀ x : ℝ,
      max (S₀ * Real.exp x - K) 0 - max (K - S₀ * Real.exp x) 0 =
      S₀ * Real.exp x - K := by
    intro x
    by_cases h : S₀ * Real.exp x ≤ K
    · have h1 : S₀ * Real.exp x - K ≤ 0 := by linarith
      have h2 : 0 ≤ K - S₀ * Real.exp x := by linarith
      rw [max_eq_right h1, max_eq_left h2]; ring
    · have h' : K < S₀ * Real.exp x := lt_of_not_ge h
      have h1 : 0 ≤ S₀ * Real.exp x - K := by linarith
      have h2 : K - S₀ * Real.exp x ≤ 0 := by linarith
      rw [max_eq_left h1, max_eq_right h2]; ring
  rw [show (fun x : ℝ =>
        max (S₀ * Real.exp x - K) 0 - max (K - S₀ * Real.exp x) 0) =
        (fun x : ℝ => S₀ * Real.exp x - K) from funext h_pointwise]
  rw [MeasureTheory.integral_sub h_int_S₀exp h_int_const,
      MeasureTheory.integral_const_mul S₀ Real.exp,
      integral_exp_gaussianReal]
  have : IsProbabilityMeasure (gaussianReal μ v) := by infer_instance
  rw [MeasureTheory.integral_const, probReal_univ, smul_eq_mul, one_mul]

open ProbabilityTheory MeasureTheory in
/-- **BS put closed form (general parametrisation).**
        `P(K) = K · Φ((log(K/S₀) − μ)/√v) −
                S₀ · exp(μ + v/2) · Φ((log(K/S₀) − μ − v)/√v)`. -/
theorem putPriceBS_closed_form_general
    {S₀ μ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    putPriceBS S₀ μ v K =
    K * stdNormalCdf
        ((Real.log (K / S₀) - μ) / Real.sqrt (v : ℝ)) -
    S₀ * Real.exp (μ + (v : ℝ) / 2) *
      stdNormalCdf
        ((Real.log (K / S₀) - μ - (v : ℝ)) / Real.sqrt (v : ℝ)) := by
  have h_parity : callPriceBS S₀ μ v K - putPriceBS S₀ μ v K =
      S₀ * Real.exp (μ + (v : ℝ) / 2) - K :=
    putCallParity_BS
  have h_closed : callPriceBS S₀ μ v K =
      S₀ * Real.exp (μ + (v : ℝ) / 2) *
        (1 - stdNormalCdf
          ((Real.log (K / S₀) - μ - (v : ℝ)) / Real.sqrt (v : ℝ))) -
      K * (1 - stdNormalCdf
        ((Real.log (K / S₀) - μ) / Real.sqrt (v : ℝ))) :=
    callPriceBS_closed_form_general hS₀ hv hK
  have h_put_eq : putPriceBS S₀ μ v K =
      callPriceBS S₀ μ v K - (S₀ * Real.exp (μ + (v : ℝ) / 2) - K) := by linarith
  rw [h_put_eq, h_closed]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes put closed form, risk-neutral / zero-rate parametrisation.**
        `P(K) = K · Φ(−d₂) − S₀ · Φ(−d₁)`. -/
theorem putPriceBS_closed_form_riskNeutral
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    putPriceBS S₀ (-((v : ℝ) / 2)) v K =
    K * stdNormalCdf
        (-((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))) -
    S₀ * stdNormalCdf
      (-((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ))) := by
  have h_parity := putCallParity_BS (S₀ := S₀) (K := K) (v := v) (μ := -((v : ℝ) / 2))
  have h_closed := callPriceBS_closed_form_riskNeutral hS₀ hv hK
  have h_exp_zero : Real.exp (-((v : ℝ) / 2) + (v : ℝ) / 2) = 1 := by
    rw [show -((v : ℝ) / 2) + (v : ℝ) / 2 = 0 from by ring, Real.exp_zero]
  rw [h_exp_zero, mul_one] at h_parity
  have h_put_eq : putPriceBS S₀ (-((v : ℝ) / 2)) v K =
      callPriceBS S₀ (-((v : ℝ) / 2)) v K - (S₀ - K) := by linarith
  rw [h_put_eq, h_closed]
  rw [stdNormalCdf_neg, stdNormalCdf_neg]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Strict convexity of the Black–Scholes put price.**  Follows from
    `callPriceBS_strictConvexOn` and put–call parity:
    `P(K) = BSC(K) + (K − S₀·exp(μ + v/2))` on `(0, ∞)`, and adding an affine
    function preserves strict convexity. -/
theorem putPriceBS_strictConvexOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (putPriceBS S₀ μ v) := by
  have h_eq : Set.EqOn (putPriceBS S₀ μ v)
      (fun K : ℝ =>
        callPriceBS S₀ μ v K + (K - S₀ * Real.exp (μ + (v : ℝ) / 2)))
      (Set.Ioi 0) := by
    intro K _
    have h_parity : callPriceBS S₀ μ v K - putPriceBS S₀ μ v K =
        S₀ * Real.exp (μ + (v : ℝ) / 2) - K :=
      putCallParity_BS
    linarith
  have h_aff : ConvexOn ℝ (Set.Ioi 0)
      (fun K : ℝ => K - S₀ * Real.exp (μ + (v : ℝ) / 2)) := by
    have h_id : ConvexOn ℝ (Set.Ioi (0:ℝ)) (id : ℝ → ℝ) :=
      convexOn_id (convex_Ioi 0)
    have h := h_id.add_const (-(S₀ * Real.exp (μ + (v : ℝ) / 2)))
    have h_eq : (id + fun _ : ℝ => -(S₀ * Real.exp (μ + (v : ℝ) / 2))) =
        (fun K : ℝ => K - S₀ * Real.exp (μ + (v : ℝ) / 2)) := by
      funext K; simp [Pi.add_apply, sub_eq_add_neg]
    rwa [h_eq] at h
  have h_combined : StrictConvexOn ℝ (Set.Ioi 0)
      (fun K : ℝ =>
        callPriceBS S₀ μ v K + (K - S₀ * Real.exp (μ + (v : ℝ) / 2))) :=
    (callPriceBS_strictConvexOn hS₀ hv).add_convexOn h_aff
  exact h_combined.congr h_eq.symm

end TailOptionPricing
