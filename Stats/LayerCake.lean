/-
  Layer-cake bridge: connects our `callPrice` (defined as `∫_K^∞ ℙ(S > s) ds`)
  to the expected payoff `E[(S − K)⁺]`.  Closes the gap between the
  layer-cake form (used in the rest of the development) and the standard
  expectation-form definition of European calls.
-/
import Stats.Pareto
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Group.MeasurableEquiv

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-- **Layer-cake bridge** (general).  For a measurable random variable `S` with
    integrable positive part `(S − K)⁺`, the expected payoff equals the
    integral of the survival function on `(K, ∞)`. -/
theorem expectation_max_eq_integral_survival
    {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    {S : Ω → ℝ} (K : ℝ)
    (h_int : Integrable (fun ω => max (S ω - K) 0) μ) :
    ∫ ω, max (S ω - K) 0 ∂μ = ∫ s in Ioi K, μ.real {ω | s < S ω} := by
  set f : Ω → ℝ := fun ω => max (S ω - K) 0 with hf
  have f_nn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall (fun _ => le_max_right _ _)
  have h_lc := h_int.integral_eq_integral_meas_lt f_nn
  rw [h_lc]
  have h_set : ∀ t ∈ Ioi (0:ℝ),
      μ.real {a : Ω | t < f a} = μ.real {a : Ω | K + t < S a} := by
    intro t ht
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, hf, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact (lt_irrefl _ (h.trans ht)).elim
    · intro h; left; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi h_set]
  -- Change of variables `s = K + t` via translation invariance.
  have h_pres : MeasurePreserving ((K : ℝ) + ·) volume volume :=
    measurePreserving_add_left volume K
  have h_emb : MeasurableEmbedding ((K : ℝ) + ·) := measurableEmbedding_addLeft K
  have h_preimage : ((K : ℝ) + ·) ⁻¹' Ioi K = Ioi (0 : ℝ) := by
    ext t; simp [Set.mem_Ioi]
  have h_eq := h_pres.setIntegral_preimage_emb h_emb
    (fun s => μ.real {a | s < S a}) (Ioi K)
  rw [h_preimage] at h_eq
  exact h_eq

/-- **Layer-cake specialised to the strong Pareto law.**  If `S` is a
    non-negative random variable whose survival function is `ℙ(S > s) = (l/s)^α`
    on the relevant tail and whose call payoff is integrable, then the
    expected payoff at strike `K ≥ l` equals our `callPrice`. -/
theorem callPrice_eq_expectation
    {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    {S : Ω → ℝ} {l α K : ℝ}
    (h_survival : ∀ s ∈ Ioi K, μ.real {ω | s < S ω} = (l / s) ^ α)
    (h_int : Integrable (fun ω => max (S ω - K) 0) μ) :
    ∫ ω, max (S ω - K) 0 ∂μ = callPrice l α K := by
  rw [expectation_max_eq_integral_survival μ K h_int]
  unfold callPrice survival
  exact setIntegral_congr_fun measurableSet_Ioi h_survival

end TailOptionPricing
