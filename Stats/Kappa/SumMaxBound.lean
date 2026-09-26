/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.SumMaxBound — Trivial bound `P(S_n > t) ≥ P(max X_i > t)` for nonneg iid.

  Used by `Stats.Kappa.Lognormal.Loulakis` (todo5.md Phase C.2):

      `ℙ(∃ i, X_i > t) ≤ ℙ(Σ_i X_i > t)`

  when each `X_i ≥ 0` pointwise.  Pointwise: if `∃ i, X_i ω > t`, then
  the sum `Σ_i X_i ω ≥ X_i ω > t` because all other terms are
  non-negative.

  Combined with `Stats.Kappa.MaxIIdBound.prob_max_iid_ge` this gives
  the operational chain

      `ℙ(S_n > t) ≥ ℙ(max X_i > t) ≥ n·ℙ(X_0 > t) − C(n,2)·ℙ(X_0 > t)²`

  used in the Loulakis subexponential argument.
-/
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory Set
open scoped NNReal

namespace TailOptionPricing.SumMaxBound

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Pointwise inclusion `{max > t} ⊆ {sum > t}` for nonneg X. -/

/-- **Pointwise**: for nonneg `X : Fin n → Ω → ℝ` and any `ω`,
    `∃ i, X i ω > t  →  ∑ i, X i ω > t`. -/
private lemma sum_gt_of_exists_gt {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_nonneg : ∀ i ω, 0 ≤ X i ω) (t : ℝ) (ω : Ω) :
    (∃ i, X i ω > t) → ∑ i, X i ω > t := by
  rintro ⟨i, hi⟩
  -- Sum splits: X i + (sum over the rest, ≥ 0).
  have h_split : ∑ j, X j ω
      = X i ω + ∑ j ∈ Finset.univ.erase i, X j ω := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
  rw [h_split]
  have h_rest : 0 ≤ ∑ j ∈ Finset.univ.erase i, X j ω :=
    Finset.sum_nonneg (fun j _ => h_nonneg j ω)
  linarith

/-! ### Set inclusion + measure monotonicity. -/

/-- **Set inclusion `{max > t} ⊆ {sum > t}`** for nonneg `X`. -/
theorem setOf_exists_gt_subset_setOf_sum_gt {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_nonneg : ∀ i ω, 0 ≤ X i ω) (t : ℝ) :
    {ω | ∃ i, X i ω > t} ⊆ {ω | ∑ i, X i ω > t} :=
  fun ω hω => sum_gt_of_exists_gt h_nonneg t ω hω

/-- **Probability inequality `P(∃ i, X_i > t) ≤ P(Σ X_i > t)`** for
    pointwise non-negative `X`.

    Combined with `prob_max_iid_ge` (Stats.Kappa.MaxIIdBound):

        `ℙ(Σ X_i > t) ≥ ℙ(max X_i > t)
                     ≥ n · ℙ(X_0 > t) − C(n, 2) · ℙ(X_0 > t)²`. -/
theorem prob_sum_ge_prob_max [IsFiniteMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_nonneg : ∀ i ω, 0 ≤ X i ω) (t : ℝ) :
    μ.real {ω | ∃ i, X i ω > t} ≤ μ.real {ω | ∑ i, X i ω > t} :=
  measureReal_mono (setOf_exists_gt_subset_setOf_sum_gt h_nonneg t)
    (measure_ne_top μ _)

end TailOptionPricing.SumMaxBound
