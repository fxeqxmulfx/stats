module

/-
  Continuous-CDF sublevel sets and the actual probability integral transform.
  Source: arXiv:1907.11162v3, Appendix B, Probability integral transform.
  Flat regions are allowed; no everywhere strictly increasing inverse is assumed.
-/
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Monotone

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- A nonempty sublevel below one of a continuous actual CDF has a
finite upper endpoint with exactly the specified CDF value. This supplies
the generalized-inverse step of arXiv:1907.11162v3, Appendix B. -/
theorem exists_cdf_sublevel_boundary (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) {q : ℝ} (hq : q < 1)
    (hne : {x : ℝ | cdf ν x ≤ q}.Nonempty) :
    ∃ t : ℝ, cdf ν t = q ∧ {x : ℝ | cdf ν x ≤ q} = Iic t := by
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually_const_lt hq).exists
  let S := {x : ℝ | cdf ν x ≤ q}
  have hB : BddAbove S := by
    refine ⟨b, ?_⟩
    intro x hx
    by_contra he
    have hbx : b ≤ x := (lt_of_not_ge he).le
    exact hb.not_ge ((monotone_cdf ν hbx).trans hx)
  have hC : IsClosed S := isClosed_Iic.preimage hc
  have ht : sSup S ∈ S := hC.csSup_mem hne hB
  have he : S = Iic (sSup S) := by
    ext x
    constructor
    · intro hx
      exact le_csSup hB hx
    · intro hx
      exact (monotone_cdf ν hx).trans ht
  obtain ⟨a, ha⟩ := hne
  have hab : a ≤ b := by
    by_contra he
    exact hb.not_ge ((monotone_cdf ν (lt_of_not_ge he).le).trans ha)
  obtain ⟨z, hz, hez⟩ := intermediate_value_Icc hab hc.continuousOn ⟨ha, hb.le⟩
  have hzS : z ∈ S := hez.le
  have hzt : z ≤ sSup S := le_csSup hB hzS
  refine ⟨sSup S, le_antisymm ht ?_, he⟩
  rw [← hez]
  exact monotone_cdf ν hzt


/-- The actual transformed probability equals its unit-interval
threshold, including zero (arXiv:1907.11162v3, Appendix B, probability integral transform). -/
theorem cdfTransform_probability_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ν.real {x : ℝ | cdf ν x ≤ q} = q := by
  by_cases hne : {x : ℝ | cdf ν x ≤ q}.Nonempty
  · obtain ⟨t, ht, hS⟩ := exists_cdf_sublevel_boundary ν hc hq1 hne
    rw [hS, ← cdf_eq_real ν t, ht]
  · have hq : q = 0 := by
      by_contra hq
      have hpos := lt_of_le_of_ne hq0 (Ne.symm hq)
      obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually_lt_const hpos).exists
      exact hne ⟨a, ha.le⟩
    have he : {x : ℝ | cdf ν x ≤ q} = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he, measureReal_empty, hq]

end TailOptionPricing
