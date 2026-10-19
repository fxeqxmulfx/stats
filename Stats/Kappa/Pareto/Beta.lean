module

/-
  Proper finite Beta integrals for the correction of Taleb's Pareto row,
  arXiv:1802.05495v3, Table I, incomplete-Beta footnote. All integration
  endpoints are strictly inside (0,1); no divergent improper integral is
  subtracted from another divergent improper integral.
-/
public import Stats.Kappa.Pareto.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing

/-- Positivity on the open support of Taleb's Table I Beta kernel,
arXiv:1802.05495v3, including negative parameters. -/
theorem betaKernel_pos (a b : ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < betaKernel a b t :=
  mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos (by linarith) _)

/-- The Table I Beta kernel is continuous away from its two endpoints. -/
theorem betaKernel_continuousOn (a b : ℝ) :
    ContinuousOn (betaKernel a b) (Ioo 0 1) := by
  exact (continuousOn_id.rpow_const (fun _ ht => Or.inl ht.1.ne')).mul
    ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun x ht => Or.inl (by change (1 - x : ℝ) ≠ 0; linarith [ht.2])))

/-- Proper Beta integrals converge between any two interior points;
this is the correction used for arXiv:1802.05495v3, Table I. -/
theorem betaKernel_intervalIntegrable (a b : ℝ) {u v : ℝ}
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    IntervalIntegrable (betaKernel a b) volume u v := by
  apply ContinuousOn.intervalIntegrable
  apply (betaKernel_continuousOn a b).mono
  intro t ht
  exact ⟨(lt_min hu.1 hv.1).trans_le ht.1, ht.2.trans_lt (max_lt hu.2 hv.2)⟩

/-- The centered primitives' difference is a single convergent integral.
This replaces the divergent difference in the Table I Pareto footnote. -/
theorem incompleteBetaCentered_sub (a b : ℝ) {u v : ℝ}
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    incompleteBetaCentered u a b - incompleteBetaCentered v a b =
      ∫ t in v..u, betaKernel a b t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (betaKernel_intervalIntegrable a b (u := 1 / 2) (by norm_num) hv)
    (betaKernel_intervalIntegrable a b hv hu)
  unfold incompleteBetaCentered
  linarith

/-- The finite Beta primitive is strictly increasing on `(0,1)`. -/
theorem incompleteBetaCentered_strictMonoOn (a b : ℝ) :
    StrictMonoOn (fun z => incompleteBetaCentered z a b) (Ioo 0 1) := by
  intro u hu v hv huv
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on
    (betaKernel_intervalIntegrable a b hu hv)
    (fun t ht => betaKernel_pos a b (hu.1.trans ht.1) (ht.2.trans hv.2)) huv
  rw [← incompleteBetaCentered_sub a b hv hu] at hpos
  linarith

/-- Continuity of the finite Beta primitive on its open support. -/
theorem incompleteBetaCentered_continuousOn (a b : ℝ) :
    ContinuousOn (fun z => incompleteBetaCentered z a b) (Ioo 0 1) := by
  intro z hz
  have hcont := betaKernel_continuousOn a b
  exact (intervalIntegral.integral_hasDerivAt_right
    (betaKernel_intervalIntegrable a b (u := 1 / 2) (by norm_num) hz)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo z hz)
    (hcont.continuousAt (isOpen_Ioo.mem_nhds hz))).continuousAt.continuousWithinAt

example : 0 < betaKernel (-2) (-1) (1 / 2) := betaKernel_pos _ _ (by norm_num) (by norm_num)

example : IntervalIntegrable (betaKernel (-2) (-1)) volume (1 / 3) (2 / 3) :=
  betaKernel_intervalIntegrable _ _ (by norm_num) (by norm_num)

example : incompleteBetaCentered (1 / 3) (-2) (-1) -
    incompleteBetaCentered (2 / 3) (-2) (-1) =
    ∫ t in (2 / 3 : ℝ)..(1 / 3), betaKernel (-2) (-1) t :=
  incompleteBetaCentered_sub _ _ (by norm_num) (by norm_num)

end TailOptionPricing
