module

/-
  Nondegenerate probability-space witnesses for the revised iid maximum
  and Loulakis interfaces (arXiv:1802.05495v3, Appendix B). Their remaining
  distributional and integrability premises come from actual Gaussian
  product laws, rather than assuming the desired bounds or moments.
-/
public import Stats.Kappa.LoulakisLognormal
public import Stats.Kappa.MaxIIdBound

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace StatsReview

open TailOptionPricing

example : (LognormalIIdSetup.μn 2).real
    {ω | ∀ i : Fin 2, LognormalIIdSetup.Xσ 1 i ω ≤ 2} =
    ((gaussianReal 0 1).real {ω | LognormalAsymptotic.Y 1 ω ≤ 2}) ^ 2 :=
  MaxIIdBound.prob_all_le_iid (ν := gaussianReal 0 1)
    (Y := LognormalAsymptotic.Y 1) (X := LognormalIIdSetup.Xσ 1)
    (LognormalIIdSetup.iIndepFun_Xσ 1 2)
    (fun i => LognormalIIdSetup.identDistrib_Xσ 1 i) 2

example : 2 * (2 * LoulakisLognormal.An 2 1 - LoulakisLognormal.Bn 2 1) ≤
    LoulakisLognormal.Mn 2 1 := by
  have h := LoulakisLognormal.M_n_lower_lognormal 2 1
  norm_num at h
  exact h

#print axioms TailOptionPricing.MaxIIdBound.prob_all_le_iid
#print axioms TailOptionPricing.LoulakisAlgebraic.M_n_lower_bound

end StatsReview
