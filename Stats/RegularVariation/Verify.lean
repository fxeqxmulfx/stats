/-
  Sanity check for `Stats.RegularVariation`: axioms for every proved
  theorem in the module.  Each line below should display only the three
  core axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

  Both the **monotone** branch (Karamata 1933) and the **measurable** branch
  (Korevaar UCT via Csiszár–Erdős) are formalised in this module.  The
  un-hypothesised `comp_translation` is *not* a theorem (pathological
  non-measurable SV functions exist for which `L(t+1)/L(t)` does not tend
  to 1).
-/
import Stats.RegularVariation

-- Definitions and the trivial RV_0 equivalence.
#print axioms TailOptionPricing.IsSlowlyVarying
#print axioms TailOptionPricing.isSlowlyVarying_iff_isRegularlyVarying_zero

-- Examples.
#print axioms TailOptionPricing.isSlowlyVarying_const
#print axioms TailOptionPricing.isSlowlyVarying_log
#print axioms TailOptionPricing.isSlowlyVarying_log_rpow

-- Closure.
#print axioms TailOptionPricing.IsSlowlyVarying.congr_eventuallyEq
#print axioms TailOptionPricing.IsSlowlyVarying.mul
#print axioms TailOptionPricing.IsSlowlyVarying.inv
#print axioms TailOptionPricing.IsSlowlyVarying.div
#print axioms TailOptionPricing.IsSlowlyVarying.rpow
#print axioms TailOptionPricing.IsSlowlyVarying.comp_translation_of_monotone

-- Bridges between SV and RV.
#print axioms TailOptionPricing.isRegularlyVarying_rpow_mul
#print axioms TailOptionPricing.IsRegularlyVarying.div_rpow_isSlowlyVarying

-- Closure of `IsRegularlyVarying`.
#print axioms TailOptionPricing.isRegularlyVarying_rpow
#print axioms TailOptionPricing.IsRegularlyVarying.mul
#print axioms TailOptionPricing.IsRegularlyVarying.div
#print axioms TailOptionPricing.IsRegularlyVarying.rpow

-- UCT (monotone variant) and Potter's bounds (monotone variant).
#print axioms TailOptionPricing.IsSlowlyVarying.uniform_convergence_of_monotone
#print axioms TailOptionPricing.IsSlowlyVarying.potter_bounds_of_monotone

-- UCT (measurable variant — Korevaar / Csiszár–Erdős) and Potter's bounds.
#print axioms TailOptionPricing.IsSlowlyVarying.uniform_convergence
#print axioms TailOptionPricing.IsSlowlyVarying.potter_bounds

-- Karamata bound (monotone variant) and downstream.
#print axioms TailOptionPricing.IsSlowlyVarying.log_isLittleO_log_of_monotone
#print axioms TailOptionPricing.IsSlowlyVarying.subexp_along_exp_grid_of_monotone

-- Karamata bound (measurable variant — via Korevaar UCT) and downstream.
#print axioms TailOptionPricing.IsSlowlyVarying.log_isLittleO_log
#print axioms TailOptionPricing.IsSlowlyVarying.subexp_along_exp_grid

-- Application: Theorem 1, full monotone slowly-varying form.
#print axioms TailOptionPricing.survivalLogReturn_not_regularlyVarying_full_of_monotone

-- Application: Theorem 1, full measurable slowly-varying form.
#print axioms TailOptionPricing.survivalLogReturn_not_regularlyVarying_full

-- Karamata representation theorem (both directions).
#print axioms TailOptionPricing.IsKaramataRepresentation.isSlowlyVarying
#print axioms TailOptionPricing.IsSlowlyVarying.karamata_representation

-- Karamata's Abelian theorem (bounded-`L` form) and the asymptotic
-- version of Result 1 / Eq. (3) for slowly-varying tails.
#print axioms TailOptionPricing.callPriceSV_asymptotic_of_bounded
#print axioms TailOptionPricing.callPriceSV_ratio_asymptotic_of_bounded
#print axioms TailOptionPricing.callPrice_eq_callPriceSV_const

-- Global Potter bound (upper) and the full-SV Karamata Abelian theorem.
#print axioms TailOptionPricing.IsSlowlyVarying.global_potter_upper
#print axioms TailOptionPricing.callPriceSV_asymptotic
#print axioms TailOptionPricing.callPriceSV_ratio_asymptotic
