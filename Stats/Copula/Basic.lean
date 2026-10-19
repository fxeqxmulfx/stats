module

/-
  Bivariate copula scaffolding.

  ## Stats.Copula.Basic

  Defines the `IsCopula` predicate (continuity, marginals, range, and
  the 2-increasing rectangle property) for a bivariate function
  `C : ℝ → ℝ → ℝ` interpreted as a copula on `[0,1]²`.

  Proves the **Fréchet–Hoeffding bounds**:
    `max (u + v - 1) 0  ≤  C u v  ≤  min u v`
  for `(u, v) ∈ [0,1]²`.

  Used as the foundation for the upper-tail-dependence coefficient
  `λ_U` (C2) and the Gaussian copula impossibility theorem (C4).
-/
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Order.MinMax
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Tactic
public import Stats.BlackScholes.StdNormal

@[expose] public section

open Set
open scoped Topology

namespace TailOptionPricing

/-- A bivariate function `C : ℝ → ℝ → ℝ` is a **copula** on `[0,1]²` iff
it is jointly continuous on the unit square, takes values in `[0,1]`,
has uniform marginals (`C u 0 = C 0 v = 0`, `C u 1 = u`, `C 1 v = v`),
and is 2-increasing (the rectangle measure is non-negative).

Note: we do NOT require `(u₁, u₂, v₁, v₂) ∈ [0,1]` in `two_increasing` —
the rectangle condition is asserted unconditionally for all reals
satisfying `u₁ ≤ u₂, v₁ ≤ v₂`.  This is harmless because the marginal
conditions only meaningfully constrain `C` on `[0,1]²`; on the
boundary the values are pinned, and outside the unit square the
predicate makes no claim about `C` other than 2-increasing-ness. -/
structure IsCopula (C : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × ℝ => C p.1 p.2)
            (Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  range : ∀ ⦃u v⦄, u ∈ Set.Icc (0:ℝ) 1 → v ∈ Set.Icc (0:ℝ) 1 →
              C u v ∈ Set.Icc (0:ℝ) 1
  marg_zero_left  : ∀ ⦃u⦄, u ∈ Set.Icc (0:ℝ) 1 → C u 0 = 0
  marg_zero_right : ∀ ⦃v⦄, v ∈ Set.Icc (0:ℝ) 1 → C 0 v = 0
  marg_one_left   : ∀ ⦃u⦄, u ∈ Set.Icc (0:ℝ) 1 → C u 1 = u
  marg_one_right  : ∀ ⦃v⦄, v ∈ Set.Icc (0:ℝ) 1 → C 1 v = v
  two_increasing  : ∀ ⦃u₁ u₂ v₁ v₂⦄, u₁ ≤ u₂ → v₁ ≤ v₂ →
                       C u₂ v₂ - C u₁ v₂ - C u₂ v₁ + C u₁ v₁ ≥ 0

namespace IsCopula

variable {C : ℝ → ℝ → ℝ}

/-- **Fréchet–Hoeffding upper bound:** `C u v ≤ min u v`
on the unit square. -/
theorem le_min (hC : IsCopula C) {u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    C u v ≤ min u v := by
  -- Two rectangles:
  -- (a) (u₁=u, u₂=1, v₁=0, v₂=v):   C(1,v) - C(u,v) - C(1,0) + C(u,0) ≥ 0
  --     ⇒ v - C(u,v) - 0 + 0 ≥ 0  ⇒  C(u,v) ≤ v
  -- (b) (u₁=0, u₂=u, v₁=v, v₂=1):   C(u,1) - C(0,1) - C(u,v) + C(0,v) ≥ 0
  --     ⇒ u - 0 - C(u,v) + 0 ≥ 0  ⇒  C(u,v) ≤ u
  have hu0 : (0:ℝ) ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hv0 : (0:ℝ) ≤ v := hv.1
  have hv1 : v ≤ 1 := hv.2
  have h_zero_mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have h_one_mem  : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, le_refl 1⟩
  have hCu0 := hC.marg_zero_left hu
  have hCv0 := hC.marg_zero_right hv
  have hCu1 := hC.marg_one_left hu
  have hC1v := hC.marg_one_right hv
  have h_le_v : C u v ≤ v := by
    have h := hC.two_increasing (u₁ := u) (u₂ := 1) (v₁ := 0) (v₂ := v) hu1 hv0
    -- C(1,v) - C(u,v) - C(1,0) + C(u,0) ≥ 0
    rw [hC1v, hCu0, hC.marg_zero_left h_one_mem] at h
    -- h : v - C u v - 0 + 0 ≥ 0  i.e.  C u v ≤ v
    linarith
  have h_le_u : C u v ≤ u := by
    have h := hC.two_increasing (u₁ := 0) (u₂ := u) (v₁ := v) (v₂ := 1) hu0 hv1
    -- C(u,1) - C(0,1) - C(u,v) + C(0,v) ≥ 0
    rw [hCu1, hC.marg_zero_right h_one_mem, hCv0] at h
    linarith
  exact _root_.le_min h_le_u h_le_v

/-- **Fréchet–Hoeffding lower bound:** `max (u + v - 1) 0 ≤ C u v`
on the unit square. -/
theorem max_le (hC : IsCopula C) {u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    max (u + v - 1) 0 ≤ C u v := by
  -- (c) (u₁=u, u₂=1, v₁=v, v₂=1):   C(1,1) - C(u,1) - C(1,v) + C(u,v) ≥ 0
  --     ⇒ 1 - u - v + C(u,v) ≥ 0  ⇒  C(u,v) ≥ u + v - 1
  -- Combined with range (C(u,v) ≥ 0):  C(u,v) ≥ max(u + v - 1, 0)
  have hu0 : (0:ℝ) ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hv0 : (0:ℝ) ≤ v := hv.1
  have hv1 : v ≤ 1 := hv.2
  have h_one_mem  : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, le_refl 1⟩
  have hCu1 := hC.marg_one_left hu
  have hC1v := hC.marg_one_right hv
  have hC11 := hC.marg_one_left h_one_mem
  -- hC11 : C 1 1 = 1
  have h_lb1 : u + v - 1 ≤ C u v := by
    have h := hC.two_increasing (u₁ := u) (u₂ := 1) (v₁ := v) (v₂ := 1) hu1 hv1
    rw [hC11, hCu1, hC1v] at h
    linarith
  have h_lb2 : (0:ℝ) ≤ C u v := (hC.range hu hv).1
  exact _root_.max_le h_lb1 h_lb2

/-- `C u v ≤ 1` on the unit square (immediate from `range`). -/
theorem le_one (hC : IsCopula C) {u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    C u v ≤ 1 :=
  (hC.range hu hv).2

/-- `0 ≤ C u v` on the unit square (immediate from `range`). -/
theorem nonneg (hC : IsCopula C) {u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ C u v :=
  (hC.range hu hv).1

end IsCopula

/-- **Upper tail dependence coefficient.**
`λ_U := lim_{u → 1⁻} (1 − 2u + C(u, u)) / (1 − u)`.
Interpretation: under the bivariate distribution with copula `C`
and uniform marginals, `λ_U = lim ℙ(V > u | U > u)`.

We use `Filter.limUnder` so the definition is total: if the limit
does not exist (the function is not convergent on `𝓝[<] 1`),
`limUnder` returns a `Classical.choice`-style fallback.  The
**meaningful** statement is always paired with a `Tendsto` hypothesis
witnessing convergence — see `upperTailDependence_mem_Icc`. -/
noncomputable def upperTailDependence (C : ℝ → ℝ → ℝ) : ℝ :=
  Filter.limUnder (𝓝[<] (1:ℝ)) (fun u : ℝ => (1 - 2 * u + C u u) / (1 - u))

/-- The upper tail dependence coefficient lies in `[0,1]` whenever the
defining limit exists.  Both bounds come from Fréchet–Hoeffding:

* upper:  `C u u ≤ min u u = u`  ⇒  `(1 − 2u + C(u,u))/(1−u) ≤ 1`.
* lower:  `C u u ≥ max(2u − 1, 0)`; on `u ∈ [1/2, 1)` this gives
          `1 − 2u + C(u,u) ≥ 0`, so the ratio is ≥ 0 (since `1 − u > 0`).

Both bounds pass through the limit. -/
theorem upperTailDependence_mem_Icc {C : ℝ → ℝ → ℝ} (hC : IsCopula C)
    (h_lim : Filter.Tendsto (fun u : ℝ => (1 - 2 * u + C u u) / (1 - u))
        (𝓝[<] (1:ℝ)) (𝓝 (upperTailDependence C))) :
    upperTailDependence C ∈ Set.Icc (0:ℝ) 1 := by
  have h_upper : upperTailDependence C ≤ 1 := by
    apply le_of_tendsto h_lim
    filter_upwards [Ico_mem_nhdsLT (by norm_num : (1/2 : ℝ) < 1)] with u hu_in
    obtain ⟨hu_ge, hu_lt⟩ := hu_in
    have hu_pos : (0:ℝ) ≤ u := by linarith
    have hu_in_Icc : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu_pos, hu_lt.le⟩
    have h_FH : C u u ≤ min u u := hC.le_min hu_in_Icc hu_in_Icc
    have h_FH' : C u u ≤ u := by simpa [min_self] using h_FH
    have h_denom_pos : 0 < 1 - u := by linarith
    have h_num_le : 1 - 2 * u + C u u ≤ 1 - u := by linarith
    rw [div_le_one h_denom_pos]
    exact h_num_le
  have h_lower : 0 ≤ upperTailDependence C := by
    apply ge_of_tendsto h_lim
    filter_upwards [Ico_mem_nhdsLT (by norm_num : (1/2 : ℝ) < 1)] with u hu_in
    obtain ⟨hu_ge, hu_lt⟩ := hu_in
    have hu_pos : (0:ℝ) ≤ u := by linarith
    have hu_in_Icc : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu_pos, hu_lt.le⟩
    have h_FH : max (u + u - 1) 0 ≤ C u u := hC.max_le hu_in_Icc hu_in_Icc
    have h_2u_ge : 2 * u - 1 ≤ C u u := by
      have h1 : u + u - 1 ≤ max (u + u - 1) 0 := le_max_left _ _
      linarith
    have h_num_nonneg : 0 ≤ 1 - 2 * u + C u u := by linarith
    have h_denom_pos : 0 < 1 - u := by linarith
    exact div_nonneg h_num_nonneg h_denom_pos.le
  exact ⟨h_lower, h_upper⟩

/-- **Bivariate Gaussian copula with correlation `ρ`.**

Defined via the linear-combination decomposition `Y = ρX + √(1-ρ²)Z`
with `X, Z` independent standard normal: for `(u, v) ∈ (0,1)²`,

  `gaussianCopula ρ u v = ∫_{-∞}^{Φ⁻¹(u)} Φ((Φ⁻¹(v) − ρx) / √(1−ρ²)) ϕ(x) dx`

where `ϕ` is the standard normal density.  This is `ℙ(U ≤ u, V ≤ v)`
when `(U, V) = (Φ(X), Φ(Y))` and `(X, Y)` is standard bivariate
normal with correlation `ρ`.

Boundary cases (`u ∈ {0, 1}` or `v ∈ {0, 1}` or outside the unit
square) are handled explicitly so the function satisfies the copula
marginal conditions definitionally.

Well-defined for `|ρ| < 1`.  For `|ρ| ≥ 1` the integrand involves
division by zero; the value is junk but the function type-checks.

NB: continuity on `[0,1]²` and the 2-increasing property are
non-trivial and left to a later stage (C3.e). -/
noncomputable def gaussianCopula (ρ u v : ℝ) : ℝ :=
  if u ≤ 0 ∨ v ≤ 0 then 0
  else if 1 ≤ u ∧ 1 ≤ v then 1
  else if 1 ≤ u then v
  else if 1 ≤ v then u
  else
    ∫ x in Set.Iic (stdNormalQuantile u),
      stdNormalCdf ((stdNormalQuantile v - ρ * x) / Real.sqrt (1 - ρ^2))
        * ProbabilityTheory.gaussianPDFReal 0 1 x ∂MeasureTheory.volume

theorem gaussianCopula_zero_left (ρ v : ℝ) :
    gaussianCopula ρ 0 v = 0 := by
  unfold gaussianCopula
  have h1 : ((0:ℝ) ≤ 0 ∨ v ≤ 0) := Or.inl (le_refl 0)
  rw [ite_eq_left h1]

theorem gaussianCopula_zero_right (ρ u : ℝ) :
    gaussianCopula ρ u 0 = 0 := by
  unfold gaussianCopula
  have h1 : (u ≤ 0 ∨ (0:ℝ) ≤ 0) := Or.inr (le_refl 0)
  rw [ite_eq_left h1]

theorem gaussianCopula_one_left (ρ v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    gaussianCopula ρ 1 v = v := by
  unfold gaussianCopula
  rcases eq_or_lt_of_le hv.1 with hv_zero | hv_pos
  · -- v = 0
    have hv_eq : v = 0 := hv_zero.symm
    subst hv_eq
    have h1 : ((1:ℝ) ≤ 0 ∨ (0:ℝ) ≤ 0) := Or.inr (le_refl 0)
    rw [ite_eq_left h1]
  · -- v > 0
    rcases eq_or_lt_of_le hv.2 with hv_one | hv_lt
    · -- v = 1
      have hv_eq : v = 1 := hv_one
      subst hv_eq
      have h1 : ¬ ((1:ℝ) ≤ 0 ∨ (1:ℝ) ≤ 0) := by
        intro h; rcases h with h | h <;> linarith
      have h2 : ((1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1) := ⟨le_refl 1, le_refl 1⟩
      rw [ite_eq_right h1, ite_eq_left h2]
    · -- 0 < v < 1
      have h1 : ¬ ((1:ℝ) ≤ 0 ∨ v ≤ 0) := by
        intro h; rcases h with h | h
        · linarith
        · linarith
      have h2 : ¬ ((1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ v) := by
        intro h; linarith [h.2]
      have h3 : (1:ℝ) ≤ 1 := le_refl 1
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]

theorem gaussianCopula_one_right (ρ u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    gaussianCopula ρ u 1 = u := by
  unfold gaussianCopula
  rcases eq_or_lt_of_le hu.1 with hu_zero | hu_pos
  · -- u = 0
    have hu_eq : u = 0 := hu_zero.symm
    subst hu_eq
    have h1 : ((0:ℝ) ≤ 0 ∨ (1:ℝ) ≤ 0) := Or.inl (le_refl 0)
    rw [ite_eq_left h1]
  · -- u > 0
    rcases eq_or_lt_of_le hu.2 with hu_one | hu_lt
    · -- u = 1
      have hu_eq : u = 1 := hu_one
      subst hu_eq
      have h1 : ¬ ((1:ℝ) ≤ 0 ∨ (1:ℝ) ≤ 0) := by
        intro h; rcases h with h | h <;> linarith
      have h2 : ((1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1) := ⟨le_refl 1, le_refl 1⟩
      rw [ite_eq_right h1, ite_eq_left h2]
    · -- 0 < u < 1
      have h1 : ¬ (u ≤ 0 ∨ (1:ℝ) ≤ 0) := by
        intro h; rcases h with h | h
        · linarith
        · linarith
      have h2 : ¬ ((1:ℝ) ≤ u ∧ (1:ℝ) ≤ 1) := by
        intro h; linarith [h.1]
      have h3 : ¬ ((1:ℝ) ≤ u) := not_le.mpr hu_lt
      have h4 : (1:ℝ) ≤ 1 := le_refl 1
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]

/-- **Conditional upper-tail integrand for the Gaussian copula.**
The integrand of the Gaussian-copula bivariate tail:
`(1 − Φ((q−ρx)/√(1−ρ²))) · ϕ(x)`.  Used to factor
`gaussianCopula ρ u u` into a mass term and a "missing-tail" integral. -/
noncomputable def gaussianCopulaTailIntegrand (ρ q x : ℝ) : ℝ :=
  (1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2)))
    * ProbabilityTheory.gaussianPDFReal 0 1 x

/-- **Conditional bivariate-tail mass, lower tail.**
`h(q) := ∫_{-∞}^q (1 − Φ((q−ρx)/√(1−ρ²))) ϕ(x) dx`.

By construction `h(q) ≥ 0` and `h(q) ≤ 1 − Φ(q)` (the marginal tail
of one component dominates the joint event `{X ≤ q, Y > q}` that it
represents).  Used to rewrite `gaussianCopula ρ u u`. -/
noncomputable def gaussianCopulaLowerTailMass (ρ q : ℝ) : ℝ :=
  ∫ x in Set.Iic q, gaussianCopulaTailIntegrand ρ q x ∂MeasureTheory.volume

/-- **Algebraic identity for `gaussianCopula ρ u u`.**

For `u ∈ Set.Ioo 0 1` and `ρ ∈ (−1, 1)`, with `q := stdNormalQuantile u`,

  `gaussianCopula ρ u u = u − gaussianCopulaLowerTailMass ρ q`.

Proof: the integrand of `gaussianCopula` is `Φ(·) ϕ(x)`; substitute
`Φ(·) = 1 − (1 − Φ(·))` and split the integral.  The constant-1 piece
gives `u`; the rest is `gaussianCopulaLowerTailMass ρ q`. -/
theorem gaussianCopula_eq_u_sub_lowerTailMass
    {ρ u : ℝ} (hρ_lb : -1 < ρ) (hρ_ub : ρ < 1)
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    gaussianCopula ρ u u = u - gaussianCopulaLowerTailMass ρ (stdNormalQuantile u) := by
  -- Unused but accepted hypotheses (the well-definedness of the inner
  -- branch only requires `u ∈ Ioo 0 1`; the `|ρ| < 1` hypotheses are
  -- placeholders for downstream consumers).
  have _hρ_lb := hρ_lb
  have _hρ_ub := hρ_ub
  unfold gaussianCopula
  have hu_pos : 0 < u := hu.1
  have hu_lt : u < 1 := hu.2
  have h_branch1 : ¬ (u ≤ 0 ∨ u ≤ 0) := by
    intro h; rcases h with h | h <;> linarith
  rw [ite_eq_right h_branch1]
  have h_branch2 : ¬ (1 ≤ u ∧ 1 ≤ u) := by intro h; linarith [h.1]
  rw [ite_eq_right h_branch2]
  have h_branch3 : ¬ (1 ≤ u) := not_le.mpr hu_lt
  rw [ite_eq_right h_branch3, ite_eq_right h_branch3]
  set q : ℝ := stdNormalQuantile u with hq_def
  unfold gaussianCopulaLowerTailMass gaussianCopulaTailIntegrand
  -- Pointwise: Φ(·) * ϕ(x) = ϕ(x) - (1 - Φ(·)) * ϕ(x)
  have h_pointwise : ∀ x : ℝ,
      stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2)) *
        ProbabilityTheory.gaussianPDFReal 0 1 x
      = ProbabilityTheory.gaussianPDFReal 0 1 x
        - (1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2))) *
          ProbabilityTheory.gaussianPDFReal 0 1 x := by
    intro x; ring
  -- Integrability of φ on Iic q.
  have h_int_pdf : MeasureTheory.IntegrableOn
      (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x)
      (Set.Iic q) MeasureTheory.volume :=
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
  -- Boundedness of the (1 - Φ(·)) factor.
  have h_bound : ∀ x : ℝ,
      ‖1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2))‖ ≤ 1 := by
    intro x
    have h_nonneg : 0 ≤ 1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2)) := by
      linarith [stdNormalCdf_le_one ((q - ρ * x) / Real.sqrt (1 - ρ^2))]
    have h_le_one : 1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2)) ≤ 1 := by
      linarith [stdNormalCdf_nonneg ((q - ρ * x) / Real.sqrt (1 - ρ^2))]
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    exact h_le_one
  -- Continuity / measurability of (1 - Φ(·)).
  have h_cdf_cont : Continuous stdNormalCdf :=
    continuous_iff_continuousAt.mpr
      fun x => (stdNormalCdf_hasDerivAt x).continuousAt
  have h_inner_cont : Continuous
      (fun x : ℝ => (q - ρ * x) / Real.sqrt (1 - ρ^2)) := by continuity
  have h_factor_cont : Continuous
      (fun x : ℝ => 1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2))) :=
    continuous_const.sub (h_cdf_cont.comp h_inner_cont)
  -- Integrability of (1 - Φ(·)) * φ on Iic q (bounded × integrable).
  have h_int_complement : MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        (1 - stdNormalCdf ((q - ρ * x) / Real.sqrt (1 - ρ^2))) *
          ProbabilityTheory.gaussianPDFReal 0 1 x)
      (Set.Iic q) MeasureTheory.volume :=
    MeasureTheory.Integrable.bdd_mul h_int_pdf
      h_factor_cont.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall h_bound)
  -- Rewrite the integral using pointwise identity.
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    (fun x _ => h_pointwise x)]
  -- Split via integral_sub.
  rw [MeasureTheory.integral_sub h_int_pdf h_int_complement]
  -- ∫_{Iic q} φ = stdNormalCdf q = u.
  rw [← stdNormalCdf_eq_setIntegral_Iic]
  have h_cdf_q : stdNormalCdf q = u := by
    rw [hq_def]; exact stdNormalCdf_stdNormalQuantile_of_mem_Ioo hu
  rw [h_cdf_q]

/-- **Reduction of the upper-tail-dependence ratio to the lower-tail
mass.**  For `u ∈ Set.Ioo 0 1` and `ρ ∈ (−1, 1)`:

  `(1 − 2u + gaussianCopula ρ u u) / (1 − u)
    = 1 − gaussianCopulaLowerTailMass ρ (stdNormalQuantile u) / (1 − u)`.

This is pure algebra on top of `gaussianCopula_eq_u_sub_lowerTailMass`.
The statement is the bridge that turns the C4 theorem
(`upperTailDependence (gaussianCopula ρ) = 0`) into showing that
`gaussianCopulaLowerTailMass ρ q / (1 − Φ q)` tends to 1 — which is
the Gaussian-marginal recovery identity that the next stage proves. -/
theorem gaussianCopula_upperTailDependence_ratio_eq
    {ρ u : ℝ} (hρ_lb : -1 < ρ) (hρ_ub : ρ < 1)
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    (1 - 2 * u + gaussianCopula ρ u u) / (1 - u)
      = 1 - gaussianCopulaLowerTailMass ρ (stdNormalQuantile u) / (1 - u) := by
  rw [gaussianCopula_eq_u_sub_lowerTailMass hρ_lb hρ_ub hu]
  have h_one_minus_u_pos : 0 < 1 - u := by linarith [hu.2]
  field_simp
  ring


end TailOptionPricing
