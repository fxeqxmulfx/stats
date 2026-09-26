/-
  Carr–Madan static replication.

  Foundation theorem:
    integral form of the second-order Taylor remainder, derived directly
    from FTC + integration by parts.

  Headline theorem (Carr–Madan, finite-strip form): any twice-differentiable
  payoff `g : [a, b] → ℝ` admits the static-replication identity
      g(S) = g(F) + g'(F)·(S − F)
           + ∫_a^F (K − S)⁺·g''(K) dK
           + ∫_F^b (S − K)⁺·g''(K) dK
  for any forward `F ∈ [a, b]` and spot `S ∈ [a, b]`.  The integrals
  represent the cost of an out-of-the-money put strip and call strip
  respectively, hedging the curvature of `g`.

  We work on a finite strip `[a, b]` to avoid integrability conditions.
  Improper-integral versions (integration over `(0, ∞)`) require additional
  decay hypotheses on `g''` and are not pursued here.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ### Integral form of the second-order Taylor remainder.

    For `g, g', g''` continuous on `[[a, b]]` (the unordered interval) with
    `HasDerivAt g (g' x) x` on the open interior and similarly for `g'`,
        g(b) = g(a) + g'(a)·(b − a) + ∫_a^b (b − t)·g''(t) dt.

    The formula is *direction-agnostic*: it holds for any `a, b ∈ ℝ`
    (signed integral on the right).  Proof: integration by parts on
    `∫(b − t)·g''(t) dt` with `u(t) = b − t`, `v(t) = g'(t)`, combined
    with FTC `∫_a^b g'(t) dt = g(b) − g(a)`. -/
theorem integral_taylor_remainder_two
    {g g' g'' : ℝ → ℝ} {a b : ℝ}
    (hg_cont   : ContinuousOn g (Set.uIcc a b))
    (hg'_cont  : ContinuousOn g' (Set.uIcc a b))
    (hg''_cont : ContinuousOn g'' (Set.uIcc a b))
    (hg_deriv  : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt g' (g'' x) x) :
    g b = g a + g' a * (b - a) + ∫ t in a..b, (b - t) * g'' t := by
  -- u(t) := b - t, u'(t) := -1.
  set u : ℝ → ℝ := fun t => b - t with hu_def
  set u' : ℝ → ℝ := fun _ => -1 with hu'_def
  have hu_cont : ContinuousOn u (Set.uIcc a b) := by
    show ContinuousOn (fun t : ℝ => b - t) _; fun_prop
  have hu_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt u (u' x) x := by
    intro x _
    show HasDerivAt (fun t : ℝ => b - t) (-1) x
    simpa using (hasDerivAt_const x b).sub (hasDerivAt_id x)
  have hu'_int : IntervalIntegrable u' volume a b := by
    apply ContinuousOn.intervalIntegrable
    show ContinuousOn (fun _ : ℝ => (-1 : ℝ)) _; fun_prop
  have hg''_int : IntervalIntegrable g'' volume a b :=
    hg''_cont.intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume a b :=
    hg'_cont.intervalIntegrable
  -- Integration by parts.
  have h_ibp := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu_cont hg'_cont hu_deriv hg'_deriv hu'_int hg''_int
  -- u(b) = 0, u(a) = b - a.
  have h_ub : u b = 0 := by show b - b = 0; ring
  have h_ua : u a = b - a := rfl
  -- ∫_a^b u'(t) · g'(t) dt = ∫_a^b (-1) · g'(t) dt = -(g b - g a) by FTC.
  have h_ftc : (∫ t in a..b, g' t) = g b - g a := by
    rcases le_total a b with hab | hba
    · exact integral_eq_sub_of_hasDerivAt_of_le hab
        (hg_cont.mono (by rw [Set.uIcc_of_le hab]))
        (fun x hx => hg_deriv x (by rw [min_eq_left hab, max_eq_right hab]; exact hx))
        hg'_int
    · have h_swap : (∫ t in a..b, g' t) = -(∫ t in b..a, g' t) :=
        intervalIntegral.integral_symm b a
      rw [h_swap]
      rw [integral_eq_sub_of_hasDerivAt_of_le hba
        (hg_cont.mono (by rw [Set.uIcc_of_ge hba]))
        (fun x hx => hg_deriv x (by rw [min_eq_right hba, max_eq_left hba]; exact hx))
        hg'_int.symm]
      ring
  have h_neg_int : (∫ t in a..b, u' t * g' t) = -(g b - g a) := by
    show (∫ t in a..b, (-1 : ℝ) * g' t) = -(g b - g a)
    rw [intervalIntegral.integral_const_mul, h_ftc]; ring
  rw [h_ub, h_ua, h_neg_int, zero_mul] at h_ibp
  -- h_ibp : ∫_a^b (b - t) · g''(t) dt = 0 - (b - a) · g'(a) - -(g b - g a)
  linarith [h_ibp]

/-! ### Carr–Madan static replication. -/

/-- **Carr–Madan, signed integral form.**  For any `S, F` with `g, g', g''`
    smooth on `[[F, S]]`,
        g(S) = g(F) + g'(F)·(S − F) + ∫_F^S (S − t)·g''(t) dt.
    Direct corollary of `integral_taylor_remainder_two` with base `F`. -/
theorem carrMadan_signed
    {g g' g'' : ℝ → ℝ} {F S : ℝ}
    (hg_cont   : ContinuousOn g (Set.uIcc F S))
    (hg'_cont  : ContinuousOn g' (Set.uIcc F S))
    (hg''_cont : ContinuousOn g'' (Set.uIcc F S))
    (hg_deriv  : ∀ x ∈ Set.Ioo (min F S) (max F S), HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x ∈ Set.Ioo (min F S) (max F S), HasDerivAt g' (g'' x) x) :
    g S = g F + g' F * (S - F) + ∫ t in F..S, (S - t) * g'' t :=
  integral_taylor_remainder_two hg_cont hg'_cont hg''_cont hg_deriv hg'_deriv

/-- **Helper: positive-part integral collapses to a directed integral.**
    For `S ∈ [F, b]`, the call-side integrand `(S − K)⁺ · h(K)` agrees
    pointwise with `(S − K) · h(K)` on `[F, S]` and vanishes on `[S, b]`,
    so the total integral on `[F, b]` equals the directed integral on
    `[F, S]`. -/
private theorem integral_max_call_eq {h : ℝ → ℝ} {F b S : ℝ}
    (hFS : F ≤ S) (hSb : S ≤ b) (hh : ContinuousOn h (Set.Icc F b)) :
    ∫ K in F..b, max (S - K) 0 * h K = ∫ K in F..S, (S - K) * h K := by
  have h_split : (∫ K in F..b, max (S - K) 0 * h K) =
      (∫ K in F..S, max (S - K) 0 * h K) +
      (∫ K in S..b, max (S - K) 0 * h K) := by
    have hh_int : IntervalIntegrable
        (fun K => max (S - K) 0 * h K) volume F b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (hFS.trans hSb)]
      exact ContinuousOn.mul (by fun_prop) hh
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hh_int.mono_set (by rw [Set.uIcc_of_le hFS, Set.uIcc_of_le (hFS.trans hSb)]; exact Set.Icc_subset_Icc_right hSb))
      (hh_int.mono_set (by rw [Set.uIcc_of_le hSb, Set.uIcc_of_le (hFS.trans hSb)]; exact Set.Icc_subset_Icc_left hFS))).symm
  rw [h_split]
  -- On [F, S]: max(S - K, 0) = S - K (since K ≤ S)
  have h_FS : (∫ K in F..S, max (S - K) 0 * h K) = ∫ K in F..S, (S - K) * h K := by
    apply intervalIntegral.integral_congr
    intro K hK
    rw [Set.uIcc_of_le hFS] at hK
    have hKS : 0 ≤ S - K := by linarith [hK.2]
    show max (S - K) 0 * h K = (S - K) * h K
    rw [max_eq_left hKS]
  -- On [S, b]: max(S - K, 0) = 0 (since K ≥ S)
  have h_Sb : (∫ K in S..b, max (S - K) 0 * h K) = 0 := by
    have h_zero : EqOn (fun K => max (S - K) 0 * h K) (fun _ => (0:ℝ))
        (Set.uIcc S b) := by
      intro K hK
      rw [Set.uIcc_of_le hSb] at hK
      have : S - K ≤ 0 := by linarith [hK.1]
      simp [max_eq_right this]
    rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]
  rw [h_FS, h_Sb, add_zero]

/-- **Helper (mirror): put-side positive-part integral.**  For
    `S ∈ [a, F]`, the put-side integrand `(K − S)⁺ · h(K)` agrees with
    `(K − S) · h(K)` on `[S, F]` and vanishes on `[a, S]`. -/
private theorem integral_max_put_eq {h : ℝ → ℝ} {a F S : ℝ}
    (haS : a ≤ S) (hSF : S ≤ F) (hh : ContinuousOn h (Set.Icc a F)) :
    ∫ K in a..F, max (K - S) 0 * h K = ∫ K in S..F, (K - S) * h K := by
  have h_split : (∫ K in a..F, max (K - S) 0 * h K) =
      (∫ K in a..S, max (K - S) 0 * h K) +
      (∫ K in S..F, max (K - S) 0 * h K) := by
    have hh_int : IntervalIntegrable
        (fun K => max (K - S) 0 * h K) volume a F := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (haS.trans hSF)]
      exact ContinuousOn.mul (by fun_prop) hh
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hh_int.mono_set (by rw [Set.uIcc_of_le haS, Set.uIcc_of_le (haS.trans hSF)]; exact Set.Icc_subset_Icc_right hSF))
      (hh_int.mono_set (by rw [Set.uIcc_of_le hSF, Set.uIcc_of_le (haS.trans hSF)]; exact Set.Icc_subset_Icc_left haS))).symm
  rw [h_split]
  have h_aS : (∫ K in a..S, max (K - S) 0 * h K) = 0 := by
    have h_zero : EqOn (fun K => max (K - S) 0 * h K) (fun _ => (0:ℝ))
        (Set.uIcc a S) := by
      intro K hK
      rw [Set.uIcc_of_le haS] at hK
      have : K - S ≤ 0 := by linarith [hK.2]
      simp [max_eq_right this]
    rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]
  have h_SF : (∫ K in S..F, max (K - S) 0 * h K) = ∫ K in S..F, (K - S) * h K := by
    apply intervalIntegral.integral_congr
    intro K hK
    rw [Set.uIcc_of_le hSF] at hK
    have hKS : 0 ≤ K - S := by linarith [hK.1]
    show max (K - S) 0 * h K = (K - S) * h K
    rw [max_eq_left hKS]
  rw [h_aS, h_SF, zero_add]

/-- **Helper: positive-part integral with `S < F` vanishes on the
    call side**, i.e. `∫_F^b (S − K)⁺ h(K) dK = 0` when `K ≥ F > S`. -/
private theorem integral_max_call_zero {h : ℝ → ℝ} {F b S : ℝ}
    (hSF : S ≤ F) (hFb : F ≤ b) :
    ∫ K in F..b, max (S - K) 0 * h K = 0 := by
  have h_zero : EqOn (fun K => max (S - K) 0 * h K) (fun _ => (0:ℝ))
      (Set.uIcc F b) := by
    intro K hK
    rw [Set.uIcc_of_le hFb] at hK
    have : S - K ≤ 0 := by linarith [hK.1]
    simp [max_eq_right this]
  rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]

/-- **Helper: positive-part integral with `S > F` vanishes on the
    put side**, i.e. `∫_a^F (K − S)⁺ h(K) dK = 0` when `K ≤ F < S`. -/
private theorem integral_max_put_zero {h : ℝ → ℝ} {a F S : ℝ}
    (haF : a ≤ F) (hFS : F ≤ S) :
    ∫ K in a..F, max (K - S) 0 * h K = 0 := by
  have h_zero : EqOn (fun K => max (K - S) 0 * h K) (fun _ => (0:ℝ))
      (Set.uIcc a F) := by
    intro K hK
    rw [Set.uIcc_of_le haF] at hK
    have : K - S ≤ 0 := by linarith [hK.2]
    simp [max_eq_right this]
  rw [intervalIntegral.integral_congr h_zero, intervalIntegral.integral_zero]

/-- **Carr–Madan static replication, finite-strip form.**  For `g` C² on
    a finite strip `[a, b]` and any `F ∈ [a, b]`, every spot
    `S ∈ [a, b]` satisfies the put–call decomposition
        g(S) = g(F) + g'(F)·(S − F)
             + ∫_a^F (K − S)⁺·g''(K) dK
             + ∫_F^b (S − K)⁺·g''(K) dK.
    Foundation for hedging arbitrary tail payoffs via vanilla options:
    the put strip pays `(K − S)⁺` weighted by `g''(K)`, the call strip
    pays `(S − K)⁺`. -/
theorem carrMadan
    {g g' g'' : ℝ → ℝ} {a b F S : ℝ}
    (hF : F ∈ Set.Icc a b) (hS : S ∈ Set.Icc a b)
    (hg_cont   : ContinuousOn g (Set.Icc a b))
    (hg'_cont  : ContinuousOn g' (Set.Icc a b))
    (hg''_cont : ContinuousOn g'' (Set.Icc a b))
    (hg_deriv  : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt g' (g'' x) x) :
    g S = g F + g' F * (S - F)
        + (∫ K in a..F, max (K - S) 0 * g'' K)
        + (∫ K in F..b, max (S - K) 0 * g'' K) := by
  obtain ⟨haF, hFb⟩ := hF
  obtain ⟨haS, hSb⟩ := hS
  -- Apply Taylor remainder on [[F, S]] (signed).
  have h_uIcc_sub : Set.uIcc F S ⊆ Set.Icc a b := by
    rw [Set.uIcc_eq_union]
    refine Set.union_subset ?_ ?_
    · exact Set.Icc_subset_Icc haF hSb
    · exact Set.Icc_subset_Icc haS hFb
  have h_Ioo_sub : Set.Ioo (min F S) (max F S) ⊆ Set.Ioo a b := by
    refine Set.Ioo_subset_Ioo ?_ ?_
    · exact le_min haF haS
    · exact max_le hFb hSb
  have h_taylor : g S = g F + g' F * (S - F) + ∫ t in F..S, (S - t) * g'' t :=
    carrMadan_signed
      (hg_cont.mono h_uIcc_sub)
      (hg'_cont.mono h_uIcc_sub)
      (hg''_cont.mono h_uIcc_sub)
      (fun x hx => hg_deriv x (h_Ioo_sub hx))
      (fun x hx => hg'_deriv x (h_Ioo_sub hx))
  -- Split into two cases: F ≤ S or S < F.
  rcases le_or_gt F S with hFS | hSF
  · -- Case F ≤ S: put-side integral is zero, call-side equals signed Taylor remainder.
    have h_put_zero :
        (∫ K in a..F, max (K - S) 0 * g'' K) = 0 :=
      integral_max_put_zero haF hFS
    have h_call_eq :
        (∫ K in F..b, max (S - K) 0 * g'' K) = ∫ K in F..S, (S - K) * g'' K :=
      integral_max_call_eq hFS hSb (hg''_cont.mono (Set.Icc_subset_Icc_left haF))
    rw [h_put_zero, h_call_eq, add_zero]
    exact h_taylor
  · -- Case S < F: call-side integral is zero, put-side equals signed Taylor remainder.
    have hSF' : S ≤ F := hSF.le
    have h_call_zero :
        (∫ K in F..b, max (S - K) 0 * g'' K) = 0 :=
      integral_max_call_zero hSF' hFb
    have h_put_eq :
        (∫ K in a..F, max (K - S) 0 * g'' K) = ∫ K in S..F, (K - S) * g'' K :=
      integral_max_put_eq haS hSF' (hg''_cont.mono (Set.Icc_subset_Icc_right hFb))
    rw [h_put_eq, h_call_zero, add_zero]
    -- h_taylor has ∫_F^S (S - t) g''(t) dt; we have ∫_S^F (K - S) g''(K) dK; show equal.
    have h_swap : (∫ t in F..S, (S - t) * g'' t) = ∫ K in S..F, (K - S) * g'' K := by
      rw [intervalIntegral.integral_symm S F, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t _ht
      show -((S - t) * g'' t) = (t - S) * g'' t
      ring
    rw [← h_swap]
    exact h_taylor

end TailOptionPricing
