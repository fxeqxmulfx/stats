module

/-
  Karamata's theory of regular variation — Uniform Convergence Theorem.

  ## Stats.RegularVariation.UCT.Measurable — measurable UCT (Korevaar et al.).

  Csiszár–Erdős proof using a Lebesgue-DCT measure-counting
  argument on indicator functions.  Includes the main
  `IsSlowlyVarying.uniform_convergence` theorem.

  See `Stats/RegularVariation/UCT.lean` for the umbrella.
-/
public import Stats.RegularVariation.UCT.Monotone
public import Mathlib.MeasureTheory.Integral.Indicator

@[expose] public section

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics MeasureTheory

namespace TailOptionPricing

/-! ### Measurable variant of UCT

    Csiszár–Erdős proof.  Reduce to the additive form `h(x) := log L(e^x)` on
    `ℝ`; pointwise SV becomes `h(x+u) − h(x) → 0` for each `u ∈ ℝ`.  For each
    bounded interval `I` and each `δ > 0`, Lebesgue DCT for indicators
    (`tendsto_measure_of_tendsto_indicator`) gives
    `m({u ∈ I : |h(x+u) − h(x)| < δ}) → m(I)` as `x → ∞`.  Then a
    measure-counting / inclusion-exclusion contradiction shows the
    convergence is in fact uniform on every compact `K ⊂ ℝ`.
-/

/-- DCT step (Csiszár–Erdős): for measurable `h` with pointwise convergence
    `h(x+u) − h(x) → 0` (atTop in `x`) for each `u`, the measure of the
    "good" set `{u ∈ Icc a b : |h(x+u) − h(x)| < δ}` converges to
    `volume (Icc a b)` as `x → ∞`. -/
private lemma additive_uct_dct_step
    {h : ℝ → ℝ} (h_meas : Measurable h)
    (h_lim_pt : ∀ u : ℝ, Tendsto (fun x => h (x + u) - h x) atTop (𝓝 0))
    (a b δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => volume (Set.Icc a b ∩ {u | |h (x + u) - h x| < δ}))
      atTop (𝓝 (volume (Set.Icc a b))) := by
  have hAs_mble : ∀ x : ℝ,
      MeasurableSet (Set.Icc a b ∩ {u | |h (x + u) - h x| < δ}) := by
    intro x
    refine measurableSet_Icc.inter (measurableSet_lt ?_ measurable_const)
    exact (continuous_abs.measurable).comp
      ((h_meas.comp (measurable_const_add x)).sub measurable_const)
  have hB_finmeas : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hAs_le_B : ∀ᶠ x in (atTop : Filter ℝ),
      Set.Icc a b ∩ {u | |h (x + u) - h x| < δ} ⊆ Set.Icc a b :=
    Eventually.of_forall fun _ => Set.inter_subset_left
  have h_lim_ind : ∀ u : ℝ, ∀ᶠ x in (atTop : Filter ℝ),
      u ∈ Set.Icc a b ∩ {u' | |h (x + u') - h x| < δ} ↔ u ∈ Set.Icc a b := by
    intro u
    by_cases hu : u ∈ Set.Icc a b
    · have h_dist : ∀ᶠ x in atTop, |h (x + u) - h x| < δ := by
        have hT := Metric.tendsto_nhds.mp (h_lim_pt u) δ hδ
        filter_upwards [hT] with x hx
        rwa [Real.dist_eq, sub_zero] at hx
      filter_upwards [h_dist] with x hx
      exact iff_of_true ⟨hu, hx⟩ hu
    · exact Eventually.of_forall fun _ =>
        iff_of_false (fun h => hu h.1) hu
  exact MeasureTheory.tendsto_measure_of_tendsto_indicator (atTop : Filter ℝ)
    hAs_mble (B := Set.Icc a b) measurableSet_Icc hB_finmeas hAs_le_B h_lim_ind

/-- **Korevaar UCT, additive form.**  For measurable `h : ℝ → ℝ` with
    pointwise convergence `h(x+u) − h(x) → 0` (atTop in `x`) for every
    `u ∈ ℝ`, the convergence is uniform on every compact interval `[α, β]`.

    *Proof (Csiszár–Erdős).*  By contradiction.  Suppose ∃ ε > 0 such that
    along arbitrarily large `x`, there is `u_x ∈ [α, β]` with
    `|h(x + u_x) − h(x)| ≥ ε`.  Set `δ := ε/3`.

    With `J := [α−1, β+1]` (length `mJ = β − α + 2`) and
    `I_T := [α−β−1, β−α+1]` (length `mIT = 2(β−α) + 2 = mJ + (β−α)`),
    apply the DCT step at base `x` on `J` and at base `x + u_x` on `I_T`.
    Both give measures `→ mJ` resp. `mIT`.

    The key algebraic fact: for any `u_n ∈ [α, β]`, we have
    `J ⊆ u_n + I_T` (verify by interval arithmetic), so
    `(u_n + T_y) ∩ J = J ∩ (u_n + T_y)` and its measure is at least
    `m(T_y) − (β − α)`.  Hence `m(S_x) ≈ mJ` and
    `m((u_x + T_{x + u_x}) ∩ J) ≈ mJ`.  Inclusion-exclusion in the ambient
    `J` then gives a strictly positive intersection.  Pick any `u` in the
    intersection: `|h(x+u) − h(x)| < δ` and
    `|h((x+u_x) + (u − u_x)) − h(x + u_x)| < δ`, i.e.,
    `|h(x+u) − h(x + u_x)| < δ`.  Triangle:
    `|h(x + u_x) − h(x)| < 2δ`, contradicting `≥ 3δ`. -/
private lemma additive_uct_aux
    {h : ℝ → ℝ} (h_meas : Measurable h)
    (h_lim_pt : ∀ u : ℝ, Tendsto (fun x => h (x + u) - h x) atTop (𝓝 0))
    {α β : ℝ} (hαβ : α ≤ β) :
    TendstoUniformlyOn (fun x u => h (x + u) - h x) (fun _ => 0) atTop
      (Set.Icc α β) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Constants.
  set δ := ε / 3 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have h2δ_lt_ε : 2 * δ < ε := by rw [hδ_def]; linarith
  have hβα : 0 ≤ β - α := sub_nonneg.mpr hαβ
  -- Intervals.
  set J : Set ℝ := Set.Icc (α - 1) (β + 1) with hJ_def
  set I_T : Set ℝ := Set.Icc (α - β - 1) (β - α + 1) with hI_T_def
  -- Real-valued lengths.
  set mJ : ℝ := β - α + 2 with hmJ_def
  set mIT : ℝ := 2 * (β - α) + 2 with hmIT_def
  have hmJ_pos : 0 < mJ := by simp only [hmJ_def]; linarith
  have hmIT_pos : 0 < mIT := by simp only [hmIT_def]; linarith
  have h_mIT_eq : mIT = mJ + (β - α) := by
    simp only [hmIT_def, hmJ_def]; ring
  -- ENNReal volumes.
  have h_volJ : volume J = ENNReal.ofReal mJ := by
    show volume (Set.Icc (α - 1) (β + 1)) = _
    rw [Real.volume_Icc]; congr 1; simp only [hmJ_def]; ring
  have h_volIT : volume I_T = ENNReal.ofReal mIT := by
    show volume (Set.Icc (α - β - 1) (β - α + 1)) = _
    rw [Real.volume_Icc]; congr 1; simp only [hmIT_def]; ring
  have h_volJ_ne_top : volume J ≠ ⊤ := by rw [h_volJ]; exact ENNReal.ofReal_ne_top
  have h_volIT_ne_top : volume I_T ≠ ⊤ := by rw [h_volIT]; exact ENNReal.ofReal_ne_top
  have h_volJ_toReal : (volume J).toReal = mJ := by
    rw [h_volJ]; exact ENNReal.toReal_ofReal hmJ_pos.le
  have h_volIT_toReal : (volume I_T).toReal = mIT := by
    rw [h_volIT]; exact ENNReal.toReal_ofReal hmIT_pos.le
  -- Threshold τR := mJ/4.
  set τR : ℝ := mJ / 4 with hτR_def
  have hτR_pos : 0 < τR := by simp only [hτR_def]; linarith
  have h_2τR_lt_mJ : 2 * τR < mJ := by simp only [hτR_def]; linarith
  have h_τR_le_mJ : τR ≤ mJ := by linarith
  have h_τR_lt_mIT : τR < mIT := by simp only [hτR_def, hmIT_def, hmJ_def]; linarith
  -- DCT steps.
  have hS_lim : Tendsto (fun x : ℝ => volume (J ∩ {u | |h (x + u) - h x| < δ}))
              atTop (𝓝 (volume J)) :=
    additive_uct_dct_step h_meas h_lim_pt (α - 1) (β + 1) δ hδ_pos
  have hT_lim : Tendsto (fun y : ℝ => volume (I_T ∩ {τ | |h (y + τ) - h y| < δ}))
              atTop (𝓝 (volume I_T)) :=
    additive_uct_dct_step h_meas h_lim_pt (α - β - 1) (β - α + 1) δ hδ_pos
  -- Eventually m(Sx) > ofReal(mJ - τR).
  have h_event_S : ∀ᶠ x in atTop,
      ENNReal.ofReal (mJ - τR) < volume (J ∩ {u | |h (x + u) - h x| < δ}) := by
    have h_lt : ENNReal.ofReal (mJ - τR) < volume J := by
      rw [h_volJ]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr (by linarith)
    exact hS_lim.eventually_const_lt h_lt
  -- Eventually m(T_y_full) > ofReal(mIT - τR).
  have h_event_T_pt : ∀ᶠ y in atTop,
      ENNReal.ofReal (mIT - τR) < volume (I_T ∩ {τ | |h (y + τ) - h y| < δ}) := by
    have h_lt : ENNReal.ofReal (mIT - τR) < volume I_T := by
      rw [h_volIT]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr (by linarith)
    exact hT_lim.eventually_const_lt h_lt
  -- Push uniformly across u ∈ [α, β].
  have h_event_T_uniform : ∀ᶠ x in atTop, ∀ u ∈ Set.Icc α β,
      ENNReal.ofReal (mIT - τR) <
        volume (I_T ∩ {τ | |h ((x + u) + τ) - h (x + u)| < δ}) := by
    rcases Filter.eventually_atTop.mp h_event_T_pt with ⟨M, hM⟩
    refine Filter.eventually_atTop.mpr ⟨M - α, fun x hx u hu => ?_⟩
    have : M ≤ x + u := by linarith [hu.1]
    exact hM (x + u) this
  -- Combine the eventual lower bounds.
  filter_upwards [h_event_S, h_event_T_uniform] with x hSx_lb_E hT_unif u hu
  -- For this single (x, u), show dist 0 (h(x+u) - h x) < ε.
  set y := x + u with hy_def
  -- Sets used in the measure-counting argument.
  set Sx : Set ℝ := J ∩ {v | |h (x + v) - h x| < δ} with hSx_def
  set T_y_full : Set ℝ := I_T ∩ {τ | |h (y + τ) - h y| < δ} with hTy_def
  set Tu : Set ℝ := J ∩ {v | |h (x + v) - h y| < δ} with hTu_def
  have h_Sx_lb : ENNReal.ofReal (mJ - τR) < volume Sx := hSx_lb_E
  have h_T_y_lb : ENNReal.ofReal (mIT - τR) < volume T_y_full := hT_unif u hu
  -- Measurability.
  have h_mble_T_y_full : MeasurableSet T_y_full := by
    refine measurableSet_Icc.inter (measurableSet_lt ?_ measurable_const)
    exact (continuous_abs.measurable).comp
      ((h_meas.comp (measurable_const_add y)).sub measurable_const)
  have h_mble_Sx : MeasurableSet Sx := by
    refine measurableSet_Icc.inter (measurableSet_lt ?_ measurable_const)
    exact (continuous_abs.measurable).comp
      ((h_meas.comp (measurable_const_add x)).sub measurable_const)
  have h_mble_Tu : MeasurableSet Tu := by
    refine measurableSet_Icc.inter (measurableSet_lt ?_ measurable_const)
    exact (continuous_abs.measurable).comp
      ((h_meas.comp (measurable_const_add x)).sub measurable_const)
  have h_mble_J : MeasurableSet J := measurableSet_Icc
  -- Algebraic fact: for v ∈ J, v - u ∈ I_T.
  have h_J_sub_uIT : ∀ v, v ∈ J → v - u ∈ I_T := by
    rintro v ⟨hα', hβ'⟩
    obtain ⟨hα, hβ⟩ := hu
    refine ⟨?_, ?_⟩
    · show α - β - 1 ≤ v - u; linarith
    · show v - u ≤ β - α + 1; linarith
  -- Translation: ϕ : v ↦ v - u.
  set ϕ : ℝ → ℝ := fun v => v - u with hϕ_def
  have hϕ_eq : ϕ = (fun w => (-u) + w) := by
    funext v; show v - u = -u + v; ring
  have hϕ_meas : Measurable ϕ := by
    rw [hϕ_eq]; exact measurable_const_add (-u)
  set uIT : Set ℝ := ϕ ⁻¹' I_T with huIT_def
  set ϕT : Set ℝ := ϕ ⁻¹' T_y_full with hϕT_def
  have h_mble_uIT : MeasurableSet uIT := hϕ_meas measurableSet_Icc
  have h_mble_ϕT : MeasurableSet ϕT := hϕ_meas h_mble_T_y_full
  -- Translation invariance.
  have h_vol_uIT : volume uIT = volume I_T := by
    show volume (ϕ ⁻¹' I_T) = volume I_T
    rw [hϕ_eq]
    exact MeasureTheory.measure_preimage_add (volume) (-u) I_T
  have h_vol_ϕT : volume ϕT = volume T_y_full := by
    show volume (ϕ ⁻¹' T_y_full) = volume T_y_full
    rw [hϕ_eq]
    exact MeasureTheory.measure_preimage_add (volume) (-u) T_y_full
  have h_ϕT_sub_uIT : ϕT ⊆ uIT := Set.preimage_mono Set.inter_subset_left
  have h_J_sub_uIT_set : J ⊆ uIT := fun v hv => h_J_sub_uIT v hv
  -- Reformulate: Tu = J ∩ ϕT.
  have h_Tu_eq : Tu = J ∩ ϕT := by
    ext v
    constructor
    · rintro ⟨hvJ, h_dist⟩
      refine ⟨hvJ, h_J_sub_uIT v hvJ, ?_⟩
      show |h (y + (v - u)) - h y| < δ
      have : y + (v - u) = x + v := by show (x + u) + (v - u) = x + v; ring
      rw [this]; exact h_dist
    · rintro ⟨hvJ, _, h_dist⟩
      refine ⟨hvJ, ?_⟩
      have : y + (v - u) = x + v := by show (x + u) + (v - u) = x + v; ring
      show |h (x + v) - h y| < δ
      rw [← this]; exact h_dist
  -- Finiteness.
  have h_vol_T_y_full_ne_top : volume T_y_full ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_of_le_of_ne le_top h_volIT_ne_top))
  have h_vol_Sx_ne_top : volume Sx ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_of_le_of_ne le_top h_volJ_ne_top))
  have h_vol_Tu_ne_top : volume Tu ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_of_le_of_ne le_top h_volJ_ne_top))
  have h_vol_ϕT_ne_top : volume ϕT ≠ ⊤ := by rw [h_vol_ϕT]; exact h_vol_T_y_full_ne_top
  have h_vol_uIT_ne_top : volume uIT ≠ ⊤ := by rw [h_vol_uIT]; exact h_volIT_ne_top
  have h_vol_ϕT_diff_J_ne_top : volume (ϕT \ J) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.sdiff_subset)
      (lt_of_le_of_ne le_top h_vol_ϕT_ne_top))
  -- Move to ℝ via .toReal.
  have h_volJ_re : (volume J).toReal = mJ := h_volJ_toReal
  have h_volIT_re : (volume I_T).toReal = mIT := h_volIT_toReal
  have h_volSx_re_lb : mJ - τR < (volume Sx).toReal := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) h_vol_Sx_ne_top).mp
    exact h_Sx_lb
  have h_volTy_re_lb : mIT - τR < (volume T_y_full).toReal := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) h_vol_T_y_full_ne_top).mp
    exact h_T_y_lb
  -- (volume Tu).toReal + (volume (ϕT \ J)).toReal = (volume T_y_full).toReal.
  have h_split_E : volume Tu + volume (ϕT \ J) = volume T_y_full := by
    have h1 : volume (ϕT ∩ J) + volume (ϕT \ J) = volume ϕT :=
      MeasureTheory.measure_inter_add_sdiff (μ := volume) ϕT h_mble_J
    rw [h_Tu_eq, Set.inter_comm J ϕT, h1, h_vol_ϕT]
  have h_split : (volume Tu).toReal + (volume (ϕT \ J)).toReal
                  = (volume T_y_full).toReal := by
    rw [← ENNReal.toReal_add h_vol_Tu_ne_top h_vol_ϕT_diff_J_ne_top, h_split_E]
  -- (volume (uIT \ J)).toReal = β - α.
  have h_vol_uIT_diff_J_ne_top : volume (uIT \ J) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.sdiff_subset)
      (lt_of_le_of_ne le_top h_vol_uIT_ne_top))
  have h_vol_uIT_diff_J_E : volume (uIT \ J) = volume uIT - volume J :=
    MeasureTheory.measure_sdiff h_J_sub_uIT_set h_mble_J.nullMeasurableSet
      h_volJ_ne_top
  have h_vol_uIT_diff_J_re : (volume (uIT \ J)).toReal = β - α := by
    rw [h_vol_uIT_diff_J_E,
        ENNReal.toReal_sub_of_le (measure_mono h_J_sub_uIT_set) h_vol_uIT_ne_top,
        h_vol_uIT, h_volIT_re, h_volJ_re, h_mIT_eq]; ring
  -- (volume (ϕT \ J)).toReal ≤ β - α.
  have h_vol_ϕT_diff_J_re_le : (volume (ϕT \ J)).toReal ≤ β - α := by
    rw [← h_vol_uIT_diff_J_re]
    exact ENNReal.toReal_mono h_vol_uIT_diff_J_ne_top
      (measure_mono (Set.sdiff_subset_sdiff_left h_ϕT_sub_uIT))
  -- Therefore (volume Tu).toReal > mJ - τR.
  have h_volTu_re_lb : mJ - τR < (volume Tu).toReal := by
    have h_eq : (volume Tu).toReal
                = (volume T_y_full).toReal - (volume (ϕT \ J)).toReal := by
      linarith [h_split]
    rw [h_eq]
    have h_mIT_calc : mIT - τR - (β - α) = mJ - τR := by rw [h_mIT_eq]; ring
    linarith [h_volTy_re_lb, h_vol_ϕT_diff_J_re_le]
  -- Inclusion-exclusion in ℝ via .toReal.
  have h_Sx_sub_J : Sx ⊆ J := Set.inter_subset_left
  have h_Tu_sub_J : Tu ⊆ J := Set.inter_subset_left
  have h_union_sub_J : Sx ∪ Tu ⊆ J := Set.union_subset h_Sx_sub_J h_Tu_sub_J
  have h_vol_union_ne_top : volume (Sx ∪ Tu) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono h_union_sub_J)
      (lt_of_le_of_ne le_top h_volJ_ne_top))
  have h_vol_inter_ne_top : volume (Sx ∩ Tu) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_of_le_of_ne le_top h_vol_Sx_ne_top))
  have h_incl_excl_E : volume (Sx ∪ Tu) + volume (Sx ∩ Tu)
                        = volume Sx + volume Tu :=
    MeasureTheory.measure_union_add_inter Sx h_mble_Tu
  have h_incl_excl : (volume (Sx ∪ Tu)).toReal + (volume (Sx ∩ Tu)).toReal
                      = (volume Sx).toReal + (volume Tu).toReal := by
    rw [← ENNReal.toReal_add h_vol_union_ne_top h_vol_inter_ne_top,
        ← ENNReal.toReal_add h_vol_Sx_ne_top h_vol_Tu_ne_top, h_incl_excl_E]
  have h_vol_union_re_le : (volume (Sx ∪ Tu)).toReal ≤ mJ := by
    rw [← h_volJ_re]
    exact ENNReal.toReal_mono h_volJ_ne_top (measure_mono h_union_sub_J)
  have h_inter_re_pos : 0 < (volume (Sx ∩ Tu)).toReal := by linarith
  -- Hence Sx ∩ Tu nonempty.
  have h_inter_pos_E : 0 < volume (Sx ∩ Tu) := by
    have h_ne_zero : volume (Sx ∩ Tu) ≠ 0 := by
      intro h_zero
      rw [h_zero, ENNReal.toReal_zero] at h_inter_re_pos
      exact lt_irrefl _ h_inter_re_pos
    exact pos_iff_ne_zero.mpr h_ne_zero
  have h_inter_nonempty : (Sx ∩ Tu).Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty, MeasureTheory.measure_empty] at h_inter_pos_E
    exact lt_irrefl _ h_inter_pos_E
  obtain ⟨v, hvSx, hvTu⟩ := h_inter_nonempty
  -- Triangle inequality.
  have hd1 : |h (x + v) - h x| < δ := hvSx.2
  have hd2 : |h (x + v) - h y| < δ := hvTu.2
  have h_tri : |h y - h x| < 2 * δ := by
    have h_split_diff : h y - h x = (h y - h (x + v)) + (h (x + v) - h x) := by ring
    rw [h_split_diff]
    have hd2' : |h y - h (x + v)| < δ := by rw [abs_sub_comm]; exact hd2
    calc |(h y - h (x + v)) + (h (x + v) - h x)|
        ≤ |h y - h (x + v)| + |h (x + v) - h x| := abs_add_le _ _
      _ < δ + δ := add_lt_add hd2' hd1
      _ = 2 * δ := by ring
  -- Final goal: dist 0 (h(x+u) - h x) < ε.
  show dist 0 (h (x + u) - h x) < ε
  rw [Real.dist_eq, zero_sub, abs_neg]
  show |h y - h x| < ε
  linarith

/-- **Korevaar UCT, measurable variant.**  For any measurable, eventually
    positive, slowly-varying `L : ℝ → ℝ`, the convergence
    `L(t·x)/L(t) → 1` is uniform in `x` over every compact `[a, b] ⊂ (0, ∞)`.

    Reduction to the additive form: with `h(x) := log L(e^x)`,
    pointwise SV at `e^u > 0` becomes `h(x + u) − h(x) → 0` for each `u ∈ ℝ`.
    Apply `additive_uct_aux`; translate the log-uniform bound back to a
    uniform bound for the ratio via `|log z| < log(1 + ε/2) ⟹ |z − 1| < ε/2`. -/

theorem IsSlowlyVarying.uniform_convergence
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_meas : Measurable L)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn (fun t x => L (t * x) / L t) (fun _ => 1)
      atTop (Set.Icc a b) := by
  -- Define h(x) := log L(e^x).
  set h_add : ℝ → ℝ := fun x => Real.log (L (Real.exp x)) with hh_def
  have hh_meas : Measurable h_add :=
    Real.measurable_log.comp (hL_meas.comp Real.measurable_exp)
  -- Pointwise additive SV: h(x + u) − h(x) → 0 for each u.
  have hh_lim_pt : ∀ u : ℝ, Tendsto (fun x => h_add (x + u) - h_add x) atTop (𝓝 0) := by
    intro u
    have h_exp_pos : 0 < Real.exp u := Real.exp_pos u
    have h_lift_exp : Tendsto (fun x : ℝ => Real.exp x) atTop atTop :=
      Real.tendsto_exp_atTop
    have h_lift_exp_u : Tendsto (fun x : ℝ => Real.exp (x + u)) atTop atTop := by
      apply Real.tendsto_exp_atTop.comp
      exact Filter.tendsto_atTop_add_const_right atTop u Filter.tendsto_id
    have hL_pos_exp : ∀ᶠ x in atTop, 0 < L (Real.exp x) := h_lift_exp.eventually hL_pos
    have hL_pos_exp_u : ∀ᶠ x in atTop, 0 < L (Real.exp (x + u)) :=
      h_lift_exp_u.eventually hL_pos
    have h_quot : Tendsto (fun x : ℝ => L (Real.exp x * Real.exp u) / L (Real.exp x))
                    atTop (𝓝 1) :=
      (hL (Real.exp u) h_exp_pos).comp h_lift_exp
    have h_log_lim : Tendsto Real.log (𝓝 1) (𝓝 0) := by
      have := (Real.continuousAt_log one_ne_zero).tendsto
      rwa [Real.log_one] at this
    have h_log_quot : Tendsto
        (fun x : ℝ => Real.log (L (Real.exp x * Real.exp u) / L (Real.exp x)))
        atTop (𝓝 0) :=
      h_log_lim.comp h_quot
    have h_eq : ∀ᶠ x in atTop,
        Real.log (L (Real.exp x * Real.exp u) / L (Real.exp x))
          = h_add (x + u) - h_add x := by
      filter_upwards [hL_pos_exp, hL_pos_exp_u] with x h_pos_x h_pos_xu
      have h_exp_swap : Real.exp x * Real.exp u = Real.exp (x + u) :=
        (Real.exp_add x u).symm
      rw [h_exp_swap, Real.log_div h_pos_xu.ne' h_pos_x.ne']
    exact h_log_quot.congr' h_eq
  -- Apply additive UCT on [log a, log b].
  have h_log_a_le : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have h_uct := additive_uct_aux hh_meas hh_lim_pt h_log_a_le
  rw [Metric.tendstoUniformlyOn_iff] at h_uct
  -- Translate to multiplicative form.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- ε' := log(1 + ε/2).
  set ε' := Real.log (1 + ε / 2) with hε'_def
  have hε'_pos : 0 < ε' := by
    rw [hε'_def]; apply Real.log_pos; linarith
  have h_event := h_uct ε' hε'_pos
  -- Eventually positivity of L(t · y) for y ∈ [a, b], t large.
  have hL_pos_ty : ∀ᶠ t in atTop, ∀ y ∈ Set.Icc a b, 0 < L (t * y) := by
    rcases Filter.eventually_atTop.mp hL_pos with ⟨N, hN⟩
    refine Filter.eventually_atTop.mpr ⟨max (N / a) 1, fun t ht y hy => hN _ ?_⟩
    obtain ⟨hya, _⟩ := hy
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) ht)
    have ht_a : N / a ≤ t := le_trans (le_max_left _ _) ht
    calc N = N / a * a := by field_simp
      _ ≤ t * a := mul_le_mul_of_nonneg_right ht_a ha.le
      _ ≤ t * y := mul_le_mul_of_nonneg_left hya ht_pos.le
  -- Lift along x = log t.
  have h_log_lift : Tendsto (Real.log : ℝ → ℝ) atTop atTop :=
    Real.tendsto_log_atTop
  filter_upwards [h_log_lift.eventually h_event, hL_pos, hL_pos_ty,
                  eventually_gt_atTop (0 : ℝ)]
    with t h_at_log_t hL_t hL_ty_all ht_pos y hy
  -- Pin down y, u := log y.
  obtain ⟨hya, hyb⟩ := hy
  have hy_pos : 0 < y := lt_of_lt_of_le ha hya
  set u := Real.log y with hu_def
  have hu_in : u ∈ Set.Icc (Real.log a) (Real.log b) :=
    ⟨Real.log_le_log ha hya, Real.log_le_log hy_pos hyb⟩
  -- Apply uniform statement at log t, u.
  have h_dist_log : dist 0 (h_add (Real.log t + u) - h_add (Real.log t)) < ε' :=
    h_at_log_t u hu_in
  -- Reduce h_add at these arguments.
  have h_exp_log_t : Real.exp (Real.log t) = t := Real.exp_log ht_pos
  have h_exp_log_y : Real.exp u = y := by rw [hu_def]; exact Real.exp_log hy_pos
  have h_exp_sum : Real.exp (Real.log t + u) = t * y := by
    rw [Real.exp_add, h_exp_log_t, h_exp_log_y]
  have h_h_log_t : h_add (Real.log t) = Real.log (L t) := by
    show Real.log (L (Real.exp (Real.log t))) = Real.log (L t)
    rw [h_exp_log_t]
  have h_h_log_t_u : h_add (Real.log t + u) = Real.log (L (t * y)) := by
    show Real.log (L (Real.exp (Real.log t + u))) = Real.log (L (t * y))
    rw [h_exp_sum]
  rw [h_h_log_t, h_h_log_t_u, Real.dist_eq, zero_sub, abs_neg] at h_dist_log
  -- h_dist_log : |log L(t · y) - log L t| < ε'.
  have hL_ty_pos : 0 < L (t * y) := hL_ty_all y ⟨hya, hyb⟩
  -- |log (L(t·y) / L t)| < ε'.
  have h_log_ratio : |Real.log (L (t * y) / L t)| < ε' := by
    rw [Real.log_div hL_ty_pos.ne' hL_t.ne']
    exact h_dist_log
  -- Translate to ratio bound.
  have hε_half_pos : 0 < ε / 2 := by linarith
  have h_one_add_pos : 0 < 1 + ε / 2 := by linarith
  set z := L (t * y) / L t with hz_def
  have hz_pos : 0 < z := div_pos hL_ty_pos hL_t
  -- |log z| < ε' = log(1 + ε/2)
  have h_log_z : -ε' < Real.log z ∧ Real.log z < ε' := abs_lt.mp h_log_ratio
  -- log z < ε' ⟹ z < 1 + ε/2.
  have hz_upper : z < 1 + ε / 2 := by
    have h_z_lt : Real.log z < Real.log (1 + ε / 2) := by rw [← hε'_def]; exact h_log_z.2
    exact (Real.log_lt_log_iff hz_pos h_one_add_pos).mp h_z_lt
  -- log z > -ε' ⟹ z > 1/(1 + ε/2).
  have hz_lower : 1 / (1 + ε / 2) < z := by
    have h_inv_pos : 0 < 1 / (1 + ε / 2) := by positivity
    have h_neg_ε' : Real.log (1 / (1 + ε / 2)) = -ε' := by
      rw [Real.log_div one_ne_zero h_one_add_pos.ne', Real.log_one, zero_sub, hε'_def]
    have h_log_lt : Real.log (1 / (1 + ε / 2)) < Real.log z := by
      rw [h_neg_ε']; exact h_log_z.1
    exact (Real.log_lt_log_iff h_inv_pos hz_pos).mp h_log_lt
  -- Conclude |z - 1| < ε.
  show dist 1 z < ε
  rw [Real.dist_eq, abs_lt]
  have h_inv_gt : 1 - ε / 2 < 1 / (1 + ε / 2) := by
    rw [lt_div_iff₀ h_one_add_pos]
    have h_expand : (1 - ε / 2) * (1 + ε / 2) = 1 - (ε / 2) ^ 2 := by ring
    have h_sq_pos : 0 < (ε / 2) ^ 2 := by positivity
    linarith [h_expand, h_sq_pos]
  exact ⟨by linarith, by linarith⟩


end TailOptionPricing
