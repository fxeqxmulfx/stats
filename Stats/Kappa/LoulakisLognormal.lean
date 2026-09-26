/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LoulakisLognormal — Lognormal-specialised Loulakis liminf.

  Final wire-up (todo6.md Phase 6.4) that takes the paper's actual
  claim from arXiv:1802.05495v3 Section "Lognormal Sums" and lands it
  as a single named Lean theorem.

  Setup (single fixed product space):

  * `Ωspace n := Fin n → ℝ` (n-fold sample space).
  * `μn n := Measure.pi (fun _ => gaussianReal 0 1)`.
  * `Xσ σ i ω := exp(σ · ω i − σ²/2) = Y σ (ω i)` (σ-parametrised iid lognormal).

  Define MADs:

  * `Mn n σ := ∫ ω, |∑ i, Xσ σ i ω − n| ∂(μn n)` (`M(n; σ)`).
  * `M1 σ  := ∫ ω, |Y σ ω − 1| ∂(gaussianReal 0 1)` (`M(1; σ)`).

  Headline theorem:

      `liminf_{σ → ∞}  Mn n σ / M1 σ  ≥  n`   for `n ≥ 1`.

  The proof wires together:

  * **Phase A** (iid triangle): `Mn n σ ≤ n · M1 σ`.
  * **Phase B.7** (`M_one_tendsto_two`): `M1 σ → 2`.
  * **Phase 6.2** (`An_tendsto_one`): `An σ → 1`.
  * **Phase C.3a** (`LoulakisAlgebraic.M_n_lower_bound`): the algebraic
    lower bound on `Mn`.
  * **Phase C.3b** (`LoulakisLiminf.liminf_M_ratio_ge_n`): the abstract
    `liminf` step.

  All pieces are closed; the headline theorem
  `liminf_M_ratio_lognormal_ge_n` is **hypothesis-free**.  In particular
  `Bn σ → 0` (Phase 6.3) is discharged via the squeeze
  `0 ≤ Bn σ ≤ ℙ_σ(Y > n) · An σ → 0 · 1 = 0`, using monotonicity of
  the tail in `t` and `prob_Y_gt_tendsto_zero`.  The Hölder bound
  `Y_tail_holder` is retained for reference (analytic estimate of the
  same tail) but is no longer on the critical path.
-/
import Stats.Kappa.LognormalIIdSetup
import Stats.Kappa.LognormalTailIntegrals
import Stats.Kappa.LoulakisAlgebraic
import Stats.Kappa.LoulakisLiminf
import Stats.Kappa.IIdTriangle
import Stats.Kappa.MadLayerCake

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing.LoulakisLognormal

open TailOptionPricing.LognormalAsymptotic (Y Y_pos Y_nonneg)
open TailOptionPricing.LognormalIIdSetup (Ωspace μn Xσ)
open TailOptionPricing.LognormalAsymptotic in
open TailOptionPricing.LognormalIIdSetup in

/-- **`M(n; σ)` of the n-fold iid lognormal**: `∫ |∑ i Xσ σ i − n| dμn`. -/
noncomputable def Mn (n : ℕ) (σ : ℝ) : ℝ :=
  ∫ ω, |(∑ i, Xσ σ i ω) - (n : ℝ)| ∂(μn n)

/-- **`M(1; σ)` (single-variable)**: `∫ |Y σ − 1| d(gaussianReal 0 1)`. -/
noncomputable def M1 (σ : ℝ) : ℝ :=
  ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1)

/-- **`An σ` (n-shifted tail integral)**: `∫_{t > 0} ℙ_σ(Y > n + t) dt`. -/
noncomputable def An (n : ℕ) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t}

/-- **`Bn σ` (n-shifted squared-tail integral)**: `∫_{t > 0} ℙ_σ(Y > n + t)² dt`. -/
noncomputable def Bn (n : ℕ) (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    ((gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t}) ^ 2

/-- **`Mn n σ ≥ 0`** (it's an integral of an absolute value). -/
theorem Mn_nonneg (n : ℕ) (σ : ℝ) : 0 ≤ Mn n σ :=
  integral_nonneg (fun _ => abs_nonneg _)

/-- **iid triangle inequality for the n-fold lognormal**: `Mn n σ ≤ n · M1 σ`.

    Direct instance of [`IIdTriangle.madSum_le_n_madSum_one`](Stats/Kappa/IIdTriangle.lean)
    applied to the iid family `Xσ σ`. -/
theorem Mn_le_n_M1 (n : ℕ) (σ : ℝ) : Mn n σ ≤ (n : ℝ) * M1 σ := by
  -- Apply `madSum_le_n_madSum_one`.  Need to convert `Mn` and `M1` to
  -- the `madSum` form.
  -- `madSum μ X n := ∫ ω, |Σ_{i < n} X i ω − n · μ[X 0]| dμ`.
  -- For our family `Xσ σ : Fin n → Ωspace n → ℝ`, we'd need to extend
  -- to `ℕ → Ωspace n → ℝ`.  Cleaner: prove directly.
  -- Pointwise: `|∑ i, Xσ σ i ω - n| ≤ ∑ i, |Xσ σ i ω - 1|` (triangle).
  -- Integrate: ∫ |∑| ≤ ∫ ∑ = ∑ ∫ = n · ∫ |Xσ σ 0 ω - 1| by IdentDistrib.
  -- ∫ |Xσ σ 0 ω - 1| = ∫ |Y σ ω - 1| (by IdentDistrib) = M1 σ.
  unfold Mn M1
  -- Replace `n` (on LHS) with `∑ i, ∫ Xσ σ i` (= n) so triangle inequality applies.
  have h_n_to_sum : (n : ℝ) = ∑ i : Fin n, ∫ ω, Xσ σ i ω ∂(μn n) := by
    rw [Finset.sum_congr rfl (fun i _ =>
      TailOptionPricing.LognormalIIdSetup.integral_Xσ_eq_one σ i)]
    simp
  conv_lhs => rw [h_n_to_sum]
  -- Pointwise triangle.
  have h_pt : ∀ ω,
      |(∑ i, Xσ σ i ω) - ∑ i : Fin n, ∫ ω', Xσ σ i ω' ∂(μn n)|
        ≤ ∑ i, |Xσ σ i ω - ∫ ω', Xσ σ i ω' ∂(μn n)| := by
    intro ω
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have h_int_each : ∀ i : Fin n,
      Integrable (fun ω => |Xσ σ i ω - ∫ ω', Xσ σ i ω' ∂(μn n)|) (μn n) := fun i =>
    ((TailOptionPricing.LognormalIIdSetup.integrable_Xσ σ i).sub (integrable_const _)).abs
  have h_int_sum_abs : Integrable
      (fun ω => ∑ i, |Xσ σ i ω - ∫ ω', Xσ σ i ω' ∂(μn n)|) (μn n) :=
    integrable_finset_sum _ (fun i _ => h_int_each i)
  have h_int_centred : Integrable
      (fun ω => (∑ i, Xσ σ i ω) - ∑ i : Fin n, ∫ ω', Xσ σ i ω' ∂(μn n)) (μn n) :=
    (TailOptionPricing.LognormalIIdSetup.integrable_sum_Xσ σ n).sub (integrable_const _)
  calc ∫ ω, |(∑ i, Xσ σ i ω) - ∑ i : Fin n, ∫ ω', Xσ σ i ω' ∂(μn n)| ∂(μn n)
      ≤ ∫ ω, ∑ i, |Xσ σ i ω - ∫ ω', Xσ σ i ω' ∂(μn n)| ∂(μn n) := by
        apply integral_mono_ae h_int_centred.abs h_int_sum_abs
        exact .of_forall h_pt
    _ = ∑ i, ∫ ω, |Xσ σ i ω - ∫ ω', Xσ σ i ω' ∂(μn n)| ∂(μn n) :=
        integral_finset_sum _ (fun i _ => h_int_each i)
    _ = ∑ _ : Fin n, ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1) := by
        apply Finset.sum_congr rfl
        intros i _
        rw [TailOptionPricing.LognormalIIdSetup.integral_Xσ_eq_one σ i]
        -- Now: ∫ |Xσ σ i ω - 1| dμn = ∫ |Y σ ω - 1| dgauss (IdentDistrib).
        have h_id_abs : IdentDistrib
            (fun ω => |Xσ σ i ω - 1|) (fun ω => |Y σ ω - 1|)
            (μn n) (gaussianReal 0 1) :=
          (TailOptionPricing.LognormalIIdSetup.identDistrib_Xσ σ i).comp
            (by fun_prop : Measurable (fun x : ℝ => |x - 1|))
        exact h_id_abs.integral_eq
    _ = (n : ℝ) * ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Discharge of `h_lower` and `h_Bn_tend` for the lognormal. -/

/-- **`Y σ` is integrable** under `gaussianReal 0 1`. -/
private lemma Y_integrable_local (σ : ℝ) : Integrable (Y σ) (gaussianReal 0 1) := by
  unfold Y
  have h_factor : (fun ω => Real.exp (σ * ω - σ^2 / 2))
      = (fun ω => Real.exp (-(σ^2/2)) * Real.exp (σ * ω)) := by
    funext ω; rw [← Real.exp_add]; congr 1; ring
  rw [h_factor]
  exact (integrable_exp_mul_gaussianReal σ).const_mul _

/-- **Tail-integrability of `t ↦ ℙ_μn(∑ Xσ σ > n + t)` on `Ioi 0`**.

    Apply [`MadLayerCake.integrableOn_measureReal_lt_Ioi`](Stats/Kappa/MadLayerCake.lean)
    to the centred non-negative partial sum `(∑ Xσ σ − n)⁺`. -/
private theorem integrableOn_prob_sum_Xσ_gt_Ioi (n : ℕ) (σ : ℝ) :
    IntegrableOn
      (fun t : ℝ => (μn n).real {ω | (∑ i, Xσ σ i ω) > (n : ℝ) + t})
      (Set.Ioi (0 : ℝ)) := by
  set S : Ωspace n → ℝ := fun ω => ∑ i, Xσ σ i ω with hS_def
  set Sp : Ωspace n → ℝ := fun ω => max ((∑ i, Xσ σ i ω) - (n : ℝ)) 0 with hSp_def
  have hS_int : Integrable S (μn n) :=
    TailOptionPricing.LognormalIIdSetup.integrable_sum_Xσ σ n
  have hSp_int : Integrable Sp (μn n) :=
    (hS_int.sub (integrable_const _)).pos_part
  have hSp_nn : 0 ≤ᵐ[μn n] Sp := .of_forall (fun _ => le_max_right _ _)
  have h_helper := TailOptionPricing.MadLayerCake.integrableOn_measureReal_lt_Ioi
    hSp_int hSp_nn
  refine h_helper.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht_pos : (0 : ℝ) < t := ht
  have h_pt : (μn n).real {ω | Sp ω > t}
      = (μn n).real {ω | (∑ i, Xσ σ i ω) > (n : ℝ) + t} := by
    congr 1
    ext ω
    show Sp ω > t ↔ (∑ i, Xσ σ i ω) > (n : ℝ) + t
    simp only [hSp_def]
    by_cases h' : 0 ≤ (∑ i, Xσ σ i ω) - (n : ℝ)
    · rw [max_eq_left h']
      constructor
      · intro h; linarith
      · intro h; linarith
    · push_neg at h'
      rw [max_eq_right h'.le]
      constructor
      · intro h; linarith
      · intro h; linarith
  exact h_pt

/-- **Algebraic Loulakis bound for the lognormal**:
    `2·(n · An n σ − C(n,2) · Bn n σ) ≤ Mn n σ`.  Direct application of
    [`LoulakisAlgebraic.M_n_lower_bound`](Stats/Kappa/LoulakisAlgebraic.lean)
    to the iid family `Xσ σ`. -/
theorem M_n_lower_lognormal (n : ℕ) (σ : ℝ) :
    (2 : ℝ) * ((n : ℝ) * An n σ - (n.choose 2 : ℝ) * Bn n σ)
      ≤ Mn n σ := by
  have h_meas_Y : Measurable (Y σ) := by unfold Y; fun_prop
  have h_meas : ∀ i : Fin n, Measurable (Xσ σ i) :=
    fun i => TailOptionPricing.LognormalIIdSetup.measurable_Xσ σ i
  have h_indep := TailOptionPricing.LognormalIIdSetup.iIndepFun_Xσ σ n
  have h_id : ∀ i : Fin n, IdentDistrib (Xσ σ i) (Y σ) (μn n) (gaussianReal 0 1) :=
    fun i => TailOptionPricing.LognormalIIdSetup.identDistrib_Xσ σ i
  have h_nonneg : ∀ (i : Fin n) (ω : Ωspace n), 0 ≤ Xσ σ i ω :=
    fun i ω => TailOptionPricing.LognormalIIdSetup.Xσ_nonneg σ i ω
  have hY_int : Integrable (Y σ) (gaussianReal 0 1) := Y_integrable_local σ
  have h_mean : (∫ ω', Y σ ω' ∂(gaussianReal 0 1)) = (1 : ℝ) :=
    TailOptionPricing.LognormalAsymptotic.integral_Y_eq_one σ
  have h_S_int : Integrable (fun ω => ∑ i, Xσ σ i ω) (μn n) :=
    TailOptionPricing.LognormalIIdSetup.integrable_sum_Xσ σ n
  have h_S_mean : (∫ ω, ∑ i, Xσ σ i ω ∂(μn n)) = (n : ℝ) * (1 : ℝ) := by
    rw [TailOptionPricing.LognormalIIdSetup.integral_sum_Xσ_eq σ n]; ring
  have h_pmax_int := TailOptionPricing.LognormalTailIntegrals.integrableOn_prob_Y_gt_Ioi σ (n : ℝ)
  have h_pmax_sq_int := TailOptionPricing.LognormalTailIntegrals.integrableOn_prob_Y_gt_sq_Ioi σ (n : ℝ)
  have h_psum_int := integrableOn_prob_sum_Xσ_gt_Ioi n σ
  -- Massage indices: lift integrability through `n * 1 = n`.
  have h_pmax_int' : IntegrableOn
      (fun t => (gaussianReal 0 1).real {ω' | Y σ ω' > (n : ℝ) * 1 + t})
      (Set.Ioi (0 : ℝ)) := by
    simp only [mul_one]; exact h_pmax_int
  have h_pmax_sq_int' : IntegrableOn
      (fun t => ((gaussianReal 0 1).real {ω' | Y σ ω' > (n : ℝ) * 1 + t}) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    simp only [mul_one]; exact h_pmax_sq_int
  have h_psum_int' : IntegrableOn
      (fun t => (μn n).real {ω | (∑ i, Xσ σ i ω) > (n : ℝ) * 1 + t})
      (Set.Ioi (0 : ℝ)) := by
    simp only [mul_one]; exact h_psum_int
  -- Apply the abstract bound.
  have h := TailOptionPricing.LoulakisAlgebraic.M_n_lower_bound
    (μ := μn n) (ν := gaussianReal 0 1) (n := n) (Y₀ := Y σ) (X := Xσ σ)
    h_meas_Y h_meas h_indep h_id h_nonneg hY_int (m := 1) h_mean
    h_S_int h_S_mean h_pmax_int' h_pmax_sq_int' h_psum_int'
  -- `n * 1 = n` simplifies the LHS/RHS of `h` to match the goal.
  simp only [mul_one] at h
  -- Now `h : 2 * (n * ∫_{Ioi 0} ... {Y > n+t} - C(n,2) * ∫_{Ioi 0} ... {Y > n+t}^2) ≤ ∫ |S - n|`.
  -- This is exactly `2 * (n * An n σ - C(n,2) * Bn n σ) ≤ Mn n σ` by defs.
  exact h

/-- **`Bn σ → 0` for the lognormal n-fold setup** (todo6.md Phase 6.3 closure).
    Direct corollary of [`LognormalTailIntegrals.Bn_tendsto_zero`](Stats/Kappa/LognormalTailIntegrals.lean). -/
theorem Bn_tendsto_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => Bn n σ) atTop (𝓝 0) :=
  TailOptionPricing.LognormalTailIntegrals.Bn_tendsto_zero hn

/-- **Headline: `liminf σ→∞ M(n; σ) / M(1; σ) ≥ n` for the lognormal**
    (paper arXiv:1802.05495v3, Section "Lognormal Sums", Loulakis result).

    **Hypothesis-free.**  The proof wires:
    * `Mn_le_n_M1` (Phase A iid triangle).
    * `LognormalAsymptotic.M_one_tendsto_two` (Phase B.7).
    * `LognormalTailIntegrals.An_tendsto_one` (Phase 6.2).
    * `M_n_lower_lognormal` (algebraic Loulakis bound, applied to `Xσ σ`).
    * `Bn_tendsto_zero` (Phase 6.3, via `ℙ(Y > n) → 0` squeeze). -/
theorem liminf_M_ratio_lognormal_ge_n
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ Filter.liminf (fun σ : ℝ => Mn n σ / M1 σ) atTop := by
  apply TailOptionPricing.LoulakisLiminf.liminf_M_ratio_ge_n
    (Mn := Mn n) (M1 := M1) (An := An n) (Bn := Bn n)
  · exact M_n_lower_lognormal n
  · exact Mn_nonneg n
  · exact Mn_le_n_M1 n
  · exact TailOptionPricing.LognormalAsymptotic.M_one_tendsto_two
  · exact TailOptionPricing.LognormalTailIntegrals.An_tendsto_one hn
  · exact Bn_tendsto_zero hn

/-! ### Full limit: `M(n; σ) / M(1; σ) → n`.

    The paper "Lognormal Sums" quotes Loulakis as proving the full
    limit `M(n)/M(1) → n` (Taleb writes "Skipping steps, we get
    liminf ≥ n" — that's the *easy half* used in the κ argument).
    Combining the iid-triangle upper bound `Mn ≤ n · M1` (which gives
    `limsup ≤ n` once `M1 → 2 > 0` makes the division valid) with
    `liminf ≥ n` yields the full limit `Mn/M1 → n`. -/

/-- **Loulakis full limit**: `Mn n σ / M1 σ → n` as `σ → ∞`.

    Squeeze:
    * **Lower bound** `2·(n · An σ − C(n,2) · Bn σ) / M1 σ → n` from
      `M_n_lower_lognormal` divided by `M1 σ` (eventually positive
      since `M1 σ → 2`).  Numerator tends to `2·(n·1 − C(n,2)·0) = 2n`;
      denominator tends to `2`; ratio tends to `n`.
    * **Upper bound** `Mn n σ / M1 σ ≤ n` from `Mn_le_n_M1` divided by
      `M1 σ` (eventually positive).  Constant `n` is its own limit. -/
theorem tendsto_M_ratio_lognormal_eq_n {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => Mn n σ / M1 σ) atTop (𝓝 (n : ℝ)) := by
  have hM1 : Tendsto M1 atTop (𝓝 2) :=
    TailOptionPricing.LognormalAsymptotic.M_one_tendsto_two
  have hAn : Tendsto (fun σ => An n σ) atTop (𝓝 1) :=
    TailOptionPricing.LognormalTailIntegrals.An_tendsto_one hn
  have hBn : Tendsto (fun σ => Bn n σ) atTop (𝓝 0) := Bn_tendsto_zero hn
  -- `M1 σ` is eventually positive.
  have h_M1_pos : ∀ᶠ σ in atTop, 0 < M1 σ :=
    hM1.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 2))
  -- Lower function `g σ := 2·(n · An σ − C(n,2) · Bn σ) / M1 σ`.
  set g : ℝ → ℝ := fun σ =>
    (2 : ℝ) * ((n : ℝ) * An n σ - (n.choose 2 : ℝ) * Bn n σ) / M1 σ with hg_def
  -- `g σ → n`.
  have h_g_tend : Tendsto g atTop (𝓝 (n : ℝ)) := by
    have h_num_tend : Tendsto
        (fun σ : ℝ => (2 : ℝ) * ((n : ℝ) * An n σ - (n.choose 2 : ℝ) * Bn n σ))
        atTop (𝓝 ((2 : ℝ) * ((n : ℝ) * 1 - (n.choose 2 : ℝ) * 0))) :=
      ((hAn.const_mul (n : ℝ)).sub (hBn.const_mul (n.choose 2 : ℝ))).const_mul 2
    have h_target : Tendsto g atTop (𝓝
        ((2 : ℝ) * ((n : ℝ) * 1 - (n.choose 2 : ℝ) * 0) / 2)) := by
      simpa [hg_def] using h_num_tend.div hM1 (by norm_num : (2 : ℝ) ≠ 0)
    have h_eq : ((2 : ℝ) * ((n : ℝ) * 1 - (n.choose 2 : ℝ) * 0) / 2) = (n : ℝ) := by ring
    rw [h_eq] at h_target
    exact h_target
  -- Squeeze.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_g_tend tendsto_const_nhds
  · -- `g σ ≤ Mn / M1` eventually.
    filter_upwards [h_M1_pos] with σ hσ
    exact div_le_div_of_nonneg_right (M_n_lower_lognormal n σ) hσ.le
  · -- `Mn / M1 ≤ n` eventually.
    filter_upwards [h_M1_pos] with σ hσ
    rw [div_le_iff₀ hσ]
    exact Mn_le_n_M1 n σ

/-! ### κ-corollary: `κ_{1, n}(σ) → 1` as `σ → ∞`.

    The whole point of paper Section "Lognormal Sums" is the κ-metric
    value: with `M(n)/M(1) → n` (Loulakis), the κ-metric
        κ(1, n) := 2 − log(n) / (log M(n) − log M(1))
    tends to `2 − log(n) / log(n) = 1` as `σ → ∞`.  This matches
    Taleb's claim that lognormal becomes "fully fat-tailed" (κ = 1)
    in the σ → ∞ limit. -/

/-- **`Mn n σ → 2n`** as `σ → ∞` (from the full limit + `M1 → 2`). -/
theorem Mn_tendsto_two_mul_n {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => Mn n σ) atTop (𝓝 ((n : ℝ) * 2)) := by
  have h_ratio := tendsto_M_ratio_lognormal_eq_n hn
  have hM1 : Tendsto M1 atTop (𝓝 2) :=
    TailOptionPricing.LognormalAsymptotic.M_one_tendsto_two
  -- Mn n σ = (Mn n σ / M1 σ) · M1 σ eventually (M1 σ ≠ 0).
  have h_M1_pos : ∀ᶠ σ in atTop, 0 < M1 σ :=
    hM1.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 2))
  have h_prod : Tendsto (fun σ : ℝ => Mn n σ / M1 σ * M1 σ) atTop
      (𝓝 ((n : ℝ) * 2)) := h_ratio.mul hM1
  refine h_prod.congr' ?_
  filter_upwards [h_M1_pos] with σ hσ
  field_simp

/-- **κ-metric `κ_{1, n}(σ) → 1`** for the lognormal as `σ → ∞`
    (paper "Lognormal Sums" Loulakis result, in κ form).

    Direct corollary of `tendsto_M_ratio_lognormal_eq_n`:
    `log (Mn n σ) − log (M1 σ) → log n`, hence `κ → 2 − log n / log n = 1`.
    Requires `n ≥ 2` (for `log n > 0`). -/
theorem kappa_lognormal_tendsto_one {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun σ : ℝ =>
        (2 : ℝ) - Real.log n / (Real.log (Mn n σ) - Real.log (M1 σ)))
      atTop (𝓝 1) := by
  have hn1 : 1 ≤ n := by omega
  have h_ratio := tendsto_M_ratio_lognormal_eq_n hn1
  have hM1 : Tendsto M1 atTop (𝓝 2) :=
    TailOptionPricing.LognormalAsymptotic.M_one_tendsto_two
  have h_M1_pos : ∀ᶠ σ in atTop, 0 < M1 σ :=
    hM1.eventually (eventually_gt_nhds (by norm_num : (0:ℝ) < 2))
  have hMn := Mn_tendsto_two_mul_n hn1
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  have h_2n_pos : (0 : ℝ) < (n : ℝ) * 2 := by positivity
  have h_Mn_pos : ∀ᶠ σ in atTop, 0 < Mn n σ :=
    hMn.eventually (eventually_gt_nhds h_2n_pos)
  -- Step 1: log (Mn n σ) - log (M1 σ) → log n.
  have h_log_diff : Tendsto (fun σ : ℝ => Real.log (Mn n σ) - Real.log (M1 σ))
      atTop (𝓝 (Real.log n)) := by
    have h_log_ratio : Tendsto (fun σ : ℝ => Real.log (Mn n σ / M1 σ))
        atTop (𝓝 (Real.log n)) :=
      (Real.continuousAt_log (by exact_mod_cast hn_real.ne' : (n:ℝ) ≠ 0)).tendsto.comp h_ratio
    refine h_log_ratio.congr' ?_
    filter_upwards [h_M1_pos, h_Mn_pos] with σ hM1pos hMnpos
    exact Real.log_div hMnpos.ne' hM1pos.ne'
  -- Step 2: log n > 0 for n ≥ 2.
  have h_log_n_pos : 0 < Real.log n := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < n)
  have h_log_n_ne : Real.log n ≠ 0 := h_log_n_pos.ne'
  -- Step 3: κ → 2 - log n / log n = 1.
  have h_kappa_tend : Tendsto (fun σ : ℝ =>
      (2:ℝ) - Real.log n / (Real.log (Mn n σ) - Real.log (M1 σ)))
      atTop (𝓝 ((2 : ℝ) - Real.log n / Real.log n)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div h_log_diff h_log_n_ne)
  have h_eq : (2 : ℝ) - Real.log n / Real.log n = 1 := by
    rw [div_self h_log_n_ne]; ring
  rw [h_eq] at h_kappa_tend
  exact h_kappa_tend

/-! ### Bridge to canonical `kappa` of [`Stats.Kappa.Basic`](Stats/Kappa/Basic.lean). -/

/-- **`Mn 1 σ = M1 σ`**.  The n-fold `Mn 1` over `Fin 1 → ℝ` reduces to
    the single-variable `M1` over `ℝ` via `IdentDistrib` (the σ-fold
    one-component product space pushes forward to the single Gaussian). -/
theorem Mn_one_eq_M1 (σ : ℝ) : Mn 1 σ = M1 σ := by
  unfold Mn M1
  simp only [Fin.sum_univ_one, Nat.cast_one]
  have h_id : IdentDistrib
      (fun ω : Ωspace 1 => |Xσ σ 0 ω - 1|) (fun ω : ℝ => |Y σ ω - 1|)
      (μn 1) (gaussianReal 0 1) :=
    (TailOptionPricing.LognormalIIdSetup.identDistrib_Xσ σ 0).comp
      (by fun_prop : Measurable (fun x : ℝ => |x - 1|))
  exact h_id.integral_eq

/-- **Canonical κ-form**: `κ(Mσ, 1, n)(σ) → 1` as `σ → ∞`, where `Mσ`
    is the σ-parametrised MAD oracle `k ↦ Mn k σ`.  Uses the
    [`kappa`](Stats/Kappa/Basic.lean) definition verbatim — paper Eq. 1
    instantiated on the lognormal family. -/
theorem kappa_lognormal_tendsto_one_canonical {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun σ : ℝ => TailOptionPricing.kappa (fun k => Mn k σ) 1 n)
      atTop (𝓝 1) := by
  refine (kappa_lognormal_tendsto_one hn).congr' ?_
  refine .of_forall fun σ => ?_
  show (2:ℝ) - Real.log n / (Real.log (Mn n σ) - Real.log (M1 σ))
      = TailOptionPricing.kappa (fun k => Mn k σ) 1 n
  simp only [TailOptionPricing.kappa, Nat.cast_one, Real.log_one, sub_zero,
    Mn_one_eq_M1]

end TailOptionPricing.LoulakisLognormal
