module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.IIdTriangle — iid triangle inequality for the MAD oracle.

  Discharges the structural-shell hypothesis `M(n) ≤ n · M(1)` of
  [`kappa_upper_bound_subadditive`](Stats/Kappa/Lognormal.lean#L60)
  from first principles: under iid + integrability of `X 0`, the
  partial-sum MAD `M(n) := 𝔼|S_n − 𝔼S_n|` satisfies

      `M(n) ≤ n · M(1)`,

  which combined with `kappa_upper_bound_subadditive` (already proved)
  yields the operational bound `κ_{1,n} ≤ 1` whenever `M(1) < M(n)`.

  Proof structure (paper Section "Lognormal Sums", Loulakis remark):

  1.  `|S_n − n·𝔼[X 0]| = |Σ_{i<n} (X i − 𝔼[X 0])| ≤ Σ_{i<n} |X i − 𝔼[X 0]|`
      pointwise (`Finset.abs_sum_le_sum_abs`).
  2.  Integrate; LHS = `M(n)`, RHS = `Σ_{i<n} ∫ |X i − 𝔼[X 0]| dμ`
      (`integral_finsetSum`).
  3.  For each `i`, `IdentDistrib.integral_eq` (composed with
      `fun x => |x − 𝔼[X 0]|`) gives
          `∫ |X i − 𝔼[X 0]| dμ = ∫ |X 0 − 𝔼[X 0]| dμ = M(1)`.
  4.  Sum: RHS = `n · M(1)`.

  This file is the *probabilistic* proof of the iid triangle bound on
  MAD.  Together with `kappa_upper_bound_subadditive` it closes one
  of the two structural shells in `Stats.Kappa.Lognormal`
  (todo5.md Phase A).
-/
public import Stats.Kappa.Lognormal
public import Mathlib.Probability.IdentDistrib

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace TailOptionPricing.IIdTriangle

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Setup: `madSum` — MAD of the iid partial sum.

    Given an iid family `X : ℕ → Ω → ℝ` (encoded externally by
    `IdentDistrib` of each `X i` against `X 0`) under a probability
    measure `μ`,
        `madSum μ X n := 𝔼|S_n − n·𝔼[X 0]|`,
    where `S_n := Σ_{i ∈ range n} X i`.  At `n = 1`, this is the
    paper's `M(1) = 𝔼|X 0 − 𝔼[X 0]|`. -/

/-- **MAD of the partial sum.**  `madSum μ X n := ∫ ω, |S_n ω − n·𝔼[X 0]| dμ`. -/
noncomputable def madSum (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, |(∑ i ∈ Finset.range n, X i ω) - (n : ℝ) * (∫ x, X 0 x ∂μ)| ∂μ

/-- **`madSum` at `n = 1`** is the paper's `M(1) = 𝔼|X 0 − 𝔼[X 0]|`. -/
theorem madSum_one (X : ℕ → Ω → ℝ) :
    madSum μ X 1 = ∫ ω, |X 0 ω - ∫ x, X 0 x ∂μ| ∂μ := by
  unfold madSum
  simp

/-! ### Integrability of the centred shifts. -/

/-- **Integrability of `|X i − 𝔼[X 0]|`** when `X i` is iid with `X 0`
    and `X 0` is integrable.  Uses `IdentDistrib.integrable_iff` to
    transport integrability from `X 0` to `X i`, then absoluteness. -/
private lemma integrable_abs_centred [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} (i : ℕ)
    (h_id : IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ) :
    Integrable (fun ω => |X i ω - ∫ x, X 0 x ∂μ|) μ := by
  -- Transport integrability of X 0 to X i.
  have hXi : Integrable (X i) μ := h_id.integrable_iff.mpr hX0
  -- |X i − c| is integrable since X i and the constant c are.
  have h_sub : Integrable (fun ω => X i ω - ∫ x, X 0 x ∂μ) μ :=
    hXi.sub (integrable_const _)
  exact h_sub.abs

/-! ### Pointwise triangle inequality. -/

/-- **Pointwise centred decomposition**: for any `ω`,
        `S_n(ω) − n·c = Σ_{i<n} (X i ω − c)`. -/
private lemma sum_centred_eq (X : ℕ → Ω → ℝ) (n : ℕ) (c : ℝ) (ω : Ω) :
    (∑ i ∈ Finset.range n, X i ω) - (n : ℝ) * c
      = ∑ i ∈ Finset.range n, (X i ω - c) := by
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_range, mul_comm]

/-- **Pointwise triangle inequality** for the centred sum. -/
private lemma abs_sum_centred_le (X : ℕ → Ω → ℝ) (n : ℕ) (c : ℝ) (ω : Ω) :
    |(∑ i ∈ Finset.range n, X i ω) - (n : ℝ) * c|
      ≤ ∑ i ∈ Finset.range n, |X i ω - c| := by
  rw [sum_centred_eq]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ### Identical distribution of `|X i − c|` and `|X 0 − c|`. -/

/-- **Integrals of `|X i − c|` agree across the iid family.**  Direct
    from `IdentDistrib.integral_eq` composed with the measurable map
    `fun x => |x − c|`. -/
private lemma integral_abs_centred_eq {X : ℕ → Ω → ℝ} (i : ℕ) (c : ℝ)
    (h_id : IdentDistrib (X i) (X 0) μ μ) :
    ∫ ω, |X i ω - c| ∂μ = ∫ ω, |X 0 ω - c| ∂μ := by
  have h_meas : Measurable (fun x : ℝ => |x - c|) := by
    fun_prop
  have h_comp : IdentDistrib (fun ω => |X i ω - c|) (fun ω => |X 0 ω - c|) μ μ :=
    h_id.comp h_meas
  exact h_comp.integral_eq

/-! ### Main theorem — `madSum μ X n ≤ n · madSum μ X 1`. -/

/-- **iid triangle inequality on MAD.**  For an iid family `X : ℕ → Ω → ℝ`
    with `X 0` integrable, the partial-sum MAD satisfies
        `M(n) ≤ n · M(1)`,
    where `M(n) := 𝔼|S_n − n·𝔼[X 0]|`.

    Proof (paper Loulakis remark, formalised):

    * pointwise: `|Σ (X i − 𝔼[X 0])| ≤ Σ |X i − 𝔼[X 0]|`;
    * integrate: `∫ Σ = Σ ∫` (integrability transports via `IdentDistrib`);
    * iid: `∫ |X i − 𝔼[X 0]| = ∫ |X 0 − 𝔼[X 0]|` for every `i`;
    * count: `Σ_{i<n} (∫ |X 0 − 𝔼[X 0]|) = n · 𝔼|X 0 − 𝔼[X 0]| = n · M(1)`. -/
theorem madSum_le_n_madSum_one
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ)
    (n : ℕ) :
    madSum μ X n ≤ (n : ℝ) * madSum μ X 1 := by
  set c : ℝ := ∫ x, X 0 x ∂μ with hc_def
  -- Step 1: rewrite madSum to expose the centred sum.
  have h_madSum_eq : madSum μ X n
      = ∫ ω, |∑ i ∈ Finset.range n, (X i ω - c)| ∂μ := by
    unfold madSum
    refine integral_congr_ae (.of_forall fun ω => ?_)
    dsimp only
    congr 1
    exact sum_centred_eq X n c ω
  -- Step 2: pointwise triangle inequality.
  have h_pointwise : ∀ ω,
      |∑ i ∈ Finset.range n, (X i ω - c)|
        ≤ ∑ i ∈ Finset.range n, |X i ω - c| := fun ω =>
    Finset.abs_sum_le_sum_abs _ _
  -- Step 3: integrability of each `|X i − c|`.
  have h_int_abs : ∀ i, Integrable (fun ω => |X i ω - c|) μ := fun i =>
    integrable_abs_centred i (h_id i) hX0
  -- Step 4: integrability of `Σ |X i − c|`.
  have h_int_sum : Integrable
      (fun ω => ∑ i ∈ Finset.range n, |X i ω - c|) μ :=
    integrable_finsetSum _ (fun i _ => h_int_abs i)
  -- Step 5: integrate the pointwise inequality.
  have h_int_le : ∫ ω, |∑ i ∈ Finset.range n, (X i ω - c)| ∂μ
      ≤ ∫ ω, ∑ i ∈ Finset.range n, |X i ω - c| ∂μ := by
    apply integral_mono_ae
    · -- LHS integrability: the centred sum is integrable, and abs of an
      -- integrable function is integrable.
      have h_int_centred : Integrable
          (fun ω => ∑ i ∈ Finset.range n, (X i ω - c)) μ := by
        apply integrable_finsetSum
        intros i _
        have hXi : Integrable (X i) μ := (h_id i).integrable_iff.mpr hX0
        exact hXi.sub (integrable_const _)
      exact h_int_centred.abs
    · exact h_int_sum
    · exact .of_forall h_pointwise
  -- Step 6: split the sum-integral via `integral_finsetSum`.
  have h_split : ∫ ω, ∑ i ∈ Finset.range n, |X i ω - c| ∂μ
      = ∑ i ∈ Finset.range n, ∫ ω, |X i ω - c| ∂μ :=
    integral_finsetSum _ (fun i _ => h_int_abs i)
  -- Step 7: each integral equals `madSum μ X 1`.
  have h_each : ∀ i ∈ Finset.range n,
      ∫ ω, |X i ω - c| ∂μ = madSum μ X 1 := by
    intros i _
    rw [madSum_one]
    exact integral_abs_centred_eq i c (h_id i)
  have h_sum_const : ∑ i ∈ Finset.range n, ∫ ω, |X i ω - c| ∂μ
      = (n : ℝ) * madSum μ X 1 := by
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
  -- Combine.
  rw [h_madSum_eq]
  calc ∫ ω, |∑ i ∈ Finset.range n, (X i ω - c)| ∂μ
      ≤ ∫ ω, ∑ i ∈ Finset.range n, |X i ω - c| ∂μ := h_int_le
    _ = ∑ i ∈ Finset.range n, ∫ ω, |X i ω - c| ∂μ := h_split
    _ = (n : ℝ) * madSum μ X 1 := h_sum_const

/-! ### Corollary discharging the κ-upper-bound shell. -/

/-- **κ-upper bound for an iid MAD oracle.**  Combines the iid
    triangle inequality (`madSum_le_n_madSum_one`) with the
    abstract κ-shell (`kappa_upper_bound_subadditive`,
    `Stats.Kappa.Lognormal`).  Under iid + integrability + the
    non-degeneracy hypotheses `0 < M(1) < M(n)`, the κ-metric is
    bounded above by `1`:

        `κ_{1, n} ≤ 1`.

    The non-degeneracy `M(1) < M(n)` is needed because the
    abstract shell requires both `M(1)` and `M(n)` to be on the
    same side of 1 (so that the log-ratio is well-signed); for
    iid sums of non-constant `X 0`, it's automatic and easy to
    check from any concrete distribution. -/
theorem kappa_upper_bound_iid
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ)
    {n : ℕ} (hn : 1 < n)
    (hM1_pos : 0 < madSum μ X 1)
    (hM_grow : madSum μ X 1 < madSum μ X n) :
    kappa (madSum μ X) 1 n ≤ 1 :=
  kappa_upper_bound_subadditive hn hM1_pos hM_grow
    (madSum_le_n_madSum_one h_id hX0 n)

/-- **Contrapositive of `kappa_upper_bound_iid`.** A single named hypothesis
test for the *presence* of bad points: if the observed empirical κ exceeds 1
(under the same growth/positivity assumptions used to define it), then the
sample is *not* iid with integrable distribution — without needing to identify
which observations are corrupt. -/
theorem not_iid_of_kappa_gt_one
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    {n : ℕ} (hn : 1 < n)
    (hM1_pos : 0 < madSum μ X 1)
    (hM_grow : madSum μ X 1 < madSum μ X n)
    (h_kappa : 1 < kappa (madSum μ X) 1 n) :
    ¬ ((∀ i, IdentDistrib (X i) (X 0) μ μ) ∧ Integrable (X 0) μ) :=
  by
  rintro ⟨h_id, hX0⟩
  have h_le := kappa_upper_bound_iid h_id hX0 hn hM1_pos hM_grow
  exact (not_lt.mpr h_le) h_kappa

end TailOptionPricing.IIdTriangle
