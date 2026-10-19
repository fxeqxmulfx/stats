module

/-
  Actual finite iid samples and their maximum, used in the sample-maximum
  construction of arXiv:2004.05894v1, "The Invisible Tail for a Power Law".
  The CDF formula holds for any real probability law, including atoms.
-/
public import Stats.Kappa.MaxIIdBound
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Topology.Order.Lattice

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The product law of `n` independent observations with marginal `ν`. -/
noncomputable def iidSampleLaw (n : ℕ) (ν : Measure ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => ν)

instance iidSampleLaw_probability (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidSampleLaw n ν) := by
  unfold iidSampleLaw
  infer_instance

/-- The observed maximum of a nonempty finite sample. -/
noncomputable def sampleMaximum {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

theorem sampleMaximum_le_iff {n : ℕ} [NeZero n] (x : Fin n → ℝ) (t : ℝ) :
    sampleMaximum x ≤ t ↔ ∀ i, x i ≤ t := by
  simp [sampleMaximum, Finset.sup'_le_iff]

theorem sampleMaximum_lt_iff {n : ℕ} [NeZero n] (x : Fin n → ℝ) (t : ℝ) :
    sampleMaximum x < t ↔ ∀ i, x i < t := by
  simp [sampleMaximum, Finset.sup'_lt_iff]

theorem le_sampleMaximum {n : ℕ} [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    x i ≤ sampleMaximum x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem measurable_sampleMaximum {n : ℕ} [NeZero n] :
    Measurable (sampleMaximum : (Fin n → ℝ) → ℝ) := by
  exact (Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => continuous_apply i)).measurable

/-- Independence follows from the actual product measure. -/
theorem iidSample_indep (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun (fun i (x : Fin n → ℝ) => x i) (iidSampleLaw n ν) :=
  iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
    (fun _ => measurable_id.aemeasurable)

/-- Each observed coordinate has the prescribed marginal law. -/
theorem iidSample_identDistrib (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (i : Fin n) :
    IdentDistrib (fun x : Fin n → ℝ => x i) id (iidSampleLaw n ν) ν := by
  refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_id, iidSampleLaw] using
    (measurePreserving_eval (fun _ : Fin n => ν) i).map_eq

/-- The genuine maximum's CDF is the `n`th power of its marginal CDF
(arXiv:2004.05894v1, sample-maximum construction before Proposition 1). -/
theorem sampleMaximum_cdf {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (t : ℝ) :
    (iidSampleLaw n ν).real {x | sampleMaximum x ≤ t} = (ν.real (Iic t)) ^ n := by
  simp_rw [sampleMaximum_le_iff]
  exact MaxIIdBound.prob_all_le_iid (Y := id) (iidSample_indep n ν)
    (iidSample_identDistrib n ν) t

/-- The strict lower-tail formula also handles atoms in the marginal law. -/
theorem sampleMaximum_cdf_lt {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (t : ℝ) :
    (iidSampleLaw n ν).real {x | sampleMaximum x < t} = (ν.real (Iio t)) ^ n := by
  have he : {x : Fin n → ℝ | sampleMaximum x < t} =
      Set.univ.pi (fun _ => Iio t) := by
    ext x
    simp [sampleMaximum_lt_iff]
  change ((Measure.pi (fun _ : Fin n => ν)) _).toReal = _
  rw [he, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- The genuine strict upper tail, complementary to the actual CDF. -/
theorem sampleMaximum_survival {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (t : ℝ) :
    (iidSampleLaw n ν).real {x | t < sampleMaximum x} = 1 - (ν.real (Iic t)) ^ n := by
  have he : {x : Fin n → ℝ | t < sampleMaximum x} =
      {x | sampleMaximum x ≤ t}ᶜ := by ext x; simp
  rw [he, measureReal_compl (measurableSet_le measurable_sampleMaximum measurable_const),
    probReal_univ, sampleMaximum_cdf]

example : sampleMaximum (fun i : Fin 2 => (i : ℝ)) = 1 := by
  apply le_antisymm
  · apply (sampleMaximum_le_iff _ _).mpr
    intro i
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  · have h := le_sampleMaximum (fun i : Fin 2 => (i : ℝ)) 1
    norm_num at h
    exact h

end TailOptionPricing
