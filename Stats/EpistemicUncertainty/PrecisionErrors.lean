module

/-
  Genuine iid signed errors for the precision argument,
  arXiv:1912.00277v2, Section V, Eqs. error1–errorn. The infinite
  probability space has independent fair signs. Each error has actual
  mean zero, finite second moment and variance epsilon squared.
-/
public import Stats.EpistemicUncertainty.SignLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.HasLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

/-- Section V's signed mean-zero multiplicative error from a fair sign. -/
def epistemicErrorSign (ε : ℝ) (b : Bool) : ℝ := if b then ε else -ε

/-- Actual two-point error distribution, independently normalized
before evaluating its moments (Section V). -/
noncomputable def epistemicErrorLaw (ε : ℝ) : Measure ℝ :=
  equalMixture (Measure.dirac ε) (Measure.dirac (-ε))

instance epistemicErrorLaw_probability (ε : ℝ) : IsProbabilityMeasure (epistemicErrorLaw ε) := by
  unfold epistemicErrorLaw
  infer_instance

theorem epistemicErrorLaw_integrable (ε : ℝ) (f : ℝ → ℝ) : Integrable f (epistemicErrorLaw ε) := by
  rw [epistemicErrorLaw, equalMixture_integrable_iff]
  exact ⟨integrable_dirac (by finiteness), integrable_dirac (by finiteness)⟩

/-- The actual signed error has mean zero, as assumed in Section V. -/
theorem epistemicErrorLaw_mean (ε : ℝ) : (∫ e : ℝ, e ∂epistemicErrorLaw ε) = 0 := by
  rw [epistemicErrorLaw, equalMixture_integral (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp

/-- The true error variance is epsilon squared, with independent L1
of the squared error; positive epsilon supplies the source's lower bound. -/
theorem epistemicErrorLaw_variance (ε : ℝ) :
    variance (fun e : ℝ => e) (epistemicErrorLaw ε) = ε ^ 2 := by
  have hm : AEMeasurable (fun e : ℝ => e) (epistemicErrorLaw ε) := measurable_id.aemeasurable
  rw [variance_eq_integral hm, epistemicErrorLaw_mean]
  simp only [sub_zero]
  rw [epistemicErrorLaw, equalMixture_integral (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp only [integral_dirac, neg_sq]
  ring

/-- The actual fair Boolean choice generates precisely the prescribed
two-point mean-zero error law (Section V). -/
theorem epistemicSignChoice_map_error (ε : ℝ) :
    epistemicSignChoice.map (epistemicErrorSign ε) = epistemicErrorLaw ε := by
  have hm : Measurable (epistemicErrorSign ε) := measurable_of_countable _
  rw [epistemicSignChoice, Measure.uniformOfFinset, Measure.map_finset_sum hm.aemeasurable]
  simp_rw [Measure.map_smul _ hm.aemeasurable, Measure.map_dirac]
  simp [epistemicErrorSign, epistemicErrorLaw, equalMixture, div_eq_mul_inv]

/-- One genuine infinite product probability space for all of Section
V's iid errors, rather than unrelated finite counterexample populations. -/
noncomputable def epistemicInfiniteSignLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => epistemicSignChoice)

instance epistemicInfiniteSignLaw_probability : IsProbabilityMeasure epistemicInfiniteSignLaw := by
  unfold epistemicInfiniteSignLaw
  infer_instance

theorem epistemicInfiniteSignLaw_independent :
    iIndepFun (fun i : ℕ => fun ω : ℕ → Bool => ω i) epistemicInfiniteSignLaw :=
  iIndepFun_infinitePi (X := fun _ : ℕ => fun b : Bool => b) (fun _ => measurable_id)

/-- The actual first n signs of the infinite process have exactly the
previously constructed uniform independent sign-vector law. -/
theorem epistemicInfiniteSignLaw_prefix (n : ℕ) :
    epistemicInfiniteSignLaw.map (fun ω : ℕ → Bool => fun i : Fin n => ω i) = epistemicSignLaw n := by
  have hi : iIndepFun (fun i : Fin n => fun ω : ℕ → Bool => ω i) epistemicInfiniteSignLaw :=
    iIndepFun.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
      epistemicInfiniteSignLaw_independent
  have h := iIndepFun.map_fun_eq_pi_map
    (f := fun i : Fin n => fun ω : ℕ → Bool => ω i)
    (fun i : Fin n => (measurable_pi_apply (i : ℕ)).aemeasurable) hi
  simp_rw [epistemicInfiniteSignLaw, Measure.infinitePi_map_eval] at h
  exact h.trans (epistemicSignLaw_eq_pi n).symm

/-- Actual error coordinate on the single infinite probability space,
with index zero representing the source's first error. -/
def epistemicErrorVariable (ε : ℝ) (i : ℕ) (ω : ℕ → Bool) : ℝ := epistemicErrorSign ε (ω i)

theorem epistemicErrorVariable_hasLaw (ε : ℝ) (i : ℕ) :
    HasLaw (epistemicErrorVariable ε i) (epistemicErrorLaw ε) epistemicInfiniteSignLaw := by
  have hm : Measurable (epistemicErrorSign ε) := measurable_of_countable _
  constructor
  · exact (hm.comp (measurable_pi_apply i)).aemeasurable
  · have h := congrArg (fun ν : Measure Bool => ν.map (epistemicErrorSign ε))
      (Measure.infinitePi_map_eval (fun _ : ℕ => epistemicSignChoice) i)
    rw [Measure.map_map hm (measurable_pi_apply i), epistemicSignChoice_map_error] at h
    exact h

/-- The actual error sequence is mutually independent (Section V). -/
theorem epistemicErrorVariable_independent (ε : ℝ) :
    iIndepFun (epistemicErrorVariable ε) epistemicInfiniteSignLaw :=
  epistemicInfiniteSignLaw_independent.comp (fun _ => epistemicErrorSign ε)
    (fun _ => measurable_of_countable _)

theorem epistemicErrorVariable_mean (ε : ℝ) (i : ℕ) :
    (∫ ω : ℕ → Bool, epistemicErrorVariable ε i ω ∂epistemicInfiniteSignLaw) = 0 :=
  (epistemicErrorVariable_hasLaw ε i).integral_eq.trans (epistemicErrorLaw_mean ε)

theorem epistemicErrorVariable_integrable_sq (ε : ℝ) (i : ℕ) :
    Integrable (fun ω : ℕ → Bool => (epistemicErrorVariable ε i ω) ^ 2) epistemicInfiniteSignLaw :=
  (epistemicErrorVariable_hasLaw ε i).integrable_fun_comp
    (epistemicErrorLaw_integrable ε (fun e => e ^ 2))

theorem epistemicErrorVariable_variance (ε : ℝ) (i : ℕ) :
    variance (epistemicErrorVariable ε i) epistemicInfiniteSignLaw = ε ^ 2 := by
  rw [(epistemicErrorVariable_hasLaw ε i).variance_eq]
  exact epistemicErrorLaw_variance ε

theorem epistemicErrorVariable_abs (ε : ℝ) (i : ℕ) (ω : ℕ → Bool) :
    |epistemicErrorVariable ε i ω| = |ε| := by
  unfold epistemicErrorVariable epistemicErrorSign
  split <;> simp

example : iIndepFun (epistemicErrorVariable (1 / 100)) epistemicInfiniteSignLaw :=
  epistemicErrorVariable_independent _

example (i : ℕ) : (∫ ω : ℕ → Bool, epistemicErrorVariable (1 / 100) i ω
    ∂epistemicInfiniteSignLaw) = 0 := epistemicErrorVariable_mean _ _

example (i : ℕ) : variance (epistemicErrorVariable (1 / 100) i) epistemicInfiniteSignLaw =
    1 / 10000 := by rw [epistemicErrorVariable_variance]; norm_num

#print axioms epistemicInfiniteSignLaw_prefix
#print axioms epistemicErrorVariable_hasLaw
#print axioms epistemicErrorVariable_independent
#print axioms epistemicErrorVariable_variance

end TailOptionPricing
