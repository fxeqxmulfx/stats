module

/-
  Explicit fair sign-vector probability space, arXiv:1912.00277v2,
  Section II's 2^n branches and matrix T. Boolean true is overestimation,
  false is underestimation; index i=0 represents source epsilon_1.
-/
public import Stats.EpistemicUncertainty.LayerLaw
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

/-- Section II's actual one-layer fair choice, as an official finite
uniform probability measure on the two Boolean signs. -/
noncomputable def epistemicSignChoice : Measure Bool := Measure.uniformOfFinset univ

instance epistemicSignChoice_probability : IsProbabilityMeasure epistemicSignChoice := by
  constructor
  norm_num [epistemicSignChoice, Measure.uniformOfFinset_apply]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Each actual branch choice has probability one-half (Section II). -/
theorem epistemicSignChoice_singleton (b : Bool) : epistemicSignChoice {b} = 1 / 2 := by
  simp [epistemicSignChoice, Measure.uniformOfFinset_apply_singleton]

/-- Section II's actual uniform probability space of all 2^n sign
vectors. Independence of its coordinates is proved below. -/
noncomputable def epistemicSignLaw (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.uniformOfFinset univ

/-- Every complete n-layer sign vector has the actual printed weight
2^(-n), derived from the official uniform measure and the true cardinality. -/
theorem epistemicSignLaw_singleton (n : ℕ) (b : Fin n → Bool) :
    epistemicSignLaw n {b} = (1 / 2 : ENNReal) ^ n := by
  simp [epistemicSignLaw, Measure.uniformOfFinset_apply_singleton,
    ENNReal.inv_pow, div_eq_mul_inv]

/-- The actual uniform sign space is the product of its genuine fair
Boolean laws. Equality is checked on every singleton of this finite space. -/
theorem epistemicSignLaw_eq_pi (n : ℕ) :
    epistemicSignLaw n = Measure.pi (fun _ : Fin n => epistemicSignChoice) := by
  apply Measure.ext_of_singleton
  intro b
  rw [epistemicSignLaw_singleton, Measure.pi_singleton]
  simp only [epistemicSignChoice_singleton, prod_const, card_univ, Fintype.card_fin]

instance epistemicSignLaw_probability (n : ℕ) : IsProbabilityMeasure (epistemicSignLaw n) := by
  rw [epistemicSignLaw_eq_pi]
  infer_instance

/-- The actual n fair signs are mutually independent (Section II).
This is a whole-space independence statement, beyond equal branch weights. -/
theorem epistemicSignLaw_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => fun b : Fin n → Bool => b i) (epistemicSignLaw n) := by
  rw [epistemicSignLaw_eq_pi]
  exact iIndepFun_pi (X := fun _ : Fin n => fun b : Bool => b)
    (fun _ => measurable_id.aemeasurable)

/-- Every coordinate of the actual sign space has the genuine fair
Boolean law (Section II), independently of the other coordinates. -/
theorem epistemicSignLaw_map_coordinate (n : ℕ) (i : Fin n) :
    (epistemicSignLaw n).map (fun b : Fin n → Bool => b i) = epistemicSignChoice := by
  rw [epistemicSignLaw_eq_pi]
  simpa only [measure_univ, prod_const_one, one_smul] using
    Measure.pi_map_eval (μ := fun _ : Fin n => epistemicSignChoice) i

/-- Section II's printed multiplicative dispersion for a specific
sign vector, with source index i+1 represented by Fin n coordinate i. -/
noncomputable def epistemicSignScale (n : ℕ) (σ : ℝ) (ε : ℕ → ℝ) (b : Fin n → Bool) : ℝ :=
  σ * ∏ i : Fin n, if b i then 1 + ε i else 1 - ε i

/-- Every source-domain sign vector gives a positive Gaussian standard
deviation; the density model therefore has no zero-variance components. -/
theorem epistemicSignScale_pos (n : ℕ) {σ : ℝ} {ε : ℕ → ℝ} (b : Fin n → Bool)
    (hσ : 0 < σ) (hε : ∀ i < n, 0 ≤ ε i ∧ ε i < 1) :
    0 < epistemicSignScale n σ ε b := by
  apply mul_pos hσ
  apply prod_pos
  intro i hi
  have he := hε i i.isLt
  split <;> linarith

/-- Appending a sign adds exactly the source's last multiplicative
error layer (Section II), matching the actual recursive model's order. -/
theorem epistemicSignScale_snoc (n : ℕ) (σ : ℝ) (ε : ℕ → ℝ) (b : Fin n → Bool) (d : Bool) :
    epistemicSignScale (n + 1) σ ε (Fin.snoc b d) =
      epistemicSignScale n (σ * (if d then 1 + ε n else 1 - ε n)) ε b := by
  unfold epistemicSignScale
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  ring

/-- Section II's displayed M^3 reverses its displayed T rows: T's first
row is all +1, but the printed M_1^3 uses all minus signs. Following
M_i=product(1+epsilon_j*T_ij), its first row is all plus signs. At
epsilon_j=1/2 it is 27/8 rather than 1/8; the summed density is unaffected. -/
theorem epistemic_sign_matrix_first_row_counterexample :
    epistemicSignScale 3 1 (fun _ => (1 / 2 : ℝ)) (fun _ => true) ≠
      (1 - (1 / 2 : ℝ)) ^ 3 := by
  norm_num [epistemicSignScale, Fin.prod_univ_castSucc]

/-- Reindex all source sign branches by their last fair sign and
preceding vector. This identity applies to actual measure-valued sums. -/
theorem epistemicSign_sum_snoc {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n + 1) → Bool) → M) :
    ∑ b, f b = (∑ b : Fin n → Bool, f (Fin.snoc b true)) +
      ∑ b : Fin n → Bool, f (Fin.snoc b false) := by
  calc ∑ b, f b = ∑ p : Bool × (Fin n → Bool), f ((Fin.snocEquiv (fun _ => Bool)) p) :=
      (Equiv.sum_comp (Fin.snocEquiv (fun _ => Bool)) f).symm
    _ = _ := by rw [Fintype.sum_prod_type, Fintype.sum_bool]; rfl

example : IsProbabilityMeasure (epistemicSignLaw 2) := inferInstance

example : epistemicSignLaw 2 {fun _ => true} = 1 / 4 := by
  rw [epistemicSignLaw_singleton]
  norm_num [← ENNReal.inv_pow]

example : iIndepFun (fun i : Fin 2 => fun b : Fin 2 → Bool => b i) (epistemicSignLaw 2) :=
  epistemicSignLaw_independent _

example : (epistemicSignLaw 2).map (fun b : Fin 2 → Bool => b 0) = epistemicSignChoice :=
  epistemicSignLaw_map_coordinate _ _

example (b : Fin 2 → Bool) : 0 < epistemicSignScale 2 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i) b := by
  apply epistemicSignScale_pos _ _ (by norm_num)
  intro i hi
  interval_cases i <;> norm_num

example : epistemicSignScale 2 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)
    (fun _ => true) = 15 / 4 := by
  norm_num [epistemicSignScale, Fin.prod_univ_castSucc]

#print axioms epistemicSignLaw_eq_pi
#print axioms epistemicSignLaw_independent
#print axioms epistemicSignScale_pos
#print axioms epistemic_sign_matrix_first_row_counterexample

end TailOptionPricing
