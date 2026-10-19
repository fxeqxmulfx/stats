module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.TableI — closed-form κ₁ for general distributions
  (paper Table I, rows 1, 3, 4, 5).

  Following the same definitional convention as
  `Stats.Kappa.GaussianSwitchingMean` and
  `Stats.Kappa.LognormalCumulants`, we take each row's M(2)/M(1)
  ratio as a primitive expression: the underlying MAD integrals
  against the respective densities are not formalised (each would
  be a multi-hundred-line probability-theory exercise blocked on
  Mathlib infrastructure).  For every row we

    1. Define the closed-form `…Ratio` (M(2)/M(1)).
    2. Build an MAD oracle `tableIMAD Ratio` with `M(1) = 1`,
       `M(2) = Ratio`.
    3. Define `…Kappa` as the paper-printed κ₁ closed form.
    4. Prove `kappa oracle 1 2 = …Kappa` by direct algebra.

  Distributions covered (paper Table I):

  * `kappa_studentT_general` — Student T tail index `α > 1`
    (row 1).  Uses Mathlib `Real.Gamma`.
  * `kappa_pareto_general` — Pareto tail index `α > 1`
    (row 3).  Uses the incomplete Beta function (defined here as a
    primitive `incompleteBeta`; Mathlib `v4.29.1` has only the
    *complete* Beta `Complex.betaIntegral`).
  * `kappa_normal_switching_variance` — Normal `(μ, σ²)` with
    switching variance `σ²·a` w.p. `p` (row 4).  Paper footnote
    (b): "switching both variance and mean … can produce negative
    values for kappa".
  * `kappa_lognormal_explicit` — Lognormal `(μ, σ²)` approximation
    (row 5).  Uses `Real.erf` (`Stats.BlackScholes.Erfc`); the
    paper itself qualifies this row as `≈`.

  Row 2 (Exponential/Gamma) lives in `Stats.Kappa.Exponential`.

  See `Stats/Kappa.lean` for the umbrella module.
-/
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Stats.BlackScholes.Erfc
public import Stats.Kappa.Basic

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing

/-! ## Generic `(1, R)`-calibrated MAD oracle. -/

/-- **`(1, R)`-calibrated MAD oracle.**  Returns `1` at `n = 1`,
    the closed-form ratio `R = M(2)/M(1)` at `n = 2`, and `0`
    elsewhere.  At the `(1, 2)` baseline the κ-metric reduces to
    the bare form `2 − log(2)/log(R)` (see `kappa_tableIMAD_bare`). -/
noncomputable def tableIMAD (R : ℝ) : ℕ → ℝ
  | 1 => 1
  | 2 => R
  | _ => 0

/-- **Bare-form κ identity for `tableIMAD`.**  Pure algebraic
    identity: `kappa (tableIMAD R) 1 2 = 2 − log(2)/log(R)` for
    every `R : ℝ`.  No positivity on `R` is needed: Mathlib's
    `Real.log` is `0` outside the positive reals by convention,
    so the identity holds syntactically. -/
private lemma kappa_tableIMAD_bare (R : ℝ) :
    kappa (tableIMAD R) 1 2 = 2 - Real.log 2 / Real.log R := by
  unfold kappa
  have hM1 : tableIMAD R 1 = 1 := rfl
  have hM2 : tableIMAD R 2 = R := rfl
  rw [hM1, hM2]
  push_cast
  rw [Real.log_one, sub_zero, sub_zero]

/-! ## Student T closed-form κ₁ (Table I row 1). -/

/-- **Student T inner factor** (paper Table I row 1, expression
    inside the `log(...)`):
        `T_StuT(α) := 2^(2 − α) · Γ(α − 1/2) / Γ(α/2)²`. -/
noncomputable def studentTInner (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 - α) * Real.Gamma (α - 1/2) / Real.Gamma (α / 2) ^ 2

/-- **Student T M(2)/M(1) ratio** (calibration: `M(1) = 1`,
    `M(2) = √π · T_StuT(α)`).  Chosen so the κ identity below
    aligns with paper Table I row 1 verbatim. -/
noncomputable def studentTRatio (α : ℝ) : ℝ :=
  Real.sqrt Real.pi * studentTInner α

/-- **Student T closed-form κ₁** (paper Table I row 1, verbatim):
        `κ₁ = 2 − 2·log(2) / (2·log(T_StuT(α)) + log(π))`. -/
noncomputable def studentTKappa (α : ℝ) : ℝ :=
  2 - 2 * Real.log 2 /
    (2 * Real.log (studentTInner α) + Real.log Real.pi)

/-- **Student T κ₁ identity** (paper Table I row 1).  Under
    positivity of the inner factor `T_StuT(α)` and a
    non-degeneracy condition on the paper-printed denominator,
    the abstract κ-metric on `tableIMAD (studentTRatio α)` at
    the `(1, 2)` baseline equals the paper's closed form
    `studentTKappa α`.

    Proof sketch.  The bare-form identity gives
        `kappa (tableIMAD R) 1 2 = 2 − log(2)/log(R)`.
    Rewriting `log(R) = log(√π · T) = (1/2)·log(π) + log(T)`,
    multiplying numerator and denominator by `2`, and matching
    the paper's printed denominator `2·log(T) + log(π)`. -/
theorem kappa_studentT_general {α : ℝ}
    (hT : 0 < studentTInner α)
    (h_den : 2 * Real.log (studentTInner α) + Real.log Real.pi ≠ 0) :
    kappa (tableIMAD (studentTRatio α)) 1 2 = studentTKappa α := by
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_sqrtπ_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ_pos
  -- Paper's denominator equals `2 · log R`:
  have h_2log_R : 2 * Real.log (studentTRatio α)
      = 2 * Real.log (studentTInner α) + Real.log Real.pi := by
    unfold studentTRatio
    rw [Real.log_mul h_sqrtπ_pos.ne' hT.ne', Real.log_sqrt hπ_pos.le]
    ring
  have h_logR_ne : Real.log (studentTRatio α) ≠ 0 := by
    intro h
    apply h_den
    have h2 := h_2log_R
    rw [h, mul_zero] at h2
    linarith
  rw [kappa_tableIMAD_bare]
  unfold studentTKappa
  rw [← h_2log_R]
  -- Goal: `2 − log(2)/log(R) = 2 − 2·log(2)/(2·log(R))`.
  field_simp

/-! ## Pareto closed-form κ₁ (Table I row 3).

    Paper Table I footnote (a): `B_z(a, b) := ∫_0^z t^(a−1)
    (1 − t)^(b−1) dt` is the incomplete Beta function.  Mathlib
    `v4.29.1` provides only the *complete* Beta function
    (`Complex.betaIntegral` on `[0, 1]`); the incomplete version
    is defined here as a primitive. -/

/-- **Incomplete Beta function** (real, primitive form):
        `B_z(a, b) := ∫_0^z t^(a − 1) · (1 − t)^(b − 1) dt`.
    For `a > 0`, `b > 0`, `z ∈ [0, 1]` the integral converges;
    outside that regime Lean's `intervalIntegral` returns `0`
    when the integrand is not integrable, consistent with the
    extended-real conventions in the rest of the κ-metric
    formalisation. -/
noncomputable def incompleteBeta (z a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, t ^ (a - 1) * (1 - t) ^ (b - 1)

/-- **Pareto integrand** (paper Table I row 3, body of the
    `∫_0^(2/(α − 1))` integral, verbatim from arXiv LaTeX source
    `kappa-n-final.tex` line 209):
        `−2 α² · (y + 2)^(−2α − 1) · (2/(α − 1) − y)
              · ( B_{1/(y+2)}(−α, 1−α) − B_{(y+1)/(y+2)}(−α, 1−α) )`.

    Audit 2026-05-13 pass 5 fix: previous transcriptions had three
    independent errors — additive bracket instead of multiplicative,
    wrong second `B` subscript (`(2/(α−1)−y)/(y+2)` instead of
    `(y+1)/(y+2)`), and wrong sign between the `B` terms.  All
    corrected per LaTeX. -/
noncomputable def paretoIntegrand (α y : ℝ) : ℝ :=
  -2 * α ^ 2 * (y + 2) ^ (-2 * α - 1) * (2 / (α - 1) - y) *
    (incompleteBeta (1 / (y + 2)) (-α) (1 - α)
      - incompleteBeta ((y + 1) / (y + 2)) (-α) (1 - α))

/-- **Pareto M(2)/M(1) ratio** (paper Table I row 3, verbatim from
    LaTeX source):
        `R_Par(α) := (α − 1)^(2 − α) · α^(α − 1) · ∫_0^(2/(α − 1))
                       paretoIntegrand α y dy`.

    Audit 2026-05-13 pass 5 fix: previous transcription had outer
    factor `((α−1)^(2−α) · α^(−α))^α` with spurious outer `^α` and
    wrong exponent on `α` (`−α` instead of `α−1`).  Corrected per
    LaTeX. -/
noncomputable def paretoRatio (α : ℝ) : ℝ :=
  (α - 1) ^ (2 - α) * α ^ (α - 1) *
    ∫ y in (0 : ℝ)..(2 / (α - 1)), paretoIntegrand α y

/-- **Pareto closed-form κ₁** (paper Table I row 3):
        `κ₁ = 2 − log(2) / log(R_Par(α))`. -/
noncomputable def paretoKappa (α : ℝ) : ℝ :=
  2 - Real.log 2 / Real.log (paretoRatio α)

/-- **Pareto κ₁ identity** (paper Table I row 3).  Direct
    instance of the bare-form κ identity on `tableIMAD`. -/
theorem kappa_pareto_general (α : ℝ) :
    kappa (tableIMAD (paretoRatio α)) 1 2 = paretoKappa α := by
  rw [kappa_tableIMAD_bare]
  rfl

/-! ## Normal switching-variance κ₁ (Table I row 4).

    Verbatim paper Table I row 4 (arXiv LaTeX source line 213).  Define
    recurring sub-expressions
        `R := √(ap/(p−1) + σ²)`,
        `Q := √(2a(1/(p−1) + 2) + 4σ²)`,
        `S := √(a + σ²)`;
    the M(2)/M(1) ratio is
        `√2 · (R + p·(−2R + p·(R − Q + S) + Q)) / (p·S − (p−1)·R)`.

    Audit 2026-05-13 pass 5: transcribed from arXiv LaTeX after
    earlier pass-3 numerical investigation suggested the formula was
    broken (negative radicand `ap/(p−1) + σ² < 0` for `p ∈ (0, 1)` and
    `a > σ²(1−p)/p`).  Restored paper-verbatim form; the
    parameter-range issue may indicate a non-standard convention for
    `p` in the original Mathematica derivation (e.g. `p > 1` rather
    than `p ∈ (0, 1)`).  Numerical comparison against the derived
    `(p²·√(2a) + 2p(1−p)·√(a+1) + (1−p)²·√2) / (p·√a + (1−p))` MAD
    ratio of the "variance σ²·a w.p. p, variance σ² w.p. 1−p" mixture
    shows partial agreement (matches to 4 dp at `σ=1, a=0.5, p=0.3`,
    disagrees elsewhere); the convention mismatch is the most likely
    explanation.

    Paper footnote (b): the row "can produce negative values for kappa"
    when switching both variance *and* mean — addressed by
    `Stats.Kappa.GaussianSwitchingMean` (Eq. 18). -/

/-- **Normal switching-variance M(2)/M(1) ratio** (paper Table I row 4,
    verbatim from LaTeX source).
    `R := √(ap/(p−1) + σ²)`, `Q := √(2a(1/(p−1) + 2) + 4σ²)`,
    `S := √(a + σ²)`;
        `ratio = √2 · (R + p·(−2R + p·(R − Q + S) + Q)) / (p·S − (p−1)·R)`.

    See module docstring for parameter-range caveat. -/
noncomputable def normalSwitchingVarianceRatio (σ a p : ℝ) : ℝ :=
  let R := Real.sqrt (a * p / (p - 1) + σ ^ 2)
  let Q := Real.sqrt (2 * a * (1 / (p - 1) + 2) + 4 * σ ^ 2)
  let S := Real.sqrt (a + σ ^ 2)
  Real.sqrt 2 *
    (R + p * (-2 * R + p * (R - Q + S) + Q)) /
    (p * S - (p - 1) * R)

/-- **Normal switching-variance closed-form κ₁** (paper Table I row 4):
        `κ₁ = 2 − log(2) / log(normalSwitchingVarianceRatio σ a p)`. -/
noncomputable def normalSwitchingVarianceKappa (σ a p : ℝ) : ℝ :=
  2 - Real.log 2 / Real.log (normalSwitchingVarianceRatio σ a p)

/-- **Normal switching-variance κ₁ identity** (paper Table I row 4).
    Direct instance of the bare-form κ identity on `tableIMAD`. -/
theorem kappa_normal_switching_variance (σ a p : ℝ) :
    kappa (tableIMAD (normalSwitchingVarianceRatio σ a p)) 1 2
      = normalSwitchingVarianceKappa σ a p := by
  rw [kappa_tableIMAD_bare]
  rfl

/-! ## Lognormal explicit κ₁ (Table I row 5).

    The paper writes Table I row 5 with `≈` rather than `=`: the
    formula is the leading-order erf approximation to the exact
    (intractable) lognormal MAD.  In the σ → 0 limit this proxy
    tends to the Gaussian κ = 0; in the σ → ∞ limit it tends to
    the Cauchy κ = 1.  See `Stats.Kappa.LognormalCumulants` for
    the small-σ cumulant proxy. -/

/-- **Lognormal explicit M(n)/M(1) ratio** (paper Table I row 5,
    verbatim from arXiv LaTeX source `kappa-n-final.tex` line 215):
        `R_LogN(σ, n) := n · erf(√(log((n + e^(σ²) − 1)/n)) / (2√2))
                       / erf(σ / (2√2))`.

    The leading `n` factor is the Loulakis ceiling `M(n)/M(1) ≤ n`
    (paper Section IV-B); the erf ratio is the leading-order correction.
    For `n = 2`, the inner argument simplifies to `log((e^(σ²) + 1)/2)`
    and the ratio matches paper Table I row 5 verbatim.

    Audit 2026-05-13 pass 5: the leading `n` factor was previously
    omitted; restored to match the paper formula.  Without the `n`
    factor, `kappa_lognormal_explicit` at `(1, 2)` baseline gave
    `2 − log(2)/log(erf(...)/erf(...))` rather than the paper's
    `2 − log(2)/log(2·erf(...)/erf(...))`. -/
noncomputable def lognormalExplicitRatio (σ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) *
    Real.erf (Real.sqrt
        (Real.log (((n : ℝ) + Real.exp (σ ^ 2) - 1) / (n : ℝ)))
        / (2 * Real.sqrt 2))
    / Real.erf (σ / (2 * Real.sqrt 2))

/-- **Lognormal explicit closed-form κ₁** (paper Table I row 5):
        `κ₁ ≈ 2 − log(2) / log(R_LogN(σ, n))`. -/
noncomputable def lognormalExplicitKappa (σ : ℝ) (n : ℕ) : ℝ :=
  2 - Real.log 2 / Real.log (lognormalExplicitRatio σ n)

/-- **Lognormal explicit κ₁ identity** (paper Table I row 5).
    Direct instance of the bare-form κ identity on `tableIMAD`. -/
theorem kappa_lognormal_explicit (σ : ℝ) (n : ℕ) :
    kappa (tableIMAD (lognormalExplicitRatio σ n)) 1 2
      = lognormalExplicitKappa σ n := by
  rw [kappa_tableIMAD_bare]
  rfl

/-! ## κ*_{1, n} upper bound (paper Appendix B, todo B.2.4).

    The `κ*_{1, n}` form is the (1, n)-baseline analogue of Table I row 5,
    using the M(n)/M(1) ratio
        `n · erf(√(log((n + e^(σ²) − 1)/n)) / (2√2)) / erf(σ / (2√2))`
    which is the leading-order erf-approximation to the exact, intractable
    lognormal MAD ratio at sample size `n`.  The factor `n` out front is
    the Loulakis ceiling `M(n)/M(1) ≤ n`, saturated up to the erf-ratio
    correction.

    Paper closed form (Appendix B):
        `κ*_{1, n} = 2 − log(n) /
                     log( n · erf(√(log((n + e^(σ²) − 1)/n)) / (2√2))
                          / erf(σ / (2√2)) )`. -/

/-- **Lognormal κ*_{1, n} closed form** (paper Appendix B, todo B.2.4).
    `lognormalExplicitRatio σ n` already includes the leading `n` factor
    (paper formula: `n · erf(...) / erf(...)`), so the κ* form is the
    bare-form κ at the `(1, n)` baseline applied to that ratio. -/
noncomputable def lognormalKappaStar (σ : ℝ) (n : ℕ) : ℝ :=
  2 - Real.log n / Real.log (lognormalExplicitRatio σ n)

/-- **Lognormal κ*_{1, n} matches paper formula** (paper Appendix B).
    The closed form `lognormalKappaStar σ n` equals
        `2 − log(n) / log( n · erf(√(log((n + e^(σ²) − 1)/n)) / (2√2))
                            / erf(σ / (2√2)) )`
    as printed in the paper. -/
theorem lognormal_kappa_star (σ : ℝ) (n : ℕ) :
    lognormalKappaStar σ n
      = 2 - Real.log n /
            Real.log ((n : ℝ) *
                Real.erf (Real.sqrt
                    (Real.log (((n : ℝ) + Real.exp (σ ^ 2) - 1) / (n : ℝ)))
                    / (2 * Real.sqrt 2))
              / Real.erf (σ / (2 * Real.sqrt 2))) := by
  unfold lognormalKappaStar lognormalExplicitRatio
  rfl

/-- **`(1, n)`-calibrated MAD oracle realising `κ*_{1, n}`.**  Builds the
    oracle `M(1) = 1`, `M(n) = lognormalExplicitRatio σ n` (which
    already includes the `n` factor per paper Table I row 5). -/
noncomputable def lognormalStarMAD (σ : ℝ) (n : ℕ) : ℕ → ℝ :=
  fun k => if k = 1 then 1
           else if k = n then lognormalExplicitRatio σ n
           else 0

/-- **κ*_{1, n} identity on `lognormalStarMAD`** (paper Appendix B).
    Combining the algebraic closed form with the κ-metric definition,
    the κ-metric on the lognormal-star MAD oracle at the `(1, n)` baseline
    equals `lognormalKappaStar σ n`. -/
theorem kappa_lognormal_star (σ : ℝ) {n : ℕ} (hn : 1 < n) :
    kappa (lognormalStarMAD σ n) 1 n = lognormalKappaStar σ n := by
  unfold kappa lognormalStarMAD lognormalKappaStar
  have hn_ne_one : n ≠ 1 := by omega
  simp only [ite_true, ite_eq_right hn_ne_one]
  push_cast
  rw [Real.log_one, sub_zero, sub_zero]

end TailOptionPricing
