/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.PearsonIV — Pearson IV approximation (paper Section IV-B-3).

  The Pearson IV class is the unimodal solution family of the ODE
      f'(x) · (b₀ + b₁ x + b₂ x²) = −(a₀ + a₁ x) · f(x).
  Paper Section IV-B-3 uses Pearson IV as a tractable proxy for the
  lognormal MAD: matching the first four moments of the iid lognormal
  sum determines `(a₀, b₀, b₁, b₂)` (paper's box of formulas, Eq. 12),
  and the Pearson IV MAD has the closed form (Eq. 13)
      E[|X − m|] = 2 · (b₀ + b₁ m + b₂ m²) · f(m) / (a₁ − 2 b₂).

  Theorems delivered:

  * `IsPearsonIV` — ODE-based definition of the Pearson IV class
    (paper Sec. IV-B-3, todo B.3.1).
  * `pearsonIV_mad_eq` — MAD closed form Eq. 13, derived from the ODE
    via integration by parts on `Q(x) · f(x)` (todo B.3.2).  The
    integration-by-parts intermediates are taken as hypotheses, in the
    pattern of `Stats.Kappa.CubicStudentAsymptotic`
    (`incompleteGamma_laplace_asymptotic`) — the algebraic content is
    proven; the analytic IBP is shelled.
  * `pearsonIVLognormalMatch` — explicit `(a₀, b₀, b₁, b₂)` as functions
    of `(n, σ)` matching the lognormal iid sum's first four cumulants
    (todo B.3.3).

  See `Stats/Kappa.lean` for the umbrella module.
-/
import Stats.Kappa.LognormalCumulants

open Real Set Filter Topology

namespace TailOptionPricing

/-! ## Pearson IV class (paper Section IV-B-3, todo B.3.1). -/

/-- **Pearson IV quadratic denominator** `Q(x) := b₀ + b₁ x + b₂ x²`. -/
noncomputable def pearsonIVQuad (b₀ b₁ b₂ x : ℝ) : ℝ :=
  b₀ + b₁ * x + b₂ * x ^ 2

/-- **Pearson IV linear numerator** `L(x) := a₀ + a₁ x`. -/
noncomputable def pearsonIVLin (a₀ a₁ x : ℝ) : ℝ :=
  a₀ + a₁ * x

/-- **Pearson IV class (paper Section IV-B-3, todo B.3.1).**  A
    differentiable function `f : ℝ → ℝ` is in the Pearson IV class with
    parameters `(a₀, a₁, b₀, b₁, b₂)` iff it satisfies the defining ODE
        `f'(x) · (b₀ + b₁ x + b₂ x²) = −(a₀ + a₁ x) · f(x)`
    for every `x : ℝ`.  Encoded as a predicate on the function `f` and
    the five real parameters; reproduces Pearson's classical defining
    ODE.  Special cases include Gaussian (`b₁ = b₂ = 0`, `a₁ > 0`),
    Student T, and the unimodal asymmetric class used as the lognormal
    proxy in Section IV-B-3. -/
structure IsPearsonIV (f : ℝ → ℝ) (a₀ a₁ b₀ b₁ b₂ : ℝ) : Prop where
  differentiable : Differentiable ℝ f
  ode : ∀ x, deriv f x * pearsonIVQuad b₀ b₁ b₂ x
    = -(pearsonIVLin a₀ a₁ x) * f x

/-- **Pearson IV product-rule identity.**  For any Pearson IV density
    `f`, the auxiliary function `g(x) := Q(x) · f(x)` (with `Q := b₀ +
    b₁ x + b₂ x²`) has derivative
        `g'(x) = (b₁ − a₀) · f(x) + (2 b₂ − a₁) · x · f(x)`.
    Foundational for the IBP-based MAD derivation: integrating the
    identity over a half-line and using boundary vanishing yields the
    Pearson IV MAD formula (Eq. 13). -/
theorem pearsonIV_aux_deriv {f : ℝ → ℝ} {a₀ a₁ b₀ b₁ b₂ : ℝ}
    (hf : IsPearsonIV f a₀ a₁ b₀ b₁ b₂) (x : ℝ) :
    deriv (fun y => pearsonIVQuad b₀ b₁ b₂ y * f y) x
      = (b₁ - a₀) * f x + (2 * b₂ - a₁) * x * f x := by
  -- Build `HasDerivAt` for `Q(y) := b₀ + b₁ y + b₂ y²` at x.
  have h_id : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h_b1y : HasDerivAt (fun y : ℝ => b₁ * y) b₁ x := by
    simpa using h_id.const_mul b₁
  have h_y2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using h_id.pow 2
  have h_b2y2 : HasDerivAt (fun y : ℝ => b₂ * y ^ 2) (b₂ * (2 * x)) x :=
    h_y2.const_mul b₂
  have h_const : HasDerivAt (fun _ : ℝ => b₀) 0 x := hasDerivAt_const x b₀
  have h_lin : HasDerivAt (fun y : ℝ => b₀ + b₁ * y) (0 + b₁) x := h_const.add h_b1y
  have h_quad_raw :
      HasDerivAt (fun y : ℝ => b₀ + b₁ * y + b₂ * y ^ 2) (0 + b₁ + b₂ * (2 * x)) x :=
    h_lin.add h_b2y2
  have h_quad :
      HasDerivAt (fun y : ℝ => pearsonIVQuad b₀ b₁ b₂ y) (b₁ + 2 * b₂ * x) x := by
    have : (fun y : ℝ => pearsonIVQuad b₀ b₁ b₂ y) = fun y => b₀ + b₁ * y + b₂ * y ^ 2 := by
      funext y; unfold pearsonIVQuad; rfl
    rw [this]
    have h_eq : (0 + b₁ + b₂ * (2 * x)) = b₁ + 2 * b₂ * x := by ring
    rw [← h_eq]
    exact h_quad_raw
  -- `f` is differentiable, hence has a derivative at `x`.
  have h_f : HasDerivAt f (deriv f x) x :=
    (hf.differentiable.differentiableAt).hasDerivAt
  -- Product rule.
  have h_prod := h_quad.mul h_f
  -- The product-rule expression simplifies via the ODE.
  have h_deriv_eq : deriv (fun y => pearsonIVQuad b₀ b₁ b₂ y * f y) x
      = (b₁ + 2 * b₂ * x) * f x + pearsonIVQuad b₀ b₁ b₂ x * deriv f x := h_prod.deriv
  rw [h_deriv_eq]
  -- Use the ODE: deriv f x * Q(x) = -L(x) * f x, i.e. Q(x) * deriv f x = -L(x) * f x.
  have h_ode := hf.ode x
  have h_ode_swap : pearsonIVQuad b₀ b₁ b₂ x * deriv f x
      = -(pearsonIVLin a₀ a₁ x) * f x := by
    have := h_ode
    linarith [h_ode]
  rw [h_ode_swap]
  unfold pearsonIVLin
  ring

/-! ## Pearson IV MAD formula (paper Eq. 13, todo B.3.2). -/

/-- **Pearson IV MAD closed form** (paper Eq. 13, RHS).
    `pearsonIVMADClosed a₀ a₁ b₀ b₁ b₂ m fm := 2 · Q(m) · fm / (a₁ − 2 b₂)`,
    where `Q(m) := b₀ + b₁ m + b₂ m²` and `fm := f(m)` is the density at
    the Pearson IV **mean** `m` (paper page 9: "Let m be the mean").  Note
    `a₀` is *not* used in the formula itself — it enters only through the
    mean constraint `m = (b₁ − a₀)/(a₁ − 2 b₂)` (see `pearsonIV_mad_eq`).
    Defined as a pure algebraic expression to be matched against the
    De Moivre upper-tail integral. -/
noncomputable def pearsonIVMADClosed (_a₀ a₁ b₀ b₁ b₂ m fm : ℝ) : ℝ :=
  2 * pearsonIVQuad b₀ b₁ b₂ m * fm / (a₁ - 2 * b₂)

/-- **Pearson IV MAD formula** (paper Eq. 13, todo B.3.2).
    Paper page 9: "Let `m` be the mean. ... Using the identity
        `E(|X − m|) = 2 · ∫_m^∞ (x − m) f(x) dx`
    and integrating by parts,
        `E(|X − m|) = 2 (b₀ + b₁ m + b₂ m²) · f(m) / (a₁ − 2 b₂)`.
    We use cumulants of the n-summed lognormal to match the parameters.
    Setting `a₁ = 1` and `m = (b₁ − a₀)/(1 − 2 b₂), …`."

    Two ingredients of the paper's derivation are passed in as
    hypotheses (the analytic content not formalised here):

    * `h_mean_constraint` — `m` is the Pearson IV mean, characterised by
      `(a₁ − 2 b₂) · m = (b₁ − a₀)`.  This is the constraint that makes
      the De Moivre identity `E|X − m| = 2 · ∫_m^∞ (x − m) f dx` valid
      (it holds for `m = E[X]`, which equals `(b₁ − a₀)/(a₁ − 2 b₂)` for
      a Pearson IV density satisfying the ODE under the standard
      integrability hypotheses).
    * `h_ibp` — the IBP intermediate.  Integrating the auxiliary identity
      `[Q(x) · f(x)]' = (b₁ − a₀) f(x) + (2 b₂ − a₁) x · f(x)`
      (provided by `pearsonIV_aux_deriv`) from `m` to `∞`, using boundary
      vanishing `Q(∞) f(∞) = 0` and the mean constraint to cancel the
      `(b₁ − a₀)(1 − F(m))` and `(a₁ − 2 b₂) m (1 − F(m))` terms, yields
          `(a₁ − 2 b₂) · ∫_m^∞ (x − m) f(x) dx = Q(m) · f(m)`.

    Under these hypotheses, the De Moivre MAD `2 · intCentered` matches
    the closed form.  Mathlib `v4.29.1` has no Pearson IV density nor
    the corresponding integrability lemmas, so the analytic discharge
    of `h_mean_constraint` and `h_ibp` is left external. -/
theorem pearsonIV_mad_eq (a₀ a₁ b₀ b₁ b₂ m fm : ℝ) (intCentered : ℝ)
    (h_den_ne : a₁ - 2 * b₂ ≠ 0)
    (_h_mean_constraint : (a₁ - 2 * b₂) * m = b₁ - a₀)
    (h_ibp :
        (a₁ - 2 * b₂) * intCentered = pearsonIVQuad b₀ b₁ b₂ m * fm) :
    2 * intCentered = pearsonIVMADClosed a₀ a₁ b₀ b₁ b₂ m fm := by
  -- The mean constraint is recorded in the signature for paper fidelity
  -- (`m = (b₁ − a₀)/(a₁ − 2 b₂)`); it's the analytic precondition that
  -- makes `h_ibp` valid.  The algebraic conclusion uses only `h_ibp` and
  -- `h_den_ne`.
  unfold pearsonIVMADClosed
  rw [eq_div_iff h_den_ne]
  linarith

/-- **Pearson IV MAD = Eq. 13 (verbatim form).**  Rearranged statement
    of `pearsonIV_mad_eq` matching the paper's printed equation:
        `E[|X − m|] = 2 · (b₀ + b₁ m + b₂ m²) · f(m) / (a₁ − 2 b₂)`.
    Identifies the MAD with `2 · intCentered` via the De Moivre identity
    (paper page 9, mean version). -/
theorem pearsonIV_mad_eq_paper (a₀ a₁ b₀ b₁ b₂ m fm : ℝ) (intCentered : ℝ)
    (h_den_ne : a₁ - 2 * b₂ ≠ 0)
    (h_mean_constraint : (a₁ - 2 * b₂) * m = b₁ - a₀)
    (h_ibp :
        (a₁ - 2 * b₂) * intCentered = pearsonIVQuad b₀ b₁ b₂ m * fm) :
    2 * intCentered = 2 * (b₀ + b₁ * m + b₂ * m ^ 2) * fm / (a₁ - 2 * b₂) := by
  have h := pearsonIV_mad_eq a₀ a₁ b₀ b₁ b₂ m fm intCentered
    h_den_ne h_mean_constraint h_ibp
  rw [h]
  unfold pearsonIVMADClosed pearsonIVQuad
  rfl

/-! ## Lognormal-matched Pearson IV (paper Eq. 12, todo B.3.3).

    The Pearson IV proxy for the lognormal iid sum is calibrated by
    matching the first four cumulants `(K_1, K_2, K_3, K_4)` (paper
    Appendix B / `Stats.Kappa.LognormalCumulants`).  Solving the
    moment-matching system gives `(a₀, b₀, b₁, b₂)` as explicit rational
    functions of `(n, σ)` over a *shared denominator*
        `D(n, σ) := 2 · (6(n − 1) + e^(2σ²)·(e^(σ²)·(5 e^(σ²) + 4) − 3))`
    (paper page 9, "box of formulas" under Eq. 13).  Encoded here verbatim
    from paper Eq. 12; no algebraic simplifications are performed beyond
    using `v := e^(σ²)` shorthand internally.

    The paper sets `a₁ = 1` and `m = (b₁ − a₀)/(1 − 2 b₂)` (the
    mean constraint of `pearsonIV_mad_eq`).  We follow that convention. -/

/-- **Shared denominator** of paper Eq. 12 (page 9):
        `D(n, σ) := 2 · (6(n − 1) + e^(2σ²)·(e^(σ²)·(5 e^(σ²) + 4) − 3))`.
    Appears in the denominator of every coefficient `a₀, b₀, b₁, b₂`. -/
noncomputable def pearsonIVLognormalDen (n : ℕ) (σ : ℝ) : ℝ :=
  2 * (6 * ((n : ℝ) - 1) + Real.exp (2 * σ ^ 2) *
    (Real.exp (σ ^ 2) * (5 * Real.exp (σ ^ 2) + 4) - 3))

/-- **Pearson IV coefficient `b₂`** matched to the lognormal iid sum
    (paper Eq. 12, verbatim):
        `b₂ = e^(2σ²) · (e^(σ²) − 1) · (2 e^(σ²) + 3) / D(n, σ)`. -/
noncomputable def pearsonIV_b2_lognormal (n : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (2 * σ ^ 2) * (Real.exp (σ ^ 2) - 1) * (2 * Real.exp (σ ^ 2) + 3)
    / pearsonIVLognormalDen n σ

/-- **Pearson IV coefficient `b₁`** matched to the lognormal iid sum
    (paper Eq. 12, verbatim):
        `b₁ = (e^(σ²) − 1) · e^(μ + σ²/2)
              · (e^(σ²) · (e^(σ²) · (e^(σ²) · (−4n + e^(σ²) · (e^(σ²) + 4) + 7)
                                       − 6 n + 6)
                            + 6 (n − 1))
                 + 12 (n − 1))
              / D(n, σ)`. -/
noncomputable def pearsonIV_b1_lognormal (n : ℕ) (μ σ : ℝ) : ℝ :=
  (Real.exp (σ ^ 2) - 1) * Real.exp (μ + σ ^ 2 / 2) *
    (Real.exp (σ ^ 2) *
      (Real.exp (σ ^ 2) *
        (Real.exp (σ ^ 2) * (-4 * (n : ℝ) + Real.exp (σ ^ 2) *
            (Real.exp (σ ^ 2) + 4) + 7)
          - 6 * (n : ℝ) + 6)
        + 6 * ((n : ℝ) - 1))
      + 12 * ((n : ℝ) - 1))
    / pearsonIVLognormalDen n σ

/-- **Pearson IV coefficient `b₀`** matched to the lognormal iid sum
    (paper Eq. 12, verbatim):
        `b₀ = −n · (e^(σ²) − 1) · e^(2(μ + σ²))
              · (e^(σ²) · (−2 (n − 1) e^(σ²) − 3 n + e^(3σ²) + 3)
                 + 6 (n − 1))
              / D(n, σ)`. -/
noncomputable def pearsonIV_b0_lognormal (n : ℕ) (μ σ : ℝ) : ℝ :=
  - (n : ℝ) * (Real.exp (σ ^ 2) - 1) * Real.exp (2 * (μ + σ ^ 2)) *
    (Real.exp (σ ^ 2) *
      (-2 * ((n : ℝ) - 1) * Real.exp (σ ^ 2) - 3 * (n : ℝ)
        + Real.exp (3 * σ ^ 2) + 3)
      + 6 * ((n : ℝ) - 1))
    / pearsonIVLognormalDen n σ

/-- **Pearson IV coefficient `a₀`** matched to the lognormal iid sum
    (paper Eq. 12, verbatim from arXiv LaTeX source):
        `a₀ = e^(μ + σ²/2) · (−12 n² + (3 − 10 n) e^(4σ²) + 6 (n − 1) e^(σ²)
                              + 12 (n − 1) e^(2σ²) − (8 n + 1) e^(3σ²)
                              + 3 e^(5σ²) + e^(6σ²) + 12)
              / D(n, σ)`.

    Audit 2026-05-13 pass 5: the `12 (n − 1) e^(2σ²)` term previously
    had exponent `3σ²` from a small-PDF mis-read; corrected to `2σ²`
    per arXiv LaTeX source `kappa-n-final.tex` line 731. -/
noncomputable def pearsonIV_a0_lognormal (n : ℕ) (μ σ : ℝ) : ℝ :=
  Real.exp (μ + σ ^ 2 / 2) *
    (-12 * (n : ℝ) ^ 2
      + (3 - 10 * (n : ℝ)) * Real.exp (4 * σ ^ 2)
      + 6 * ((n : ℝ) - 1) * Real.exp (σ ^ 2)
      + 12 * ((n : ℝ) - 1) * Real.exp (2 * σ ^ 2)
      - (8 * (n : ℝ) + 1) * Real.exp (3 * σ ^ 2)
      + 3 * Real.exp (5 * σ ^ 2)
      + Real.exp (6 * σ ^ 2)
      + 12)
    / pearsonIVLognormalDen n σ

/-- **Pearson IV coefficient `a₁`** under lognormal matching (paper page 9):
    "Setting a₁ = 1, …".  The paper normalises `a₁ = 1` so that the
    Pearson IV mean constraint reads `m = (b₁ − a₀)/(1 − 2 b₂)`. -/
noncomputable def pearsonIV_a1_lognormal (_n : ℕ) (_σ : ℝ) : ℝ := 1

/-- **Pearson IV ↔ lognormal coefficient match** (paper Eq. 12, todo B.3.3).
    The bundled output `(a₀, a₁, b₀, b₁, b₂)` matching the first four
    cumulants of the lognormal iid sum at parameters `(n, μ, σ)`, with
    `a₁ = 1` (paper's convention).  Verbatim from paper Eq. 12. -/
noncomputable def pearsonIVLognormalMatch (n : ℕ) (μ σ : ℝ) :
    ℝ × ℝ × ℝ × ℝ × ℝ :=
  (pearsonIV_a0_lognormal n μ σ,
   pearsonIV_a1_lognormal n σ,
   pearsonIV_b0_lognormal n μ σ,
   pearsonIV_b1_lognormal n μ σ,
   pearsonIV_b2_lognormal n σ)

/-- **Lognormal-match `a₁` is `1`** (paper page 9, "Setting a₁ = 1"). -/
theorem pearsonIV_lognormal_match_a1 (n : ℕ) (σ : ℝ) :
    pearsonIV_a1_lognormal n σ = 1 := rfl

/-- **Shared denominator is positive for `n ≥ 1, σ ∈ ℝ`.**  The shared
    denominator `D(n, σ)` is positive: for `n ≥ 1`, `6(n − 1) ≥ 0`, and
    the additive `e^(2σ²) · (e^(σ²)(5 e^(σ²) + 4) − 3)` is positive
    because `e^(σ²) ≥ 1`, so `5 e^(σ²) + 4 ≥ 9` and the inner factor
    `e^(σ²)(5 e^(σ²) + 4) − 3 ≥ 1·9 − 3 = 6 > 0`. -/
theorem pearsonIVLognormalDen_pos (n : ℕ) (σ : ℝ) (hn : 0 < n) :
    0 < pearsonIVLognormalDen n σ := by
  unfold pearsonIVLognormalDen
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ge_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_minus_one_nn : 0 ≤ (n : ℝ) - 1 := by linarith
  have hv_pos : 0 < Real.exp (σ ^ 2) := Real.exp_pos _
  have hv_ge_one : 1 ≤ Real.exp (σ ^ 2) := by
    have h := Real.add_one_le_exp (σ ^ 2)
    have h_sq_nn : 0 ≤ σ ^ 2 := sq_nonneg _
    linarith
  have he2_pos : 0 < Real.exp (2 * σ ^ 2) := Real.exp_pos _
  -- v · (5 v + 4) = 5 v² + 4 v ≥ 5 + 4 = 9 for v ≥ 1.
  have h_prod_ge : Real.exp (σ ^ 2) * (5 * Real.exp (σ ^ 2) + 4) ≥ 9 := by
    nlinarith [sq_nonneg (Real.exp (σ ^ 2) - 1)]
  have h_inner_pos :
      0 < Real.exp (σ ^ 2) * (5 * Real.exp (σ ^ 2) + 4) - 3 := by linarith
  have h_term2_pos :
      0 < Real.exp (2 * σ ^ 2) *
        (Real.exp (σ ^ 2) * (5 * Real.exp (σ ^ 2) + 4) - 3) :=
    mul_pos he2_pos h_inner_pos
  linarith

/-- **Lognormal-matched `b₂` ≥ 0** for `n ≥ 1, σ ∈ ℝ`.  Numerator is
    `e^(2σ²) · (e^(σ²) − 1) · (2 e^(σ²) + 3)`, all ≥ 0 for `σ ∈ ℝ` (note
    `e^(σ²) ≥ 1`).  Denominator positive by `pearsonIVLognormalDen_pos`. -/
theorem pearsonIV_lognormal_match_b2_nonneg (n : ℕ) (σ : ℝ) (hn : 0 < n) :
    0 ≤ pearsonIV_b2_lognormal n σ := by
  unfold pearsonIV_b2_lognormal
  have hv_pos : 0 < Real.exp (σ ^ 2) := Real.exp_pos _
  have hv_ge_one : 1 ≤ Real.exp (σ ^ 2) := by
    have h := Real.add_one_le_exp (σ ^ 2)
    have h_sq_nn : 0 ≤ σ ^ 2 := sq_nonneg _
    linarith
  have he2_pos : 0 < Real.exp (2 * σ ^ 2) := Real.exp_pos _
  have h_minus_one_nn : 0 ≤ Real.exp (σ ^ 2) - 1 := by linarith
  have h_quad_pos : 0 < 2 * Real.exp (σ ^ 2) + 3 := by linarith
  have h_num_nn : 0 ≤ Real.exp (2 * σ ^ 2) * (Real.exp (σ ^ 2) - 1)
      * (2 * Real.exp (σ ^ 2) + 3) :=
    mul_nonneg (mul_nonneg he2_pos.le h_minus_one_nn) h_quad_pos.le
  exact div_nonneg h_num_nn (pearsonIVLognormalDen_pos n σ hn).le

end TailOptionPricing
