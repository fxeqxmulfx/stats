# TODO7 — Heavy-tail-aware bad-point detection: formal foundations

Historical planning and audit notes. For the current verified scope,
use [REVIEW.md](REVIEW.md) and the generated [INDEX.md](INDEX.md).
Checked items below may record formula identities or conditional
results; they do not certify complete probability-law formalizations.
References to former axioms or unfinished steps describe the state
at that audit, rather than the current source.

> **New direction (2026-05-19)**: With todo3–todo6 the κ-metric paper
> (arXiv:1802.05495v3) and the slowly-varying machinery are end-to-end
> formalised.  This file proposes the next layer: turn that machinery
> into the foundation of a *formal* heavy-tail-aware bad-point detector,
> as motivated in [note.tex](note.tex).
>
> Unlike todo6, this is not "finish formalising paper X" — it is
> "use what we have to prove statistically-meaningful detection
> theorems that are missing from the literature in formal form".
>
> **Audit (2026-05-19, post-review)**: every signature below was
> checked against the actual code.  Names verified: `paretoMLE`
> ([Stats/RiskMeasures/MLE.lean#L48](Stats/RiskMeasures/MLE.lean#L48)),
> `paretoMomentIntegrand_integrableOn_iff`
> ([Stats/RiskMeasures/Moments.lean#L72](Stats/RiskMeasures/Moments.lean#L72)),
> `madSum` ([Stats/Kappa/IIdTriangle.lean#L53](Stats/Kappa/IIdTriangle.lean#L53)),
> `kappa_upper_bound_iid`
> ([Stats/Kappa/IIdTriangle.lean#L202](Stats/Kappa/IIdTriangle.lean#L202)),
> `paretoSampleMaxSurvival_union_bound`
> ([Stats/RiskMeasures/Drawdown.lean#L75](Stats/RiskMeasures/Drawdown.lean#L75)),
> `IsSlowlyVarying.uniform_convergence`,
> `stdNormal_mills_ratio`, `gaussianReal_real_Ioi_eq`.
>
> **Findings that changed the plan:**
> 1. `paretoMLE` is defined only as `n / S` (algebraic, no data-MLE);
>    A3 must split into algebraic-`HasDerivAt` + chain-rule.
> 2. There is no `paretoMeasure` in the project; A4 must construct
>    it from `paretoDensity · volume` first.
> 3. Project has **no** `EuclideanSpace`/`InnerProductSpace` use;
>    Phase B is greenfield infrastructure, not a small extension.
>    A cheaper alternative (avoid `EuclideanSpace`, use `Fin d → ℝ`
>    with explicit inner product) is noted in B1.
> 4. There is no bivariate Gaussian or copula machinery anywhere;
>    Phase C is also greenfield.
> 5. D4 as originally stated was wrong (tensorisation actually
>    strengthens distinguishability, not impossibility).  Rewritten.
> 6. D3 (finite-sample uniform conformal) needs DKW-type
>    concentration which is not in Mathlib.  Split into D3a
>    (asymptotic, doable) and D3b (finite-sample, separate effort).

## Motivation

The detection pipeline sketched in [note.tex](note.tex) (RuLSIF +
quantile-MLP residual + influence + conformal) needs four formal
guarantees that the project currently lacks:

1. A **hypothesis test for the *existence* of bad points** without
   identifying them (κ-violation contrapositive).
2. A **closed-form influence score** with `HasDerivAt` certificate,
   not numerical approximation.
3. **Conformal coverage under heavy-tail null** (slowly-varying),
   exploiting Karamata UCT + Potter bounds.
4. **Identifiability impossibility** (Le Cam) — the formal statement
   that corruption and tail are unidentifiable without extra structure.

For the multivariate case (X ∈ ℝᵈ, Y ∈ ℝᵏ) we additionally need:

5. **Multivariate regular variation (MRV)** as a Lean predicate.
6. **Copula tail dependence** λ_U as a Lean definition, with the
   Gaussian-copula impossibility theorem.

All six are doable on top of existing infrastructure.

## Dependency graph (revised)

```
A1 (MAD vs MSE)   ← integrability infra (done)
A2 (κ-violation)  ← kappa_upper_bound_iid (done)
A5 (FDR threshold) ← paretoSampleMaxSurvival_le_n_survival (done)
A3a (paretoMLE HasDerivAt in S)   ← MLE.lean (done)
                ↓
A3b (chain rule to per-point)     ← A3a + paretoLogSumStat (new)
A4a (paretoMeasure construction)  ← paretoDensity (done) + withDensity glue
                ↓
A4b (Le Cam scalar)               ← A4a + survival_eq_exp_neg_α_log_ratio (done)
                ↓
        D1 (multi-FDR Bonferroni)  ← A5
        D2 (matrix influence)       ← A3b
        D4 (product power bound)    ← A4a

B1 (MRV def, projection form)  ← Fin d → ℝ + euclidInner (new)
B2 (projection RV invariance)  ← B1 + IsSlowlyVarying.uniform_convergence (done)
B3 (κ invariance across v)     ← B2 + kappa_stable_invariance (done)

C1 (copula structure)          ← greenfield
C2 (λ_U def)                   ← C1
C3 (bivariate Gauss + Φ⁻¹)     ← gaussianReal, stdNormalCdf_* (done)
C4 (λ_U Gaussian = 0)          ← C3 + stdNormal_mills_ratio (done)

D3a (asymptotic uniform conformal) ← UCT + Potter (done) + Glivenko-Cantelli (Mathlib)
D3b (finite-sample)               DEFERRED (needs DKW)
```

## Phase A — Scalar foundation (~225 lines, mostly low risk)

### A1 — MAD vs MSE integrability gap (~10 lines)

Trivial composition of two existing `_integrableOn_iff` lemmas.

```lean
theorem mad_integrable_mse_not {l α : ℝ}
    (hl : 0 < l) (hα_lb : 1 < α) (hα_ub : α ≤ 2) :
    IntegrableOn (paretoMomentIntegrand l α 1) (Ioi l) volume
      ∧ ¬ IntegrableOn (paretoMomentIntegrand l α 2) (Ioi l) volume
```

**Risk**: trivial. Direct from `paretoMomentIntegrand_integrableOn_iff`
applied at `k = 1` and `k = 2`.

**Why it matters**: formalises the foundational claim that, in
Pareto-α ∈ (1, 2], MAD-regression is well-defined and MSE-regression
is not.  This is the entire reason quantile loss is required.

### A2 — κ-violation existence test (~30 lines)

Contrapositive of `IIdTriangle.kappa_upper_bound_iid`.  The integrability
hypothesis matches the original — `Integrable (X 0) μ`, not pointwise
per `i` (iid + integrability of `X 0` is what `kappa_upper_bound_iid`
assumes).

```lean
theorem not_iid_of_kappa_gt_one
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    {n : ℕ} (hn : 1 < n)
    (hM1_pos : 0 < madSum μ X 1)
    (hM_grow : madSum μ X 1 < madSum μ X n)
    (h_kappa : 1 < kappa (madSum μ X) 1 n) :
    ¬ ((∀ i, IdentDistrib (X i) (X 0) μ μ) ∧ Integrable (X 0) μ)
```

**Risk**: low.  Pure contrapositive of an existing theorem.  Shorter
than the original estimate because the hypothesis structure of
`kappa_upper_bound_iid` is already exactly what we contrapose.

**Why it matters**: gives a single named theorem stating "if observed
empirical κ exceeds 1, the sample is not iid" — a hypothesis test
for the *presence* of bad points without identifying them.

### A3 — Influence function for `paretoMLE`

Splits into two pieces because the project does not yet define
`paretoMLE` as a function of the raw data — only of the sufficient
statistic `S = Σ log(x_i / l)`
(see comment at [Stats/RiskMeasures/MLE.lean#L40](Stats/RiskMeasures/MLE.lean#L40)).

#### A3a — Algebraic `HasDerivAt` of `paretoMLE` in `S` (~10 lines)

```lean
theorem paretoMLE_hasDerivAt {S : ℝ} {n : ℕ}
    (hS : S ≠ 0) (hn : 0 < n) :
    HasDerivAt (fun S' => paretoMLE S' n) (-(n : ℝ) / S^2) S
```

**Risk**: trivial.  `paretoMLE S n = n / S` (literal definition);
HasDerivAt from `HasDerivAt.const_div` or direct calculation.

#### A3b — Chain rule to per-point influence (~40 lines)

Define the data-side sufficient statistic as a function:

```lean
noncomputable def paretoLogSumStat (l : ℝ) (xs : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (xs i / l)
```

Then prove `HasDerivAt` of `paretoMLE` viewed as a function of each
`xs j` (partial derivative — actually `HasFDerivAt` against
`Fin n → ℝ`, or one-coordinate `HasDerivAt`):

```lean
theorem paretoMLE_data_hasDerivAt {l : ℝ} {xs : Fin n → ℝ} {j : Fin n}
    (hl : 0 < l) (hxs_pos : ∀ i, 0 < xs i) (n_pos : 0 < n) :
    HasDerivAt
      (fun t : ℝ => paretoMLE (paretoLogSumStat l (Function.update xs j t)) n)
      (-(paretoMLE (paretoLogSumStat l xs) n)^2 / (n * xs j)) (xs j)
```

(Chain rule: `d/dt log((xs j)/l) = 1/xs j`, then propagate through `n/S`.)

**Risk**: low-medium.  Combinatorial care with `Function.update` and
`Finset.sum`; otherwise pure calculus.

**Why it matters**: gives the C-score in the three-score detector
as a closed-form analytic object, not a TracIn-style numerical
approximation.

### A4 — Le Cam impossibility, scalar Pareto (~120 lines)

Two sub-pieces because the project has no `paretoMeasure`:

#### A4a — Construct `paretoMeasure` (~70 lines)

```lean
noncomputable def paretoMeasure (l α : ℝ) : Measure ℝ :=
  volume.withDensity
    (fun x => if l < x then ENNReal.ofReal (paretoDensity l α x) else 0)
```

Lemmas needed:
* `paretoMeasure_real_univ_eq_one` (probability) — uses
  `densityMass_eq` and an integral computation
  (an unconditional Pareto, not the truncated form used in
  [Stats/Pareto/Mispricing.lean#L153](Stats/Pareto/Mispricing.lean#L153)
  for the option-pricing density).
* `paretoMeasure_real_Ioi_eq_survival` — `μ(t, ∞) = (l/t)^α`
  for `t ≥ l`.
* Measurability glue.

**Risk**: medium — `withDensity` + integrability bookkeeping.

#### A4b — Le Cam two-point inequality (~50 lines)

```lean
theorem leCam_pareto_scale {l₀ l₁ α : ℝ}
    (hα : 0 < α) (hl₀ : 0 < l₀) (hl_lt : l₀ < l₁) :
    ∀ (A : Set ℝ), MeasurableSet A →
      (paretoMeasure l₀ α).real A + (paretoMeasure l₁ α).real Aᶜ
        ≥ (l₀ / l₁) ^ α
```

Le Cam in the "sum of false-positive + false-negative ≥ 1 − TV" form
is cleaner than the `max ≥ ...` form for Lean.  The TV bound comes
from `paretoMeasure_real_Ioi_eq_survival` evaluated at `t = l₁`:
the mass under `paretoMeasure l₀` of `(l₁, ∞)` is `(l₀/l₁)^α`,
which is exactly the irreducible disagreement.

**Risk**: low once A4a is in place.

**Why it matters**: formally proves that no statistic of a single
observation can distinguish two Pareto-α distributions with different
scale, with quantitative power bound — making the identifiability
section of [note.tex](note.tex) a theorem instead of a remark.

### A5 — Sample-bag FDR threshold form (~15 lines)

The marginal bound `paretoSampleMaxSurvival_le_n_survival` already
exists; the only new content is the *inverted threshold form*
solving for `t` given target FDR `ε`:

```lean
theorem paretoSampleMax_threshold_for_FDR {n : ℕ} {l α ε : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hn_pos : 0 < n) (hε_pos : 0 < ε) :
    paretoSampleMaxSurvival n l α (l * ((n : ℝ) / ε) ^ (1 / α)) ≤ ε
```

**Risk**: trivial.  Compose `paretoSampleMaxSurvival_le_n_survival`
with `Real.rpow_natCast`/`rpow_inv_rpow` algebra.

## Phase B — Multivariate regular variation (~800 lines, greenfield)

The project currently has **no** use of `EuclideanSpace`,
`InnerProductSpace`, or sphere measures (verified by grep).  Phase B
is greenfield infrastructure.  To keep the design surface small we
**avoid** `EuclideanSpace`/`Metric.sphere` and use `Fin d → ℝ` with
an explicit inner product `⟨v, x⟩ = ∑ i, v i * x i`.  This matches
the style already established by
[Stats/Kappa/LognormalIIdSetup.lean](Stats/Kappa/LognormalIIdSetup.lean)
(which uses `Fin n → ℝ` with `Measure.pi`).

### B1 — MRV predicate definition (~150 lines)

```lean
noncomputable def euclidInner {d : ℕ} (v x : Fin d → ℝ) : ℝ :=
  ∑ i, v i * x i

noncomputable def euclidNorm {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (euclidInner x x)

/-- Multivariate regular variation via projection (Resnick-style):
`X` is MRV(α) if every linear projection `v · X` is scalar regularly
varying with the same index `−α`, with limiting ratio given by a
"spectral function" σ(v) ≥ 0. -/
def IsMultivariateRegularlyVarying
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin d → ℝ) (α : ℝ) (σ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ v : Fin d → ℝ, euclidNorm v = 1 →
    IsRegularlyVarying (fun t : ℝ => μ.real {ω | t < euclidInner v (X ω)}) (-α)
    ∧ Tendsto (fun t : ℝ =>
        μ.real {ω | t < euclidInner v (X ω)} / t ^ (-α))
        atTop (𝓝 (σ v))
```

(The full spectral-measure formulation is recoverable from `σ` via
the inverse Mellin transform, but for downstream use this projection
form is sufficient and easier to reason about.)

**Risk**: medium — picking the right formulation is the main risk;
the lemmas (inner product algebra, norm positivity, projection
measurability) are standard.

### B2 — Projection invariance under MRV (~400 lines)

```lean
theorem isRegularlyVarying_of_MRV_projection
    {d : ℕ} {μ : Measure Ω} {X : Ω → Fin d → ℝ} {α : ℝ} {σ : _ → ℝ}
    (hX : IsMultivariateRegularlyVarying μ X α σ)
    {v : Fin d → ℝ} (hv : euclidNorm v = 1) (hσv : 0 < σ v) :
    IsRegularlyVarying (fun t : ℝ => μ.real {ω | t < euclidInner v (X ω)}) (-α)
```

By definition (B1 gives this directly).  The non-trivial content is
the **comparison** lemma — for any two directions `v, w` with
`σ v, σ w > 0`, the ratio of tails converges to `σ v / σ w`.  This
uses Karamata UCT (`IsSlowlyVarying.uniform_convergence`).

**Risk**: medium-high.  The UCT plumbing is the dominant cost.

### B3 — Vector-κ invariance (~250 lines)

```lean
noncomputable def projectedMadSum
    {d : ℕ} (μ : Measure Ω) (X : ℕ → Ω → Fin d → ℝ) (v : Fin d → ℝ)
    (n : ℕ) : ℝ :=
  madSum μ (fun i ω => euclidInner v (X i ω)) n

theorem kappa_invariance_under_MRV
    {d : ℕ} {μ : Measure Ω} {X : ℕ → Ω → Fin d → ℝ} {α : ℝ} {σ : _ → ℝ}
    (hX_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_mrv : IsMultivariateRegularlyVarying μ (X 0) α σ)
    {v w : Fin d → ℝ} (hv : euclidNorm v = 1) (hw : euclidNorm w = 1)
    (hσv : 0 < σ v) (hσw : 0 < σ w)
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa (projectedMadSum μ X v) n₀ n
      = kappa (projectedMadSum μ X w) n₀ n
```

Statement: **κ is the same along every direction with positive
spectral mass**.  Combines B2 with scalar `kappa_stable_invariance`.

**Risk**: medium.  Most lines spent translating MRV → scalar RV
for each projection and quoting `kappa_stable_invariance`.

**Why it matters**: gives the inv-by-direction diagnostic — if
empirical κ̂ varies across projections, MRV hypothesis fails.
The detector then has a *formal* signal "the bag is non-MRV".

## Phase C — Copula and tail dependence (~600 lines, greenfield)

No copula, bivariate Gaussian, or tail-dependence machinery in the
project today (verified by grep).  The project has 1D `gaussianReal`
and `stdNormalCdf` infrastructure — enough to build the bivariate
case without pulling in fresh Mathlib subsystems.

### C1 — Domain and copula definition (~150 lines)

To avoid the subtype-product nightmare of `Set.Icc 0 1 × Set.Icc 0 1`,
work with `ℝ × ℝ → ℝ` and quantify membership in `[0,1]²` where
needed:

```lean
/-- Bivariate copula: a function `[0,1]² → [0,1]` with uniform
marginals and the 2-increasing (rectangle) property. -/
structure IsCopula (C : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × ℝ => C p.1 p.2)
           (Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  range : ∀ u v, u ∈ Set.Icc (0:ℝ) 1 → v ∈ Set.Icc (0:ℝ) 1 →
              C u v ∈ Set.Icc (0:ℝ) 1
  marg_zero_left  : ∀ u ∈ Set.Icc (0:ℝ) 1, C u 0 = 0
  marg_zero_right : ∀ v ∈ Set.Icc (0:ℝ) 1, C 0 v = 0
  marg_one_left   : ∀ u ∈ Set.Icc (0:ℝ) 1, C u 1 = u
  marg_one_right  : ∀ v ∈ Set.Icc (0:ℝ) 1, C 1 v = v
  two_increasing  : ∀ u₁ u₂ v₁ v₂, u₁ ≤ u₂ → v₁ ≤ v₂ →
                       0 ≤ Set.Icc 0 1 →  -- shape condition
                       C u₂ v₂ - C u₁ v₂ - C u₂ v₁ + C u₁ v₁ ≥ 0
```

Skipping Sklar (not strictly needed; would be a follow-up).

**Risk**: medium — structural design; standard once decided.

### C2 — Upper tail dependence coefficient (~100 lines)

```lean
/-- Upper tail dependence coefficient: `λ_U = lim_{u → 1⁻} (1 − 2u + C(u,u)) / (1 − u)`.
Equivalent to `lim ℙ(V > u | U > u)` under the bivariate distribution
with copula `C` and uniform marginals. -/
noncomputable def upperTailDependence (C : ℝ → ℝ → ℝ) : ℝ :=
  Filter.limUnder (𝓝[<] 1) (fun u : ℝ => (1 - 2 * u + C u u) / (1 - u))

theorem upperTailDependence_mem_Icc {C : ℝ → ℝ → ℝ} (hC : IsCopula C)
    (h_lim : Tendsto (fun u : ℝ => (1 - 2 * u + C u u) / (1 - u))
        (𝓝[<] 1) (𝓝 (upperTailDependence C))) :
    upperTailDependence C ∈ Set.Icc (0:ℝ) 1
```

**Risk**: low — limit + Fréchet-Hoeffding bounds on copula.

### C3 — Bivariate Gaussian copula (~150 lines)

Construct the bivariate Gaussian copula directly via inverse-CDF
composition; **no separate bivariate Gaussian measure required**:

```lean
/-- Bivariate Gaussian copula with correlation `ρ`. Defined directly
via the bivariate-normal CDF `Φ₂(·, · ; ρ)` and the standard normal
inverse `Φ⁻¹`:
    C_ρ(u, v) = Φ₂(Φ⁻¹(u), Φ⁻¹(v); ρ). -/
noncomputable def gaussianCopula (ρ : ℝ) (u v : ℝ) : ℝ :=
  bivariateStdNormalCdf ρ (stdNormalQuantile u) (stdNormalQuantile v)
```

where `bivariateStdNormalCdf` is constructed as the iterated integral
of the bivariate density using the project's 1D `gaussianReal` infra
and the linear-combination trick `(X₂ = ρ X₁ + √(1−ρ²) Z)`.

Sub-lemmas needed:
* `bivariateStdNormalCdf` well-defined and a CDF.
* `stdNormalQuantile` exists (inverse of strictly monotone `stdNormalCdf`).
* `gaussianCopula` is `IsCopula`.

**Risk**: medium-high — `stdNormalQuantile` requires a strict-monotone
inverse construction not in the project.

### C4 — Gaussian copula has λ_U = 0 (~200 lines)

**The deep theorem.**

```lean
theorem gaussianCopula_upperTailDependence_zero
    {ρ : ℝ} (hρ_lb : -1 < ρ) (hρ_ub : ρ < 1) :
    upperTailDependence (gaussianCopula ρ) = 0
```

Proof sketch: write
`λ_U = lim_{q → ∞} ℙ(X₂ > q | X₁ > q)`
with `(X₁, X₂)` standard bivariate Gaussian, correlation `ρ`. Using
`X₂ = ρ X₁ + √(1−ρ²) Z` with `Z ⊥ X₁`,
the conditional tail
`ℙ(X₂ > q | X₁ > q) ≤ ℙ(ρ X₁ + √(1−ρ²) Z > q | X₁ > q)`
collapses, via `stdNormal_mills_ratio`, to a ratio of Gaussian tails
that decays exponentially in `(1−ρ)·q`.

Uses (already in project):
* `stdNormal_mills_ratio` — tail of one-sided standard normal.
* `gaussianReal_real_Ioi_eq` — translation/scale of Gaussian tail.
* `stdNormalCdf_*` family.

**Risk**: medium — careful conditioning + tail dominance.

**Why it matters**: this is the canonical "Gaussian copula → no joint
tail risk" theorem, central to every modern critique of multivariate
Gaussian modelling.  Formalising it makes the heavy-tail warning in
1802.05495v3 (and finance more broadly) a Lean theorem.

## Phase D — Multivariate detector theorems (~510 lines)

### D1 — Per-coordinate FDR Bonferroni bound (~30 lines)

For Y ∈ ℝᵏ with each component Pareto:

```lean
theorem multivariate_sample_max_fdr_bound
    {k n : ℕ} {l α t : ℝ} (hl : 0 < l) (hα : 0 < α) (ht : l ≤ t) :
    -- ℙ(∃ i ∈ Fin n, ∃ j ∈ Fin k, Y i j > t)
    --   ≤ k · n · (l / t) ^ α
    ...
```

Direct union bound on top of A5.  Trivial composition.

**Risk**: trivial.

### D2 — Matrix influence function for joint paretoMLE (~80 lines)

```lean
theorem paretoMLE_joint_hasFDerivAt
    {k : ℕ} {S : Fin k → ℝ} {n : ℕ}
    (hS : ∀ j, 0 < S j) (hn : 0 < n) :
    HasFDerivAt (fun S' : Fin k → ℝ => fun j => paretoMLE (S' j) n)
      (ContinuousLinearMap.pi
        fun j => (-(n : ℝ) / (S j)^2) • ContinuousLinearMap.proj j)
      S
```

Componentwise lifting of A3.

**Risk**: low — straightforward `HasFDerivAt.pi`.

### D3 — Conformal coverage under SV null

Split into asymptotic (doable) and finite-sample (out-of-scope).

#### D3a — Asymptotic uniform coverage under SV (~300 lines)

```lean
theorem conformal_asymptotic_uniform_coverage_under_SV
    {L : ℝ → ℝ} {α : ℝ}
    (hL : IsSlowlyVarying L) (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hα_pos : 0 < α) (target : ℝ) (h_target : target ∈ Set.Ioo 0 1) :
    -- For data with survival proportional to L(x) · x^(-α):
    -- the conformal prediction set built from an iid calibration
    -- sequence has coverage → target as m → ∞, uniformly over the
    -- threshold (not merely marginally).
    Tendsto (fun m : ℕ => conformalCoverage L α m target)
      atTop (𝓝 target)
```

Uses `IsSlowlyVarying.uniform_convergence` + `potter_bounds` (both
already done).  No finite-sample concentration is needed if we settle
for *asymptotic* uniform coverage.  The proof passes the empirical
distribution through Glivenko–Cantelli (in Mathlib) and applies UCT
to the survival ratios.

**Risk**: high.  The longest single task in the entire plan.  The
novelty is the *uniform-over-threshold* strengthening — marginal
conformal coverage is standard, but proving uniform coverage under
SV requires the UCT path.

#### D3b — Finite-sample uniform coverage (DEFERRED)

Would require DKW-type concentration (not in Mathlib).  Add to todo8
or later — D3a is the publication-grade theorem; the finite-sample
strengthening is a refinement, not a prerequisite for downstream use.

### D4 — Pareto product detection-power bound (~80 lines)

**Originally** stated as "Le Cam impossibility tensorisation".  That
direction is wrong: with iid product data, two different scales
become *easier*, not harder, to distinguish; TV grows with `d`.  The
correct multivariate analogue is a **detection-power lower bound**
on the optimal test:

```lean
theorem optimal_test_power_pareto_product {d : ℕ} {l₀ l₁ α : ℝ}
    (hα : 0 < α) (hl₀ : 0 < l₀) (hl_lt : l₀ < l₁)
    (h_supp : l₀ < l₁) :  -- already implied; written for clarity
    -- The optimal test between Pareto(l₀,α)^⊗d and Pareto(l₁,α)^⊗d
    -- has type-I + type-II error sum bounded by
    --   (l₀ / l₁) ^ (α · d)
    -- → 0  as d → ∞.
    ∀ (A : Set (Fin d → ℝ)), MeasurableSet A →
      (productPareto d l₀ α).real A + (productPareto d l₁ α).real Aᶜ
        ≥ ... and ≤ (l₀/l₁)^(α·d)
```

The two-sided form: the irreducible error sum (LeCam-type) lower bound
is at most `(l₀/l₁)^(α·d)` for the **best** test — exponentially
small in `d`.  So:

* **Identifiability is recovered** in the multivariate iid case as
  long as `l₀ ≠ l₁`, with exponential power.
* The note.tex identifiability *warning* is therefore scalar-only
  (or non-iid).

**Risk**: medium.  `Measure.pi` + product TV via independent
`paretoMeasure` (A4a).  The exponential bound uses
`survival_eq_exp_neg_α_log_ratio` for each factor.

**Why it matters**: clarifies the scope of the identifiability
warning.  Without multiple iid copies, corruption and tail are
unidentifiable (A4); with `d` iid copies, the bound shrinks as
`(l₀/l₁)^(αd)`.  This justifies the multivariate part of the
note.tex pipeline (using `d > 1` to compensate for the scalar
identifiability obstruction).

## Total scope (revised after audit)

| Phase | Tasks | Lines | Risk | Notes |
|---|---|---|---|---|
| **A** scalar | A1, A2, A3a, A3b, A4a, A4b, A5 | ~225 | mostly low | A4 split because no `paretoMeasure` exists |
| **B** MRV | B1, B2, B3 | ~800 | medium-high | greenfield (no inner product use in project today) |
| **C** copula | C1, C2, C3, C4 | ~600 | high (C3, C4) | greenfield; C3 splits bivariate Gaussian out of C4 |
| **D** detector | D1, D2, D3a, D4 | ~510 | mixed | D3b deferred (DKW out of scope) |
| **Total** | 17 tasks | **~2135** | several focused sessions |

The ~50% growth vs the first draft is real, not slack: A4 needed the
measure constructed, Phase B is greenfield (originally underestimated
because we assumed `EuclideanSpace` reuse), Phase C needs a bivariate
Gaussian sub-task that wasn't separated, and D3 had to split.

## Suggested order of attack (revised)

1. **A1, A5, A2** — trivial-to-low risk wrappers.  ~55 lines.  Single
   afternoon, each lands a named detection theorem.
2. **A3a** — algebraic HasDerivAt of paretoMLE.  ~10 lines.
3. **A4a** — construct `paretoMeasure` (unlocks A4b, D4).  ~70 lines.
4. **A4b, A3b** — Le Cam scalar + data-side chain rule.  ~90 lines.
5. **D1, D2, D4** — multivariate wire-ups using A4a + A3.  ~170 lines.
6. **C1, C2** — copula scaffolding (independent of B).  ~250 lines.
7. **B1, B2, B3** — MRV layer.  ~800 lines.  (Can run in parallel with 8.)
8. **C3, C4** — bivariate Gaussian + the deep λ_U = 0 theorem.  ~350 lines.
9. **D3a** — asymptotic uniform conformal under SV.  Capstone.  ~300 lines.

After step 5, the project has a self-contained **scalar** heavy-tail
detection foundation with full Verify entries — that alone makes
[note.tex](note.tex) Sections 1–8 formally backed.

After step 9, the multivariate, copular, and asymptotic-conformal
layers are also in place, matching [note.tex](note.tex) Sections 9–10.

## Why this is worth doing

The κ-metric formalisation (todo3–todo6) was *reactive* — it
formalised an existing paper.  This todo is *generative*: the
literature on heavy-tail-valid bad-point detection, conformal
under non-i.i.d. exchangeability, and formal identifiability
impossibility for tail-scale problems is fragmented and mostly
informal.  Each theorem in Phases A and D would be, to my knowledge,
its first formal proof.

C3 (Gaussian copula → no upper tail dependence) is the most
practically important: it makes rigorous the warning behind every
"why Gaussian is wrong for joint risk" remark in the heavy-tail
literature, including 1802.05495v3.

## After 7.x — what remains

A natural follow-up (todo8) would be:
- **Extreme value theory** infrastructure: Generalized Pareto, POT
  threshold selection, return-level estimation.
- **Multivariate EVT**: angular-measure estimation, Hill estimator
  with confidence intervals as `HasDerivAt`-certified.
- **Hawkes-process / temporal heavy-tail** if the data has time
  structure.

These are not prerequisites for the detector — they are extensions.
