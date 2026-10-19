# TODO6 — Lognormal-specific assembly of the Loulakis liminf

Historical planning and audit notes. For the current verified scope,
use [REVIEW.md](REVIEW.md) and the generated [INDEX.md](INDEX.md).
Checked items below may record formula identities or conditional
results; they do not certify complete probability-law formalizations.
References to former axioms or unfinished steps describe the state
at that audit, rather than the current source.

**Pass 8 finding (2026-05-13)**: project is fully axiom-clean
(274/274 in [Stats/Verify.lean](Stats/Verify.lean)), but the paper's
actual Loulakis claim is *not* assembled as a single theorem — only
the abstract template + components.

## Goal

Deliver, as a single Lean theorem, the paper's claim from
arXiv:1802.05495v3 (Section "Lognormal Sums", Loulakis' Proof):

```
liminf_{σ → ∞}  M(n; lognormal_σ) / M(1; lognormal_σ)  ≥  n
```

where `M(k; σ) := 𝔼|S_k − k|` for `S_k := Σ_{i<k} Y σ Z_i`, `Y σ z :=
exp(σ z − σ²/2)`, and `Z_i` iid `gaussianReal 0 1`.

## Status of inputs

| Hypothesis of [`LoulakisLiminf.liminf_M_ratio_ge_n`](Stats/Kappa/LoulakisLiminf.lean#L55) | Lognormal source | Status |
|---|---|---|
| `h_lower` (algebraic Loulakis bound on `M(n)`) | [`LoulakisAlgebraic.M_n_lower_bound`](Stats/Kappa/LoulakisAlgebraic.lean#L76) applied to n-fold iid `Y σ` | ⏸ NOT instantiated |
| `h_Mn_nn` (`M(n) ≥ 0`) | trivial (`M(n) = ∫|·|`) | ⏸ trivial-but-not-written |
| `h_Mn_triangle` (`M(n) ≤ n·M(1)`) | [`IIdTriangle.madSum_le_n_madSum_one`](Stats/Kappa/IIdTriangle.lean) applied to n-fold iid `Y σ` | ⏸ NOT instantiated |
| `h_M1_tend` (`M(1) → 2`) | ✅ [`LognormalAsymptotic.M_one_tendsto_two`](Stats/Kappa/LognormalAsymptotic.lean) | ✅ done |
| `h_An_tend` (`An σ → 1`) | DCT on `∫_1^n ℙ_σ(Y > u) du → 0` + `M(1)/2 → 1` | ⏸ not proved |
| `h_Bn_tend` (`Bn σ → 0`) | [`LognormalMarkov.lognormalReal_real_Ioi_le`](Stats/Kappa/LognormalMarkov.lean) + `∫_n^∞ t^(−2γ) dt` integrability | ⏸ not proved |

## Tasks (in dependency order)

### 6.1 — n-fold iid lognormal on a product space (~80 lines)

Construct `μ_n : Measure (Fin n → ℝ) := MeasureTheory.Measure.pi
(fun _ => gaussianReal 0 1)`.  Define `X σ i : (Fin n → ℝ) → ℝ` by
`X σ i ω := Y σ (ω i)`.  Show:
* `iIndepFun (X σ) μ_n` (via `iIndepFun_pi`).
* `∀ i, IdentDistrib (X σ i) (Y σ) μ_n (gaussianReal 0 1)`.
* `∀ i ω, 0 ≤ X σ i ω` (from `Y_pos`).
* `Integrable (∑ i, X σ i ·) μ_n` and `(∫ ∑ X σ i) = n` (from `integral_Y_eq_one` + linearity).

### 6.2 — `An σ → 1` (~150 lines)

`An σ := ∫_{t > 0} ℙ(Y σ > n + t) dt`.  Show as σ → ∞:

* `ℙ(Y σ > u) → 0` for each `u > 0` (already pointwise from
  `tendsto_Y_atTop_zero`; package as `tendsto_lognormal_tail_zero`).
* Bounded convergence on `[1, n]`: `∫_1^n ℙ_σ(Y > u) du → 0` (bound by 1, pointwise → 0).
* `M(1; σ) / 2 = ∫_{u > 1} ℙ_σ(Y > u) du = ∫_1^n ℙ + ∫_n^∞ ℙ → 1` (from B.7 + arithmetic).
* `An σ = ∫_{u > n} ℙ_σ(Y > u) du = (M(1)/2) − ∫_1^n ℙ → 1 − 0 = 1`.

(Translation `∫_{t > 0} ℙ(Y > n + t) dt = ∫_{u > n} ℙ(Y > u) du` via
substitution `u := n + t`; this is the only piece needing a
non-trivial measure-translation tool, e.g.
`MeasureTheory.integral_comp_add_left` for `intervalIntegral` lifted
to `Ioi`.)

### 6.3 — `Bn σ → 0` (~100 lines)

`Bn σ := ∫_{t > 0} ℙ_σ(Y > n + t)² dt`.  Fix `γ ∈ (1/2, 1)`.  From
[`LognormalMarkov.lognormalReal_real_Ioi_le`](Stats/Kappa/LognormalMarkov.lean):

```
ℙ_σ(Y > n + t)² ≤ (n + t)^(−2γ) · exp(γ(γ − 1)·σ²)
```

(using `μ = −σ²/2`, so `2γμ + γ²σ² = γ(γ−1)σ²`).

* `∫_{t > 0} (n + t)^(−2γ) dt = n^(1−2γ)/(2γ − 1)` (finite for `γ > 1/2`).
* `exp(γ(γ − 1)·σ²) → 0` as `σ → ∞` (since `γ(γ−1) < 0`).
* Hence `Bn σ ≤ const · exp(γ(γ−1)·σ²) → 0`.

### 6.4 — Final theorem (~30 lines)

```lean
theorem liminf_M_ratio_lognormal_ge_n {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ Filter.liminf
      (fun σ : ℝ => M_lognormal n σ / M_lognormal 1 σ) atTop := by
  apply LoulakisLiminf.liminf_M_ratio_ge_n
  · exact 6.1-derived algebraic bound
  · intro σ; exact integral_abs_nonneg
  · exact 6.1-derived iid triangle
  · exact LognormalAsymptotic.M_one_tendsto_two
  · exact 6.2  -- An → 1
  · exact 6.3  -- Bn → 0
```

Where `M_lognormal k σ := ∫ ω, |∑ i, Y σ (ω i) − k| ∂(Measure.pi ...)`.

## Total scope

| Task | Lines | Risk |
|---|---|---|
| 6.1 (iid product construction) | ~80 | low — Mathlib glue |
| 6.2 (An → 1) | ~150 | medium — DCT on `[1, n]` + translation lemma |
| 6.3 (Bn → 0) | ~100 | medium — Hölder + improper integral |
| 6.4 (wire-up) | ~30 | trivial |
| **Total** | **~360** | one focused session |

## Why this is worth doing

After 6.1–6.4, the paper's *literal* claim from arXiv:1802.05495v3
"Lognormal Sums" section becomes a single named theorem in
[Stats/Kappa](Stats/Kappa/), wired into Verify.lean, axiom-clean.
This closes the κ-metric formalisation of paper 1802.05495v3 with
zero structural shells, zero abstract hypothesis chains —
fully concrete paper-faithful statements throughout.

## After 6.x — what remains in the project

Nothing.  At that point the κ-metric paper is end-to-end formalised,
matching the paper claim-by-claim, axiom-clean, no `sorry`.
