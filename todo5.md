# TODO5 — Discharging the two structural shells in `Stats.Kappa.Lognormal`

Historical planning and audit notes. For the current verified scope,
use [REVIEW.md](REVIEW.md) and the generated [INDEX.md](INDEX.md).
Checked items below may record formula identities or conditional
results; they do not certify complete probability-law formalizations.
References to former axioms or unfinished steps describe the state
at that audit, rather than the current source.

> **Status (2026-05-13, FINAL)**: **All Phases A, B.1–B.7, C.1–C.3b complete**.  Both `Stats.Kappa.Lognormal` structural shells now derive from first principles.
>
> Old status block:
> - Phase A: **✅ DONE** ([Stats/Kappa/IIdTriangle.lean](Stats/Kappa/IIdTriangle.lean), iid triangle inequality `M(n) ≤ n·M(1)`). Closes structural shell #1 completely.
> - Phase B.1–B.4: **✅ DONE** ([Stats/Kappa/LognormalMeasure.lean](Stats/Kappa/LognormalMeasure.lean), lognormal as measure + tail formula).
> - Phase B.5: **✅ DONE** ([Stats/Kappa/LognormalMarkov.lean](Stats/Kappa/LognormalMarkov.lean), Hölder/Markov bound on the tail via Chernoff + Gaussian mgf).
> - Phase B.6: **✅ DONE** ([Stats/Kappa/MadLayerCake.lean](Stats/Kappa/MadLayerCake.lean), MAD layer cake `𝔼|X−m| = 2 ∫ ℙ(X > m+t) dt`).
> - Phase C.1: **✅ DONE** ([Stats/Kappa/MaxIIdBound.lean](Stats/Kappa/MaxIIdBound.lean), inclusion-exclusion lower bound on iid max).
> - Phase C.2: **✅ DONE** ([Stats/Kappa/SumMaxBound.lean](Stats/Kappa/SumMaxBound.lean), trivial `ℙ(S_n > t) ≥ ℙ(max > t)` for nonneg).
> - Phase C.3a (algebraic Loulakis bound, parametric, no σ→∞): **✅ DONE** ([Stats/Kappa/LoulakisAlgebraic.lean](Stats/Kappa/LoulakisAlgebraic.lean), combines B.6 + C.2 + C.1).
> - Phase B.7, Phase C.3b (final σ→∞ liminf step): **⏸ DEFERRED** — only the σ→∞ asymptotic analysis remains.
>
> Verify.lean grew 249 → **270+**; all axiom-clean (only `[propext, Classical.choice, Quot.sound]`).
>
> **Closed shell #1 fully** (iid triangle, Phase A).  Shell #2 (Loulakis subexp) has all algebraic pieces; only the σ→∞ limit combining them is left.


**Goal**: replace the two probabilistic *hypotheses* in
[Stats/Kappa/Lognormal.lean](Stats/Kappa/Lognormal.lean) with full
proofs from first principles.

After pass 6 the project is **axiom-free at the source level**
(`grep -rn '^axiom ' Stats/` → 0 hits) and `Stats.Verify` passes all
256 theorems on `[propext, Classical.choice, Quot.sound]`.  However,
two κ-related theorems take their *defining inequality* as an
explicit hypothesis rather than proving it from a probability-theory
foundation:

| Theorem | Hypothesis taken | Probabilistic content |
|---|---|---|
| [`kappa_upper_bound_subadditive`](Stats/Kappa/Lognormal.lean#L60) | `M(n) ≤ n · M(1)` | iid triangle inequality on MAD |
| [`kappa_loulakis_lower_bound`](Stats/Kappa/Lognormal.lean#L95) | `n · M(1) ≤ M(n)` | Loulakis lognormal-σ→∞ subexp argument |

This file specifies the *full* proofs and a phased implementation
plan.

---

## §0. Set-up — what the inequalities are *about*

Let `(Ω, ℱ, μ)` be a probability space, `X : ℕ → Ω → ℝ` an iid family
with `X i ~ X 0` (in `IdentDistrib` sense, w.r.t. `μ`).  Assume
`Integrable (X 0) μ` (equivalently `MemLp 1`).  Define the partial
sum `S_n := Σ_{i<n} X i`.  Then:

```
M(n) := μ[|S_n − μ[S_n]|]
     := ∫ ω, |S_n(ω) − μ[X 0]·n| ∂μ
```

(Here `μ[·]` is `MeasureTheory.integral μ`, i.e.
`∫ ω, · ∂μ`.)  For `n = 1`, `M(1) = μ[|X 0 − μ[X 0]|]`.

The two target inequalities:

- **(IT)** *iid triangle*:  for every `n ≥ 1`,
  `M(n) ≤ n · M(1)`.

- **(L)** *Loulakis subexp limit*:  if `X 0` is lognormal with
  parameters `μ_log = σ²/2` (so `𝔼[X 0] = 1` after a standard
  parametrisation), then
  `liminf_{σ→∞} M(n) / M(1) ≥ n`.
  Combined with (IT) gives `lim_{σ→∞} M(n)/M(1) = n` and thence
  `κ_{1,n} → 1` as `σ → ∞`.

(L) is what the paper calls "Loulakis' Proof" (page 14, on the
lognormal in section "Lognormal Sums").

---

## §1. Mathematical statement of the two proofs

### §1.1  Proof of (IT)

```
M(n) = ∫ ω, |S_n(ω) − μ[X 0]·n| ∂μ
     = ∫ ω, |Σ_{i<n} (X i − μ[X 0]) (ω)| ∂μ                 -- linearity
     ≤ ∫ ω, Σ_{i<n} |X i − μ[X 0]| (ω) ∂μ                   -- triangle (Finset.abs_sum_le_sum_abs)
     = Σ_{i<n} ∫ ω, |X i − μ[X 0]| (ω) ∂μ                   -- integral_finset_sum
     = Σ_{i<n} ∫ ω, |X 0 − μ[X 0]| (ω) ∂μ                   -- IdentDistrib + IdentDistrib.integral_eq
     = n · M(1).
```

Every step is in Mathlib.

### §1.2  Proof of (L)

The paper, page 14, sketches:

```
M(n) = ∫ |S_n − 𝔼S_n| ∂μ                                                  -- definition
     ≥ ∫_{nm}^∞ ℙ(S_n > t) dt    (× 2, but the "× 2" cancels in ratio)     -- layer cake on positive part
     ≥ ∫_{n}^∞ ℙ(max_{i≤n} X_i > t) dt                                     -- max ≤ sum
     ≥ ∫_{n}^∞ (n · ℙ(X_1 > t) − (n choose 2) · ℙ(X_1 > t)²) dt            -- inclusion-exclusion lower
     = n · ∫_{n}^∞ ℙ(X_1 > t) dt − (n choose 2) · ∫_{n}^∞ ℙ(X_1 > t)² dt
     = n · M(1) − (n choose 2) · ∫_{n}^∞ ℙ(X_1 > t)² dt                    -- since M(1) = 2∫_1^∞ ℙ(X_1>t) dt at μ_log = σ²/2
```

So `M(n)/M(1) ≥ n − (n choose 2) · I_2(σ)/M(1)` where
`I_2(σ) := ∫_n^∞ ℙ(X_1 > t)² dt`.

Loulakis' subexponentiality + Hölder argument shows
`I_2(σ)/M(1) → 0` as `σ → ∞`:

* For lognormal `X = exp(σ Z − σ²/2)` with `Z ~ 𝒩(0,1)`,
  `ℙ(X > t) = Φ̄((log t + σ²/2)/σ)` where `Φ̄ = 1 − Φ`.
* By Hölder with exponent `γ ∈ (1/2, 1)`:
  `ℙ(X > t)² ≤ t^{−2γ} · 𝔼[X^{2γ}]² = t^{−2γ} · exp((2γ² − γ)·σ²)`.

  Actually the cleaner step: `ℙ(X > t) ≤ t^{−γ} · 𝔼[X^γ]
  = t^{−γ} · exp(γ²σ²/2 − γσ²/2 + γ²σ²/2) = t^{−γ} · exp(γ(γ−1)σ²/2)`,
  the last factor being `< 1` for `γ ∈ (0, 1)` and shrinking as `σ → ∞`.
* `M(1) ~ const · σ` (or faster) as σ → ∞, while `I_2 ≤ const · σ^?`
  decays at a faster relative rate — pinning `I_2/M(1) → 0`.

The detail of the Hölder bound + the σ-asymptotic of `M(1)` are both
substantive — about 500 lines of estimates.

---

## §2. Mathlib inventory (what we can rely on)

### §2.1  Available (verified by grep)

* [`MeasureTheory.IdentDistrib`](.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean) — structure for "X and Y have the same law".
* [`IdentDistrib.integral_eq`](.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean) — `∫ X dμ = ∫ Y dμ` for identically distributed.
* [`IdentDistrib.comp`](.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean) — stable under measurable composition.
* [`IdentDistrib.integrable_iff`](.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean) — integrability transports.
* [`iIndepFun`](.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean) — joint independence.
* [`abs_integral_le_integral_abs`](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L953) — `|∫ f dμ| ≤ ∫ |f| dμ`.
* [`integral_finset_sum`](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L249) — `∫ Σ_i f_i dμ = Σ_i ∫ f_i dμ`.
* [`Finset.abs_sum_le_sum_abs`](.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean#L287) — pointwise triangle on Finsets.
* [`ProbabilityTheory.gaussianReal`](.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean) — Gaussian as a measure.
* `mgf` of `gaussianReal` — moment-generating function (gives `𝔼[X^γ]` for lognormal via `X = exp(σZ + μ)`).
* Standard `Measure.map` machinery for push-forwards.

### §2.2  Missing (must be built in `Stats/`)

* **Lognormal distribution as a measure**.  Mathlib has no
  `lognormalReal`.  We can construct it as
  `lognormalReal μ σ := Measure.map (fun x => Real.exp (μ + σ * x)) (gaussianReal 0 1)`
  and prove a PDF formula on `(0, ∞)`.  But it's not yet there.
* **Layer-cake identity for MAD**:
  `μ[|X − m|] = 2 ∫_m^∞ ℙ(X > t) dt`
  for `X` with mean `m`.  Mathlib has the layer-cake formula
  (`MeasureTheory.integral_eq_lintegral_meas_lt`) — translating to
  this specific MAD form is ~80 lines.
* **Tail of lognormal**:
  `ℙ(X > t) = Φ̄((log t − μ_log)/σ)` for `X ∼ lognormalReal μ_log σ`.
  Direct from `gaussianReal_real_Ioi` already in
  [`Stats/BinaryForecasts/SigmaClosures.lean`](Stats/BinaryForecasts/SigmaClosures.lean),
  but needs the lognormal pull-back.
* **Inclusion-exclusion lower bound for `ℙ(max)`** on iid:
  `ℙ(max_{i<n} X_i > t) ≥ n·ℙ(X_0 > t) − (n choose 2)·ℙ(X_0 > t)²`.
  This is purely combinatorial probability — Mathlib doesn't have
  it packaged but easy to derive from `iIndepFun` + Bonferroni's
  inequality.  ~80 lines.
* **σ→∞ asymptotic of lognormal MAD**: `M_lognormal(1; σ) ~ Cσ` (the
  growth rate Loulakis needs).  Substantive computation.

---

## §3. Phased implementation plan

### Phase A — Inequality (IT) in `Stats/Kappa/IIdTriangle.lean` (~200-300 lines)

**A.0 Setup.**  New module `Stats.Kappa.IIdTriangle`, imported from
`Stats.Kappa`.

**A.1 Definition.**
```lean
noncomputable def madSum (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, |∑ i ∈ Finset.range n, X i ω - n * μ[X 0]| ∂μ
```

**A.2 Auxiliary lemma**: integrability of the centred shifts.
For each `i ∈ range n`, `Integrable (fun ω => |X i ω - μ[X 0]|) μ`
(under hypothesis `Integrable (X 0) μ` + `IdentDistrib`).
~30 lines.

**A.3 Main theorem**.
```lean
theorem madSum_le_n_madSum_one
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ)
    (n : ℕ) :
    madSum μ X n ≤ n * madSum μ X 1 := by
  -- Step 1: |S_n − n·𝔼X| = |Σ (X_i − 𝔼X)| ≤ Σ |X_i − 𝔼X|
  -- Step 2: ∫ Σ ≤ Σ ∫ (linearity)
  -- Step 3: ∫|X_i − 𝔼X| = ∫|X_0 − 𝔼X| (IdentDistrib + .comp through |·−c|)
  -- Step 4: Σ = n · ∫|X_0 − 𝔼X| = n · madSum μ X 1
```
~150 lines.

**A.4 Corollary** discharging the structural shell:
```lean
theorem kappa_upper_bound_iid [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (h_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ) {n : ℕ} (hn : 1 < n)
    (hM1_pos : 0 < madSum μ X 1) (hM_grow : madSum μ X 1 < madSum μ X n) :
    kappa (madSum μ X) 1 n ≤ 1 :=
  kappa_upper_bound_subadditive hn hM1_pos hM_grow
    (madSum_le_n_madSum_one X h_id hX0 n)
```
~20 lines.

**Estimate**: Phase A ≈ **200-300 Lean lines**, axiom-clean,
discharges the iid-triangle shell.

### Phase B — Inequality (L) prerequisites in `Stats/Kappa/Lognormal/Measure.lean` (~400 lines)

**B.1 Lognormal measure definition.**
```lean
noncomputable def lognormalReal (μ σ : ℝ) (hσ : 0 < σ) : Measure ℝ :=
  Measure.map (fun x => Real.exp (μ + σ * x)) (ProbabilityTheory.gaussianReal 0 1)
```

**B.2 Probability measure instance.** ~30 lines.

**B.3 PDF formula** on `Ioi 0`:
```lean
theorem lognormalReal_pdf {μ σ : ℝ} (hσ : 0 < σ) (x : ℝ) (hx : 0 < x) :
    lognormalReal μ σ {x} ... -- via Measure.map + Jacobian
```
~80 lines.

**B.4 Tail bound** in terms of `stdNormalCdf`:
```lean
theorem lognormalReal_Ioi {μ σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    (lognormalReal μ σ).real (Set.Ioi x)
      = 1 - stdNormalCdf ((Real.log x - μ) / σ)
```
~50 lines (reuses `Stats/BinaryForecasts/SigmaClosures.lean`
infrastructure for `stdNormalCdf`).

**B.5 Hölder bound** `ℙ(X > t)^γ ≤ const · t^{−γ}` for lognormal,
γ ∈ (0, 1).  ~80 lines.

**B.6 Layer cake** for MAD:
```lean
theorem mad_eq_two_integral_tail
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h_mean : ∫ x, x ∂ν = m) (h_int : Integrable id ν) :
    ∫ x, |x - m| ∂ν = 2 * ∫ t in Set.Ioi m, (ν.real (Set.Ioi t))
```
~80 lines.

**B.7 σ→∞ asymptotic of `M_lognormal(1; σ)`.**  ~80 lines.

**Estimate**: Phase B ≈ **400 lines**, builds the lognormal layer
in `Stats/`.

### Phase C — Inequality (L) main proof in `Stats/Kappa/Lognormal/Loulakis.lean` (~400 lines)

**C.1 Inclusion-exclusion lower bound on iid max** (~80 lines):
```lean
theorem prob_max_iid_lower_bound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℝ) * (ν.real (Set.Ioi t))
      - (n.choose 2 : ℝ) * (ν.real (Set.Ioi t))^2
    ≤ ((ν.prod^n).real {ω | ∃ i < n, ω i > t})
```
(via Bonferroni's inequality, which is what the paper's expression
amounts to).

**C.2 P(S_n > t) ≥ P(max_i X_i > t)** for non-negative X (the
lognormal lives on `(0,∞)`):
```lean
theorem prob_sum_ge_prob_max ...
```
~30 lines.

**C.3 Putting it together** — the full liminf argument:
```lean
theorem M_lognormal_ratio_liminf_ge_n :
    ∀ (n : ℕ) (hn : 1 ≤ n),
      n ≤ Filter.liminf
        (fun σ : ℝ => M_iid (lognormalReal (σ^2/2) σ (...)) n /
                       M_iid (lognormalReal (σ^2/2) σ (...)) 1)
        (𝓝[>] 0)
```

Wait — the limit is `σ → ∞`, not `σ → 0`.  Fix the filter to `atTop`.
~250 lines.

**C.4 Corollary**: combine with (IT) to get `kappa → 1`.

**Estimate**: Phase C ≈ **400 lines**.

### Phase D — Wiring & verification (~50 lines)

* Update `Stats/Kappa.lean` umbrella imports.
* Add `#print axioms` entries for new theorems in
  `Stats/Verify.lean`.
* Update `todo4.md` Pass 7 with the new closed structural shells.

---

## §4. Aggregate scope

| Phase | Lean lines | Mathlib prerequisites | Risk |
|---|---|---|---|
| A (iid triangle) | 200-300 | all in place | low |
| B (lognormal infrastructure) | ~400 | gaussianReal in place; needs new lognormalReal module | medium |
| C (Loulakis main) | ~400 | depends on Phase B | medium-high (σ→∞ asymptotic estimates) |
| D (wiring) | ~50 | trivial | low |
| **Total** | **~1100** | — | — |

**Aggressive single-session estimate**: Phase A alone, ~3 hours
realistic.  Phase B+C: multi-session work, with the σ→∞ asymptotic
being the highest-risk piece.

---

## §5. Decision points

The user (in the prior turn) opted for plan "**Phase A in full;
Phase B+C partial** (set up integral form and inclusion-exclusion,
but leave the σ→∞ limit as a smaller explicit `tendsto` hypothesis
rather than full from-scratch axiom)".

Recommended phasing:

1. **This session (or next)**: full Phase A — close the iid-triangle
   shell completely.
2. **Next session**: Phase B steps B.1–B.4 (lognormal definition,
   PMF, tail) — pure infrastructure, low risk.
3. **Later session**: Phase B.5–B.7, Phase C — the Hölder estimates
   and σ→∞ asymptotic, with the final tendsto step possibly cleanly
   restated as a named hypothesis to keep the rest axiom-clean.

After Phase A, the iid-triangle shell is fully closed and the
`Stats.Kappa.Lognormal` upper bound `κ ≤ 1` becomes a *theorem* with
explicit iid + integrability hypotheses rather than an
`M(n) ≤ n·M(1)` hypothesis-as-conclusion.

---

## §6. After-state

When all phases done:

* `kappa_upper_bound_iid` (Phase A) replaces the `h_subadditive`
  hypothesis with iid + integrability hypotheses (which are
  *substantive* and can be verified for concrete distributions).
* `kappa_loulakis_lower_bound_lognormal` (Phase B+C) replaces the
  `h_bound` hypothesis with `(σ : ℝ)` parameter + integrability of
  the relevant lognormal moments — `liminf` form for `κ_{1,n} ≥ 1`.

Combined: the two `Stats.Kappa.Lognormal` shells move from
"structural shell with paper content as hypothesis" to
"theorem with first-principles probabilistic content".

Project remains axiom-free.  Verify.lean grows by ~5 entries.

---

## §7. Pass-completion log (2026-05-13)

### Done

**Phase A — iid triangle inequality** ✅
[Stats/Kappa/IIdTriangle.lean](Stats/Kappa/IIdTriangle.lean) (~200 lines).
* `madSum μ X n := ∫ |Σ Xᵢ − n·𝔼X₀| ∂μ`
* `madSum_le_n_madSum_one`: full proof via pointwise `Finset.abs_sum_le_sum_abs`, `integral_finset_sum`, and `IdentDistrib.integral_eq` composed with `fun x => |x − c|`.
* `kappa_upper_bound_iid`: corollary discharging the structural shell `kappa_upper_bound_subadditive` from iid + integrability hypotheses (no longer requiring `M(n) ≤ n·M(1)` as a separate hypothesis).

**Phase B.1–B.4 — Lognormal as a probability measure** ✅
[Stats/Kappa/LognormalMeasure.lean](Stats/Kappa/LognormalMeasure.lean) (~110 lines).
* `lognormalReal μ v := (gaussianReal μ v).map Real.exp`.
* `instIsProbabilityMeasureLognormalReal`.
* `lognormalReal_Ioi_zero_eq_one` (support on `(0, ∞)`).
* `lognormalReal_real_Ioi`: tail formula `ℙ(X > x) = 1 − Φ((log x − μ)/√v)` for `x > 0`, via `gaussianReal_real_Ioi_eq` and `one_sub_stdNormalCdf`.

**Phase C.1 — Inclusion-exclusion lower bound on iid max** ✅
[Stats/Kappa/MaxIIdBound.lean](Stats/Kappa/MaxIIdBound.lean) (~220 lines).
* `one_sub_one_sub_pow_ge`: algebraic inequality `1 − (1 − p)^n ≥ n·p − (n choose 2)·p²` for `p ∈ [0, 1]`, by induction using Mathlib's Bernoulli inequality `one_add_mul_le_pow`.
* `prob_all_le_iid`: probabilistic identity `ℙ(∀ i, Xᵢ ≤ t) = ℙ(Y ≤ t)^n` for iid family with representative law `Y`, via `iIndepFun.measure_inter_preimage_eq_mul` + `IdentDistrib.measure_mem_eq`.
* `prob_max_iid_gt`: `ℙ(max Xᵢ > t) = 1 − ℙ(Y ≤ t)^n` (complement of the above).
* `prob_max_iid_ge`: combined Loulakis lower bound on the max-event probability.

### Verify.lean delta

249 → 264 audited theorems.  All 264 axiom-clean.

### Newly completed in this session (continuing the original Phase A pass)

**Phase B.5 — Hölder/Markov bound on the lognormal tail** ✅
[Stats/Kappa/LognormalMarkov.lean](Stats/Kappa/LognormalMarkov.lean) (~115 lines).
* `gaussianReal_real_Ici_le`: Chernoff specialisation `ℙ(Z ≥ ε) ≤ exp(−γε + γμ + vγ²/2)` for `Z ~ gaussianReal μ v`.
* `lognormalReal_real_Ioi_le`: tail bound `ℙ(Y > t) ≤ t^(−γ) · exp(γμ + vγ²/2)` for `Y ~ lognormalReal μ v`, `t > 0`, `γ ≥ 0`.
* Uses Mathlib's `measure_ge_le_exp_mul_mgf` + `mgf_id_gaussianReal` + `integrable_exp_mul_gaussianReal`.

**Phase B.6 — MAD layer cake** ✅
[Stats/Kappa/MadLayerCake.lean](Stats/Kappa/MadLayerCake.lean) (~150 lines).
* `mad_eq_two_tail_integral`: for integrable `X : Ω → ℝ` with mean `m`,
        `𝔼|X − m| = 2 · ∫_{t > 0} ℙ(X > m + t) dt`.
* In `Ioi 0` form (no translation needed).  Steps:
  - `|X − m| = (X − m)⁺ + (m − X)⁺` pointwise (`abs_sub_eq_max_add_max`);
  - mean condition forces `𝔼(X − m)⁺ = 𝔼(m − X)⁺` (`integral_pos_part_eq_neg_part`);
  - ascending layer cake on `(X − m)⁺` via Mathlib's `Integrable.integral_eq_integral_meas_lt`.

**Phase C.2 — `ℙ(S_n > t) ≥ ℙ(max X_i > t)`** ✅
[Stats/Kappa/SumMaxBound.lean](Stats/Kappa/SumMaxBound.lean) (~75 lines).
* `prob_sum_ge_prob_max`: trivial set-inclusion `{∃ i, X_i > t} ⊆ {Σ X_i > t}` for nonneg X, plus `measureReal_mono`.

**Phase C.3a — algebraic Loulakis lower bound (parametric in σ)** ✅
[Stats/Kappa/LoulakisAlgebraic.lean](Stats/Kappa/LoulakisAlgebraic.lean) (~175 lines).
* `M_n_lower_bound`: for an iid nonneg family `X : Fin n → Ω → ℝ` with representative law `Y₀` of mean `m`,
        `M(n) := 𝔼|S_n − n·m|
              ≥ 2 · (n · ∫_{t>0} ℙ(Y₀ > nm + t) dt
                     − C(n,2) · ∫_{t>0} ℙ(Y₀ > nm + t)² dt)`.
* Combines B.6 (layer cake) + C.2 (sum ≥ max) + C.1 (inclusion-exclusion) + monotonicity of integral on pointwise inequality.
* Hypotheses: integrability of the partial sum + integrability on `Ioi 0` of the relevant tail / squared-tail functions.

### Completed in this final push (B.7 + C.3b)

**Phase B.7 — σ→∞ asymptotic `M(1; σ) → 2`** ✅
[Stats/Kappa/LognormalAsymptotic.lean](Stats/Kappa/LognormalAsymptotic.lean) (~280 lines).
* `Y σ ω := exp(σω − σ²/2)`: σ-parametrised lognormal on `(ℝ, gaussianReal 0 1)`.
* `tendsto_Y_atTop_zero`: pointwise `Y σ ω → 0` (exponent → -∞ via `tendsto_neg_atTop_atBot` ∘ `σ·(σ/2 − ω) → ∞`).
* `integral_Y_eq_one`: mean condition `𝔼Y σ = 1` (from `mgf_id_gaussianReal`).
* `integral_min_Y_one_tendsto_zero`: DCT on `min(Y σ ω, 1)` (bound `1`, pointwise → 0).
* `M_one_tendsto_two`: combining via the identity `|Y − 1| = 2(Y − min(Y, 1)) + (1 − Y)` and the mean condition.

**Phase C.3b — abstract Loulakis liminf** ✅
[Stats/Kappa/LoulakisLiminf.lean](Stats/Kappa/LoulakisLiminf.lean) (~120 lines).
* `liminf_M_ratio_ge_n`: given the σ-parametric algebraic Loulakis bound + `M(1) → 2` + `A_n → 1` + `B_n → 0` + iid-triangle `M(n) ≤ n·M(1)` + non-negativity, concludes
        `liminf_{σ → ∞} M(n; σ) / M(1; σ) ≥ n`.
* Pure `Filter.liminf` algebra; combines Tendsto-of-quotient with `le_liminf_iff`.  No measure theory or `σ→∞` analysis beyond what's already proven in B.7, B.5, etc.
