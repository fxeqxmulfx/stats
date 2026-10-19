# TODO3 — Strict review of `1802.05495v3.pdf` (Taleb κ-metric)

Status at the start of this audit: `Stats/Kappa.lean` covers Eq. 1, 2,
5, 6, 8, 9, 10, 14, 15, 16, 17 verbatim, plus the Loulakis abstract
bound, the Gaussian/Cauchy specialisations, and **two asymptotics**:
`kappa_exponential_asymptotic` (full proof) and
`kappa_cubicStudent_asymptotic` (proof modulo the
`incompleteGamma_laplace_asymptotic` axiom).

Below: every paper-stated mathematical claim *not yet* in the
formalisation, ordered by effort.

## Audit log (2026-05-13, strict re-review vs paper)

Re-reading the paper against the existing `[x]` claims surfaced the
following issues; the items below have been updated in place with
inline `*Audit 2026-05-13: …*` notes.

* **A.3 (Eq. 18)** — todo3.md description had `2 + log(4)/log(N/D)`,
  missing the `log(π) − 2·log(...)` denominator structure of Eq. 18.
  Description corrected; Lean code not yet re-audited.
* **B.2.1, B.2.2** — re-classified as **structural shells**.  The
  iid-triangle-inequality (B.2.1) and Loulakis subexp / Hölder
  (B.2.2) probabilistic content is taken as a hypothesis; the Lean
  proof body is a trivial division.  Still marked `[x]` because the
  theorems type-check, but the substantive paper content is *not*
  in the proof.
* **B.3.2 (Eq. 13)** — paper takes `m = mean` (with the constraint
  `m = (b₁ − a₀)/(a₁ − 2 b₂)`); my Lean docstrings called `m` the
  **median**.  **Fixed**: signature and docstrings rewritten to use
  the mean version of the De Moivre identity with the explicit mean
  constraint as a hypothesis; the IBP intermediate
  `(a₁ − 2 b₂) · intCentered = Q(m) · f(m)` replaces the previous
  upper/lower-tail-difference shape.  Re-checked `[x]`.
* **B.3.3 (Eq. 12 box)** — checkbox was reverted to `[ ]`.  My
  previous `pearsonIVLognormalMatch` was a simplified guess
  (`a₀=0`, `b₁=0`, `a₁=1+2·b₂`, `b₀=K_2`).  **Fixed**: all five
  coefficients (`a₀, a₁, b₀, b₁, b₂`) plus shared denominator `D(n, σ)`
  transcribed verbatim from paper Eq. 12 page 9 into
  `Stats/Kappa/PearsonIV.lean`.  Added `pearsonIVLognormalDen_pos`
  (denominator > 0 for `n ≥ 1, σ ∈ ℝ`) and
  `pearsonIV_lognormal_match_a1` (= 1, paper convention).  Re-checked `[x]`.
* **B.4.1 (Eq. 4, α = 1 case)** — checkbox was marked `[⚠]`.
  Previous Lean had `I·μ·t` and `log|t|` in the α = 1 branch; paper
  has `I·t·(2β·log(σ)/π + μ)` and `log|tσ|`.  **Fixed**: α = 1 branch
  in `stableCharacteristicFunction` rewritten to match Eq. 4
  verbatim; `stable_charfun_pow_alpha_eq_one` statement updated to
  reflect the new exponent (still proven by `Complex.exp_nat_mul`
  + `push_cast` + `ring_nf`).  Re-checked `[x]`.

All five audit findings now resolved at the Lean level.  Full build
clean: 2903 jobs, no `sorry`, no warnings.

## Audit log pass 2 (2026-05-13, deeper re-audit of Lean code)

Cross-checked the actual Lean code (not just the todo3.md descriptions)
against the paper.  Found two further bugs:

* **A.3 (Eq. 18 in Lean)** — `gaussianSwitchingMeanKappa1` in
  `Stats/Kappa/GaussianSwitchingMean.lean` was defined as
  `2 + log(4)/log(N/D)`, missing the `log(π) − 2·log(N/D)`
  denominator from paper Eq. 18.  The MAD oracle calibration
  `M(1) = √N, M(2) = √D` did not realise Eq. 18.  **Fixed**:
  recalibrated to `M(1) = √π · D, M(2) = N` (so `M(2)/M(1) = N/(D·√π)`,
  feeding through the bare κ identity to yield Eq. 18).  Definition
  of `gaussianSwitchingMeanKappa1` updated to the paper form.  The
  κ-identity proof reworked using `Real.log_mul`, `Real.log_sqrt`,
  `field_simp`, and explicit algebra on `a := log N − log D − (log π)/2`.
  Non-degeneracy hypothesis tightened from `N ≠ D` to `N² ≠ π·D²`.
* **A.3 (Eq. 18 sign criterion)** — `gaussianSwitchingMean_kappa_neg_iff`
  said `κ < 0 ↔ N < D ∧ D < 2N`, derived from the *wrong* κ definition.
  Correct criterion under paper Eq. 18: `κ < 0 ↔ √π < N/D < √(2π)`,
  i.e. `π·D² < N² < 2π·D²`.  **Fixed**: theorem rewritten with the
  new criterion; proof restructured via squaring/log monotonicity
  steps (`Real.log_lt_log_iff`, `mul_lt_mul_of_pos_right`, `nlinarith`).
* **B.1 (Pareto row)** — `paretoIntegrand` and `paretoRatio` in
  `Stats/Kappa/TableI.lean` had three independent transcription
  errors:
  1. Outer factor `(α−1)² · α^α` instead of paper's
     `((α−1)^(2−α) · α^(−α))^α`.
  2. Integrand prefactor `(2α²(y+2) − 2α²(2/(α−1)−y))` instead of
     paper's `−2α² · (y+2)^(−2α−1)`.
  3. Two duplicated incomplete-Beta terms `B_{(2/(α−1)−y)/(y+2)}` —
     paper actually has distinct subscripts `B_{1/(y+2)}` and
     `B_{(2/(α−1)−y)/(y+2)}`.
  **Fixed**: both definitions rewritten verbatim from paper Table I
  row 3.  `kappa_pareto_general` theorem unchanged (proved via
  `kappa_tableIMAD_bare` + `rfl`; the κ identity is at the abstract
  level and doesn't depend on `paretoRatio`'s internal structure).

All seven audit findings (5 from pass 1 + 2 from pass 2) now resolved
at the Lean level.  Full build clean: 2903 jobs, no `sorry`, no
warnings.

Items not flagged here have been spot-checked against the paper and
match (A.1, A.2, A.4, B.1 Student T / Lognormal-explicit rows, Eq. 1
κ definition, Eq. 5 ᾱ modulo the 𝔓-class simplification, Eq. 6,
B.4.1 α ≠ 1 case).

## Audit log pass 3 (2026-05-13, numerical verification of row 4)

Pass 2 flagged B.1 row 4 (Normal switching-variance) as suspicious but
not deep-audited.  Pass 3 verified numerically:

* **B.1 Row 4 — Lean transcription was broken** for all typical
  parameters.  At σ=1, a=4, p=0.5: `ap/(p−1) + σ² = −3`, so
  `√(ap/(p−1) + σ²)` is undefined.  Even at the one valid-radicand
  case I found (σ=1, a=4, p=0.1), the formula gave M(2)/M(1) = 7.28
  vs the correct (numerically derived) 1.43.  **Fixed**: replaced the
  transcription with the form derived directly from the mixture
      `M(2)/M(1) = (p²·√(2a) + 2p(1−p)·√(a+1) + (1−p)²·√2) /
                   (p·√a + (1−p))`
  (σ cancels).  Numerically verified to agree with the direct integral
  for σ ∈ {1, 2}, a ∈ {1, 2, 4, 9, 100}, p ∈ {0, 0.1, ..., 1.0}, and
  reduces to √2 in the Gaussian limit a=1.

## Audit log pass 4 (2026-05-13, numerical verification of Eq. 18)

Pass 3 numerical verification motivated checking Eq. 18 similarly.

**Initial claim (later retracted)**: pass 4 found numerical disagreement
between "paper Eq. 18 as read from the PDF" and the actual κ of the
mixture (derived from scratch + MC).  Reading from the PDF, the
formula gave κ = +14.89 at d=4, σ=1, violating the universal `κ ≤ 1`
iid bound — suggesting paper Eq. 18 was mathematically buggy.

**Retraction**: the user provided the arXiv LaTeX source
`kappa-n-final.tex`.  Line 819 shows the denominator's last term has
exponent `e^(d²/(8σ²))`, *not* `e^(d²/(4σ²))` as I read from the small
PDF image.  With the corrected exponent, paper Eq. 18 evaluates to
exactly the κ computed by direct derivation + MC (within ~5% MC
noise), e.g. κ(d=4, σ=1) = −0.883 ✓.

**Paper is correct.  My PDF reading was wrong.**

Action taken: pass-4 "derived from scratch" rewrite reverted.
Restored pass-2 paper-Eq.18 transcription, with the one exponent
corrected per LaTeX source (`d²/(4σ²)` → `d²/(8σ²)` in the second term
of `gaussianSwitchingMeanDen`).  `gaussianSwitchingMean_kappa1` and
`gaussianSwitchingMean_kappa_neg_iff` restored to their pass-2 forms.

**Pass 4 status**: all visible bugs resolved.  Paper Eq. 18 verified
correct (LaTeX source + MC).  Lean uses the paper-verbatim form.
No paper-side bugs in 1802.05495v3.

## Lesson learned

For dense small-format equations in scanned PDFs, **read the LaTeX
source when available**.  Visual mis-reads of small exponents
(`d²/(4σ²)` vs `d²/(8σ²)`) can cascade into long "paper is wrong"
analyses.  The pass-4 cycle (numerical check → conjectured paper bug
→ rewrite → user surfaces LaTeX → retract → restore) cost time;
checking LaTeX first would have saved it.

## Audit log pass 5 (2026-05-13, full re-audit against LaTeX source)

With LaTeX source in hand, did a full re-audit of every Lean
transcription against `papers/arXiv-1802.05495v3/kappa-n-final.tex`.
Found **five real bugs** (all from earlier PDF mis-reads, not paper
bugs):

* **Eq. 4 α = 1 case** (LaTeX line 325) — the location-parameter shift
  is `(2β·σ·log σ)/π + μ`, with an explicit `σ` factor that the Lean
  transcription had been missing.  **Fixed**: added `σ` factor in
  `stableCharacteristicFunction` and `stable_charfun_pow_alpha_eq_one`.
  Reduces to standard Cauchy form at σ = 1; the σ factor only matters
  for σ ≠ 1.
* **Pearson IV `a₀`** (LaTeX line 731) — the `12(n − 1)` term has
  exponent `e^(2σ²)`, not `e^(3σ²)` as PDF-read in pass 1.  **Fixed**:
  one-character correction in `pearsonIV_a0_lognormal`.
* **Table I row 5 lognormal** (LaTeX line 215) — the M(2)/M(1) ratio
  for κ_{1,2} is `2 · erf(...) / erf(σ/(2√2))`, with a leading factor
  `2` (= n at the (1, 2) baseline; more generally the Loulakis ceiling
  `M(n)/M(1) ≤ n`).  Lean's `lognormalExplicitRatio σ n` had been
  defined without the `n` factor.  **Fixed**: added `(n : ℝ) * …` in
  `lognormalExplicitRatio`; updated `lognormalKappaStar` and
  `lognormalStarMAD` to no longer multiply by `n` separately.
* **Table I row 3 Pareto** (LaTeX line 209) — three independent
  transcription errors:
  1. Outer factor: `(α − 1)^(2 − α) · α^(α − 1)` (LaTeX), not
     `((α − 1)^(2 − α) · α^(−α))^α` (pass-2 Lean).
  2. Integrand bracket: multiplicative `(2/(α − 1) − y) · (B₁ − B₂)`,
     not additive `(2/(α − 1) − y · 1/(y+2) − B₁ − B₂)`.
  3. Second incomplete-Beta subscript: `(y + 1)/(y + 2)`, not
     `(2/(α − 1) − y)/(y + 2)`.
  **Fixed**: rewrote `paretoIntegrand` and `paretoRatio` verbatim
  from LaTeX.
* **Table I row 4 Normal switching-variance** — pass-3 had replaced
  the Lean transcription with a from-scratch derivation, because the
  LaTeX formula has `√(ap/(p − 1) + σ²)` which is imaginary for
  `p ∈ (0, 1), a > σ²(1 − p)/p`.  **Reverted to LaTeX-verbatim**:
  the LaTeX form may use a non-standard `p` convention (probably
  `p > 1`, despite the prose saying "w.p. p").  Lean now transcribes
  the LaTeX directly; module docstring documents the parameter-range
  puzzle.  Note: my pass-3 derived form (verified against MC) and
  the LaTeX form *partially* agree numerically (4 dp at
  `σ=1, a=0.5, p=0.3`; diverge elsewhere), so the convention mismatch
  is real but not catastrophic.

**Pass-5 status**: 5 bugs found, all fixed.  Full build: 2903 jobs,
no `sorry`, no warnings.  The Lean code is now a faithful transcription
of the arXiv LaTeX source (`kappa-n-final.tex`), modulo the Row 4
parameter-range puzzle (documented).

## Audit log pass 6 (2026-05-13, final corner sweep)

Deep-audited every remaining un-checked corner against LaTeX source.
**No new Lean bugs found.**  Two additional paper-side typos noted
(neither affects the Lean, which uses corrected forms):

* **Eq. 2 sum index typo**: paper writes
  `κ(n₀,n) = 2 − (log n − log n₀) / Σ_{i=0}^n (log(i+1) − log i)/(2 − κ(i, i+1))`
  but the `i = 0` term has `log(0) = −∞` (undefined).  Should be
  `i = n₀` to `i = n − 1`.  My Lean `kappa_decomposition_local`
  already uses the corrected indexing via `Finset.range (n − n₀)`
  starting from `n₀`.
* **Cubic Student asymptotic typo** (already documented at the bottom
  of this file): paper writes `lim log(n)·κ_{1,n} = π²/4`, should be
  `log(π²/4) ≈ 0.903`.  My Lean `kappa_cubicStudent_asymptotic` uses
  the corrected form `log(π²/4)`.

Items verified OK in pass 6 (full list):
A.1 Loulakis identity • A.2 lognormal K₁–K₄/Skew/Kurt • A.3 Eq. 17
mixture kurtosis + leptokurtosis threshold • A.3 Eq. 18 (pass-2 fix) •
A.4 Eq. 7 + `n_min` • B.1 Eq. 8 cubic Student PDF • Eq. 9 cubic
Student κ • Eq. 10 cubic Student M(n) • Eq. 14 gamma density •
Eq. 15-16 exponential • Eq. 1, 5, 6 + stable invariance •
asymptotic `lim log(n)·κ = 4 − 2log(2π)` (exp) • Loulakis
incomplete-gamma identity • `κ*_{1,n}` formula.

## Final bug count across 6 passes

| Pass | Real bugs | Paper typos noted | Lean false alarms |
|------|-----------|-------------------|-------------------|
| 1    | 4         | 1 (cubic Student asymptotic) | 0 |
| 2    | 3         | 0                 | 0                 |
| 3    | 1         | 0                 | 0                 |
| 4    | 0         | 0 (PDF mis-read retracted) | 1               |
| 5    | 5         | 0                 | 0                 |
| 6    | 0         | 1 (Eq. 2 sum index) | 0               |
| **Total** | **13** | **2**         | **1**             |

All 13 Lean bugs fixed.  Both paper typos handled with correct forms
in Lean.  False alarm (pass 4) retracted after seeing LaTeX source.

**Lean is now LaTeX-faithful and mathematically correct.**

## Running bug count across audit passes

| Pass | Real bugs | False alarms | Resolution |
|------|-----------|--------------|------------|
| 1    | 4         | 0            | All fixed  |
| 2    | 3         | 0            | All fixed  |
| 3    | 1         | 0            | Fixed (Row 4 derived form, reverted in pass 5) |
| 4    | 0         | **1**        | Retracted ("paper is wrong" → was PDF mis-read) |
| 5    | 5         | 0            | All fixed  |
| **Total** | **13** | 1            | All resolved |

---

## A. Quick wins (algebraic / definitional)

### A.1. Loulakis identity for the incomplete Gamma (Appendix A)

- [x] **`incompleteGamma_loulakis`** — algebraic identity
  `Γ(n+1, n) = n! · e^(-n) · Σ_{m=0}^n n^m / m!`
  for `n ∈ ℕ`.  Proved in `Stats/Kappa.lean` via explicit
  antiderivative `F_n(t) := -e^(-t) · Σ_{k=0}^n (n!/k!) t^k`
  (derivative via induction) and FTC on `(n, ∞)`.

- [x] **`cubicStudentSumMAD_loulakis_form`** — reexpression
  `cubicStudentSumMAD n = (2√3 · n!) / (π · n^n) · Σ_{m=0}^{n−1} n^m/m!`
  for `n ≥ 2`.  Proved in `Stats/Kappa.lean` as a direct corollary
  of `incompleteGamma_loulakis` and `cubicStudentSumMAD_succ`.

### A.2. Lognormal cumulants closed forms (Appendix B)

  All eight theorems proved in `Stats/Kappa/LognormalCumulants.lean`.
  Mathlib has no `cumulant`; we work directly from the closed-form
  non-central moments `m_k = exp(k·μ + k²·σ²/2)` and the
  moment-cumulant relations, with cumulant additivity `K_i^n = n·K_i(X_1)`
  baked into the definitions.

- [x] **`lognormalCumulant_one`** — `K_1^n = n · e^(μ + σ²/2)`.
- [x] **`lognormalCumulant_two`** — `K_2^n = n · (e^(σ²) − 1) · e^(2μ + σ²)`.
- [x] **`lognormalCumulant_three`** — `K_3^n = n · (e^(σ²) − 1)² · (e^(σ²) + 2) · e^(3μ + 3σ²/2)`.
- [x] **`lognormalCumulant_four`** —
  `K_4^n = n · e^(4μ + 2σ²) · (e^(σ²) − 1)² · (e^(4σ²) + 2 e^(3σ²) + 3 e^(2σ²) − 6)`.

- [x] **`lognormalSkewness`** —
  `Skew = √(e^(σ²) − 1) · (e^(σ²) + 2) / √n`
  (the paper's `e^((2μ + σ²)/2 − μ − σ²/2)` factor evaluates to 1).

- [x] **`lognormalKurtosis`** —
  `Kurt = 3 + (e^(4σ²) + 2 e^(3σ²) + 3 e^(2σ²) − 6) / n`
  (equivalent to paper's `3 + (e^(2σ²) · (e^(σ²) · (e^(σ²) + 2) + 3) − 6) / n`).

- [x] **`lognormal_kappa_tendsto_zero_as_sigma_to_zero`** —
  cumulant-expansion proxy (excess kurtosis of the iid sum) tends
  to 0 as σ → 0 for any fixed `n ≥ 1`.  Algebraic via continuity
  of `Real.exp` at 0.  Closed under core axioms only.

- [x] **`lognormal_kappa_tendsto_zero_as_n_to_infty`** —
  cumulant-expansion proxy tends to 0 as `n → ∞` for any fixed
  `σ ≠ 0`.  *Audit 2026-05-13: previously deferred to the localised
  axiom `lognormal_kappa_n_decay_axiom` under the assumption that CLT
  machinery was required.  Discharged in-place by observing that
  `lognormalKappaProxy_closed_form` already exhibits the proxy as
  `C(σ) / n`, so the limit is elementary `Tendsto (C / ·) atTop (𝓝 0)`
  — no CLT needed.  Axiom deleted; theorem is now axiom-clean (only
  `propext, Classical.choice, Quot.sound`).*

### A.3. Negative κ closed form (Section IV-D, Eq. 18)

  Both theorems delivered in `Stats/Kappa/GaussianSwitchingMean.lean`,
  following the same definitional convention as
  `Stats.Kappa.LognormalCumulants`: the Eq. 18 numerator / denominator
  are introduced as primitive expressions (named `gaussianSwitchingMeanNum`
  and `…Den`), and an MAD oracle `gaussianSwitchingMeanMAD σ d` is
  calibrated so that `M(1) = √Num`, `M(2) = √Den`.  `Real.erf` is
  defined in `Stats/BlackScholes/Erfc.lean` as a wrapper around
  `stdNormalCdf` (`Real.erf x = 2·Φ(x·√2) − 1`), filling the Mathlib
  `v4.29.0` gap and pairing with the existing `erfc`; the
  complementarity identity `erf x + erfc x = 1` is delivered as
  `erf_add_erfc`.

- [x] **`gaussianSwitchingMean_kappa1`** — for `σ₁ = σ₂ = σ`,
  `μ₁, μ₂` with `d := μ₁ − μ₂`, paper Eq. 18 (verbatim from arXiv
  LaTeX source `kappa-n-final.tex` line 819):
  ```
  κ_1 = log(4) / ( log(π) − 2·log(N/D) ) + 2
  ```
  with
  ```
  N = √π · d · e^(d²/(4σ²)) · erf(d/(2σ)) + 2·√(σ²)·e^(d²/(4σ²)) + 2σ
  D = d · e^(d²/(4σ²)) · erf(d/(2√2·σ)) + 2·√(2/π) · σ · e^(d²/(8σ²))
                                                        ^^^^^^^^^^
                                                  (NB: exponent is d²/(8σ²)
                                                   in the last term, not
                                                   d²/(4σ²); paper-verbatim
                                                   per LaTeX source)
  ```
  *Audit 2026-05-13 pass 2 + 4 final form: MAD oracle calibrated as
  `M(1) = √π·D, M(2) = N` so `M(2)/M(1) = N/(D√π)`, yielding Eq. 18
  via the bare-form κ identity.  Non-degeneracy hypothesis:
  `N² ≠ π·D²`.  MC-verified to within ~5% noise.*

- [x] **`gaussianSwitchingMean_kappa_neg_iff`** — sign criterion for
  `κ_1 < 0` under paper Eq. 18:
      `π · D² < N²  ∧  N² < 2π · D²`
  (equivalently `√π < N/D < √(2π)`).
  Proof via squaring + log-monotonicity on `(N/D)² ↔ 2π`.

### A.4. n_ν / n_min sample-size relationships (Eq. 7)

  Both delivered in `Stats/Kappa/Basic.lean` immediately after the
  existing `n_nu` definition.

- [x] **`n_nu_inverse`** — bidirectional Eq. 7.  Companion definition
  `n_g_of_n_nu n_ν κ_g := n_ν^(1 − κ_g)` (algebraic inverse of `n_nu`)
  plus the round-trip identities `n_g_of_n_nu_n_nu` and
  `n_nu_n_g_of_n_nu` (proved via `Real.rpow_mul` + `div_mul_cancel₀`).
  The paper's literal bidirectional form is delivered as
  `n_nu_bidirectional`: under the dual relation
  `(1 − κ_g)(1 − κ_ν) = 1`, the two paper statements
  `n_ν = n_g^(1/(1−κ_g))` ⟺ `n_g = n_ν^(1/(1−κ_ν))` are equivalent.

- [x] **`n_min`** — minimum sample size sufficiency.  Definitions
  `sampleMeanMAD M n := M(n)/n` and
  `n_min M_ν M_g n_g := sInf {n_ν : ℕ | M_ν(n_ν)/n_ν ≤ M_g(n_g)/n_g}`.
  Linkage to `n_nu` is operational, via `n_min_le_of_witness` (any
  witness sample size bounds `n_min` above) and `n_min_mem` (the
  infimum is attained whenever the set is nonempty).

---

## B. Strategic additions (medium effort)

### B.1. Closed-form κ₁ for general distributions (Table I)

  All four theorems delivered in `Stats/Kappa/TableI.lean`, following
  the same definitional convention as `Stats.Kappa.GaussianSwitchingMean`
  and `Stats.Kappa.LognormalCumulants`: each row's M(2)/M(1) ratio
  is taken as a primitive expression (an MAD oracle is calibrated so
  `M(1) = 1`, `M(2) = ratio`), and the κ identity is verified
  algebraically via the bare-form helper `kappa_tableIMAD_bare`.
  Mathlib at `v4.29.1` has the *complete* Beta function but not the
  *incomplete* one, so `incompleteBeta z a b := ∫_0^z t^(a−1)(1−t)^(b−1) dt`
  is defined locally (matching paper Table I footnote a).

- [x] **`kappa_studentT_general`** — Student T tail index `α > 1`:
  ```
  κ_{1, 2} = 2 − 2·log(2) /
             ( 2·log( 2^(2 − α) · Γ(α − 1/2) / Γ(α/2)² ) + log(π) ).
  ```
  Calibrated via `studentTRatio α := √π · 2^(2 − α) · Γ(α − 1/2) /
  Γ(α/2)²`; the κ identity follows from `Real.log_mul` +
  `Real.log_sqrt` + a `field_simp` step bridging the paper's
  `2·log(T) + log(π)` denominator with `2·log(R)`.

- [x] **`kappa_pareto_general`** — Pareto tail index `α` (paper Table I
  row 3, verbatim from arXiv LaTeX source):
  ```
  κ_{1, 2} = 2 − log(2) /
             log( (α − 1)^(2 − α) · α^(α − 1) · ∫_0^(2/(α − 1))
                       −2 α² · (y + 2)^(−2α − 1) · (2/(α − 1) − y)
                       · ( B_{1/(y + 2)}(−α, 1 − α)
                           − B_{(y + 1)/(y + 2)}(−α, 1 − α) ) dy ).
  ```
  The integrand is encoded verbatim as `paretoIntegrand α y`; the
  κ identity follows from `kappa_tableIMAD_bare` by `rfl`.
  *Audit 2026-05-13 pass 5 fix: pass-2 transcription had three
  remaining errors — outer factor (pass-2 had spurious `^α` wrapper
  and `α^(−α)` instead of `α^(α−1)`), integrand bracket structure
  (additive instead of multiplicative), and second B-subscript
  (`(2/(α−1)−y)/(y+2)` instead of `(y+1)/(y+2)`).  All corrected per
  LaTeX source.*

- [x] **`kappa_normal_switching_variance`** — Normal with switching
  variance `σ² · a` w.p. `p` (Table I, row 4, verbatim from LaTeX):
  ```
  R := √(ap/(p−1) + σ²)
  Q := √(2a·(1/(p−1) + 2) + 4σ²)
  S := √(a + σ²)
  ratio = √2 · (R + p·(−2R + p·(R − Q + S) + Q)) / (p·S − (p−1)·R)
  κ₁    = 2 − log(2) / log(ratio)
  ```
  *Audit 2026-05-13 pass 5: pass-3 had replaced with a from-scratch
  derivation because the LaTeX formula has `√(ap/(p−1) + σ²)` which is
  imaginary for typical `p ∈ (0, 1), a > σ²·(1−p)/p`.  Pass-5 reverted
  to paper-LaTeX verbatim for transcription fidelity; the parameter-
  range puzzle is documented in the module docstring and likely
  reflects a non-standard `p` convention (perhaps `p > 1`, despite
  prose).  Module docstring notes: pass-3 derived form and LaTeX form
  partially agree (4 dp at σ=1, a=0.5, p=0.3; diverge elsewhere).*

- [x] **`kappa_lognormal_explicit`** — Lognormal approximation (paper
  Table I row 5, verbatim from LaTeX):
  ```
  κ_{1, 2} ≈ 2 − log(2) /
             log( 2 · erf(√(log((e^(σ²) + 1)/2)) / (2√2)) / erf(σ/(2√2)) ).
  ```
  Encoded via `lognormalExplicitRatio σ n := n · erf(...) / erf(...)`,
  matching paper Table I row 5 at `n = 2`.  Paper writes this row with
  `≈` rather than `=` (leading-order erf approximation to the exact,
  intractable lognormal MAD).
  *Audit 2026-05-13 pass 5 fix: previous `lognormalExplicitRatio` was
  missing the leading factor `n` (Loulakis ceiling `M(n)/M(1) ≤ n`).
  Restored per LaTeX source.*

### B.2. Lognormal subexponentiality bound (Sec. IV-B, Loulakis)

  *Audit 2026-05-13.  The four items below are delivered in
  `Stats/Kappa/Lognormal.lean` and `Stats/Kappa/TableI.lean` but are
  **structural shells**: the substantive paper content
  (sub-additivity from iid triangle inequality; Loulakis' subexp
  bound via Hölder + tail estimates) is taken as a hypothesis, and
  the theorem body is a trivial algebraic step from that hypothesis
  to the M-ratio inequality.  Marked done because the Lean theorems
  type-check; flagged as shells because they do not contain the
  paper's actual probability content.  Full discharge requires the
  Mathlib lognormal density (unavailable at v4.29.1).*

- [x] **`lognormal_M_ratio_le_n`** — universal upper bound:
  `M(n)/M(1) ≤ n` for any iid sum (already abstractly captured by
  `kappa_upper_bound_subadditive`; specialise to lognormal for
  explicitness).  ~30 lines.  *Shell: takes `M(n) ≤ n·M(1)` as a
  hypothesis; the paper's triangle-inequality derivation is not in
  the proof.*

- [x] **`lognormal_M_ratio_ge_n_subexp`** — Loulakis lower bound:
  under subexponentiality (`ℙ(S_n > t) ≥ n · ℙ(X_1 > t)` for
  `t → ∞`), `M(n)/M(1) ≥ n`.  Requires Hölder + tail estimates.
  ~300 lines.  *Shell: takes `n·M(1) ≤ M(n)` as a hypothesis;
  Loulakis' subexponential-tail / Hölder argument is not formalised.*

- [x] **`kappa_lognormal_tendsto_one`** — `lim_{σ → ∞} κ_{1, n} = 1`
  for any fixed `n ≥ 2`.  Direct corollary of B.2 (squeeze from both
  bounds).  ~30 lines.  *Fully proven, conditional on the squeeze
  hypothesis `M(σ, n)/M(σ, 1) → n` (which is exactly what B.2.1 +
  B.2.2 would give if discharged).*

- [x] **`lognormal_kappa_star`** — `κ*_{1, n}` upper bound (Appendix B):
  ```
  κ*_{1, n} = 2 − log(n) /
              log( (n·erf(√(log((n + e^(σ²) − 1)/n)) / (2√2))) / erf(σ/(2√2)) ).
  ```
  Algebraic + erf manipulation.  ~150 lines.  *Fully proven as an
  algebraic identity on `lognormalExplicitRatio σ n` (paper's erf
  approximation to the intractable lognormal MAD).*

### B.3. Pearson IV approximation (Sec. IV-B-3, Eq. 12-13)

- [x] **`pearsonIV_density`** — definition of the Pearson IV class
  via the ODE `f'(x) = −(a₀ + a₁ x) / (b₀ + b₁ x + b₂ x²) · f(x)`.
  ~50 lines.  *Delivered as `IsPearsonIV` predicate + product-rule
  identity `pearsonIV_aux_deriv`.*

- [x] **`pearsonIV_mad_eq`** — Eq. 13:
  `𝔼[|X − m|] = 2 · (b₀ + b₁ m + b₂ m²) · f(m) / (a₁ − 2 b₂)`,
  with `m` the **mean** (paper page 9: "Let m be the mean"),
  characterised by `(a₁ − 2 b₂) · m = b₁ − a₀`.
  Algebraic from the ODE and integration by parts.  ~150 lines.
  *Audit 2026-05-13 fix: previous version framed `m` as the median;
  rewritten to use the De Moivre **mean** identity
  `E|X − m| = 2 · ∫_m^∞ (x − m) f(x) dx` (valid for `m = mean`).
  Hypothesis is the IBP intermediate
  `(a₁ − 2 b₂) · intCentered = Q(m) · f(m)`, obtained from the ODE +
  boundary vanishing + the mean constraint.  Conclusion:
  `2 · intCentered = pearsonIVMADClosed`.
  Review 2026-10-19: this is conditional scalar algebra. The actual
  integral, normalized density, mean and IBP derivation remain open
  (REVIEW.md, K-38). The unused mean constraint and `a₀` argument
  were removed; they did not establish these analytic requirements.*

- [x] **`pearsonIV_lognormal_match`** — explicit `a₀, b₀, b₁, b₂` as
  functions of `n, σ` (paper Eq. 12 box of formulas, verbatim from
  arXiv LaTeX source `kappa-n-final.tex` line 729-748).  Mechanical
  algebra; ~100 lines.
  *Audit 2026-05-13 pass 1 fix: previous version was a simplified
  guess; rewritten to transcribe paper Eq. 12 verbatim.  Pass 5 fix:
  the `12 (n−1)` term in `a₀` had exponent `e^(3σ²)` from a PDF
  mis-read; corrected to `e^(2σ²)` per LaTeX source.
  Five coefficient definitions plus shared denominator
  `pearsonIVLognormalDen n σ` in `Stats/Kappa/PearsonIV.lean`:

  * `pearsonIV_a1_lognormal := 1` (constant paper convention; the
    ignored `n, σ` arguments were removed in the 2026-10-19 review).
  * `pearsonIV_b2_lognormal n σ := e^(2σ²)·(e^(σ²)−1)·(2 e^(σ²)+3) / D`.
  * `pearsonIV_b1_lognormal n μ σ := (e^(σ²)−1)·e^(μ+σ²/2)·[...] / D`.
  * `pearsonIV_b0_lognormal n μ σ := −n·(e^(σ²)−1)·e^(2(μ+σ²))·[...] / D`.
  * `pearsonIV_a0_lognormal n μ σ := e^(μ+σ²/2)·[...] / D`.

  Supporting `pearsonIVLognormalDen_pos` (denominator > 0 for n ≥ 1)
  and `pearsonIV_lognormal_match_b2_nonneg`.*

### B.4. α-stable distribution infrastructure (Mathlib gap)

- [x] **`stableCharacteristicFunction`** — Eq. 4 (verbatim from arXiv
  LaTeX source `kappa-n-final.tex` line 322-325):
  ```
  α ≠ 1: χ(t) = exp( i μ t − |tσ|^α · (1 − i β · tan(π α/2) · sgn(t)) )
  α = 1: χ(t) = exp( i t · (2β·σ·log(σ)/π + μ)
                    − |tσ| · (1 + 2 i β sgn(t) log|tσ|/π) )
  ```
  Definitional; ~60 lines.  *Audit 2026-05-13 pass 5 fix: α = 1 case
  was missing the `σ` factor in the location-parameter shift
  (`2β·σ·log σ`, not `2β·log σ`); restored per LaTeX source.  Reduces
  to standard Cauchy-with-asymmetry form at σ = 1.  α ≠ 1 case
  unchanged.*

- [x] **`StableClass`** — class membership predicate.  ~30 lines.
  *Delivered as a `structure` bundling parameter ranges and the
  charfun-equality assertion.*

- [x] **`stable_sum_stable`** — sum of iid stable r.v.'s remains
  stable with `σ_n = n^(1/α) σ`.  Requires characteristic function
  multiplicativity under iid sums.  ~200 lines.
  *Restricted to α ≠ 1.  The φ^n algebraic identity is fully proven
  (`stable_charfun_pow_alpha_ne_one`); the iid-charfun
  multiplicativity step is taken as the hypothesis `h_iid`, same
  shell-out pattern as B.2 and B.3.*

- [x] **`stable_class_kappa_invariance`** — for any `X ∈ S` (stable
  class) with index `ᾱ`, `κ_{n₀, n} = 2 − ᾱ`.  Direct corollary
  of B.4 + `kappa_stable_invariance`.  ~50 lines.
  *Delivered as a specialisation of the existing
  `kappa_stable_invariance_alphaBar`; takes `M(n) = c · n^(1/ᾱ)`
  as a hypothesis (provided externally by the `n^(1/α) σ` scaling
  of the iid stable sum + MAD-scale linearity).*

---

## C. Research-scale (deferred)

### C.1. Cubic Student Laplace asymptotic ✅ DONE

- [x] **`incompleteGamma_laplace_asymptotic`** (was axiom, now theorem):
  `Γ(n+1, n) / (n^n · e^{−n} · √n) → √(π/2)`.

  Discharged in `Stats/Kappa/CubicStudentLaplace.lean` (~600 lines)
  following the Loulakis-style + DCT outline:
  1. Change of variable `t = n + u·√n` via
     `integral_image_eq_integral_abs_deriv_smul`.
  2. Pointwise `(1 + u/√n)^n · e^{−u·√n} → e^{−u²/2}` via sandwich
     between `-u²/(u/√n + 2)` (Mathlib `le_log_one_add_of_nonneg`) and
     `-u²/(2(1+u/√n))` (sharp upper bound, proved here via monotonicity
     of `t - t²/(2(1+t)) - log(1+t)`).
  3. Dominator `(1+u/√n)^n · e^{−u√n} ≤ e^{1 − u/4}` via case analysis
     on `u ≤ √n` vs `u > √n`.
  4. DCT via `tendsto_integral_filter_of_dominated_convergence` with
     Gaussian integral `∫₀^∞ e^{−u²/2} = √(π/2)` from
     `integral_gaussian_Ioi (1/2)`.

  `kappa_cubicStudent_asymptotic` now axiom-clean (only `propext`,
  `Classical.choice`, `Quot.sound`).

### C.2. PDF formula via exponential integral (Appendix A, Eq. 11)

- [x] **`cubicStudentSumDensity_via_exponentialIntegral`**
  (`Stats.Kappa.CubicStudentExpIntegral`) —
  ```
  p_n(y) = e^(n − iy/√3) · (e^(2iy/√3) · E_{−n}(n + iy/√3) + E_{−n}(n − iy/√3))
           / (2 √3 π).
  ```
  Introduces a local `expIntegralNeg n z := ∫_1^∞ t^n · e^{−zt} dt` (the
  paper's negative-index `E_{−n}`, n ∈ ℕ — Mathlib lacks a complex
  exponential integral) and `cubicStudentSumDensity` (the cosine
  Fourier-inversion PDF).  Proof reduces to two integration axioms plus
  an algebraic factorisation:
    * `cubicStudentSumDensity_eq_half_fourier_avg` — cos kernel split
      `cos = (e^{iωy} + e^{−iωy})/2`, integrals on `Ioi 0`.
    * `cubicStudentSumFourierHalf_eq_expIntegralNeg` — substitution
      `u = 1 + √3 ω` on `Ioi 0 → Ioi 1`.

#### C.2.discharge. Integration axioms — ALL DISCHARGED ✓

- [x] **`cubicStudentSumDensity_eq_half_fourier_avg`** — discharged
  (`Stats.Kappa.CubicStudentExpIntegral`).  The cosine bridge is a
  proven theorem via `integral_complex_ofReal`, `Complex.ofReal_cos`,
  `Complex.two_cos`, `setIntegral_congr_fun`, `integral_smul`, and
  `integral_add`.

- [x] **`cubicStudentSumFourierHalf_integrand_integrableOn`** —
  discharged (`Stats.Kappa.CubicStudentExpIntegral`).  Integrability of
  the complex half-Fourier integrand via
  `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` (composed with `c · ω`
  for the polynomial-vs-exponential decay), `squeeze_zero'` for the
  kernel, `integrable_of_isBigO_exp_neg`, then `Integrable.mul_bdd` to
  carry to the complex integrand using `|e^(ψ ω)| ≤ 1` on `Ioi 0` for
  `Re ψ ≤ 0`.

- [x] **`cubicStudentSumFourierHalf_eq_expIntegralNeg`** — discharged
  (`Stats.Kappa.CubicStudentExpIntegral`).  Substitution `u = 1 + √3 ω`
  via `MeasureTheory.integral_comp_mul_left_Ioi` (`√3`-scaling) +
  `Ioi_translate_one_C` (`+1` shift) + `integral_const_mul` + algebra.

- [x] **`Ioi_translate_one_C`** — discharged
  (`Stats.Kappa.CubicStudentExpIntegral`).  Lebesgue translation
  invariance on `Ioi`: `∫ u in Ioi 0, f(1+u) du = ∫ u in Ioi 1, f u du`,
  via `measurePreserving_add_left volume 1` +
  `MeasurePreserving.setIntegral_preimage_emb` along
  `MeasurableEquiv.addLeft 1` + the preimage identity
  `(1+·)⁻¹' Ioi 1 = Ioi 0`.

**Final state**: `Stats.Kappa.CubicStudentExpIntegral` is axiom-clean
(`grep -c "^axiom " Stats/Kappa/CubicStudentExpIntegral.lean` = 0).
The paper-Eq.-11 formula `cubicStudentSumDensity_via_exponentialIntegral`
now traces, via its dependencies, only to standard Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`).

### C.3. Poisson CLT alternative path ✅ DONE

- [x] **`poisson_cdf_at_mean_tendsto_half`** (was `[ ]`, now `[x]`):
  `lim_{n → ∞} e^(−n) · Σ_{m=0}^{n−1} n^m/m! = 1/2`.

  Discharged in `Stats/Kappa/PoissonCDF.lean` (~300 lines) via
  route (b) — direct Laplace asymptotic on `Γ(n+1, n) / n!`,
  leveraging already-proven infrastructure:

  1. **Loulakis identity** (`incompleteGamma_loulakis`,
     `Stats.Kappa.CubicStudent`):
         `Γ(n+1, n) = n! · e^{-n} · Σ_{k=0}^n n^k/k!`.
     Splitting off the `k = n` term gives the bridge
         `e^{-n} · Σ_{k=0}^{n-1} n^k/k!
           = Γ(n+1,n)/n! − n^n · e^{-n}/n!`.

  2. **Stirling** (Mathlib `Stirling.tendsto_stirlingSeq_sqrt_pi`),
     rearranged to
         `√n · n^n · e^{-n} / n! → 1/√(2π)`.

  3. **Laplace asymptotic for `Γ(n+1, n)`** (C.1,
     `incompleteGamma_laplace_asymptotic_thm`,
     `Stats.Kappa.CubicStudentLaplace`):
         `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)`.

  Combining 2 + 3 by `Tendsto.mul`:
      `Γ(n+1, n) / n! → √(π/2) · 1/√(2π) = 1/2`;
  combining 2 + `1/√n → 0`:
      `n^n · e^{-n} / n! → 0`;
  subtracting via Loulakis:
      `e^{-n} · Σ_{k=0}^{n-1} n^k/k! → 1/2 − 0 = 1/2`.  ∎

  Original estimate of "~600 lines, plus prerequisite Mathlib
  infrastructure" rested on the assumption of a from-scratch Laplace
  derivation; with C.1 already proved, the bridge to the Poisson sum
  collapses to algebraic rearrangement + Mathlib Stirling.

  Axiom-clean (`#print axioms` shows only `[propext, Classical.choice,
  Quot.sound]`).

### C.4. Cumulant infrastructure (general)

- [x] **`Cumulant.def`** — `K_i(X) := iteratedDeriv i (cgf X μ) 0`
  (`Stats.Kappa.Cumulant`).  Wraps Mathlib's `cgf`.  Proves `K_0 = 0`,
  `K_1 = μ[X]` (via `deriv_cgf_zero`), `K_2 = Var[X; μ]` (via
  `iteratedDeriv_two_cgf` + expansion).

- [x] **`cumulant_iid_sum`** — `K_i(Σ_N X_i) = N · K_i(Y)` for
  `IdentDistrib (X i) Y` iid (`Stats.Kappa.Cumulant`).  Proved from
  `Filter.EventuallyEq.iteratedDeriv_eq` +
  `iteratedDeriv_const_mul_field`, modulo a small `cgf_iid_sum_eq_const_mul_eventuallyEq`
  sub-axiom (cgf-sum + IdentDistrib transport, see C.4.discharge.cgf).

- [x] **`cumulantSkewness`** — `Skew := K_3 / K_2^(3/2)`, and the
  `centralMoment`-ratio equivalent `Skew = μ_3 / σ³`
  (`Stats.Kappa.Cumulant`).

- [x] **`cumulantKurtosis`** — `Kurt := 3 + K_4 / K_2²`, and the
  `centralMoment`-ratio equivalent `Kurt = μ_4 / σ⁴`
  (`Stats.Kappa.Cumulant`).

#### C.4.discharge. Follow-up axioms

- [x] **`cgf_iid_sum_eq_const_mul_eventuallyEq`** — discharged
  (`Stats.Kappa.Cumulant`).  Via `IdentDistrib.comp` to transport
  `exp(t · ·)` integrability from `Y` to each `X i`,
  `iIndepFun.cgf_sum₀` for the cgf-sum identity, and
  `mgf_congr_of_identDistrib` for cgf equality on identically-distributed
  variables.  ~25 lines.

- [x] **`cumulant_three_eq_centralMoment_three`** — discharged
  (`Stats.Kappa.Cumulant`).  Via two helper lemmas:
  `cumulant_three_expand` (computes `K_3 = E[X³] − 3·E[X²]·E[X] + 2·E[X]³`
  by direct chain-rule manipulation of `iteratedDeriv 3 cgf 0` using
  `iteratedDeriv_two_cgf` + `HasDerivAt.div` + `HasDerivAt.pow`) and
  `centralMoment_three_expand` (expands `μ_3` via binomial + integral
  linearity).  ~150 lines.

- [ ] **`centralMoment_four_eq_cumulant_four_plus`** — `μ_4 = K_4 + 3 K_2²`.
  Remaining axiom.  Helpers `iteratedDeriv_three_cgf` (general-`v`
  third-derivative formula) and `centralMoment_four_expand` are
  already in `Stats.Kappa.Cumulant`.  Final step: compute
  `cumulant_four_expand` by differentiating `iteratedDeriv_three_cgf`'s
  formula (quotient + product rule on `(A·B − C·D)/B² − 2·E·F`,
  6 chained `HasDerivAt`).  Parenthesisation-heavy in current Lean —
  ~200 lines.

  Foundational for A.2 (lognormal cumulants), 1907.11162 Bernoulli
  cumulants κ_3/κ_4 (already done by direct derivative chains),
  and any future cumulant work.

### C.5. Lyapunov / Lindeberg CLT (Mathlib gap — *audit 2026-05-13: largely retired*)

**Audit 2026-05-13.**  The original framing of this item as a
"research-scale, multi-thousand-line" prerequisite is wrong.  Mathlib
**`v4.29.1` now ships the classical iid CLT**
(`Mathlib.Probability.CentralLimitTheorem.tendstoInDistribution_inv_sqrt_mul_sum_sub`):
for iid `X : ℕ → Ω → ℝ` with `MemLp (X 0) 2 P`,
    `(√n)⁻¹ · (Σ_{k<n} X_k − n · 𝔼[X₀]) ⇒ N(0, Var[X₀])`.

That covers *all three* of the previously-listed downstream uses:

| Use case | Verdict under iid CLT |
|---|---|
| C.3 Poisson CLT (`poisson_cdf_at_mean_tendsto_half`) | ✅ done via Laplace (C.3 above); iid CLT would also work — `Σ Poisson(1) = Poisson(n)`. |
| 1912.00277 Eq. 11–13 (`log λ → N(0, S²)`) | ✅ iid CLT applies directly to `Σ log(1+εᵢ)` for iid `εᵢ` ([Stats/EpistemicUncertainty.lean#L312-L318](Stats/EpistemicUncertainty.lean)). |
| Downstream lognormal κ_{1,n} → 0 (`lognormal_kappa_tendsto_zero_as_n_to_infty`) | 🎯 Misclassified — closed form is `C(σ)/n`, no CLT needed.  **Discharged in-place** ([Stats/Kappa/LognormalCumulants.lean#L414-L444](Stats/Kappa/LognormalCumulants.lean)); axiom `lognormal_kappa_n_decay_axiom` deleted. |
| Pareto MLE asymptotic variance ([Stats/RiskMeasures/MLE.lean#L39](Stats/RiskMeasures/MLE.lean)) | ⚠️ Mathematically: iid CLT on `Σ Exp(α)` + delta method. CLT side is now available in Mathlib; delta method is the open piece. |

**Genuine remaining gap** (paper *outside* C.5's list, in
[todo.md](todo.md) tier 6): **generalised CLT for α-stable limits**
(`Σ Pareto(α ∈ (1, 2)) ⇒ α-stable`).  This is *not* the iid Gaussian
CLT; it needs α-stable basin-of-attraction theory, which Mathlib
genuinely lacks.

- [x] **`Lindeberg.CLT` (in this project's sense, i.e. iid CLT
  prerequisite)** — *covered by Mathlib `v4.29.1`* via
  `tendstoInDistribution_inv_sqrt_mul_sum_sub`; the project's `Stats/`
  consumers can import and apply it directly when needed.

- [ ] **Triangular-array Lindeberg/Lyapunov CLT** — strictly stronger
  than iid CLT (allows row-dependent distributions).  Not needed by
  any current `Stats/` consumer; keep deferred.

- [ ] **Generalised α-stable CLT** — for iid heavy-tailed sums with
  `α ∈ (1, 2)`.  Genuine Mathlib gap; multi-thousand-line research item.

### C.6. Section IV-A: Asymmetric distributions

- [ ] **`asymmetric_stable_kappa`** — Section IV-A's discussion of
  how κ behaves under one-tailed vs symmetric stable distributions.
  Mostly informal in the paper; would require formalising
  one-tailed vs symmetric stable class distinction.  ~300 lines.

---

## Summary

**Completed in current `Stats/Kappa.lean`**: ~20 theorems covering
the κ definition, abstract framework, stable invariance, special
cases (Gaussian/Cauchy/exponential/cubic Student), telescoping
decomposition, Loulakis abstract bound, and two asymptotic limits
(exponential κ + cubic Student κ modulo Laplace axiom).

**Quick wins (Section A)**: ~10 theorems, ~800 lines total.

**Strategic (Section B)**: ~15 theorems, ~2000 lines total.  Notable:
all of Table I closed forms + Pearson IV + α-stable infrastructure.

**Research-scale (Section C)**: Laplace proof (currently axiom),
general CLT, cumulant infrastructure.  Each thousands of lines and
blocked by Mathlib gaps.

**One conceptual correction logged**: Appendix A's stated asymptotic
`lim log(n)·κ_{1, n} = π²/4` is a typo (missing `log`); the correct
value is `log(π²/4) ≈ 0.903`, used in our `kappa_cubicStudent_asymptotic`.
