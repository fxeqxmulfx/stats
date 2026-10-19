"""Numerical κ estimators and reference-curve checks (arXiv:1802.05495v3).

Definition 1 of the paper, for iid variables with finite mean:

    κ(n0, n) := 2 − log(n / n0) / log(M(n) / M(n0)),

where M(k) := E|S_k − k·E[X]|, S_k = X_1 + … + X_k, X_i iid ~ X.
The logarithmic ratio requires n > n0 >= 1, positive MADs and a nonzero
denominator. A supplied function M is not automatically the MAD of a law.

Scope of the corresponding Lean results (Stats.Kappa.*):
    * kappa_gaussian:          supplied M(k) = c·√k gives κ = 0.
    * kappa_cauchy:            supplied M(k) = c·k gives κ = 1.
    * kappa_stable_invariance: supplied M(k) = c·k^(1/ᾱ) gives κ = 2 − ᾱ.
    * kappa_upper_bound_iid:   κ ≤ 1 for the actual sum MAD under its
                               integrability and growth hypotheses.
    * n_nu:                   algebra of the paper's proposed power formula;
                               its actual minimum-size interpretation is open.

The first three statements assume the reference curve; they do not derive
it from a distribution. A Cauchy law has no finite mean or finite MAD for
Definition 1. Its linear reference curve is only an algebraic benchmark.
Bootstrap tests are numerical checks, not proofs of distributional laws.

Implementation:
    * `mad_of_iid_sum`           - bootstrap estimate of M(k) with centering
                                   at k·plug-in-mean (matches the formal
                                   finite-mean target in Definition 1).
    * `mad_of_iid_sum_layercake` - alternative estimator via layer-cake
                                   E|Z| = ∫ P(|Z|>t) dt; cross-check.
    * `kappa`                    - main bootstrap κ estimator.
    * `kappa_with_ci`            - outer bootstrap for CI on κ̂.
    * `kappa_from_M`             - deterministic check of the definition on
                                   a closed-form k → M(k).
    * `n_nu`                     - proposed power expression (`simpleequiv`).
    * `n_g_of_n_nu`              - algebraic inverse of `n_nu`.

Run tests:
    ./run.py test
"""

from __future__ import annotations

import math
import unittest
from typing import Callable, Optional, Tuple

import numpy as np

try:
    from scipy.stats import levy_stable
    HAS_LEVY_STABLE = True
except ImportError:
    HAS_LEVY_STABLE = False


def mad_of_iid_sum(
    x: np.ndarray,
    k: int,
    B: int = 2000,
    mu: Optional[float] = None,
    rng: Optional[np.random.Generator] = None,
) -> float:
    """Estimate E|S_k − k·E[X]| via bootstrap resampling of `x`.

    Centering is at `k·mu` (with `mu` a plug-in for E[X]), not at the
    empirical mean of bootstrap sums. This matches the formal definition
    M(k) = E|S_k − k·E[X]|; centering at the empirical bootstrap mean
    yields a different (consistent but noisier) estimator.

    Args:
        x: One-dimensional sample X_1, …, X_N.
        k: Size of the iid sum; `k > N` is allowed (advantage of bootstrap
            over subsampling).
        B: Number of bootstrap resamples of size k.
        mu: Plug-in estimate of E[X]. Defaults to `x.mean()`.
        rng: Random generator. Defaults to `np.random.default_rng()`.

    Returns:
        Monte-Carlo estimate of M(k).

    Raises:
        ValueError: If `x` is empty, `k < 1`, or `B < 1`.
    """
    if rng is None:
        rng = np.random.default_rng()
    x = np.asarray(x, dtype=float)
    if x.size == 0:
        raise ValueError("Empty sample.")
    if k < 1:
        raise ValueError("k must be >= 1.")
    if B < 1:
        raise ValueError("B must be >= 1.")
    if mu is None:
        mu = float(x.mean())
    if k == 1:
        return float(np.mean(np.abs(x - mu)))
    N = x.size
    idx = rng.integers(0, N, size=(B, k))
    sums = x[idx].sum(axis=1)
    return float(np.mean(np.abs(sums - k * mu)))


def mad_of_iid_sum_layercake(
    x: np.ndarray,
    k: int,
    B: int = 2000,
    n_grid: int = 400,
    mu: Optional[float] = None,
    rng: Optional[np.random.Generator] = None,
) -> float:
    """Alternative estimate of M(k) via the layer-cake formula.

    Uses the layer-cake identity E|Z| = ∫_0^∞ P(|Z| > t) dt. The related
    Lean theorem `MadLayerCake.mad_eq_two_tail_integral` integrates the
    positive centered tail and multiplies by two; this implementation
    instead integrates the survival function of the absolute deviation.
    The empirical survival of |S_k − k·μ| over B bootstrap samples is
    integrated against a finite trapezoidal t-grid. This approximates the
    direct empirical MAD in `mad_of_iid_sum`; finite-grid quadrature error
    remains, so the two estimates need not have the same expected value.

    Args:
        x: One-dimensional sample.
        k: Size of the iid sum.
        B: Number of bootstrap resamples of size k.
        n_grid: Number of intervals in the trapezoidal t-grid.
        mu: Plug-in estimate of E[X]. Defaults to `x.mean()`.
        rng: Random generator. Defaults to `np.random.default_rng()`.

    Returns:
        Layer-cake estimate of M(k).

    Raises:
        ValueError: If `x` is empty.
    """
    if rng is None:
        rng = np.random.default_rng()
    x = np.asarray(x, dtype=float)
    if x.size == 0:
        raise ValueError("Empty sample.")
    if mu is None:
        mu = float(x.mean())
    N = x.size
    idx = rng.integers(0, N, size=(B, k))
    sums = x[idx].sum(axis=1)
    z_abs = np.abs(sums - k * mu)
    t_max = float(z_abs.max())
    if t_max == 0.0:
        return 0.0
    t_grid = np.linspace(0.0, t_max, n_grid + 1)
    survival = np.mean(z_abs[:, None] > t_grid[None, :], axis=0)
    return float(np.trapezoid(survival, t_grid))


def kappa(
    x: np.ndarray,
    n0: int = 1,
    n: int = 30,
    B: int = 2000,
    rng: Optional[np.random.Generator] = None,
    mu: Optional[float] = None,
) -> float:
    """Estimate Taleb's κ(n0, n) by bootstrap from sample `x`.

    Args:
        x: One-dimensional sample.
        n0: Baseline sum size; must be >= 1.
        n: Target sum size; must satisfy n > n0.
        B: Number of bootstrap samples per M(k) estimate.
        rng: Random generator.
        mu: Plug-in for E[X]. If None, uses the sample mean. Pass an
            explicit value (e.g. `mu=0` for symmetric X) when the true
            mean is known — more stable, especially for fat tails with
            α ∈ (1, 2).

    Returns:
        κ̂(n0, n), or NaN if the sample is degenerate (some M(·) = 0
        or log(M(n)/M(n0)) ≈ 0).

    Raises:
        ValueError: If `n0 < 1`, `n <= n0`, or `B < 1`.
    """
    if n0 < 1:
        raise ValueError("n0 must be >= 1.")
    if n <= n0:
        raise ValueError("Require n > n0.")
    if B < 1:
        raise ValueError("B must be >= 1.")
    if rng is None:
        rng = np.random.default_rng()
    x = np.asarray(x, dtype=float)
    if mu is None:
        mu = float(x.mean())

    M_n0 = mad_of_iid_sum(x, n0, B=B, mu=mu, rng=rng)
    M_n  = mad_of_iid_sum(x, n,  B=B, mu=mu, rng=rng)

    if M_n0 <= 0.0 or M_n <= 0.0:
        return float("nan")
    log_ratio = math.log(M_n / M_n0)
    if abs(log_ratio) < 1e-15:
        return float("nan")
    return 2.0 - math.log(n / n0) / log_ratio


def kappa_with_ci(
    x: np.ndarray,
    n0: int = 1,
    n: int = 30,
    B: int = 2000,
    B_outer: int = 200,
    ci_levels: Tuple[float, float] = (2.5, 97.5),
    mu: Optional[float] = None,
    seed: Optional[int] = 0,
) -> dict:
    """Estimate κ̂ with a bootstrap CI from an outer resample of `x`.

    The point estimate `kappa_hat` is κ̂ on the original sample (not the
    bootstrap mean, to avoid inheriting bootstrap bias). The outer
    resample is used only to construct the CI.

    Args:
        x: One-dimensional sample.
        n0: Baseline sum size.
        n: Target sum size.
        B: Inner bootstrap size for each M(k) estimate.
        B_outer: Number of outer bootstrap resamples of `x`.
        ci_levels: Lower/upper percentiles for the CI (in [0, 100]).
        mu: Plug-in for E[X]. If None, sample mean is used inside each
            outer iterate, which captures mean-estimation uncertainty.
        seed: Seed for the random generator.

    Returns:
        Dict with keys `kappa_hat`, `ci_lo`, `ci_hi`, `n_valid`
        (number of non-NaN outer estimates).
    """
    rng = np.random.default_rng(seed)
    x = np.asarray(x, dtype=float)
    N = x.size
    kappa_hat = kappa(x, n0=n0, n=n, B=B, rng=rng, mu=mu)
    boot = []
    for _ in range(B_outer):
        xb = rng.choice(x, size=N, replace=True)
        k_hat = kappa(xb, n0=n0, n=n, B=B, rng=rng, mu=mu)
        if not math.isnan(k_hat):
            boot.append(k_hat)
    if not boot:
        return {"kappa_hat": kappa_hat,
                "ci_lo": float("nan"),
                "ci_hi": float("nan"),
                "n_valid": 0}
    arr = np.asarray(boot)
    lo, hi = np.percentile(arr, ci_levels)
    return {"kappa_hat": kappa_hat,
            "ci_lo": float(lo), "ci_hi": float(hi),
            "n_valid": int(arr.size)}


def kappa_from_M(M_fun: Callable[[int], float], n0: int, n: int) -> float:
    """Compute κ(n0, n) deterministically from a closed-form M(·).

    Useful for verifying the definition on analytic forms:
        M(k) = c · k^(1/α)  ⇒  κ(n0, n) = 2 − α exactly
        (theorem `kappa_stable_invariance` in Stats.Kappa.Basic).

    Args:
        M_fun: Closed-form k → M(k).
        n0: Baseline sum size.
        n: Target sum size.

    Returns:
        κ(n0, n) under the given M.
    """
    M_n0 = M_fun(n0)
    M_n  = M_fun(n)
    return 2.0 - math.log(n / n0) / math.log(M_n / M_n0)


def n_nu(n_g: float, kappa_g: float) -> float:
    """The paper's proposed sample-size power expression (`simpleequiv`).

    Closed form, formalized as `n_nu` in Stats.Kappa.Basic:

        n_ν := n_g ^ (1 / (1 − κ_g)).

    This formula is not a computed positive-integer minimum from actual MADs.
    For fixed n_g > 1 it diverges as κ_g → 1⁻. The Python +∞ return at
    κ_g >= 1 is a boundary convention; Lean's total real-valued `n_nu`
    instead evaluates to 1 at κ_g = 1.

    Args:
        n_g: Positive baseline sample size.
        kappa_g: κ-value at the n_g anchor; requires κ_g < 1 for a finite
            answer.

    Returns:
        n_ν > 0, or +∞ if `kappa_g >= 1`.
    """
    if kappa_g >= 1.0:
        return float("inf")
    return n_g ** (1.0 / (1.0 - kappa_g))


def n_g_of_n_nu(n_nu_val: float, kappa_g: float) -> float:
    """Algebraic inverse of `n_nu` (paper III-B, Lean `n_g_of_n_nu`).

    Closed form:

        n_g_of_n_nu n_ν κ_g := n_ν ^ (1 − κ_g).

    On positive finite inputs with κ < 1, the round-trip identity corresponds
    to theorem `n_g_of_n_nu_n_nu` in Stats.Kappa.Basic:
    `n_g_of_n_nu(n_nu(n_g, κ), κ) = n_g`. The Python infinity convention at
    κ >= 1 is outside this round-trip statement.

    Args:
        n_nu_val: ν-sample size.
        kappa_g: κ-value at the n_g anchor.

    Returns:
        Gaussian-equivalent sample size n_g.
    """
    return n_nu_val ** (1.0 - kappa_g)


class TestKappaClosedForm(unittest.TestCase):
    """Deterministic tests on closed-form M(k) — verify the κ definition
    without bootstrap noise."""

    def test_gaussian_M_eq_c_sqrt_k_gives_kappa_zero(self):
        """M(k) = c·√k  ⇒  κ = 0  (theorem `kappa_gaussian`)."""
        for c in [0.5, 1.0, 2.0]:
            for (n0, n) in [(1, 2), (1, 30), (2, 100), (5, 1000)]:
                k_val = kappa_from_M(lambda k, c=c: c * math.sqrt(k),
                                     n0, n)
                self.assertAlmostEqual(
                    k_val, 0.0, places=12,
                    msg=f"c={c}, ({n0},{n}): κ={k_val}")

    def test_stable_M_eq_c_k_pow_one_over_alpha(self):
        """M(k) = c · k^(1/α)  ⇒  κ = 2 − α  (`kappa_stable_invariance`)."""
        for alpha in [0.5, 0.9, 1.0, 1.3, 1.5, 1.7, 1.99, 2.0]:
            for c in [0.7, 1.0, 3.14]:
                k_val = kappa_from_M(
                    lambda k, a=alpha, c=c: c * k ** (1.0 / a),
                    n0=1, n=100)
                self.assertAlmostEqual(
                    k_val, 2.0 - alpha, places=10,
                    msg=f"α={alpha}, c={c}: κ={k_val}")

    def test_full_kappa_range_via_stable_alphaBar(self):
        """Full κ range via closed form M(k) = k^(1/ᾱ).

        ᾱ ∈ (0, 3]  ⇒  κ = 2 − ᾱ  ∈  [−1, 2):
            ᾱ → 0+ : κ → 2   (super-heavy-tail limit)
            ᾱ = 1  : κ = 1   (Cauchy)
            ᾱ = 2  : κ = 0   (Gaussian)
            ᾱ > 2  : κ < 0   (sub-Gaussian, CLT-violating M)

        A 30-point grid covers all regimes.
        """
        alpha_grid = np.linspace(0.1, 3.0, 30)
        for alpha in alpha_grid:
            k_val = kappa_from_M(
                lambda k, a=alpha: k ** (1.0 / a),
                n0=1, n=1000)
            self.assertAlmostEqual(
                k_val, 2.0 - alpha, places=10,
                msg=f"ᾱ={alpha:.3f}: κ={k_val}, expected={2-alpha:.3f}")
        self.assertAlmostEqual(
            kappa_from_M(lambda k: k ** (1.0 / 0.01), 1, 1000),
            2.0 - 0.01, places=10)
        self.assertAlmostEqual(
            kappa_from_M(lambda k: k ** (1.0 / 1.5), 1, 1000),
            0.5, places=10)

    def test_cauchy_M_proportional_to_k_gives_kappa_one(self):
        """M(k) ∝ k  ⇒  κ = 1  (theorem `kappa_cauchy`)."""
        for c in [0.5, 1.0, 2.0]:
            k_val = kappa_from_M(lambda k, c=c: c * k, 1, 50)
            self.assertAlmostEqual(k_val, 1.0, places=12)

    def test_invariance_to_n0_for_stable(self):
        """For the stable class, κ(n0, n) does not depend on (n0, n)."""
        def M(k):
            return 1.5 * k ** (1.0 / 1.4)
        values = [kappa_from_M(M, n0, n)
                  for (n0, n) in [(1, 2), (1, 10), (3, 50), (10, 1000)]]
        for v in values:
            self.assertAlmostEqual(v, 2.0 - 1.4, places=10)


class TestNNu(unittest.TestCase):
    """Tests for the effective-sample-size formula `n_ν` (paper Eq. 7,
    formalized in [Stats/Kappa/Basic.lean](Stats/Kappa/Basic.lean)).

    Covers the named Lean theorems:
        * `n_nu_gaussian`      - n_ν = n_g at κ = 0
        * `n_nu_gt_n_g`        - n_ν > n_g for κ ∈ (0, 1)
        * `n_g_of_n_nu_n_nu`   - round-trip: n_g_of_n_nu(n_nu(n_g, κ), κ) = n_g
        * `n_nu_n_g_of_n_nu`   - reverse round-trip
        * `n_nu_bidirectional` - duality when (1−κ_g)(1−κ_ν) = 1
    """

    def test_n_nu_gaussian(self):
        """`n_nu_gaussian`: at κ = 0, n_ν = n_g (Gaussian requires no
        extra summands)."""
        for n_g in [1, 2, 10, 100, 1000, 10_000]:
            self.assertAlmostEqual(n_nu(n_g, 0.0), float(n_g), places=12,
                msg=f"n_g={n_g}, κ=0: n_ν={n_nu(n_g, 0.0)} ≠ {n_g}")

    def test_n_nu_gt_n_g_strict(self):
        """`n_nu_gt_n_g`: for n_g > 1 and κ ∈ (0, 1), strictly n_ν > n_g."""
        for n_g in [2, 10, 100, 1000]:
            for kappa_g in [0.01, 0.1, 0.3, 0.5, 0.7, 0.9, 0.99]:
                nv = n_nu(n_g, kappa_g)
                self.assertGreater(
                    nv, float(n_g),
                    msg=f"n_g={n_g}, κ={kappa_g}: n_ν={nv} ≤ n_g")

    def test_n_nu_monotone_increasing_in_kappa(self):
        """n_ν strictly increases in κ for fixed n_g > 1 (1/(1−κ) is
        monotone increasing; base > 1)."""
        n_g = 100
        kappas = np.linspace(0.0, 0.95, 20)
        n_vs = [n_nu(n_g, k) for k in kappas]
        for i in range(len(n_vs) - 1):
            self.assertLess(
                n_vs[i], n_vs[i + 1],
                msg=f"κ={kappas[i]:.3f} → {kappas[i+1]:.3f}: "
                    f"n_ν={n_vs[i]:.3f} ≥ n_ν={n_vs[i+1]:.3f}")

    def test_n_nu_diverges_as_kappa_to_one(self):
        """n_ν → ∞ as κ → 1⁻ (Cauchy boundary).

        Compared on log n_ν to avoid float overflow.
        """
        n_g = 10
        log_prev = math.log(n_nu(n_g, 0.5))
        for kappa_g in [0.9, 0.99, 0.999, 0.9999]:
            log_nv = math.log(n_g) / (1.0 - kappa_g)
            self.assertGreater(log_nv, log_prev,
                msg=f"κ={kappa_g}: log n_ν={log_nv} not greater than previous")
            log_prev = log_nv
        self.assertEqual(n_nu(10, 1.0), float("inf"))
        self.assertEqual(n_nu(10, 1.5), float("inf"))

    def test_n_g_of_n_nu_round_trip(self):
        """`n_g_of_n_nu_n_nu`: n_g_of_n_nu(n_nu(n_g, κ), κ) = n_g."""
        for n_g in [1, 2, 10, 100, 1000]:
            for kappa_g in [-0.5, 0.0, 0.1, 0.3, 0.5, 0.7, 0.9, 0.99]:
                nv = n_nu(n_g, kappa_g)
                recovered = n_g_of_n_nu(nv, kappa_g)
                self.assertAlmostEqual(
                    recovered, float(n_g), places=8,
                    msg=f"n_g={n_g}, κ={kappa_g}: round-trip={recovered}")

    def test_n_nu_n_g_of_n_nu_round_trip(self):
        """`n_nu_n_g_of_n_nu`: reverse round-trip
        n_nu(n_g_of_n_nu(n_ν, κ), κ) = n_ν."""
        for n_nu_val in [1.0, 5.5, 100.0, 1234.567]:
            for kappa_g in [-0.5, 0.0, 0.1, 0.3, 0.7, 0.99]:
                n_g_back = n_g_of_n_nu(n_nu_val, kappa_g)
                if 1.0 - kappa_g == 0.0:
                    continue
                nv_back = n_g_back ** (1.0 / (1.0 - kappa_g))
                self.assertAlmostEqual(
                    nv_back, n_nu_val, places=8,
                    msg=f"n_ν={n_nu_val}, κ={kappa_g}: ↩ ={nv_back}")

    def test_n_nu_bidirectional_dual(self):
        """`n_nu_bidirectional`: if (1−κ_g)(1−κ_ν) = 1, then
            n_ν = n_g^(1/(1−κ_g))   ⇔   n_g = n_ν^(1/(1−κ_ν)).

        Numerical verification over several (κ_g, κ_ν) pairs.
        """
        for kappa_g in [-0.5, -0.1, 0.1, 0.3, 0.5, 0.7, 0.9]:
            kappa_nu = -kappa_g / (1.0 - kappa_g)
            self.assertAlmostEqual(
                (1 - kappa_g) * (1 - kappa_nu), 1.0, places=12)
            for n_g in [2.0, 10.0, 100.0]:
                n_nu_val = n_g ** (1.0 / (1.0 - kappa_g))
                n_g_back = n_nu_val ** (1.0 / (1.0 - kappa_nu))
                self.assertAlmostEqual(
                    n_g_back, n_g, places=8,
                    msg=f"n_g={n_g}, κ_g={kappa_g}, κ_ν={kappa_nu}: "
                        f"recovered n_g={n_g_back}")

    def test_n_nu_exact_formula_spot_checks(self):
        """Spot checks against the panic-scale table.

        For large values, compares relative error (floats have ~16
        significant digits).
        """
        self.assertAlmostEqual(n_nu(1000, 0.5) / 1e6, 1.0, places=10)
        self.assertAlmostEqual(n_nu(1000, 0.8) / 1e15, 1.0, places=10)
        self.assertAlmostEqual(n_nu(1000, 0.9) / 1e30, 1.0, places=10)
        self.assertAlmostEqual(n_nu(30, 0.0), 30.0, places=12)
        self.assertAlmostEqual(n_nu(1, 0.7), 1.0, places=12)
        self.assertAlmostEqual(n_nu(1, 0.99), 1.0, places=12)

    def test_n_nu_consistent_with_paper_eq7(self):
        """The implementation follows paper Eq. 7 exactly (Lean
        `n_nu`).

        Note: a naive sample-mean-MAD equivalence derivation gives the
        exponent (2−κ)/(2(1−κ)), which differs from Taleb's algebraic
        form 1/(1−κ). Both diverge as κ → 1⁻ but agree only at κ = 0.
        This test asserts that the implementation matches Eq. 7.
        """
        n_g = 100.0
        for kappa_g in [0.1, 0.3, 0.5, 0.7]:
            taleb_form = n_nu(n_g, kappa_g)
            expected_taleb = n_g ** (1.0 / (1.0 - kappa_g))
            self.assertAlmostEqual(taleb_form, expected_taleb, places=8)


class TestKappaBootstrap(unittest.TestCase):
    """Empirical convergence tests of the bootstrap estimator on real
    samples with large B and N."""

    def test_gaussian_kappa_near_zero(self):
        """Empirical κ̂ for N(0, 1) is close to 0."""
        rng = np.random.default_rng(42)
        x = rng.standard_normal(50_000)
        k_hat = kappa(x, n0=1, n=30, B=5000, rng=rng, mu=0.0)
        self.assertLess(abs(k_hat), 0.05,
            f"κ̂={k_hat:.4f} for N(0,1) should be ≈ 0")

    def test_laplace_kappa_near_zero(self):
        """Thin-tailed Laplace: κ̂ should be close to 0.

        Uses n=100 to substantially reduce pre-asymptotic CLT bias
        (max|κ̂| ≈ 0.12 across 20 seeds).
        """
        rng = np.random.default_rng(7)
        x = rng.laplace(0.0, 1.0, size=50_000)
        k_hat = kappa(x, n0=1, n=100, B=5000, rng=rng, mu=0.0)
        self.assertLess(abs(k_hat), 0.14,
            f"κ̂={k_hat:.4f} for Laplace should be ≈ 0")

    def test_uniform_kappa_near_zero(self):
        """Uniform — finite variance, thin tail: κ̂ ≈ 0.

        Uses n=100; max|κ̂| ≈ 0.09 across 20 seeds.
        """
        rng = np.random.default_rng(3)
        x = rng.uniform(-1.0, 1.0, size=50_000)
        k_hat = kappa(x, n0=1, n=100, B=5000, rng=rng, mu=0.0)
        self.assertLess(abs(k_hat), 0.10)

    @unittest.skipUnless(HAS_LEVY_STABLE, "scipy.stats.levy_stable required")
    def test_symmetric_stable_kappa_near_2_minus_alpha(self):
        """Symmetric α-stable: κ̂ ≈ 2 − α.

        Tolerances are calibrated from max|err| over 15 seeds plus 30%
        margin.
        """
        rng = np.random.default_rng(11)
        for alpha, delta in [(1.7, 0.08), (1.9, 0.05)]:
            x = levy_stable.rvs(alpha=alpha, beta=0, size=100_000,
                                random_state=rng)
            k_hat = kappa(x, n0=1, n=30, B=5000, rng=rng, mu=0.0)
            expected = 2.0 - alpha
            self.assertAlmostEqual(
                k_hat, expected, delta=delta,
                msg=f"α={alpha}: κ̂={k_hat:.3f}, expected={expected:.3f}")

    @unittest.skipUnless(HAS_LEVY_STABLE, "scipy.stats.levy_stable required")
    def test_bootstrap_kappa_sweep_full_range(self):
        """Bootstrap sweep through Lévy-stable α ∈ [1.1, 1.95]: recovers
        κ̂ across the full range κ ∈ (0.05, 0.9).

        Ground truth: κ = 2 − α decreases monotonically with α.
        Tolerances are calibrated from max|err| over 15 seeds plus 30%
        margin; they widen as the tail thickens.
        """
        rng = np.random.default_rng(1729)
        for alpha, delta in [(1.95, 0.05), (1.7, 0.10), (1.5, 0.13),
                             (1.3, 0.18), (1.1, 0.25)]:
            x = levy_stable.rvs(alpha=alpha, beta=0, size=100_000,
                                random_state=rng)
            k_hat = kappa(x, n0=1, n=30, B=5000, rng=rng, mu=0.0)
            expected = 2.0 - alpha
            self.assertAlmostEqual(
                k_hat, expected, delta=delta,
                msg=f"α={alpha}: κ̂={k_hat:.3f}, expected={expected:.3f}")

    @unittest.skipUnless(HAS_LEVY_STABLE, "scipy.stats.levy_stable required")
    def test_bootstrap_kappa_monotone_in_alpha(self):
        """Monotonicity of κ̂ in α for Lévy-stable: heavier tail (smaller
        α) gives larger κ̂. Tolerates one violation from bootstrap noise.
        """
        rng = np.random.default_rng(31415)
        alphas = [1.95, 1.7, 1.5, 1.3, 1.15]
        k_hats = []
        for alpha in alphas:
            x = levy_stable.rvs(alpha=alpha, beta=0, size=100_000,
                                random_state=rng)
            k_hats.append(kappa(x, n0=1, n=30, B=5000, rng=rng, mu=0.0))
        violations = sum(1 for i in range(len(k_hats) - 1)
                         if k_hats[i + 1] < k_hats[i])
        self.assertLessEqual(
            violations, 1,
            f"Monotonicity violations: {violations}; κ̂={k_hats}")
        self.assertLess(k_hats[0], k_hats[-1],
            f"κ̂(α=1.95)={k_hats[0]:.3f} should be < κ̂(α=1.15)={k_hats[-1]:.3f}")

    def test_kappa_in_unit_interval_for_finite_mean(self):
        """`kappa_upper_bound_iid`: κ ≤ 1 for iid with finite mean."""
        rng = np.random.default_rng(0)
        cases = {
            "gaussian":    rng.standard_normal(20_000),
            "laplace":     rng.laplace(0.0, 1.0, size=20_000),
            "exponential": rng.exponential(1.0, size=20_000),
        }
        for name, x in cases.items():
            k_hat = kappa(x, n0=1, n=30, B=3000, rng=rng)
            self.assertLess(k_hat, 0.3,
                f"{name}: κ̂={k_hat:.3f} outside expected range")
            self.assertGreater(k_hat, -0.05,
                f"{name}: κ̂={k_hat:.3f} below sensible range")


class TestKappaLayerCakeConsistency(unittest.TestCase):
    """The layer-cake estimator should agree with the direct MC estimate
    within a tolerance allowing for finite-grid quadrature error."""

    def test_layercake_close_to_direct_mc(self):
        """Direct MC and layer-cake estimates agree to 1% relative error."""
        rng_seed = 2024
        x = np.random.default_rng(rng_seed).standard_normal(5000)
        rng_a = np.random.default_rng(rng_seed)
        rng_b = np.random.default_rng(rng_seed)
        m_direct = mad_of_iid_sum(x, k=10, B=10_000, mu=0.0, rng=rng_a)
        m_layercake = mad_of_iid_sum_layercake(x, k=10, B=10_000,
                                               n_grid=500, mu=0.0,
                                               rng=rng_b)
        rel_err = abs(m_direct - m_layercake) / m_direct
        self.assertLess(rel_err, 0.01,
            f"Direct={m_direct:.4f}, LC={m_layercake:.4f}, rel_err={rel_err:.4f}")


class TestKappaEdgeCases(unittest.TestCase):
    """Behavior on degenerate inputs."""

    def test_constant_sample_returns_nan(self):
        """Constant X: M(k) ≡ 0 → κ̂ = NaN (no crash, no lie)."""
        x = np.full(1000, 3.14)
        k_hat = kappa(x, n0=1, n=10, B=500)
        self.assertTrue(math.isnan(k_hat))

    def test_bad_args_raise(self):
        """Invalid arguments raise `ValueError`."""
        rng = np.random.default_rng(0)
        x = rng.standard_normal(1000)
        with self.assertRaises(ValueError):
            kappa(x, n0=0, n=10)
        with self.assertRaises(ValueError):
            kappa(x, n0=10, n=10)
        with self.assertRaises(ValueError):
            kappa(x, n0=10, n=5)
        with self.assertRaises(ValueError):
            kappa(x, n0=1, n=10, B=0)
        with self.assertRaises(ValueError):
            mad_of_iid_sum(np.array([]), k=5)
        with self.assertRaises(ValueError):
            mad_of_iid_sum(x, k=0)

    def test_k_can_exceed_N(self):
        """Bootstrap advantage: k may exceed N (the sample size)."""
        rng = np.random.default_rng(42)
        x = rng.standard_normal(100)
        m = mad_of_iid_sum(x, k=500, B=200, mu=0.0, rng=rng)
        self.assertGreater(m, 0.0)
        self.assertFalse(math.isnan(m))


class TestKappaWithCI(unittest.TestCase):
    """The CI should include the truth for thin-tailed distributions."""

    def test_ci_covers_zero_for_gaussian(self):
        """For Gaussian, the CI tightly covers 0 and the point estimate
        κ̂ is close to 0.

        Across 10 seeds: kappa_hat ∈ [-0.024, 0.020], ci_lo ∈ [-0.048,
        -0.034], ci_hi ∈ [0.032, 0.047].
        """
        rng_seed = 12345
        rng = np.random.default_rng(rng_seed)
        x = rng.standard_normal(20_000)
        out = kappa_with_ci(x, n0=1, n=30, B=2000, B_outer=200,
                           mu=0.0, seed=rng_seed)
        self.assertGreater(out["n_valid"], 150,
            "Too many NaNs in bootstrap")
        self.assertLess(abs(out["kappa_hat"]), 0.05,
            f"κ̂={out['kappa_hat']:.3f} should be ≈ 0")
        self.assertLess(out["ci_lo"], -0.02)
        self.assertGreater(out["ci_hi"], 0.02)

    def test_ci_lo_above_zero_for_heavy_tail(self):
        """For fat-tailed X (Pareto α=1.5), the point estimate κ̂ is
        significantly > 0, and the lower CI bound is also > 0.

        Across 10 seeds: kappa_hat ∈ [0.586, 0.782], ci_lo ∈ [0.512,
        0.633].
        """
        rng = np.random.default_rng(2024)
        alpha_p = 1.5
        x = (1.0 + rng.pareto(alpha_p, size=20_000))
        out = kappa_with_ci(x, n0=1, n=30, B=2000, B_outer=200,
                           seed=2024)
        self.assertGreater(out["kappa_hat"], 0.4,
            f"κ̂={out['kappa_hat']:.3f} for Pareto(α=1.5) should be > 0.4")
        self.assertGreater(out["ci_lo"], 0.3,
            f"ci_lo={out['ci_lo']:.3f} for Pareto(α=1.5) should be > 0.3")


if __name__ == "__main__":
    unittest.main(verbosity=2)
