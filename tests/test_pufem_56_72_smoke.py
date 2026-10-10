"""Finite-sample coefficient regression only; NOT a formal proof of W1,2."""
import math
import random

def test_pufem_active_overlap_and_h_rate_smoke():
    rng = random.Random(20261010)
    for trial in range(1000):
        kappa = rng.randrange(1, 8)
        n = rng.randrange(1, 20)
        cinf = rng.uniform(.05, 5)
        cchi = rng.uniform(.05, 5)
        h = rng.uniform(.1, .97)
        r = rng.randint(2, 6)
        high_sq = h ** (2 * r)
        rate_sq = h ** (2 * (r - 1))
        hinv = 1 / h
        active = set(rng.sample(range(n), min(n, kappa)))
        values, derivatives = [], []
        allowances, errors_sq, derivs_sq, weighted_sq = [], [], [], []
        for j in range(n):
            L = rng.uniform(0, cchi * hinv)
            psi = rng.uniform(-cinf, cinf) if j in active else 0.
            psi_prime = rng.uniform(-L, L) if j in active else 0.
            error = rng.uniform(-1, 1) * h ** r
            deriv = rng.uniform(-1, 1) * h ** (r - 1)
            values.append(psi * error)
            derivatives.append(psi_prime * error + psi * deriv)
            errors_sq.append(error ** 2)
            derivs_sq.append(deriv ** 2)
            weighted_sq.append(L ** 2 * error ** 2)
            allowances.append(
                (cinf ** 2 + 2 * L ** 2) * error ** 2
                + 2 * cinf ** 2 * deriv ** 2
            )
        actual = sum(values) ** 2 + sum(derivatives) ** 2
        pointwise_budget = kappa * sum(allowances)
        tol = 1e-9 * (1 + abs(pointwise_budget))
        assert actual <= pointwise_budget + tol, trial
        assert sum(weighted_sq) <= cchi ** 2 * hinv ** 2 * sum(errors_sq) + tol
        C0 = sum(errors_sq) / high_sq * rng.uniform(1, 2)
        C1 = sum(derivs_sq) / rate_sq * rng.uniform(1, 2)
        scale_constant_sq = kappa * (
            (cinf ** 2 + 2 * cchi ** 2) * C0 + 2 * cinf ** 2 * C1
        )
        bound_sq = scale_constant_sq * rate_sq
        assert actual <= bound_sq + 1e-9 * (1 + abs(bound_sq)), trial
        assert math.sqrt(actual) <= math.sqrt(scale_constant_sq) * h ** (r - 1) + tol
        assert abs(hinv ** 2 * high_sq - rate_sq) < 1e-10
