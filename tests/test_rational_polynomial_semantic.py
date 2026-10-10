"""Exact-rational regression tests for Rocq's actual polynomial code.
These 4,000 seeded Fraction tests are not substitutes for a Rocq proof.
"""
from fractions import Fraction as Q
from random import Random


def qpoly_add(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p[0] + q[0]] + qpoly_add(p[1:], q[1:])


def qpoly_scale(c, p):
    return [c * a for a in p]


def qpoly_mul(p, q):
    if not p:
        return []
    return qpoly_add(qpoly_scale(p[0], q), [Q(0)] + qpoly_mul(p[1:], q))


def qpoly_eval(p, x):
    if not p:
        return Q(0)
    return p[0] + x * qpoly_eval(p[1:], x)


def qpoly_deriv(p):
    return [Q(i + 1) * a for i, a in enumerate(p[1:])]


def qpoly_integral(p, a, b):
    return sum(
        (c * (b ** (i + 1) - a ** (i + 1)) / Q(i + 1)
         for i, c in enumerate(p)), Q(0)
    )


def random_poly(rng):
    return [Q(rng.randint(-9, 9), rng.randint(1, 7))
            for _ in range(rng.randrange(0, 7))]


def test_exact_polynomial_product_leibniz_and_integral():
    rng = Random(20261010)
    for _ in range(4000):
        p, q = random_poly(rng), random_poly(rng)
        x = Q(rng.randint(-10, 10), rng.randint(1, 7))
        a = Q(rng.randint(-6, 6), rng.randint(1, 7))
        b = Q(rng.randint(-6, 6), rng.randint(1, 7))
        c = Q(rng.randint(-6, 6), rng.randint(1, 7))
        dp, dq = qpoly_deriv(p), qpoly_deriv(q)
        assert qpoly_eval(qpoly_add(p, q), x) == qpoly_eval(p, x) + qpoly_eval(q, x)
        assert qpoly_eval(qpoly_scale(c, p), x) == c * qpoly_eval(p, x)
        assert qpoly_eval(qpoly_mul(p, q), x) == qpoly_eval(p, x) * qpoly_eval(q, x)
        assert qpoly_eval(qpoly_deriv(qpoly_mul(p, q)), x) == (
            qpoly_eval(dp, x) * qpoly_eval(q, x)
            + qpoly_eval(p, x) * qpoly_eval(dq, x))
        assert qpoly_eval(qpoly_deriv(qpoly_mul([a, b], p)), x) == (
            b * qpoly_eval(p, x) + (a + b * x) * qpoly_eval(dp, x))
        assert qpoly_integral(qpoly_add(p, q), a, b) == (
            qpoly_integral(p, a, b) + qpoly_integral(q, a, b))
        assert qpoly_integral(qpoly_scale(c, p), a, b) == c * qpoly_integral(p, a, b)
