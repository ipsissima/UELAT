"""Regression for the rational piecewise weak-derivative identity.
Exact Fraction arithmetic; passing this is NOT a Rocq kernel proof.
"""
from fractions import Fraction as F
from random import Random

def add(a, b):
    return [(a[i] if i < len(a) else F(0)) +
            (b[i] if i < len(b) else F(0))
            for i in range(max(len(a), len(b)))]

def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1) if a and b else []
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out

def deriv(p):
    return [i * p[i] for i in range(1, len(p))]

def evaluate(p, x):
    v = F(0)
    for a in reversed(p):
        v = a + x * v
    return v

def integrate(p, a, b):
    return sum((v * (b ** (i + 1) - a ** (i + 1)) / F(i + 1)
                for i, v in enumerate(p)), F(0))

def random_poly(rng):
    return [F(rng.randint(-6, 6), rng.randint(1, 5))
            for _ in range(rng.randint(1, 6))]

def test_piecewise_polynomial_weak_identity():
    rng = Random(20261010)
    for case in range(1600):
        n = rng.randint(1, 9)
        knots = sorted({F(0), F(1)} |
                       {F(rng.randrange(1, 50), 50) for _ in range(n - 1)})
        pieces = []
        for k in range(len(knots) - 1):
            p = random_poly(rng)
            if pieces:
                previous_value = evaluate(pieces[-1], knots[k])
                p[0] += previous_value - evaluate(p, knots[k])
                assert evaluate(pieces[-1], knots[k]) == evaluate(p, knots[k])
            pieces.append(p)
        test = mul([F(0), F(-1), F(1)], random_poly(rng))
        assert evaluate(test, F(0)) == evaluate(test, F(1)) == 0
        L = R = boundary_sum = F(0)
        for p, a, b in zip(pieces, knots, knots[1:]):
            left = integrate(mul(deriv(p), test), a, b)
            right = integrate(mul(p, deriv(test)), a, b)
            boundary = (evaluate(p, b) * evaluate(test, b)
                        - evaluate(p, a) * evaluate(test, a))
            assert left + right == boundary, (case, "cell FTC")
            L += left
            R += right
            boundary_sum += boundary
        assert boundary_sum == 0, (case, "seam cancellation")
        assert L + R == 0, (case, "weak test identity")
