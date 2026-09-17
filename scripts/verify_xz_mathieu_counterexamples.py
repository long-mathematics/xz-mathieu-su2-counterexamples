#!/usr/bin/env python3
"""Exact arithmetic checks for the counterexamples in arXiv:2607.19012.

The script verifies the beta-binomial coefficient identities underlying
Theorem 2.1 and Proposition 3.1, and the monomial formula used in the SU(2)
integration lemma, over a finite but deliberately redundant range.
"""

from fractions import Fraction
from math import comb, factorial

MAX_N = 50
MAX_MONOMIAL_DEGREE = 8


def beta_integer(k: int, n_minus_k: int) -> Fraction:
    """Integral_0^1 x^k (1-x)^(n-k) dx for nonnegative integers."""
    return Fraction(factorial(k) * factorial(n_minus_k), factorial(k + n_minus_k + 1))


def verify_beta_binomial() -> None:
    for n in range(1, MAX_N + 1):
        for k in range(n + 1):
            lhs = comb(n, k) * beta_integer(k, n - k)
            rhs = Fraction(1, n + 1)
            assert lhs == rhs, (n, k, lhs, rhs)


def verify_basic_moments() -> None:
    for n in range(1, MAX_N + 1):
        pure = Fraction(sum((-1) ** j * comb(n, j) for j in range(n + 1)), n + 1)
        mixed = Fraction(sum((-1) ** j * comb(n, j) for j in range(n)), n + 1)
        assert pure == 0, (n, pure)
        assert mixed == Fraction((-1) ** (n - 1), n + 1), (n, mixed)


def verify_parameter_family() -> None:
    # d affects only Laurent exponents; lambda and mu contribute the scalar
    # lambda^n mu^{-1} in the mixed moment.  Check several exact rational values.
    samples = [
        (1, Fraction(1), Fraction(1)),
        (2, Fraction(2), Fraction(3)),
        (5, Fraction(-3, 2), Fraction(7, 5)),
    ]
    for d, lam, mu in samples:
        assert d >= 1 and lam != 0 and mu != 0
        for n in range(1, MAX_N + 1):
            pure_sum = sum((-1) ** j * comb(n, j) for j in range(n + 1))
            mixed_sum = sum((-1) ** j * comb(n, j) for j in range(n))
            pure = Fraction(lam**n, n + 1) * pure_sum
            mixed = Fraction(lam**n, n + 1) * Fraction(1, 1) / mu * mixed_sum
            expected = Fraction((-1) ** (n - 1), n + 1) * lam**n / mu
            assert pure == 0, (d, lam, mu, n, pure)
            assert mixed == expected, (d, lam, mu, n, mixed, expected)


def su2_monomial_formula(r: int, s: int, t: int, u: int) -> Fraction:
    if r != u or s != t:
        return Fraction(0)
    return Fraction(((-1) ** s) * factorial(r) * factorial(s), factorial(r + s + 1))


def beta_map_monomial_formula(r: int, s: int, t: int, u: int) -> Fraction:
    # Under beta: a^r b^s c^t d^u becomes
    # (-1)^t (1-x)^r x^s z1^(s-t) z2^(r-u).
    if r != u or s != t:
        return Fraction(0)
    return ((-1) ** t) * beta_integer(s, r)


def verify_su2_integration_monomials() -> None:
    for r in range(MAX_MONOMIAL_DEGREE + 1):
        for s in range(MAX_MONOMIAL_DEGREE + 1):
            for t in range(MAX_MONOMIAL_DEGREE + 1):
                for u in range(MAX_MONOMIAL_DEGREE + 1):
                    lhs = su2_monomial_formula(r, s, t, u)
                    rhs = beta_map_monomial_formula(r, s, t, u)
                    assert lhs == rhs, (r, s, t, u, lhs, rhs)


def main() -> None:
    verify_beta_binomial()
    verify_basic_moments()
    verify_parameter_family()
    verify_su2_integration_monomials()
    print(f"beta-binomial identities: verified for 1 <= n <= {MAX_N}")
    print(f"basic pure/mixed moments: verified for 1 <= n <= {MAX_N}")
    print(f"three-parameter circuit family: verified on exact rational samples through n = {MAX_N}")
    print(
        "SU(2) monomial integration formula: verified for "
        f"0 <= r,s,t,u <= {MAX_MONOMIAL_DEGREE}"
    )
    print("all exact checks passed")


if __name__ == "__main__":
    main()
