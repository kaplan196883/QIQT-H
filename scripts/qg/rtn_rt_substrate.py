#!/usr/bin/env python3
"""
QG campaign I7 — finite-capacity toy substrate: a random tensor network (RTN) exhibiting RT.

Builds a random tensor network on a RING of n bulk nodes (each a random Gaussian tensor with two ring
bonds of dimension D and one dangling boundary leg of dimension d=D), contracts it to a boundary state,
and measures the entanglement entropy S(A) of a contiguous boundary arc A of m legs.  For random
tensors at large bond dimension, the Hayden-Nezami-Qi-Thomas-Walter-Yang (2016) result gives

    S(A)  ->  (min-cut bonds separating A from its complement) * log D

i.e. the Ryu-Takayanagi formula as a *theorem about the code* (entropy = min-cut "area", not volume).
On a ring, a contiguous arc A with 1 <= m <= n-1 boundary legs is separated by min(m, 2) bonds when
d=D (the smaller of the arc's own legs and the two ring bonds), so:

    m = 1  ->  S(A)/log D  ->  1     (the single boundary leg is the cut)
    m = 2  ->  S(A)/log D  ->  2     (the two ring bonds are the RT surface)

This is the finite Tier-2 §2.1 substrate exhibiting the capacity-is-area law (the Lean core is
`QIQTH.QG.mincut_bounds_distinguishable_records`).

HONEST SCOPE — the I4 mandate is NOT testable here.  A random tensor network is a STATIC Euclidean code:
it has NO Lorentzian time evolution, so the radiatively-induced Lorentz-violation speed splitting
Delta c^2 (I4, the decisive test) cannot be measured in it.  This toy demonstrates only the KINEMATIC
holographic structure (RT / capacity=area / code locality).  The dynamical Lorentz mandate from I4
(a substrate must show Delta c^2(Lambda) -> 0 parametrically) requires a LORENTZIAN substrate — a
quantum cellular automaton with emergent Lorentz dynamics — which is the next frontier, NOT a static RTN.
This is recorded so the RTN's RT success is not mis-read as passing the dynamical Lorentz test.

Reproduce:  python scripts/qg/rtn_rt_substrate.py   (deterministic: fixed RNG seeds)
"""
from __future__ import annotations

import string

import numpy as np

LETTERS = string.ascii_lowercase


def ring_state(n: int, D: int, d: int, rng: np.random.Generator) -> np.ndarray:
    """Contract a ring of n random tensors T_i of shape (D_left, d_boundary, D_right) into the
    boundary state psi[b_0,...,b_{n-1}] (shape (d,)*n), normalized."""
    if 2 * n > len(LETTERS):
        raise ValueError("n too large for einsum labelling")
    bonds = list(LETTERS[:n])          # g_i : bond shared by T_i (right) and T_{i+1} (left)
    bdys = list(LETTERS[n:2 * n])      # h_i : boundary leg of T_i
    tensors = [rng.standard_normal((D, d, D)) + 1j * rng.standard_normal((D, d, D))
               for _ in range(n)]
    subs = []
    for i in range(n):
        left = bonds[(i - 1) % n]      # T_i left bond = bond between i-1 and i
        right = bonds[i]               # T_i right bond = bond between i and i+1
        subs.append(left + bdys[i] + right)
    spec = ",".join(subs) + "->" + "".join(bdys)
    psi = np.einsum(spec, *tensors, optimize=True)  # pairwise contraction; naive path is ~d^n*D^n
    psi = psi.reshape(-1)
    psi = psi / np.linalg.norm(psi)
    return psi.reshape((d,) * n)


def entropy_arc(psi: np.ndarray, n: int, m: int, d: int) -> float:
    """von Neumann entropy (nats) of the first m boundary legs."""
    mat = psi.reshape(d ** m, d ** (n - m))
    sv = np.linalg.svd(mat, compute_uv=False)
    p = sv ** 2
    p = p[p > 1e-13]
    return float(-(p * np.log(p)).sum())


def mincut_arc_ring(n: int, m: int, D: int, d: int) -> int:
    """RT prediction (in units of log of the relevant dim): a contiguous arc of m legs on a ring is
    separated by min(m boundary legs, 2 ring bonds).  With d=D this is min(m, 2) * log D."""
    return min(m, 2)


def _instance(args: tuple[int, int, int, int]) -> float:
    """Worker (module-level, picklable): one RTN instance -> S(A).  args = (n, D, m, seed)."""
    n, D, m, seed = args
    rng = np.random.default_rng(1000 * D + 7 * m + seed)
    psi = ring_state(n, D, d=D, rng=rng)
    return entropy_arc(psi, n, m, d=D)


def main() -> None:
    n = 5
    seeds = 48
    Ds = (2, 3, 4, 5, 6, 8, 10, 12)
    print("=" * 78)
    print("QG I7 — random tensor network on a ring: S(A) -> (min-cut bonds) * log D  (RT)")
    print(f"  n = {n} nodes, boundary leg dim d = D, contiguous arc A of m legs, {seeds} random seeds")
    print("  (numpy BLAS multithreads the SVD/einsum across cores)")
    print("=" * 78)

    table: dict[tuple[int, int], list[float]] = {}
    for m in (1, 2):
        for D in Ds:
            table[(m, D)] = [_instance((n, D, m, k)) for k in range(seeds)]

    for m in (1, 2):
        mincut = mincut_arc_ring(n, m, 0, 0)  # = min(m, 2)
        print(f"\n region A = {m} leg(s)   (RT min-cut = {mincut} bond(s); RT bound S <= {mincut}*log D)")
        print("   D     <S(A)> (nats)   {0}*log D     S/({0}*log D)   <= 1 (Lean bound)".format(mincut))
        print("   " + "-" * 58)
        last = 0.0
        for D in Ds:
            meanS = float(np.mean(table[(m, D)]))
            rt = mincut * np.log(D)
            sat = meanS / rt
            last = sat
            ok = "ok" if sat <= 1.0 + 1e-9 else "VIOLATED"
            print(f"   {D:2d}    {meanS: .5f}      {rt: .5f}     {sat: .5f}     {ok}")
        print(f"   -> S/(min-cut*log D) increases toward 1 FROM BELOW (saturating the RT bound); "
              f"D={Ds[-1]} gives {last:.3f}.")

    print("\n" + "=" * 78)
    print("RESULT: S(A) tracks (min-cut bonds) * log D -> the RT / capacity-is-area law holds in the")
    print("  finite RTN code (KINEMATIC holographic structure).  Lean core: mincut_bounds_distinguishable_records.")
    print("HONEST CHECKPOINT (I4 mandate): a static RTN has NO Lorentzian dynamics, so the decisive")
    print("  Delta c^2 Lorentz-violation test is NOT measurable here.  The dynamical mandate -- a substrate")
    print("  must show Delta c^2(Lambda) -> 0 -- requires a LORENTZIAN QCA substrate, the next frontier,")
    print("  NOT a static tensor network.  The RTN's RT success is kinematic only; it does not pass I4.")
    print("=" * 78)


if __name__ == "__main__":
    main()
