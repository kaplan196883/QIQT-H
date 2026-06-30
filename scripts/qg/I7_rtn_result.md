# I7 — finite-capacity toy substrate (random tensor network): RT holds, dynamical Lorentz NOT tested

**Date:** 2026-06-30. **Reproduce:** `python scripts/qg/rtn_rt_substrate.py` (deterministic; data in
`scripts/qg/rtn_rt_data.txt`). **Lean core:** `QIQTH.QG.mincut_bounds_distinguishable_records`. Tier-2 §2.1 /
§2.2 of the QG roadmap; the last planned increment of `QG_CAMPAIGN_PLAN.md`.

## What was built and measured

A random tensor network (RTN) on a **ring** of `n = 5` bulk nodes (each a random complex-Gaussian tensor with two
ring bonds of dimension `D` and one dangling boundary leg of dimension `d = D`), contracted to a boundary state.
For a contiguous boundary arc `A` of `m` legs we measure the entanglement entropy `S(A)` and compare to the
Ryu–Takayanagi prediction `S(A) → (min-cut bonds) · log D` (Hayden–Nezami–Qi–Thomas–Walter–Yang 2016). On a ring,
a contiguous arc is separated by `min(m, 2)` bonds, so the RT bound is `min(m,2)·log D`.

| `D` | `S/(1·log D)`, m=1 | `S/(2·log D)`, m=2 |
|----:|----:|----:|
| 2 | 0.503 | 0.420 |
| 4 | 0.869 | 0.695 |
| 6 | 0.933 | 0.785 |
| 8 | 0.962 | 0.830 |
| 12 | **0.980** | **0.872** |

(48 random seeds per point.)

## Result — RT / capacity-is-area holds (kinematically)

`S(A)/(min-cut · log D)` increases **monotonically toward 1 from below** as `D` grows, and **never exceeds 1** in
any instance — i.e. `S(A) ≤ min-cut · log D` always. That upper bound is exactly the Lean theorem
`mincut_bounds_distinguishable_records` (`log #records ≤ cut`, equivalently `S ≤ cut`, built on Track C's
`entropy_le_cut`). So the finite RTN code **saturates the RT bound from below**: the distinguishable-record
capacity across a cut is the **min-cut "area," not the volume** — the Tier-2 §2.2 area law, exhibited in a model
and proved (as the bound) in Lean. The slower approach for `m = 2` (larger cut) is the expected finite-`D`
`−O(1)` correction.

## ⚠️ Honest checkpoint — the I4 dynamical-Lorentz mandate is NOT tested here

A random tensor network is a **static Euclidean code**: it has **no Lorentzian time evolution**, so the decisive
one-loop speed splitting `Δc² = Z_s/Z_t − 1` (I4 — the test that killed the naive finite-cutoff branch) **cannot
be measured in it**. This toy demonstrates only the **kinematic** holographic structure (RT, capacity = area, code
locality/reconstruction). It does **not** address whether finite capacity can carry approximate Lorentz invariance
*dynamically* — and after I4, that is the binding question.

The I4 mandate — *a substrate must show `Δc²(Λ) → 0` parametrically* — therefore requires a **Lorentzian**
substrate (a quantum cellular automaton with emergent Lorentz dynamics, or one of the protection mechanisms:
exact symmetry / SUSY-like cancellation / deformed–statistical Lorentz invariance / a genuinely nonlocal
holographic substrate). That is the **next frontier**, not a static tensor network. The RTN's RT success must
**not** be mis-read as passing the dynamical Lorentz test.

## Where this leaves the campaign

The finite-capacity substrate exhibits the holographic **kinematics** cleanly (RT/area law, machine-checked
bound). The **dynamics** — the part I4 showed is the real obstruction — remains open and now has a sharp,
measurable bar: build a Lorentzian finite-capacity substrate and show `Δc²(Λ) → 0`. The `1/4` and the value of
`G` are never asserted; `min-cut = A/4ℓ_P²` stays the carried UV datum.
