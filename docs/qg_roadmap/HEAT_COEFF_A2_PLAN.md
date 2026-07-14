# The a₂ Seeley–DeWitt coefficient — determination plan (the "new mathematics" brick)

**Date 2026-07-15.** Extends `HeatCoeffDetermination.lean` (which determined `a₁ = R/6`) to the **next**
heat-kernel coefficient `a₂`. Target file: `QIQTH/HeatCoeff2Determination.lean`, `[AF]` std-3.

## The invariant ansatz (Gilkey weight-4 basis)

The diagonal heat coefficient `a₂(x)` of the scalar Laplacian is a UNIVERSAL linear combination of the
weight-4 local scalar Riemannian invariants (Gilkey Lemma 4.8.5 — the 4-dimensional invariant space):

```
a₂ = α·R² + β·|Ric|² + γ·|Rm|² + δ·ΔR
```

`R` scalar curvature, `|Ric|² = R_{ij}R^{ij}`, `|Rm|² = R_{ijkl}R^{ijkl}`, `ΔR` the Laplacian of `R`.
The universality (that `a₂` lies in this span, with dimension-independent constants) is the CARRIED
invariance input (option b), exactly as `HeatCoeffDetermination` carried the weight-2 span `{R, tr E}`.

**Known answer (to reproduce):** `a₂ = (1/360)(5R² − 2|Ric|² + 2|Rm|² + 12ΔR)`, i.e.
`(α,β,γ,δ) = (5, −2, 2, 12)/360 = (1/72, −1/180, 1/180, 1/30)`.

## ★ The elegant self-contained step: `α = 1/72` from products + `a₁ = R/6`

The heat trace multiplies under Riemannian products, `Θ_{M×N}(t) = Θ_M(t)·Θ_N(t)`; expanding the
Weyl-normalized series `(1 + a₁^M t + a₂^M t² + …)(1 + a₁^N t + a₂^N t² + …)` gives the product rule

```
a₂(M×N) = a₂(M) + a₂(N) + a₁(M)·a₁(N).
```

On a product, the geometry is block-diagonal, so `R`, `|Ric|²`, `|Rm|²`, `ΔR` are all ADDITIVE — EXCEPT
`R² = (R_M+R_N)² = R_M² + R_N² + 2 R_M R_N`. Applying the ansatz:

```
a₂(M×N) − a₂(M) − a₂(N) = α·(2 R_M R_N).
```

But the product rule says this equals `a₁(M)·a₁(N) = (R_M/6)(R_N/6) = R_M R_N / 36`. Hence

```
2α = 1/36   ⟹   α = 1/72 = 5/360.      ✓ (matches Gilkey)
```

**Self-contained** — needs only `a₁ = R/6` (have) and the product rule (elementary). No carried `a₂` value.
This is the genuinely new, elegant derivation and the centerpiece of the brick.

## `β, γ` from constant-curvature model values (carried classical inputs)

On a space of constant sectional curvature `κ`, dimension `m`:
`R = κ m(m−1)`, `|Ric|² = κ² m(m−1)²`, `|Rm|² = 2κ² m(m−1)`, `ΔR = 0`.
So (κ = 1, `ΔR` drops):
```
a₂(S^m) = m(m−1)·[ α·m(m−1) + β·(m−1) + 2γ ].
```
Carry the classical Weyl-normalized `a₂(S^m)` values (from the round-sphere heat trace / literature):
```
a₂(S²) = 1/15,   a₂(S³) = 1/2,   a₂(S⁴) = 29/15.
```
Dividing by `m(m−1)` (= 2, 6, 12) gives the linear system in `(α,β,γ)`:
```
m=2:  2α +  β + 2γ = 1/30
m=3:  6α + 2β + 2γ = 1/12
m=4: 12α + 3β + 2γ = 29/180
```
Solving (verified): `α = 1/72`, `β = −1/180`, `γ = 1/180` — the `α` here CROSS-CHECKS the product
derivation (independent confirmation), and `β, γ` are pinned. (`δ` is invisible on spheres since `ΔR=0`.)

## `δ` (the `ΔR` coefficient)

`ΔR = 0` on all homogeneous models, so `δ` is NOT fixed by spheres or products. Carry `δ = 12/360 = 1/30`
as the cited classical value (it requires a non-homogeneous/conformal computation — Gilkey §4.8), clearly
labelled. The curvature-squared part `(α,β,γ)` — the physically load-bearing piece — is the derived content.

## Brick structure (`HeatCoeff2Determination.lean`)

1. `a2Invariant α β γ δ R Ric2 Rm2 boxR := α*R^2 + β*Ric2 + γ*Rm2 + δ*boxR`.
2. ★ `alpha_from_product` : from the product rule `a₂(M×N)−a₂(M)−a₂(N) = a₁(M)a₁(N)` (stated with the
   ansatz + additive `R,Ric2,Rm2` and `a₁=R/6`) DERIVE `2α = 1/36`, so `α = 1/72`. Self-contained.
3. `constCurvA2 α β γ κ m := a2Invariant α β γ δ (κ*m*(m-1)) (κ^2*m*(m-1)^2) (2*κ^2*m*(m-1)) 0` and the
   three carried model equations `constCurvA2 .. 1 2 = 1/15`, `.. 1 3 = 1/2`, `.. 1 4 = 29/15`.
4. `constants_determined` : those three equations ⟹ `α=1/72 ∧ β=−1/180 ∧ γ=1/180` (linear solve;
   `α` agrees with step 2).
5. `a2_formula` : `a2Invariant (5/360) (-2/360) (2/360) (12/360) R Ric2 Rm2 boxR = (1/360)*(5*R^2 - 2*Ric2 + 2*Rm2 + 12*boxR)` (algebraic).
6. Capstone tying it together + the honest firewall.

## Firewall (binding, honest)

This DETERMINES the universal `a₂` constants from the invariance ansatz + product structure + carried model
values — the SAME status as `HeatCoeffDetermination` for `a₁`. It does NOT construct the manifold heat kernel
or PROVE `a₂(x)` is this invariant for an arbitrary metric (that is the manifold heat-kernel PARAMETRIX — the
wall). `α = 1/72` is genuinely self-contained (products + `a₁=R/6`); `β,γ` use carried classical sphere
values; `δ` is a cited classical input. NOT the conjecture, NOT the strong principle, NOT QG.
