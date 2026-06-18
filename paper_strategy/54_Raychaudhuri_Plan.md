# Plan 54 — Raychaudhuri focusing: machine-checking the geometry of Jacobson's front half

User directive: the Bekenstein→per-null arrow has a *geometric* sub-step (Raychaudhuri focusing) that
is NOT QFT (unlike Unruh) — so formalize it. Goal: remove the geometry from the cited front-half list.

## Jacobson's actual derivation (fetched from arXiv:gr-qc/9504004, 2026-06-19)

Verbatim steps and their classification:

1. **Raychaudhuri (focusing):** `dθ/dλ = −½θ² − σ² − R_{ab}k^a k^b`. **[GEOMETRY]**
2. **Stationary horizon at P:** `θ = σ = 0` there; `θ²,σ²` are higher order ⟹ to first order
   `θ = −λ R_{ab}k^a k^b`. **[GEOMETRY]**
3. **Area variation:** `δA = ∫_H θ dλ d𝒜 = −∫_H λ R_{ab}k^a k^b dλ d𝒜`. **[GEOMETRY]**
4. **Heat:** `δQ = ∫ T_{ab}χ^a dΣ^b = −κ ∫_H λ T_{ab}k^a k^b dλ d𝒜`. **[physics: boost-energy flux]**
5. **Unruh temperature:** `T = ℏκ/2π`. **[QFT — cited, not formalizable]**
6. **Entropy ∝ area:** `δS = η δA`. **[the area law / postulate — cited]**
7. **Clausius:** `δQ = T δS`. **[thermodynamics — cited]**
8. Matching integrands ∀ null `k`: `T_{ab}k^a k^b = (ℏη/2π) R_{ab}k^a k^b` ⟹
   `(2π/ℏη)T_{ab} = R_{ab} + f g_{ab}`. **[the per-null relation = our `pernull`/`crux`]**
9. **Contracted Bianchi** `∇^a G_{ab}=0` ⟹ `f = −R/2 + Λ`. **[GEOMETRY — ALREADY MACHINE-CHECKED:
   `twice_contracted_bianchi`]**. With `G = (4ℏη)⁻¹`: `R_{ab} − ½R g_{ab} + Λ g_{ab} = (2π/ℏη)T_{ab}`.

So the **geometry** = steps 1–3 (Raychaudhuri + area variation) and step 9 (Bianchi, already done). The
**cited physics** = Unruh (5) + area law (6) + Clausius (7) — none of which is geometry.

## Formalization target (component framework, `QIQTH/Raychaudhuri.lean`)

The geometric heart of steps 1–2 is the **Ricci identity** + the **raw Raychaudhuri equation**:

- **Ricci identity:** `(∇_μ∇_ν − ∇_ν∇_μ)V^ρ = R^ρ_{σμν} V^σ`. Proof: expand; ∂∂V cancels (Schwarz,
  `pd_comm`); ∂V terms cancel in symmetric pairs; geodesic-direction Γ∂V + ΓΓ cancel (torsion-free,
  `christoffel_symm`); the ∂Γ and ΓΓ curvature terms reassemble into `riemann` (reindexed). Bianchi-scale
  sum bookkeeping.
- **Contracted Ricci identity** (ρ=μ): `∑_μ(∇_μ∇_ν − ∇_ν∇_μ)V^μ = R_{σν}V^σ` (= `ricci`) — this is where
  `−R_{μν}k^μk^ν` is born.
- **Raw Raychaudhuri:** for a **geodesic** `k` (`k^σ∇_σ k^μ=0`) with expansion `θ = ∇_μ k^μ`:
  `k^σ ∂_σ θ = −(∇_μ k^σ)(∇_σ k^μ) − R_{σρ}k^σ k^ρ`. The `−(∇k)(∇k)` term decomposes into Jacobson's
  `−½θ²−σ²+ω²` (ω=0 hypersurface-orthogonal) — the shear/trace decomposition is optional polish.

## Status / build order
- ✅ `covDeriv2Vec` (second covariant derivative `∇_μ∇_ν V^ρ`) + `pd_covDerivVec` (the ∂(∇V) product-rule
  expansion). Axiom-free, builds.
- NEXT: **`ricci_identity`** (the commutator = Riemann) — the big index computation.
- THEN: contracted version → `ricci`; geodesic + divergence → raw Raychaudhuri; (optional) shear/trace
  decomposition to Jacobson's exact `−½θ²−σ²` form.

## Honest scope
This closes the **geometry** of Jacobson's front half. It does **not** make `Bekenstein+QIQT-H ⟹ GR`
fully Lean-checked — Unruh (5) + area law (6) + Clausius (7) remain cited (Unruh is irreducibly QFT; the
area law is the postulate / gap 1). But it removes Raychaudhuri from the cited list, leaving the cited
front-half as exactly {Unruh, area law, Clausius} — all non-geometry.
