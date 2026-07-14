# Coordinate-free algebraic Riemannian geometry — curvature, Ricci, scalar, Levi-Civita

**Date 2026-07-15.** Builds the coordinate-free (algebraic / Koszul-connection) skeleton of Riemannian
curvature, on a commutative ring `A` (= smooth functions), vector fields `V = Derivation R A A` (Lie algebra,
acting on `A`), and modules. **Honest scope (binding):** this is the ALGEBRAIC coordinate-free theory — the
tensorial skeleton the smooth-manifold objects instantiate. It is NOT the smooth-manifold tangent-bundle /
Riemannian-metric / Levi-Civita construction (Mathlib-WIP #36036/#36845), and NOT the general heat kernel.

## Brick 1 — `CoordinateFreeCurvature.lean` (curvature of a Koszul connection)
`KoszulConnection` (`cd : Derivation R A A → (M →ₗ[R] M)`, `cd_add`, `leibniz`); curvature
`F(X,Y) = cd X ∘ cd Y − cd Y ∘ cd X − cd ⁅X,Y⁆`; ★ `curvature_smul` (F(X,Y) is `A`-linear — Leibniz
cross-terms cancel, TENSORIALITY); `curvatureTensor : M →ₗ[A] M`; antisymmetry; flat witness.

## Brick 2 — `RicciScalar.lean` (Ricci + scalar as coordinate-free traces)
Finite-free `A`-module `V`; abstract curvature `curv : V →ₗ[A] V →ₗ[A] (V →ₗ[A] V)`.
- `ricciContraction curv : V →ₗ[A] V →ₗ[A] A`, `Ric Y Z := trace_A (fun X => curv X Y Z)` — the first-slot
  contraction; **coordinate-free because `LinearMap.trace` is basis-independent**.
- `scalarContraction curv (ginv : Module.Dual A V →ₗ[A] V) : A := trace_A (ginv ∘ (Ric : V →ₗ Dual))` — the
  metric-trace of the Ricci endomorphism (raise the second index by `ginv = g⁻¹`).
- Flat witness ⟹ `Ric = 0`, `scalar = 0`. Connects to Brick 1's `curvatureTensor`.

## Brick 3 — `LeviCivita.lean` (the fundamental theorem, coordinate-free / algebraic)
Vector fields `V = Derivation R A A`; metric `g : V → V → A` symmetric `A`-bilinear. A connection on the
tangent module is `∇ : KoszulConnection R A V` (so `∇.cd X : V →ₗ[R] V`, `∇.cd X Y = ∇_X Y ∈ V`).

**The Koszul form** (`= 2⟨∇_X Y, Z⟩`):
```
koszul g X Y Z := X (g Y Z) + Y (g X Z) − Z (g X Y) + g ⁅X,Y⁆ Z − g ⁅X,Z⁆ Y − g ⁅Y,Z⁆ X
```
- ★ `koszul_smul_Z` : `koszul g X Y (a • Z) = a • koszul g X Y Z` — `A`-linearity in `Z` (the non-tensorial
  bracket/derivative terms cancel; analogue of curvature tensoriality). Uses `g` `A`-bilinearity + derivation
  Leibniz + bracket Leibniz `⁅X, a•Z⁆ = a•⁅X,Z⁆ + (X a)•Z`.
- Defs `IsTorsionFree ∇ := ∀ X Y, ∇.cd X Y − ∇.cd Y X = ⁅X,Y⁆`;
  `IsMetricCompat g ∇ := ∀ X Y Z, X (g Y Z) = g (∇.cd X Y) Z + g Y (∇.cd X Z)`.
- ★★★ `koszul_formula` : `IsTorsionFree ∇ → IsMetricCompat g ∇ → (g symmetric) →
  2 • g (∇.cd X Y) Z = koszul g X Y Z`. THE fundamental identity — pure algebra (combine the three cyclic
  metric-compat equations, use torsion-free to swap `∇`-orders, `g` symmetry). NO nondegeneracy needed.
- `leviCivita_unique` : two torsion-free metric-compatible connections for the same NONDEGENERATE `g` (and
  `2` invertible) are equal — from `koszul_formula` + nondegeneracy (`2 g(∇¹−∇², Z)=0 ∀Z ⟹ ∇¹=∇²`).
- (Existence — construct `∇` via a musical iso `gSharp : Dual A V ≃ₗ[A] V` and `½ koszul`: OPTIONAL /
  checkpoint if the duality packaging fights; the characterization + uniqueness are the core.)

## Capstone (after all three)
The Levi-Civita connection's curvature (via Brick 1) is the Riemann tensor; its Brick-2 Ricci/scalar are the
Riemannian Ricci/scalar curvature — all coordinate-free (algebraic). Firewall: the SMOOTH-MANIFOLD
instantiation (tangent bundle + Riemannian metric + Levi-Civita on a manifold) remains Mathlib-WIP; NOT the
general curved heat kernel; NOT the conjecture/strong-principle/QG.

## Build discipline
One `lake` build at a time (`ps -W|grep -ci lake` = 0). Order: Brick 1 → Brick 2 → Brick 3. Each: `[AF]` std-3,
no `sorry`, structure fields are hypotheses NOT Lean axioms, wire `QIQTH.lean` + `AxiomAudit` pin + budget 0 +
commit explicit paths + push + docs/memory. Honest firewall in every module docstring.
