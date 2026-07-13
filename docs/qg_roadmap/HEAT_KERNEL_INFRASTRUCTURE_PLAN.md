# HEAT-KERNEL ANALYTIC-INFRASTRUCTURE PLAN — building the heat semigroup + kernel

**Date:** 2026-07-14. **Parent:** `HEAT_KERNEL_GAP_PLAN.md` (this is its Phase-3 analytic core, expanded).
**Companion books (`refs/`):** Rosenberg (Ch. 1 spectral + §3.2 parametrix), BGV (§2.4), Gilkey.
**Scope honesty (binding):** the FULL stack (elliptic regularity, Rellich compactness, Sobolev-on-
manifolds, the smooth kernel) is a **multi-year, Mathlib-grade** undertaking that CANNOT be finished in
bricks. This plan phases it so value lands incrementally, marks exactly which phases are tractable NOW
(on our own `QIQTH/Spectral/` tower) vs which are the genuine wall, and builds the tractable ones. No
phase is claimed done until it is a machine-checked, axiom-free theorem.

---

## 0. The two routes to the heat kernel — and why we take the spectral one

`e^{−tP}` for the Laplacian `P = Δ` on a compact manifold can be built via:
- **(a) C₀/analytic one-parameter semigroup theory** (Engel–Nagel / Pazy). Mathlib has *none* of this —
  building it is itself the multi-year project. Rejected as the entry route.
- **(b) the SPECTRAL route** — `Δ` on `L²(M)` is positive self-adjoint with discrete spectrum `{λᵢ}`
  and eigenbasis `{φᵢ}`, so `e^{−tΔ} = Σ e^{−λᵢt} Pᵢ` and `K_t(x,y) = Σ e^{−λᵢt} φᵢ(x)φᵢ(y)`. This is
  Rosenberg's Ch. 1 approach, and it reuses machinery **we already own** (`QIQTH/Spectral/`: PVM,
  `boundedFC`, unbounded Stone, the spectral theorem). We take route (b).

## 1. What we already own (the substrate — `QIQTH/Spectral/`)

- `ProjectionValuedMeasure Ω H` (the genuine σ-additive PVM); `boundedFC` (bounded Borel functional
  calculus) with `boundedFC_mul` (multiplicativity), `_add`, `_smul`, `_const`, `_norm_le`,
  `inner_boundedFC`; the bounded spectral theorem `PVM_of_selfAdjoint`; the unbounded Stone theorem +
  `cayleyStoneU` (the unitary group `e^{itA}`); Gårding density; `UnboundedFC`.
- The Gaussian / flat heat kernel content (G1).

## 2. The phases (each an axiom-free Lean checkpoint; ✅=built, ⚠=tractable-now, ⛔=wall)

- **Phase A — the ABSTRACT heat semigroup `e^{−tA}` via our functional calculus. ⚠ TRACTABLE NOW → BUILDING.**
  For a PVM `P` and a measurable nonneg generator symbol `a : Ω → ℝ` (`a ≥ 0`), define
  `heatSemigroup t := P.boundedFC (fun ω => exp(−(t·a ω)))` (bounded by `1` for `t ≥ 0`, `a ≥ 0`). This
  is `e^{−tA}` for the positive self-adjoint `A = ∫ a dE`. No new infrastructure — pure reuse of our tower.
- **Phase B — the semigroup PROPERTIES. ⚠ mostly tractable.** From the `boundedFC` laws: the semigroup
  law `e^{−sA}e^{−tA} = e^{−(s+t)A}` (`boundedFC_mul`), the identity `e^{−0·A} = 1` (`boundedFC_const`),
  contraction `‖e^{−tA}‖ ≤ 1` (`boundedFC_norm_le`), self-adjointness + positivity (real nonneg symbol,
  `inner_boundedFC`). *Stretch:* strong continuity `e^{−tA} → 1` as `t → 0⁺` (needs dominated
  convergence on the scalar spectral measure) — attempt, else carry.
- **Phase C — `Δ` on `L²(M)` IS a positive self-adjoint operator. ⛔ mostly wall.** Needs the manifold
  `L²` space (Bochner integral against the Riemannian volume), `Δ` as an unbounded operator, and
  essential self-adjointness. Partly reachable (we have unbounded self-adjoint theory), but the manifold
  `L²`/`Δ` setup is missing and substantial.
- **Phase D — discrete spectrum / compact resolvent. ⛔ THE WALL.** On a COMPACT manifold, `(Δ+1)⁻¹` is
  compact ⟹ discrete spectrum `λᵢ → ∞`. Needs **Rellich–Kondrachov** (compactness of `H¹ ↪ L²`) —
  absent from Mathlib.
- **Phase E — the smooth integral kernel. ⛔ THE WALL.** `e^{−tΔ}` is an integral operator with a
  SMOOTH kernel `K_t(x,y)`. Needs **elliptic regularity** + Sobolev embedding (smooth eigenfunctions) +
  Weyl-law series convergence — absent from Mathlib.
- **Phase F — the trace `Tr e^{−tΔ} = Σ e^{−λᵢt} = ∫ K_t(x,x)`. ⛔ given D–E.** McKean–Singer; feeds the
  short-time expansion (already have the diagonal coefficient `u₁(x,x)=R/6`, `DeWittDiagonal.lean`).

## 3. What THIS document delivers now

**Phase A (+ as much of B as compiles)** — the abstract heat semigroup on our PVM tower, axiom-free.
This is the honest first real increment of the analytic core: the semigroup `e^{−tA}` exists as an
operator with its group law, contraction, self-adjointness, and `t=0` identity — for an *abstract*
positive self-adjoint generator. It is NOT the manifold heat kernel (Phases C–E, the wall); it is the
operator-semigroup foundation that the spectral route stands on, built from machinery we own.

## 4. Firewall (binding)

Phases C–E are the genuine wall — Rellich compactness, elliptic regularity, Sobolev-on-manifolds — none
in Mathlib, none supplied by any book, none buildable in bricks; they are named here, not done. Phase A
is the abstract operator semigroup only. NOTHING here builds the manifold heat kernel or discharges
`a₁ = R/6` (already derived two ways at the coefficient level). NOT the conjecture, NOT the strong
holographic principle, NOT QG.
