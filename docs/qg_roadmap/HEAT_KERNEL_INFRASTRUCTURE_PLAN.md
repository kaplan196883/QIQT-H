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

- **Phase A + core of B — the ABSTRACT heat semigroup `e^{−tA}` via our functional calculus. ✅ BUILT**
  (`QIQTH/Spectral/HeatSemigroup.lean`, `5f0a132d`, [AF] std-3). For a PVM `P` and a measurable nonneg
  symbol `a : Ω → ℝ`, `heatSemigroup t = P.boundedFC (fun ω => exp(−(t·a ω)))` = `e^{−tA}` for the
  positive self-adjoint `A = ∫ a dE`. Delivered: ★★ `heatSemigroup_mul` (the SEMIGROUP LAW
  `e^{−sA}e^{−tA} = e^{−(s+t)A}`, via `boundedFC_mul` + `Complex.exp_add`), `heatSemigroup_zero`
  (`e^{0·A}=1`), `heatSemigroup_norm_le` (`‖e^{−tA}‖ ≤ 2` — the tower's `2C`, honestly NOT the sharp
  `≤1`), and `heatSemigroup_inner_nonneg` (positivity). No new infrastructure — pure reuse of our tower.
  **Phase B remainder — sharp contraction + strong continuity ✅ BUILT** (same file, `c53978ac`): via the
  tower's `norm_boundedFC_sq` isometry identity — `heatSemigroup_norm_le_one` (the SHARP `‖e^{−tA}‖ ≤ 1`,
  upgrading the `2C` bound) and strong continuity in L²-spectral form (`heatSemigroup_sub_id_normSq`:
  `‖e^{−tA}x−x‖² = ∫‖e^{−ta}−1‖² dμ_x`; `heatSemigroup_L2_tendsto_zero`: that integral `→ 0` as `t→0⁺`
  by dominated convergence) — together, `e^{−tA}x → x`, a genuine **C₀-semigroup**. *Remaining in B (the
  harder piece, unbuilt):* the generator `= −A` (`d/dt e^{−tA}|₀` — unbounded operator + domains).
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

## 3′. CONCRETE BUILD SEQUENCE (the loop) — per-phase sub-bricks, tractable vs wall

Ordered list of the next bricks, each an axiom-free green increment on our own tower until the genuine
wall. The loop attempts these in order; at a wall it CHECKPOINTS honestly (records what's missing, does
NOT force, NEVER axiom-izes) and stops.

- **B1 — the generator `= −A`. ⚠ tractable-hard (NEXT).** For `x` in the domain (`∫ λ² dμ_x < ∞`),
  `lim_{t→0⁺} (e^{−tA}x − x)/t = −Ax`, where `Aх = ∫ a dE x` (the tower's unbounded FC, `UnboundedFC`).
  Spectral-integral + dominated-convergence argument (like strong continuity, one order up:
  `‖(e^{−tA}x−x)/t + Ax‖² = ∫ |(e^{−ta}−1)/t + a|² dμ_x → 0`). Consult first; build.
- **C0 — the abstract positive self-adjoint generator. ✅ ALREADY HAVE.** Any PVM / nonneg symbol gives
  a positive self-adjoint `A` (our tower); the abstract "Laplace-type" operator is done. The MANIFOLD
  instantiation is C1 below.
- **F0 — the abstract McKean–Singer / trace formula. ⚠ possibly tractable (finite-dim / trace-class
  hypothesis form).** `Tr e^{−tA} = Σ_i e^{−λᵢ t}` for a positive self-adjoint `A` with discrete
  spectrum `{λᵢ}` — as a CONDITIONAL statement carrying "discrete spectrum + trace-class" as a
  hypothesis (the manifold guarantees it via D, the wall). Finite-dim version certainly; the
  trace-class abstract version if Mathlib's `Schatten`/trace API suffices. Attempt; checkpoint if the
  trace API fights.
- **C1 — `Δ` on `L²(M)` is positive self-adjoint. ⛔ WALL (manifold `L²`/`Δ`).** Needs the Riemannian
  volume `L²`, `Δ` as an unbounded operator on it, essential self-adjointness. Substantial; likely wall.
- **D — discrete spectrum / compact resolvent. ⛔ THE WALL.** Rellich–Kondrachov (`H¹ ↪ L²` compact) —
  ABSENT from Mathlib. Not buildable in bricks. CHECKPOINT here.
- **E — smooth integral kernel. ⛔ THE WALL.** Elliptic regularity + Sobolev embedding — ABSENT. Not
  buildable. CHECKPOINT.

**STOP CONDITION for the loop:** build B1 (+ F0 if tractable); when the next needed brick is C1/D/E
(the manifold `L²`/Rellich/elliptic-regularity infrastructure, absent from Mathlib), STOP — record the
exact missing Mathlib pieces in this doc, give the honest summary, and end. Do NOT spin on the wall; do
NOT fake it with an axiom or a vacuous hypothesis.

## 4. Firewall (binding)

Phases C–E are the genuine wall — Rellich compactness, elliptic regularity, Sobolev-on-manifolds — none
in Mathlib, none supplied by any book, none buildable in bricks; they are named here, not done. Phase A
is the abstract operator semigroup only. NOTHING here builds the manifold heat kernel or discharges
`a₁ = R/6` (already derived two ways at the coefficient level). NOT the conjecture, NOT the strong
holographic principle, NOT QG.
