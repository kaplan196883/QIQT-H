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
  by dominated convergence) — together, `e^{−tA}x → x`, a genuine **C₀-semigroup**. **B1 — the generator
  `= −A` ✅ BUILT** (`28995c75`): the real analogue of the tower's unitary Stone generator —
  `heatSymbol_diffQuotient_L2_tendsto` (slope `(e^{−tA}x−x)/t → −Ax` in `L²(μ_x)`) AND the full one-sided
  `hasDerivWithinAt_heatSemigroup` (`HasDerivWithinAt (fun t => e^{−tA}x) (−fcOp a x) (Ici 0) 0`),
  `A = ∫a dE` the tower's unbounded `fcOp`. ⟹ **Phase B COMPLETE: the abstract heat semigroup is a
  genuine C₀-semigroup with generator −A**, entirely on our own tower.
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

- **B1 — the generator `= −A`. ✅ BUILT (`28995c75`).** Both the L²-slope form and the full one-sided
  `HasDerivWithinAt`; the C₀-semigroup now has its generator `−A`. (Original scope below.) For `x` in the domain (`∫ λ² dμ_x < ∞`),
  `lim_{t→0⁺} (e^{−tA}x − x)/t = −Ax`, where `Aх = ∫ a dE x` (the tower's unbounded FC, `UnboundedFC`).
  Spectral-integral + dominated-convergence argument (like strong continuity, one order up:
  `‖(e^{−tA}x−x)/t + Ax‖² = ∫ |(e^{−ta}−1)/t + a|² dμ_x → 0`). Consult first; build.
- **C0 — the abstract positive self-adjoint generator. ✅ ALREADY HAVE.** Any PVM / nonneg symbol gives
  a positive self-adjoint `A` (our tower); the abstract "Laplace-type" operator is done. The MANIFOLD
  instantiation is C1 below.
- **F0 — the abstract McKean–Singer / trace formula. ⛔ CHECKPOINTED — BLOCKED (2026-07-14).** The
  genuine (infinite-dim) `Tr e^{−tA} = Σ_i e^{−λᵢ t}` is **not even definable** in our setting: Mathlib
  has **no trace-class / Schatten / Hilbert–Schmidt operator API** (verified — absent from
  `Mathlib/Analysis`). So the operator trace itself does not exist to state the formula. The only
  tractable version is the FINITE-DIM matrix identity (`Matrix.trace (exp(−t•A)) = ∑ exp(−t μᵢ)`, via
  `Analysis/Matrix/Spectrum`) — disconnected from the manifold heat kernel and low-value, so NOT built
  (would be a box-checking toy). ⟹ **F0 joins the wall: the infinite-dim operator trace needs a
  trace-class API that Mathlib lacks** (a further missing-infrastructure piece, alongside C1/D/E).
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

### LOOP OUTCOME (2026-07-14) — STOPPED at the wall, honestly

**Built (the full abstract C₀-semigroup, on our own `Spectral/` tower, axiom-free):** Phase A
(`heatSemigroup` + semigroup law + `t=0` + positivity, `5f0a132d`), Phase B (sharp `‖·‖≤1` + strong
continuity, `c53978ac`), **B1 the generator `= −A`** (`28995c75`). ⟹ `e^{−tA}` is a genuine strongly-
continuous contraction semigroup with generator `−A`, for any positive self-adjoint `A = ∫a dE`.

**The wall — the exact missing Mathlib infrastructure (no brick/book closes these):**
1. **Manifold `L²(M)` + `Δ` as an unbounded operator + essential self-adjointness** (Phase C1) — the
   Riemannian-volume `L²` and the Laplacian on it are not set up.
2. **Rellich–Kondrachov compactness** (`H¹ ↪ L²` compact on a compact manifold) (Phase D) — ABSENT.
   Without it, no discrete spectrum.
3. **Elliptic regularity + Sobolev embedding on manifolds** (Phase E) — ABSENT. Without it, no smooth
   heat kernel `K_t(x,y)`.
4. **A trace-class / Schatten operator API** (Phase F0) — ABSENT. Without it, `Tr e^{−tA}` is undefined.

These four are the genuine, infrastructure-level frontier: each is a Mathlib-team-scale formalization,
none QIQT-H-specific, none a knowledge gap. The heat-kernel EXISTENCE on a manifold is unreached; the
`a₁ = R/6` coefficient stays derived (two ways) but not analytically discharged.

### CRACK IN THE WALL (2026-07-14) — the flat-torus heat trace, one explicit geometry breached

`QIQTH/FlatTorusHeatKernel.lean` (`92350369`, [AF] std-3): the heat trace of `e^{tΔ}` on the flat circle
`ℝ/ℤ` — the ONE geometry where the heat kernel is fully explicit and needs NONE of the four walls. Via the
explicit Fourier spectrum `{(2πk)²}` / eigenfunctions `e^{2πikx}`: `heatTraceCircle t = Σ_k e^{−t(2πk)²}`
(`heatTraceCircle_summable`), proven `= jacobiTheta(I·4πt)` (`heatTraceCircle_eq_jacobiTheta`, Mathlib's
theta function) with the short-time **Weyl asymptotic** `~ (4πt)^{−1/2}` (`heatTraceCircle_asymptotic`, via
the theta S-transformation functional equation) — the **Seeley–DeWitt `a₀ = 1` leading term on a REAL
manifold**, axiom-free. This is the first actual heat trace in the repo: it demonstrates the heat-kernel
program IS computable on an explicitly-solvable geometry, bypassing Rellich / elliptic regularity /
trace-class / manifold-`L²`-`Δ` entirely. ⚠ HONEST: breaks the wall ONLY for this flat case; the general
CURVED heat kernel stays walled; flat ⟹ `R = 0`, so it validates `a₀ = 1` but NOT `a₁ = R/6` (the flat
torus has `a₁ = 0`). The curvature-carrying analytic discharge of `a₁ = R/6` still needs the wall.

**The curved case — unit 2-sphere `S²` (`92350369`→`e271b1ea`, `QIQTH/SphereHeatTrace.lean`): `a₀`
validated on a CURVED manifold; `a₁ = R/6` CHECKPOINTED.** `sphereHeatTrace t = Σ_l (2l+1) e^{−t l(l+1)}`
(explicit `S²` Laplacian spectrum) with `sphereHeatTrace_asymptotic : t·Θ(t) → 1` (`Θ ~ 1/t`, the Weyl
`a₀` on a curved geometry, via sum-integral comparison + explicit sandwich bounds; `weyl_density_integral`
= the exact continuum `∫ = 1/t`). ⚠ The **constant `Θ(t) − 1/t → 1/3 = a₁ = R/6`** (`R=2`) is NOT proven —
the sum-integral slack is `O(1/√t)`, swamping the `O(1)` constant. The math is settled (2nd-order
Euler–Maclaurin: `f(0)/2 − f'(0)/12 = 1/2 − 1/6 = 1/3`) — it is a **formalization gap: Euler–Maclaurin is
ABSENT from Mathlib**, a fifth missing-infrastructure piece. So `a₀` is validated on both a flat (circle)
and a curved (sphere) manifold; the curvature-sensitive `a₁ = R/6` on the sphere is the current analytic
frontier, blocked on Euler–Maclaurin.

**Progress on the sphere `a₁` (EM-1 identity, `e9908e3e`):** `sphereHeatTrace_em1` formalizes the exact
first-order Euler–Maclaurin decomposition `Θ(t) = 1/t + 1/2 + ∫_{(0,∞)} (fract x − ½)·φ'(x) dx` (φ = the
trace density `(2x+1)e^{−t x(x+1)}`), via Mathlib's **Abel summation** (`sum_mul_eq_sub_integral_mul'`).
This reduces `a₁ = R/6 = 1/3` to the single named limit `∫ (fract − ½) φ' → −1/6`.

**★★★ `a₁ = R/6` PROVEN on the curved 2-sphere (`139eb004`).** `sphereHeatTrace_a1 : Θ(t) − 1/t → 1/3`
— the Seeley–DeWitt `a₁ = R/6` (`R = 2` for the unit `S²`), analytically closed at the sum level from the
EXPLICIT `S²` spectrum, axiom-free. The `∫(fract−½)φ' → −1/6` limit (`sphere_R_limit`) is proven by a
**double integration by parts against the periodic Bernoulli functions `B₂, B₃`** — built entirely from
scratch (Mathlib has no EM-remainder formula and no periodic-Bernoulli-on-ℝ API): per-interval IBP +
telescoping (`sphere_R_identity`: `R(t) = −(2−t)/12 + ∫ Q₃ φ'''`) + the `∫|φ'''| = O(√t) → 0` scaling
bound, with `B₃(integer) = 0` supplying the mean-zero cancellation that kills the stubborn `O(1)` term.
It matches `CoordinateCurvature` (sphere `R = 2`) and `DeWittDiagonal` (`u₁ = τ/6 = 1/3`): the SAME
`a₁ = R/6` now confirmed from the actual heat trace. ⚠ HONEST: validates `a₁ = R/6` on THIS curved
geometry via the explicit spectrum + periodic-Bernoulli EM; it does NOT analytically discharge the GENERAL
curved `a₁ = R/6` (the general curved heat-kernel EXISTENCE stays the wall). So `a₁ = R/6` is now validated
on a curved manifold — through the crack, not the whole wall.

## 4. Firewall (binding)

Phases C–E are the genuine wall — Rellich compactness, elliptic regularity, Sobolev-on-manifolds — none
in Mathlib, none supplied by any book, none buildable in bricks; they are named here, not done. Phase A
is the abstract operator semigroup only. NOTHING here builds the manifold heat kernel or discharges
`a₁ = R/6` (already derived two ways at the coefficient level). NOT the conjecture, NOT the strong
holographic principle, NOT QG.
