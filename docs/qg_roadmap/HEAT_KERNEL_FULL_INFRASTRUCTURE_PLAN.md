# HEAT-KERNEL FULL INFRASTRUCTURE PLAN — the general `a₁ = R/6` on any closed manifold

**Date:** 2026-07-14. **Parent:** `HEAT_KERNEL_INFRASTRUCTURE_PLAN.md` (the abstract-semigroup slice, DONE)
and `HEAT_KERNEL_GAP_PLAN.md` (the coefficient side, DONE). This document is the FULL dependency tower for
the *general* curved case: `Tr e^{−tΔ} ~ (4πt)^{−d/2} ∫ (a₀ + a₁ t + …)` with `a₁ = R/6`, on an arbitrary
closed Riemannian manifold — the thing the sphere/torus cracks validate but do not generalize.

**Scope honesty (binding):** the whole tower is a **multi-year, Mathlib-community-scale** effort. This plan
marks exactly which layers we already OWN, which are UPSTREAM (WIP in Mathlib), which are the big
COMMUNITY-scale analysis walls, and the ONE self-contained layer we can BUILD OURSELVES in bricks
(trace-class). No layer is claimed done until it is a machine-checked, axiom-free theorem.

---

## Why the general case needs this at all

The sphere/torus heat traces are computable because **symmetry gives the spectrum in closed form**, so we
sum a series and never prove the heat kernel *exists*. A general manifold has **no explicit spectrum**
(eigenvalues are transcendental functionals of the metric with no formula), so the spectral shortcut is
mathematically unavailable. The only route to the general `a₁ = R/6` is to **construct the heat kernel
directly** and prove its short-time expansion — which is the tower below.

## The dependency tower (bottom → top; ✅ ours · 🟡 upstream · ⛔ community-wall · 🔨 build-ourselves)

- **L0 — Riemannian substrate. 🟡 UPSTREAM (WIP).** Metric ✅(Gouëzel). Levi-Civita 🟡(#36845). Riemann/
  Ricci/scalar `R` 🟡(#36036, WIP). Exp map / normal coords 🟡. Riemannian volume `Measure` ⚪. — *Track
  upstream; contribute the Ricci/scalar-`R` contractions when the tensor lands. Coordinate `R` already
  self-built (`CoordinateCurvature.lean`).*
- **L1 — Function spaces on `M`. ⛔ community, medium-large.** `L²(M)` vs the volume measure; Sobolev
  `Hᵏ(M)` via charts + partition of unity (Mathlib has `Sobolev` on `ℝⁿ`, partial). — *Standard but
  substantial; needs L0's volume.*
- **L2 — `Δ` as an operator. ✅/🟡 (machinery ours).** `Δf = −div grad f`; then `Δ` unbounded, essentially
  self-adjoint on `L²(M)`. — *We OWN the unbounded self-adjoint / Stone / PVM tower (`QIQTH/Spectral`);
  missing = the manifold-specific essential-self-adjointness (needs L3's Gårding).*
- **L3 — Elliptic theory. ⛔ THE CRUX (community, large).** Gårding's inequality → elliptic regularity →
  Rellich–Kondrachov (`Hᵏ⁺¹↪Hᵏ` compact) ⟹ discrete spectrum + smooth eigenfunctions. — *The hardest,
  most load-bearing layer; nothing exists.*
- **L4 — Heat kernel. ✅ (abstract half ours).** `e^{−tΔ}` ✅ (**built** — `HeatSemigroup.lean`: the
  abstract C₀-semigroup + generator `−A`). Then the smooth kernel `K_t(x,y) = Σ e^{−λt} φᵢ(x)φᵢ(y)` via
  Sobolev embedding + Weyl-law convergence. — *Reachable once L3 gives smooth eigenfunctions.*
- **L5 — Trace-class + trace. 🔨 BUILD OURSELVES (self-contained).** A Schatten/trace-class API →
  `Tr e^{−tΔ} = Σ e^{−λt} = ∫ K_t(x,x)` (McKean–Singer). — *Pure functional analysis, NO manifold/PDE
  needed — the ONE big missing layer we can build in bricks and contribute upstream. Sub-plan below.*
- **L6 — Short-time expansion → `a₁ = R/6`. ✅ (coefficient algebra ours).** `K_t(x,x) ~ (4πt)^{−d/2}Σaₖtᵏ`
  via the transport recursion — **built** (`DeWittDiagonal.lean`: `u₁(x,x)=R/6`; `CoordinateCurvature`,
  `HeatCoeffDetermination`). — *The top; needs the kernel below it to feed it.*

**What we already own:** L2's machinery, L4's abstract semigroup+generator, L6's coefficient algebra, and
L0's coordinate `R`. The general theorem *assembles* from these once L1/L3/L5 exist.

---

## L5 — THE TRACE-CLASS / SCHATTEN API (the buildable layer) — sub-plan

Self-contained functional analysis on a complex Hilbert space `H` with a `HilbertBasis`. Mathlib HAS:
`HilbertBasis` (`l2Space`), `ContinuousLinearMap.adjoint`, positive operators (`InnerProductSpace/Positive`),
CFC `sqrt` (for `|T| = √(T⋆T)`), the finite-dim trace (`InnerProductSpace/Trace`). Mathlib LACKS: everything
infinite-dim trace-class. Phased bricks (each axiom-free, green):

- **T1 — Hilbert–Schmidt operators.** `IsHilbertSchmidt T := Summable (fun i => ‖T (b i)‖²)`; the HS
  norm-squared `‖T‖²_HS := ∑' i, ‖T (b i)‖²`. ★ **basis-independence** via the Parseval double-sum swap
  `∑ᵢ‖Teᵢ‖² = ∑ᵢⱼ|⟪eⱼ,Teᵢ⟫|² = ∑ⱼ‖T⋆eⱼ‖²` (`HilbertBasis.tsum` / Parseval + `ENNReal`/`tsum` Tonelli swap)
  ⟹ `‖T‖_HS = ‖T⋆‖_HS`, ONB-independent. HS operators form a two-sided ideal; `‖ST‖_HS ≤ ‖S‖·‖T‖_HS`.
- **T2 — Trace-class + the trace.** `IsTraceClass T := IsHilbertSchmidt |T|^{1/2}`... (or `T = A B` with
  `A,B` HS). The trace `Tr T := ∑' i, ⟪b i, T (b i)⟫`; ★ **basis-independence** for trace-class `T`;
  `|Tr T| ≤ ‖T‖₁` (trace norm). Trace-class ⊆ HS ⊆ compact.
- **T3 — Ideal + cyclicity.** `A` trace-class, `B` bounded ⟹ `AB, BA` trace-class; ★ `Tr(AB) = Tr(BA)`;
  `Tr` linear; `Tr T⋆ = conj (Tr T)`.
- **T4 — Positive discrete-spectrum ⟹ `Tr = Σλ`.** For positive self-adjoint `A` with an eigenbasis
  `{φᵢ, λᵢ}` (from L3, carried as hypothesis until then): `A` trace-class ⟺ `Summable λ`, and
  `Tr A = ∑' λᵢ` — the McKean–Singer bridge; specializes to `Tr e^{−tΔ} = Σ e^{−λt}` (feeds L5→L6).

**Value:** T1–T4 give Mathlib a genuine trace-class API (upstream-worthy) and close the L5 layer. ⚠ Even
with L5 done, the general `a₁=R/6` still waits on L1 + L3 (the manifold-analysis walls) — L5 unblocks the
*trace/spectral* side, not the *manifold-existence* side.

---

## The loop scope (what is autonomously buildable)

The **whole** tower is NOT loopable by us: L1/L3 are community-scale analysis on the upstream L0 geometry.
The **loopable** part is exactly **L5 (the trace-class API, T1→T4)** — self-contained, brick-shaped, ours to
build. The loop drives T1→T4 to completion, each an axiom-free green brick under the standard discipline,
then **checkpoints at the L1/L3 manifold-analysis wall** (records the exact missing pieces, does NOT force,
NEVER axiom-izes) and stops. L2/L4/L6 are already ours; L0 is tracked upstream.

## Firewall (binding)

L1/L3 (manifold `L²`/Sobolev/elliptic-regularity/Rellich) are the genuine community-scale walls — no brick,
no book. L5 (trace-class) is self-contained and buildable. NOTHING here builds the manifold heat kernel or
discharges the general `a₁ = R/6` until L1+L3+L5 all exist and are assembled with L2/L4/L6. `a₁ = R/6` stays
VALIDATED on the specific cracks (`S²`), derived at the coefficient level, but not generally discharged. NOT
the conjecture, NOT the strong holographic principle, NOT QG.
