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
- **L3 — Elliptic theory. ⛔ THE CRUX (community, large) — now DECOMPOSED.** Gårding's inequality →
  elliptic regularity → Rellich–Kondrachov (`Hᵏ⁺¹↪Hᵏ` compact) ⟹ discrete spectrum + smooth
  eigenfunctions. **The load-bearing conclusion "discrete spectrum + orthonormal eigenbasis" splits into
  two independent pieces:** (L3a) the ABSTRACT Hilbert-space fact *a compact self-adjoint operator has an
  orthonormal eigen-`HilbertBasis`* (Riesz–Schauder; NO manifold) — **buildable now**, see L3a below; and
  (L3b) the genuine manifold-analytic input *the resolvent `(Δ+1)⁻¹` is compact* (= Rellich–Kondrachov;
  still the community wall). Building L3a turns "the eigenbasis" from a monolithic wall into exactly the
  single labelled input "resolvent-compact", pushing the irreducible analysis as far up as it goes.
- **L3a — Compact self-adjoint ⟹ eigen-`HilbertBasis`. 🔨 BUILDING (self-contained, manifold-free).**
  Mathlib HAS the pieces (`InnerProductSpace/Spectrum.lean`: `orthogonalComplement_iSup_eigenspaces_eq_bot`
  for compact self-adjoint = eigenspaces dense; `finite_dimensional_eigenspace`; `orthogonalFamily_eigenspaces`;
  `orthonormal_sigma_orthonormal`; `exists_hilbertBasis`; `mkOfOrthogonalEqBot`) but does NOT ASSEMBLE the
  infinite-dim eigen-`HilbertBasis`. That assembly (`QIQTH/TraceClass/CompactSpectral.lean`:
  `compactSelfAdjoint_hasEigenbasis` + `compactSelfAdjoint_traceE_eq_tsum_eigenvalues`) DISCHARGES T4's
  carried eigenbasis hypothesis for every compact self-adjoint operator — upstream-worthy. ⚠ removes the
  eigenbasis assumption only for the COMPACT self-adjoint case; the manifold input (L3b) is untouched.
- **L3b — Resolvent of `Δ` is compact (Rellich–Kondrachov). ⛔ community wall.** `(Δ+1)⁻¹` compact on
  `L²(M)` — the one genuine manifold-analytic input that, fed to L3a, delivers `Δ`'s discrete spectrum +
  eigenbasis. Nothing in Mathlib; needs L1 (Sobolev-on-`M`) + the compact-embedding theorem.
- **L4 — Heat kernel. ✅ (abstract half ours).** `e^{−tΔ}` ✅ (**built** — `HeatSemigroup.lean`: the
  abstract C₀-semigroup + generator `−A`). Then the smooth kernel `K_t(x,y) = Σ e^{−λt} φᵢ(x)φᵢ(y)` via
  Sobolev embedding + Weyl-law convergence. — *Reachable once L3 gives smooth eigenfunctions.*
- **L5 — Trace-class + trace. ✅ DONE (built ourselves, T1–T4, axiom-free).** A Schatten/trace-class API →
  `Tr e^{−tΔ} = Σ e^{−λt}` (McKean–Singer). — *Pure functional analysis, NO manifold/PDE needed — the ONE
  big missing layer we built in bricks (upstream-worthy): `QIQTH/TraceClass/{HilbertSchmidt,Trace,Cyclic,
  Spectral}.lean`. **Complete.** ⚠ the spectral bridge (T4) carries the eigenbasis as a HYPOTHESIS — the
  discrete spectrum is exactly L3, not supplied here. Sub-plan below, all four bricks landed.*
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
- **T4 — Positive discrete-spectrum ⟹ `Tr = Σλ`. ✅ `517561f4`.** For `A` with an eigenbasis
  `A(bᵢ)=μᵢ•bᵢ` (from L3, carried as hypothesis `hA` until then): `traceE_eq_tsum_eigenvalues` gives
  `Tr A = ∑' μᵢ` unconditionally; `isTraceClass_of_summable_eigenvalues` gives the `Summable μ ⟹` trace-class
  direction (ℓ²-diagonal √μ-multiplier); `mckean_singer_heatTrace` specializes to `Tr e^{−tΔ} = Σ e^{−λt}`
  (feeds L5→L6). `re_traceE_eq_tsum_eigenvalues` for the real part.

**Status: L5 COMPLETE.** T1 `c9a943e8` · T2 `335d88ab` · T3 `37a8ed45` · T4 `517561f4` — all axiom-free,
budget 0. T1–T4 give Mathlib a genuine trace-class API (upstream-worthy) and close the L5 layer. ⚠ Even
with L5 done, the general `a₁=R/6` still waits on L1 + L3 (the manifold-analysis walls) — L5 unblocks the
*trace/spectral* side, not the *manifold-existence* side.

---

## The loop scope (what is autonomously buildable)

The **whole** tower is NOT loopable by us: L1/L3 are community-scale analysis on the upstream L0 geometry.
The **loopable** part is exactly **L5 (the trace-class API, T1→T4)** — self-contained, brick-shaped, ours to
build. **DONE 2026-07-14:** the loop drove T1→T4 to completion, each an axiom-free green brick under the
standard discipline, and **stopped at the L1/L3 manifold-analysis wall** (recorded below, not forced, not
axiom-ized). L2/L4/L6 are already ours; L0 is tracked upstream.

**WHERE THE TOWER STANDS (2026-07-14).** OURS/DONE: L2 machinery, L4 abstract semigroup+generator, L5
trace-class API (T1–T4), L6 coefficient algebra, L0 coordinate `R`. UPSTREAM (WIP, tracked): L0 Riemannian
tensors. **THE REMAINING WALLS — L1 + L3 (community-scale, NOT buildable by us):** L1 = `L²(M)`/Sobolev
`Hᵏ(M)` on a manifold vs the Riemannian volume measure (needs L0's volume + charts + partition of unity);
L3 = Gårding's inequality → elliptic regularity → Rellich–Kondrachov compact embedding ⟹ **discrete spectrum
+ smooth eigenfunctions** (nothing exists in Mathlib; this is the input T4 CARRIES as a hypothesis). Only once
L1+L3 exist and are assembled with L2/L4/L5/L6 does the general `a₁=R/6` become a theorem. Until then it stays
VALIDATED on the specific cracks (`S²`, derived at coefficient level three ways), not generally discharged.

## Firewall (binding)

L1/L3 (manifold `L²`/Sobolev/elliptic-regularity/Rellich) are the genuine community-scale walls — no brick,
no book. L5 (trace-class) is self-contained and buildable. NOTHING here builds the manifold heat kernel or
discharges the general `a₁ = R/6` until L1+L3+L5 all exist and are assembled with L2/L4/L6. `a₁ = R/6` stays
VALIDATED on the specific cracks (`S²`), derived at the coefficient level, but not generally discharged. NOT
the conjecture, NOT the strong holographic principle, NOT QG.
