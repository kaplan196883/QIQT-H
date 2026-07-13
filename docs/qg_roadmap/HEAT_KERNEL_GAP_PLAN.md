# HEAT-KERNEL GAP PLAN — the Riemannian heat-kernel / Seeley–DeWitt frontier (to fill later)

**Date:** 2026-07-13. **Companions:** `FLAT_RECORD_GRAVITY_CONJECTURE.md` (the conjecture whose
input #3 this discharges), `DUALITY_ROADMAP.md` (the D6 row / D5 warp that share this gap).
**Status:** DEFERRED by decision — for now QIQT-H carries `a₁ = R/6` as an explicit labelled physical
input (option **(b)**, already implemented in `CorrespondenceAssembly.lean`'s `PhysicalInputs`); this
document is the eventual discharge. We return to it once everything else is closed.

---

## 0. What the wall is (one sentence)

The **short-time (Seeley–DeWitt) asymptotic expansion of the Riemannian heat kernel** —
`Tr e^{−tP} ~ (4πt)^{−d/2} ∫ (a₀ + a₁ t + a₂ t² + …)` for a Laplace-type operator
`P = −(∇² + E)`, with `a₁ = R/6 + tr E` — **exists in no proof assistant.** It is the single missing
analytic theory behind three QIQT-H frontier items at once. This is an ecosystem-wide (Mathlib's own
differential-geometry) gap, not a QIQT-H-specific one.

## 1. Why it is load-bearing (three uses, one theory)

| Downstream target | What it needs from this theory |
|---|---|
| **Conjecture input #3** (`a₁ = R/6`, `FLAT_RECORD_GRAVITY_CONJECTURE.md`) | the analytic identity `heatTraceCoeff₁ = ∫ (R/6 + tr E)` — the coefficient itself. |
| **D5 warp / curvature** of the radial axis (`DUALITY_ROADMAP.md`) | the same coefficient fixes the AdS warp factor; without it D5a's radial metric is a *chosen* no-warp L¹ product. |
| **D4 autonomous bulk EOM** | the Einstein-equation content that closes the bulk dynamics comes from varying the same curvature action. |

Discharging this theory turns the G3 conditional theorem's input #3 from a carried hypothesis into a
derived lemma, and unblocks the warp/curvature content of D4/D5.

## 2. Current Mathlib starting point (verified 2026-07-13)

**HAS (build on):**
- smooth-manifold infrastructure (`Mathlib/Geometry/Manifold/*`: `IsManifold`, `ContMDiff`, `MFDeriv`,
  `IntegralCurve`), tangent + vector bundles;
- **a covariant derivative / connection on vector bundles** —
  `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/*` (the connection substrate exists);
- Riemannian metrics + path-length distance — `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`,
  `PathELength.lean`; `VectorBundle/Riemannian.lean`;
- the flat-space Gaussian integral (`integral_gaussian`), continuous functional calculus, the matrix /
  bounded-operator exponential, Bochner integration, `NormedSpace.exp` derivative lemmas.

**LACKS (must build):**
- the **Riemann curvature tensor**, **Levi-Civita connection** (as the metric-compatible torsion-free
  connection), Ricci and **scalar curvature `R`** — no files exist (Mathlib's own acknowledged frontier);
- the **connection/Bochner Laplacian** `∇²` on bundle sections and the Laplace-type class `P = −(∇²+E)`;
- the **heat semigroup** `e^{−tP}` with a smooth **integral kernel** `K_t(x,y)`;
- the **short-time asymptotic expansion** of `K_t(x,x)` and the **Seeley–DeWitt recursion** (transport
  equations in normal coordinates);
- the **conical / distributional** heat kernel (for the replica/entanglement-entropy use).

## 3. The phased build (bottom-up; each phase an axiom-free, green Lean checkpoint)

Every phase ships independently and is **Mathlib-contributable in its own right** — the plan is written
so value lands upstream even if we never reach Phase 6.

- **Phase 1 — curvature.** Levi-Civita connection from a Riemannian metric (existence + uniqueness:
  metric-compatible, torsion-free) on top of Mathlib's `CovariantDerivative`; the Riemann tensor
  `R(X,Y)Z`; Ricci; **scalar curvature `R`**. *(This is the largest sub-project and overlaps Mathlib's
  own diff-geo roadmap — coordinate upstream; contribute here first.)*
- **Phase 2 — Laplace-type operators.** The connection (Bochner) Laplacian `∇²` on sections of a
  Riemannian vector bundle; the endomorphism term `E`; the Laplace-type class `P = −(∇² + E)`; its
  principal symbol and (formal) self-adjointness w.r.t. the metric volume.
- **Phase 3 — the heat semigroup + kernel.** Existence of `e^{−tP}` on `L²` sections (spectral, via the
  self-adjoint `P`), and its smooth **integral kernel** `K_t(x,y)` — the parametrix construction
  (Levi's method / the formal solution truncated + remainder estimate).
- **Phase 4 — the short-time expansion.** `K_t(x,x) ~ (4πt)^{−d/2} Σₖ aₖ(x) tᵏ` as `t → 0⁺`, with the
  **Seeley–DeWitt transport recursion** in Riemann normal coordinates producing the `aₖ` as universal
  local invariants. This is the analytic heart.
- **Phase 5 — the coefficients.** `a₀ = 1`; **`a₁ = R/6 + tr E`** (the target — discharges input #3);
  optionally `a₂` (Gilkey's formula) for higher corrections. The conformal specialization `ξ = 1/6`
  (`a₁ = (1/6−ξ)R`) already lives algebraically in `CorrespondenceAssembly.lean` (G3) and connects here.
- **Phase 6 — the conical / replica version.** The heat kernel on a cone `C_β` / `ℤ_n` orbifold and the
  **conical contribution** to the coefficients — the piece the entanglement-entropy replica argument
  actually uses (ties to D3c's exact conical coefficient `(1/12)(n−1/n)`).
- **Phase 7 — the discharge.** Replace G3's carried `a1_eq_R_div_six` `PhysicalInputs` field with the
  now-derived theorem; retire input #3 from cited to proved; feed the coefficient into the D5 warp and
  the D4 autonomous-EOM curvature content.

## 4. The pragmatic unblock (the interface pattern — BUILT 2026-07-13)

The repo's established move for a cited analytic frontier is the **structure/typeclass-interface +
instance** pattern (as with `EntropyBridge → DonaldSystem`). This is now **built**
(`QIQTH/SeeleyDeWittInterface.lean`, commit `9dc0ad19`, axiom-free): `SeeleyDeWittData` names the
heat-kernel facts `a₀ = 1`, `a₁ = R/6 + tr E` as structure fields (never a Lean `axiom`);
`a1_eq_scalarA1_of_minimal` bridges the minimal-scalar case to G3's `scalarA1 0 R` form;
`physicalInputs_of_seeleyDeWitt` sources G3's input #3 **from the interface**; and
`flatSpaceCorrespondence_of_seeleyDeWitt` restates the conditional correspondence with its `a₁` input
now an interface field. This **is option (b)** in its clean form: the assumption is named once,
reusably, instead of an ad-hoc `PhysicalInputs` field — so the eventual **Phase-7 discharge is a single
instance** (a `SeeleyDeWittData` built from the derived Phase-5 coefficient), not a refactor.

**The asymptotic-SHAPE layer is also built** (`QIQTH/HeatTraceAsymptotics.lean`, commit `3d03943a`,
axiom-free): `HeatTraceAsymptotics` extends `SeeleyDeWittData` with the trace function and the carried
short-time expansion `Tr e^{−tP} = (4πt)^{−d/2}(a₀ + a₁ t + o(t))` (the `asymptotic` field — the
deferred Phase-4 heat-kernel fact, never proved, never an axiom). What is PROVED is the coefficient
EXTRACTION: `normalizedTrace_tendsto_one` (the normalized trace → 1, the leading Seeley–DeWitt
normalization as a genuine limit) and `subleading_slope_eq_a1Laplace` (the subleading slope = R/6 + tr E
= the carried `a₁`). This shows the interface is **non-vacuous** — the coefficients are determined by
the trace — and pins down **exactly what Phase 4's eventual instance must supply**. The analytic content
(building the actual asymptotic) stays the Phase-4 wall.

## 5. Honest scale + the operative stance

- **Scale:** Phases 1–6 are a **multi-year, Mathlib-grade** undertaking; Phase 1 (curvature) and
  Phase 4 (the asymptotic expansion) are each research-level formalization projects. The honest path is
  to **contribute upstream to Mathlib's differential-geometry effort**, not to build a private
  curvature library.
- **Operative stance now — option (b):** `a₁ = R/6` is carried as an **explicit labelled physical
  input** (`CorrespondenceAssembly.lean`, the `PhysicalInputs.a1_eq_R_div_six` hypothesis — never a Lean
  `axiom`). The G3 conditional theorem is honest and complete *given* this input; the algebraic content
  (`scalarA1 ξ R = (1/6−ξ)R`, minimal `⟹ R/6`, 4D conformal `⟹ 0`) is already proved. We **close
  everything else first**, then return here to derive the coefficient and discharge the input.

## 6. Scope firewall (binding)

This is a PLAN; it builds nothing and claims nothing proved. The heat-kernel / Seeley–DeWitt theory is
absent from every proof assistant; until it is built, `a₁ = R/6` remains a carried physical input, and
no QIQT-H result silently assumes the derived coefficient — every use is a labelled hypothesis. NOT the
conjecture, NOT the strong holographic principle, NOT QG.
