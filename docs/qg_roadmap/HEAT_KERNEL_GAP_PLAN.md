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

**LACKS — but Phase 1 is IN FLIGHT upstream (status checked 2026-07-13):**
- the **Levi-Civita connection** — Rothgang/Massot: *uniqueness complete, existence near complete*
  (~3k lines merged, ~4k in review; PR **#36845** "the Levi-Civita connection on a manifold", uniting
  branch **#36036**, superseding the older #26221 "Mr. Covariant Derivatives");
- the **Riemann curvature tensor** `R(X,Y)Z` — **actively under development** (WIP `curvatureTensorAux`,
  `curvatureEndomorphismTensor` in #36036, last touched July 2026) — no longer absent, being written now;
- **Ricci** and **scalar curvature `R`** (abstract) — not yet begun upstream, but these are metric
  *contractions* of the Riemann tensor (mechanical once it lands). ⟹ the abstract Phase 1 endpoint is on
  a foreseeable-quarters horizon, not years.
- **Coordinate scalar `R`** — ✅ NOW SELF-BUILT (`CoordinateCurvature.lean`, `ae04203a`): the
  component-level `R(g)` as algebra over the metric 2-jet, sign-certified (flat/cone `R=0`, sphere
  `R=2`). We have a computable scalar `R` today, sidestepping the abstract machinery.

**LACKS — the DEEP wall, no upstream activity (Phases 3–4, the true heart):**
- the **connection/Bochner Laplacian** `∇²` on bundle sections and the Laplace-type class `P = −(∇²+E)`;
- the **heat semigroup** `e^{−tP}` with a smooth **integral kernel** `K_t(x,y)`;
- the **short-time asymptotic expansion** of `K_t(x,x)` and the **Seeley–DeWitt recursion** (transport
  equations in normal coordinates) — the analytic heart, on NO Mathlib roadmap;
- the **conical / distributional** heat kernel (for the replica/entanglement-entropy use).

⚠ Getting scalar `R` from Mathlib does NOT discharge `a₁ = R/6` — it only lets Phases 2–5 build on a
real curvature substrate; the coefficient still waits on the Phase-3/4 heat-kernel expansion.

## 3. The phased build (bottom-up; each phase an axiom-free, green Lean checkpoint)

Every phase ships independently and is **Mathlib-contributable in its own right** — the plan is written
so value lands upstream even if we never reach Phase 6.

- **Phase 1 — curvature. TWO flavors:**
  - **Abstract (coordinate-free), IN FLIGHT UPSTREAM (do not duplicate).** Levi-Civita connection
    (uniqueness done, existence near done: PR #36845), the Riemann tensor `R(X,Y)Z` (WIP in the uniting
    branch #36036), then Ricci and scalar `R` (mechanical contractions, not yet begun). WATCH
    #36036/#36845 and contribute the Ricci/scalar-`R` contractions when the tensor stabilizes — do NOT
    build a private coordinate-free library.
  - **Coordinate/component, SELF-BUILT ✅ (`CoordinateCurvature.lean`, `ae04203a`, [AF] std-3).** The
    scalar curvature `R(g)` as a pure ALGEBRAIC function of the metric's 0/1/2-jet (`ginv, dg, ddg`) via
    Christoffel→Riemann→Ricci→trace, with `∂(g⁻¹)=−g⁻¹dg g⁻¹` *defined into* the formula (no Lean
    differentiation, no `Matrix.inv` derivative). Sign conventions CERTIFIED by three checks: flat ⟹
    `R=0`, cone (polar-flat) ⟹ `R=0`, and the unit 2-sphere ⟹ `R=2` (the nonzero check). This gives us
    scalar `R` as a *computable geometric quantity* now — it feeds `SeeleyDeWittData.R`. ⚠ It is the
    COORDINATE expression (tying it to a metric needs `ginv=inverse(g)`, symmetry, `dg/ddg`=actual
    partials — carried), and it does NOT discharge `a₁=R/6` (that is Phases 3–4, below).
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

  **REFERENCE GROUNDING — Gilkey, *Invariance Theory…* (1st ed., `refs/InvarianceTheory1Ed.pdf`), read
  2026-07-13.** Our carried identity is EXACTLY **Theorem 4.8.16(b):** for a Laplace-type operator
  `P = P_∇ − E`, `a₂(x,P) = (4π)^{−m/2}·Tr(−R_ijij + 6E)/6` — i.e. `a₁ = R/6 + tr E` after stripping
  `(4π)^{−m/2}·Tr` (Gilkey's `−R_ijij` = scalar curvature `τ` in his sign convention). Gilkey's
  **invariance-theory method** is the formalizable route and shows *what is carriable vs derivable*:
  - **Lemma 4.8.5(a):** the weight-2 invariant polynomials `S_{m,2,k}` are spanned by *exactly two* —
    `R_ijij·I` and `E`. **Lemma 4.8.6:** `a₂ = Tr(S)` for `S` in that span. ⟹ `a₂ = c₁·τ + c₂·tr E` for
    universal constants. This ansatz is the CARRIED heat-expansion+Weyl-invariance fact (Weyl invariant
    theory for O(m) is itself not in Mathlib — carry it).
  - The **DETERMINATION** `c₁ = 1/6, c₂ = 1` is fixed by evaluating on model operators (flat-torus
    normalization `a₀ = (4π)^{−m/2}`, product/additivity Lemma 1.7.5) — this is ALGEBRA, formalizable.
  - ⟹ **The honest coefficient-determination brick** (Phase-5 downpayment, tractable NOW): carry the
    two-term ansatz + the model normalizations as labelled hypotheses, and DERIVE `c₁ = 1/6` (with our
    sphere `R=2` check as one model evaluation). This *reduces* the carried assumption from the specific
    number `a₁=R/6` up to the weaker Weyl-invariance ansatz — the 1/6 becomes derived, not stipulated.
    Still does NOT build the heat expansion itself (Phases 3–4, the analytic wall).
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
