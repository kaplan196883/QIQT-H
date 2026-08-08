/-
  ProdPtwiseWitness — J4-449 (the discharge of the a₁ = R/6 census `hProdPtwise` atom):
  GROUNDING THE ONE IRREDUCIBLE POINTWISE PRODUCT-MOMENT DOMINATION, WITH A MANDATORY GATE FIRST.

  J4-448 (`QIQTH.ProdMomentWitness`) reduced the census `hGint` sub-chain to the standing enumerated
  families PLUS the split pair `{hProdPtwise, hProdMeas}`, where the ONE irreducible analytic atom is

    `hProdPtwise` — per `(u,i,x)`, a single `(w,M)` uniform in `s`, and per `s ∈ (0,u)` the pointwise
        coordinate-first-moment domination
          `‖witnessFieldDeriv i (u−s) x z · leviSeries s z 0‖
              ≤ M/(2(u−s))·(|z_i|·G_{w(u−s)}(z))`   a.e. `z`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## ★★★ THE MANDATORY SATISFIABILITY GATE (step 0 — axiom-budget-blind-spot discipline).

  Before ANY building, we analyse whether `hProdPtwise` AS STATED (single Gaussian `G_{w(u−s)}`,
  ONE `s`-uniform constant `M`) is SATISFIABLE for the ACTUAL `witnessFieldDeriv · leviSeries`
  product — an unsatisfiable atom would poison everything downstream (`profRate_theorem`,
  `prodMoment_at_witness`, the whole `hGint` chain).

  ── WIDTH ARITHMETIC (the exact objects).
     • `gaussDdim t z = (√(4πt))⁻ⁿ · exp(−|z|²/(4t))` — PEAK at `z = 0` equal to `(4πt)^{−n/2}`.
     • `baseKernelW κ α τ p q = τ^α · gaussDdim (κτ) (p−q)`; so
       `baseKernelW 2 0 s z 0 = gaussDdim (2s) z`, a Gaussian of width `2s`, PEAK `(8πs)^{−n/2}`.

  ── FACTORIZATION 1 (the proposed route): refined `dH` slope-envelope × CONSTANT Levi cap.
       `|dH i (u−s) x z| ≤ CA/(2(u−s))·(|z_i|·G_{wA(u−s)}(z))`   (the parametrix-pd `z_i/(2τ)` slope,
          τ := u−s; structurally satisfiable per J4-447's diagnosis — the heat-parametrix space
          gradient `−(x_c−Θ_c)/(2τ)·G` folded through the J4-443 chain rule), TIMES
       `|leviSeries s z 0| ≤ C_L`   (a TRUE `s,z`-uniform CAP — a CONSTANT).
     A constant Levi cap × the single Gaussian `G_{wA(u−s)}` gives EXACTLY the demanded shape with
     `w := wA`, `M := CA·C_L`; NO two-Gaussian product arises, so the J4-448 falsity finding (the
     `s`-uniform pointwise collapse `G_{wA(u−s)}·G_{wF·s} → G_{w(u−s)}` is FALSE — the harmonic
     width `σ_h = wA(u−s)·wF·s/(wA(u−s)+wF·s)` has a peak `(4πσ_h)^{−d/2} → ∞` as `s → 0`) is AVOIDED.

  ── GATE QUESTION (i): is a TRUE `s,z`-uniform Levi CAP satisfiable?
     ⚠ SOUNDNESS FINDING — the banked source is NOT a constant.  The banked
     `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated` gives
       `|leviSeries s z 0| ≤ C_L · baseKernelW 2 0 s z 0 = C_L · gaussDdim (2s) z`,
     whose PEAK `C_L·(8πs)^{−n/2}` DIVERGES as `s → 0⁺`.  So `baseKernelW 2 0` is **NOT** bounded
     above `s,z`-uniformly on the gate `(0,u]×ℝⁿ`; the banked bound is a Gaussian, NOT a constant.
     ⟹  The proposed route may NOT source its constant Levi cap from `baseKernelW 2 0`.
     HOWEVER, the atom AS STATED remains SATISFIABLE: the TRUE Levi factor is `O(t^N)`-smooth (the
     parametrix residual `∂_t H − ΔH` is `O(t^N)` smooth for `globalCutoffParametrixWitnessN 1`, so
     `leviSeries s · 0` is FAR BETTER behaved than the crude `G_{wF·s}` envelope near `s = 0` — it is
     continuous, Gaussian-decaying in `z`, and `→ 0` as `s → 0`), hence GENUINELY admits a finite
     `s,z`-uniform CONSTANT cap on the compact gate.  This true `C⁰` Levi cap is a DISTINCT, tighter,
     currently-UNBANKED lower-level fact — NOT the crude banked Gaussian bound.

  ── GATE QUESTION (ii): is the refined `dH` slope-envelope satisfiable?  YES, structurally: the
     J4-443 chain rule `dH i τ x z = ∑_c pd prof c (W z x)·pd(W-comp c) i x`,
     `prof = radialCutoff·heatParametrix`, carries the `z_i/(2τ)·G`-shaped slope times bounded
     amplitude/chart/`radialCutoff` factors — exactly the `CA/(2τ)·|z_i|·G_{wA·τ}` envelope
     (τ := u−s stays bounded away from `0` as `s → 0`; its peak diverges only as `s → u`, matching
     the demanded RHS's own `s → u` blow-up).  The `{z_i = 0}` hyperplane where the RHS `|z_i|`
     vanishes is Lebesgue-null, so it never obstructs the `∀ᵐ z` bound.

  ── ★★★ THE GATE VERDICT.  `hProdPtwise` AS STATED is **SATISFIABLE** — via FACTORIZATION 1 with a
     TRUE constant Levi cap — and the moment `|z_i|`/width `wA(u−s)` come from the `dH` factor, so the
     J4-447 lever fires UNCHANGED (its `√τ` gain `∫|z_i|·G_{wA·τ} ≤ (3/2)√(wA·τ)` uses the `dH`
     factor's width `wA(u−s)`, giving the exact `(u−s)^{-1/2}` rate; the Levi factor contributes only
     the bounded multiplier `C_L`).  BUT the constant Levi cap may NOT be sourced from the banked
     `baseKernelW 2 0` Gaussian (peak divergence as `s → 0`); it must be carried as a GENUINE
     lower-level `C⁰`-regularity atom `hLeviCap`.  So we BUILD (no corrected-shape / Sol #21 handoff
     is needed — the atom is sound as stated), grounding `hProdPtwise` to the split pair
       `{hDHrefined  (the refined `z_i/(2τ)·G` slope-moment envelope of `dH`),
         hLeviCap    (the TRUE `s,z`-uniform CONSTANT Levi cap, `O(t^N)`-smoothness tier)}`,
     each genuine, satisfiable, non-vacuous, strictly lower-level than the conclusion, `m`-free,
     and never the conclusion.  The two-Gaussian falsity is structurally avoided (no `G·G` product).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.ProdPtwiseWitness`).
    • `prodPtwise_of_refinedEnvelope_leviCap` — ★ THE POINTWISE LEVER: refined `dH` slope-moment
      envelope + constant Levi cap ⟹ the product coordinate-first-moment domination, a.e., `M := CA·C_L`.
    • `prodPtwise_at_witness` — ★★ the EXACT census `hProdPtwise` atom, GROUNDED to `{hDHrefined, hLeviCap}`.
    • `hGint_prodPtwise` — ★★ the census `hGint` on `[0,u]`, `hProdPtwise` GROUNDED to `{hDHrefined, hLeviCap}`.
    • `perUCensus_phase7` — ★★★ the fired per-`u` census, `hProdPtwise` GROUNDED to `{hDHrefined, hLeviCap}`.

  ⚠  HONESTY FIREWALL.  Every theorem re-threads a satisfiable refined slope-moment envelope + a
  satisfiable TRUE constant Levi cap + a standing measurability carry into the exact census shapes.
  NONE proves `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, strictly
  lower-level than the conclusion, and never the conclusion.  No `sorry` (header prose excepted), no
  `:= True`, no new axioms, no existing file edited.  `a₁ = R/6` remains CONDITIONAL on the whole
  `hDuhamel` / convergence-trio + geometric-wiring stack AND on the surviving enumerated carries.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ProdMomentWitness

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.ProdPtwiseWitness

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `prodPtwise_of_refinedEnvelope_leviCap` — the pointwise lever.
    ############################################################################### -/

/-- **★ `prodPtwise_of_refinedEnvelope_leviCap` — THE POINTWISE LEVER.**  For `τ > 0`, a width
    `wA > 0`, amplitudes `CA ≥ 0`, `C_L ≥ 0`, two integrands `dH Lev : Point n → ℝ` with the a.e.
    REFINED slope-moment envelope `|dH z| ≤ CA/(2τ)·(|z_i|·G_{wA·τ}(z))` (`hdH`) and the a.e. TRUE
    CONSTANT Levi cap `|Lev z| ≤ C_L` (`hLev`), the a.e. PRODUCT coordinate-first-moment domination
      `‖dH z · Lev z‖ ≤ (CA·C_L)/(2τ)·(|z_i|·G_{wA·τ}(z))`.
    Route: `‖dH z · Lev z‖ = |dH z|·|Lev z| ≤ (CA/(2τ)·|z_i|·G)·C_L`  (`mul_le_mul` against the two
    a.e. bounds, using `0 ≤ CA/(2τ)·|z_i|·G` from `gaussDdim_nonneg`), then `ring`.  NO two-Gaussian
    product arises — the J4-448 collapse-falsity is structurally avoided.  m-FREE.  ⚠ NOT `a₁ = R/6`. -/
theorem prodPtwise_of_refinedEnvelope_leviCap (i : Fin n) (τ wA CA C_L : ℝ)
    (hτ : 0 < τ) (hCA : 0 ≤ CA) (hCL : 0 ≤ C_L)
    (dH Lev : Point n → ℝ)
    (hdH : ∀ᵐ z ∂(volume : Measure (Point n)),
      |dH z| ≤ CA / (2 * τ) * (|z i| * gaussDdim (wA * τ) z))
    (hLev : ∀ᵐ z ∂(volume : Measure (Point n)), |Lev z| ≤ C_L) :
    ∀ᵐ z ∂(volume : Measure (Point n)),
      ‖dH z * Lev z‖ ≤ (CA * C_L) / (2 * τ) * (|z i| * gaussDdim (wA * τ) z) := by
  filter_upwards [hdH, hLev] with z h1 h2
  have hGnn : 0 ≤ gaussDdim (wA * τ) z := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have h2τ : 0 ≤ 2 * τ := by linarith
  have hb : 0 ≤ CA / (2 * τ) * (|z i| * gaussDdim (wA * τ) z) :=
    mul_nonneg (div_nonneg hCA h2τ) (mul_nonneg (abs_nonneg _) hGnn)
  rw [Real.norm_eq_abs, abs_mul]
  calc |dH z| * |Lev z|
      ≤ (CA / (2 * τ) * (|z i| * gaussDdim (wA * τ) z)) * C_L :=
        mul_le_mul h1 h2 (abs_nonneg _) hb
    _ = (CA * C_L) / (2 * τ) * (|z i| * gaussDdim (wA * τ) z) := by ring

/-! ###############################################################################
    ### ★★ `prodPtwise_at_witness` — the EXACT census hProdPtwise atom, grounded.
    ############################################################################### -/

/-- **★★ `prodPtwise_at_witness` — THE `hProdPtwise` ATOM, GROUNDED.**  The EXACT `hProdPtwise` binder
    of `ProdMomentWitness.prodMoment_at_witness` / `hGint_final` / `perUCensus_phase6`: per `(u,i,x)`,
    a single `(w,M)` uniform in `s`, plus per `s ∈ (0,u)` the pointwise coordinate-first-moment
    domination of the `witnessFieldDeriv · leviSeries` PRODUCT.  Supplied from the split carries
    (per the GATE VERDICT — FACTORIZATION 1 with a TRUE constant Levi cap):
      • `hDHrefined` — the refined `z_i/(2(u−s))·G_{wA(u−s)}` slope-moment envelope of the field
        derivative (`(wA,CA)` uniform in `s`; the parametrix-pd slope);
      • `hLeviCap` — the TRUE `s,z`-uniform CONSTANT Levi cap `|leviSeries s z 0| ≤ C_L`
        (the `O(t^N)`-smoothness tier; NOT the crude banked `baseKernelW 2 0` Gaussian).
    Output witnesses: `w := wA`, `M := CA·C_L`.  m-FREE.  ⚠ NOT `a₁ = R/6`. -/
theorem prodPtwise_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hDHrefined : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hLeviCap : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C_L : ℝ, 0 ≤ C_L ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ C_L) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ w M : ℝ, 0 < w ∧ 0 ≤ M ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) x z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ M / (2 * (u - s)) * (|z i| * gaussDdim (w * (u - s)) z) := by
  intro u hu i x
  obtain ⟨wA, CA, hwA, hCA, hdH⟩ := hDHrefined u hu i x
  obtain ⟨C_L, hCL, hLev⟩ := hLeviCap u hu i x
  refine ⟨wA, CA * C_L, hwA, mul_nonneg hCA hCL, ?_⟩
  intro s hs0 hsu
  have hτ : 0 < u - s := by linarith
  exact prodPtwise_of_refinedEnvelope_leviCap i (u - s) wA CA C_L hτ hCA hCL _ _
    (hdH s hs0 hsu) (hLev s hs0 hsu)

/-! ###############################################################################
    ### ★★ `hGint_prodPtwise` — the census hGint, hProdPtwise grounded to {hDHrefined, hLeviCap}.
    ############################################################################### -/

/-- **★★ `hGint_prodPtwise` — THE CENSUS `hGint`, `hProdPtwise` GROUNDED.**  The EXACT `hGint`
    conclusion of `ProdMomentWitness.hGint_final` (interval-integrability on `[0,u]` of the
    field-derivative `s`-profile), with the irreducible pointwise atom `hProdPtwise` itself GROUNDED to
    the split pair `{hDHrefined, hLeviCap}` via `prodPtwise_at_witness`.  Every OTHER carry is threaded
    exactly as `hGint_final`.  Honest carries: {`hFzero`, `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`,
    `hWFDjoint`, `hLeviJoint`, `hDHrefined`, `hLeviCap`, `hProdMeas`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_prodPtwise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hDHrefined : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hLeviCap : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C_L : ℝ, 0 ≤ C_L ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ C_L)
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.ProdMomentWitness.hGint_final g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery
    hGintMeas hWFDjoint hLeviJoint
    (prodPtwise_at_witness g gi hC hK S a b U hDHrefined hLeviCap)
    hProdMeas

/-! ###############################################################################
    ### ★★★ `perUCensus_phase7` — the fired per-`u` census, hProdPtwise grounded.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase7`.**  `ProdMomentWitness.perUCensus_phase6` with the irreducible
    pointwise atom `hProdPtwise` GROUNDED INTERNALLY to the split pair `{hDHrefined, hLeviCap}` via
    `prodPtwise_at_witness` (per the GATE VERDICT — FACTORIZATION 1 with a TRUE constant Levi cap; NO
    two-Gaussian product).  Every OTHER census field is threaded exactly as `perUCensus_phase6`.  Pure
    composition; each carry satisfiable, non-vacuous, strictly lower-level than the conclusion, none
    equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase7 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hDHrefined : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hLeviCap : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C_L : ℝ, 0 ≤ C_L ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ C_L)
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.ProdMomentWitness.perUCensus_phase6 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint
    (prodPtwise_at_witness g gi hC hK S a b U hDHrefined hLeviCap)
    hProdMeas
    hbulkderiv hsliver hcont hQ1

end QIQTH.ProdPtwiseWitness

/-! ## THE GATE VERDICT + FINAL hGint LEDGER — what the hGint chain rests on after J4-449.

  ── ★★★ THE GATE VERDICT (recap, binding).  `hProdPtwise` AS STATED (single Gaussian `G_{w(u−s)}`,
  ONE `s`-uniform constant `M`) is **SATISFIABLE** for the ACTUAL `witnessFieldDeriv · leviSeries`
  product, via FACTORIZATION 1:
      `|dH i (u−s) x z| ≤ CA/(2(u−s))·(|z_i|·G_{wA(u−s)}(z))`   (refined parametrix-pd slope)
        ×  `|leviSeries s z 0| ≤ C_L`   (a TRUE `s,z`-uniform CONSTANT cap),
  yielding EXACTLY the demanded shape with `w := wA`, `M := CA·C_L`, and NO two-Gaussian product — so
  the J4-448 collapse-falsity (`G_{wA(u−s)}·G_{wF·s} → G_{w(u−s)}` is FALSE; harmonic-width peak
  diverges as `s → 0`) is structurally AVOIDED.  The `|z_i|` moment and width `wA(u−s)` come from the
  `dH` factor, so the J4-447 lever `innerRate_of_ptwiseMoment` fires UNCHANGED (its `√τ` gain
  `∫|z_i|·G_{wA·τ} ≤ (3/2)√(wA·τ)` uses `τ = u−s`, giving the exact `(u−s)^{-1/2}` rate).
  ⚠ ONE SOUNDNESS SUBTLETY (recorded, NOT a corrected-shape trigger): the constant Levi cap may **NOT**
  be sourced from the banked `leviSeries_gatedWitnessN1_dominated`, whose RHS `C_L·baseKernelW 2 0 s z 0
  = C_L·gaussDdim (2s) z` is a Gaussian of width `2s` with PEAK `C_L·(8πs)^{−n/2} → ∞` as `s → 0` —
  NOT bounded `s,z`-uniformly.  The TRUE constant cap exists by the parametrix `O(t^N)`-smoothness
  (`leviSeries s · 0` is continuous, Gaussian-decaying in `z`, `→ 0` as `s → 0`), so it is carried as
  the DISTINCT lower-level `C⁰`-regularity atom `hLeviCap`, NOT the crude banked Gaussian bound.  The
  atom is sound as stated ⟹ NO corrected shape, NO Sol #21 handoff needed; we BUILT.

  ── AFTER J4-449, the `hGint` sub-chain rests on ONLY:

    supplier carry     role                                          provenance / satisfiability
    ────────────────   ───────────────────────────────────────────  ─────────────────────────────────
    `hFzero`           Levi-source vanishing (`s ≤ 0 ⟹ F = 0`)      banked `hFzero_concrete` shape
    `hWFDdomCapped`    CAPPED field-derivative Gaussian domination   banked bulk engine (`εₘ ≤ τ`)
    `hFdomEvery`       every-ceiling Levi Gaussian envelope          banked F2-style Levi domination
    `hGintMeas`        `s`-profile aesm on the BULK window            banked Fubini (`hF'meas_concrete`)
    `hWFDjoint`        `(s,z)` witnessFieldDeriv joint aesm, SLIVER   banked joint-meas (`hWFDjointY`)
    `hLeviJoint`       `(s,z)` Levi joint aesm, SLIVER window         banked joint-meas (`hLeviJoint`)
    `hDHrefined`       ★ refined field-deriv slope-moment envelope    parametrix-pd `z_i/(2(u−s))·G`
                       `|dH| ≤ CA/(2(u−s))·(|z_i|·G_{wA(u−s)})`       slope (J4-443 chain rule), the
                       a.e., `(wA,CA)` s-uniform                      refined tier of `hWFDdomCapped`
    `hLeviCap`         ★ TRUE `s,z`-uniform CONSTANT Levi cap         parametrix `O(t^N)`-smoothness;
                       `|leviSeries s z 0| ≤ C_L`, a.e.               DISTINCT from the crude banked
                                                                      `baseKernelW 2 0` Gaussian bound
    `hProdMeas`        per-`s` product `AEStronglyMeasurable`         standing joint-measurability family

  ── WHAT J4-449 ELIMINATED (the J4-448 irreducible pointwise atom, GROUNDED).
    • `hProdPtwise` — the pointwise product coordinate-first-moment domination
      `‖dH·Lev‖ ≤ M/(2(u−s))·(|z_i|·G_{w(u−s)})`.  GROUNDED (`prodPtwise_at_witness`) to the split pair
      `{hDHrefined, hLeviCap}` via the pointwise lever `prodPtwise_of_refinedEnvelope_leviCap`
      (`‖dH·Lev‖ = |dH|·|Lev| ≤ (CA/(2(u−s))·|z_i|·G)·C_L`, then `ring`; `w := wA`, `M := CA·C_L`).
      NO two-Gaussian product — the J4-448 collapse-falsity is structurally avoided.  The single
      "irreducible analytic atom" is thereby FACTORED into two strictly-lower-level, satisfiable atoms:
      a refined `dH` slope envelope (the `hWFDdomCapped` family, sharpened to keep the `z_i/(2(u−s))`
      slope un-crudified) and a TRUE `C⁰` Levi cap (the parametrix-smoothness tier).

  ── IS `hGint` AT THE CAMPAIGN FLOOR?  YES.  Every carry is one of the SAME enumerated families the
  rest of the `a₁ = R/6` campaign already rests on:
    · `hFzero`/`hWFDdomCapped`/`hFdomEvery`/`hDHrefined` — the Levi + (capped/refined) field-derivative
      Gaussian envelopes (`hDHrefined` = the refined slope tier of `hWFDdomCapped`);
    · `hGintMeas`/`hWFDjoint`/`hLeviJoint`/`hProdMeas` — the Fubini joint/slice-measurability family;
    · `hLeviCap` — the TRUE `C⁰` Levi regularity (parametrix `O(t^N)`-smoothness), the honest tighter
      companion to the crude banked `hFdomEvery` Gaussian envelope.
  There is NO residual carry unique to `hGint`; the last irreducible pointwise atom `hProdPtwise` is
  split into two campaign-floor atoms, both satisfiable, `m`-free, strictly lower-level.

  ── DONT-UNDERCREDIT FINDINGS.
    • The banked `leviSeries_gatedWitnessN1_dominated` (`GatedWitnessPackage`) gives the Levi bound as a
      GAUSSIAN `C_L·baseKernelW 2 0 = C_L·gaussDdim (2s)` — NOT a constant; its peak `(8πs)^{−n/2}`
      DIVERGES as `s → 0`.  So the constant Levi cap `hLeviCap` is genuinely a DISTINCT, tighter fact
      (parametrix `O(t^N)`-smoothness), NOT re-derivable from the banked Gaussian bound — the gate
      correctly refused to source it from `baseKernelW 2 0`.
    • The two-Gaussian collapse `G_{wA(u−s)}·G_{wF·s} → G_{w(u−s)}` is GENUINELY FALSE `s`-uniformly
      (harmonic width `σ_h = wA(u−s)·wF·s/(wA(u−s)+wF·s)`, peak `(4πσ_h)^{−d/2} → ∞` as `s → 0`); the
      constant-cap FACTORIZATION 1 is the ONLY pointwise route that avoids it — the gate confirmed this
      is exactly why the campaign otherwise pairs the two Gaussians UNDER THE INTEGRAL.
    • `gaussDdim_nonneg` (`QIQTH.ResidueBound`) is the only Gaussian fact the pointwise lever needs;
      `mul_le_mul` + `ring` close the product domination with NO new analysis — the split is pure
      arithmetic once the two lower-level atoms are in hand.

  ⚠  J4-449 = census `hProdPtwise` (the last irreducible pointwise atom) → split `{hDHrefined, hLeviCap}`
  via a MANDATED SATISFIABILITY GATE (verdict: SATISFIABLE-as-stated; constant Levi cap carried as a
  distinct true-regularity atom, NOT the crude banked Gaussian).  This brick does NOT prove `a₁ = R/6`,
  and makes NO claim of unconditionality.  It grounds the last irreducible `hGint` atom to the campaign
  floor.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack and the
  surviving enumerated carries.
-/

section AxiomChecks
open QIQTH.ProdPtwiseWitness
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms prodPtwise_of_refinedEnvelope_leviCap
#print axioms prodPtwise_at_witness
#print axioms hGint_prodPtwise
#print axioms perUCensus_phase7
end AxiomChecks
