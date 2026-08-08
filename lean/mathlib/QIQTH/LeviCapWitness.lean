/-
  LeviCapWitness — J4-450: the `hLeviCap` atom of the `a₁ = R/6` census `hGint` floor.
  A MANDATORY SATISFIABILITY GATE, then the honest deliverable.

  J4-449 (`QIQTH.ProdPtwiseWitness`) split the last irreducible pointwise `hGint` atom `hProdPtwise`
  into `{hDHrefined, hLeviCap}`, where

    `hLeviCap` — per `(u,i,x)`, a TRUE `s,z`-uniform CONSTANT cap
        `∃ C_L ≥ 0, ∀ s ∈ (0,u), ∀ᵐ z, |leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0| ≤ C_L`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ★★★ THE MANDATORY SATISFIABILITY GATE (step 0 — axiom-budget-blind-spot discipline).

  We ask, BEFORE building: is a TRUE `s,z`-uniform CONSTANT cap on
  `leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0` over the FULL gate `(0,u]×ℝⁿ` satisfiable,
  and is it sourceable from banked facts?

  ── WHAT `leviSeries` IS (`TrueHeatKernel.leviSeries`).
       `leviSeries E s z 0 = ∑' k, (−1)^(k+1) · iterE E (k+1) s z 0`  (the signed Levi/Neumann series,
       leading term `−E s z 0`, the parametrix residual `E = (∂_t−Δ)·(gated van-Vleck parametrix)`).

  ── WHAT IS BANKED (the ONLY quantitative Levi control).
       • `HeatResidualBound.leviSeries_dominatedW_le` / `leviSeries_gatedWitnessN1_dominated`
         (GatedWitnessPackage) — a **GAUSSIAN**, NOT a constant:
             `|leviSeries E s z 0| ≤ C_L · baseKernelW 2 0 s z 0 = C_L · gaussDdim (2s) z`,
         whose PEAK (at `z = 0`) is `C_L·(8πs)^{−n/2}` — this **DIVERGES as `s → 0⁺`**.  Its `s,z`-uniform
         supremum over `(0,u]×ℝⁿ` is `+∞`.  (This is exactly the census carry `hFdomEvery`.)
       • `LeviMTest.leviSeries_boxContOn` / `leviSeries_stripContOn` — joint continuity ONLY on the
         POSITIVE-time-compact box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`τ₀ > 0`), whose Weierstrass
         majorant is `gaussDdim τ₀ (0) = (4πτ₀)^{−n/2}` — again **DIVERGES as `τ₀ → 0`**.  The strip
         `Ioc 0 T ×ˢ univ` is OPEN at `0` and non-compact ⟹ NO `IsCompact.exists_bound` there.
       • `hFzero` — `leviSeries s z 0 = 0` for `s ≤ 0`.  Combined with the `s → 0⁺` peak blow-up above,
         the `0`-slice is DISCONTINUOUS at `(s,z) = (0,0)` — the analytic signature of NO constant cap.

  ── THE FINER (UNBANKED) ESTIMATE hLeviCap SILENTLY NEEDS, AND WHY IT FAILS IN GENERAL.
       A constant cap requires controlling the on-diagonal Levi value `leviSeries s 0 0 ~ −E s 0 0` as
       `s → 0`.  For the van-Vleck / Minakshisundaram–Pleijel parametrix of order `N`, the on-diagonal
       residual is `(∂_t−Δ)H_N |_{diag} ~ (4πs)^{−n/2}·s^N·Δu_N = O(s^{N − n/2})` (`Δu_N` generically
       ≠ 0).  This `→ 0` — giving a constant cap — ONLY when `N ≥ n/2`.  The census uses the FIXED
       witness `globalCutoffParametrixWitnessN 1`, i.e. `N = 1`, so the on-diagonal Levi value is
         · `O(s^{1/2}) → 0`   for `n = 1`,          (cap OK)
         · `O(1)     → const` for `n = 2`,          (cap OK)
         · `O(s^{1−n/2}) → ∞` for `n ≥ 3`.          (cap FAILS)
       The higher Levi terms `E*E, E*E*E, …` are STRICTLY smoother (each convolution gains regularity),
       so they do NOT cancel the leading `−E` singularity: `leviSeries` inherits the `O(s^{1−n/2})`
       on-diagonal blow-up.  The census is stated at general `{n : ℕ}` (`prodPtwise_at_witness` is
       general-`n`), so `hLeviCap` AS STATED is **NOT** unconditionally satisfiable.

  ── ★★★ THE GATE VERDICT — `hLeviCap` (a TRUE `s,z`-uniform CONSTANT cap over `(0,u]×ℝⁿ`) is
     **UNSATISFIABLE AS STATED / NOT SOURCEABLE** (a J4-450 SOUNDNESS FINDING):
       (1) It is NOT derivable from any banked fact — every banked Levi bound (`hFdomEvery`,
           `leviSeries_dominatedW_le`) and every banked continuity (`leviSeries_boxContOn`) carries a
           majorant that DIVERGES as `s → 0` (peak `(cs)^{−n/2}`); the strip is non-compact at `0`.
       (2) The finer on-diagonal estimate that WOULD source it is itself only bounded near `0` when the
           parametrix order `N ≥ n/2`; with the FIXED `N = 1` witness the constant cap is provably
           dimension-dependent and FAILS for `n ≥ 3`.
     The J4-449 gate reasoning ("the Levi factor is `O(t^N)`-smooth, `→ 0` as `s → 0`, hence admits a
     constant cap") OMITTED the `(4πt)^{−n/2}` normalization; `O(t^N)` alone does not `→ 0` unless
     `N > n/2`.  So `hLeviCap` is NOT sound as stated ⟹ we DO NOT build a (false) constant cap and do
     NOT wire a `perUCensus_phase8` that would depend on it.

  ── THE CORRECTED SHAPE (Sol #21 handoff).  The honest, satisfiable, ALREADY-BANKED shape is the
     GAUSSIAN ENVELOPE
         `∃ C_L ≥ 0, ∀ s ∈ (0,u], ∀ z, |leviSeries s z 0| ≤ C_L · gaussDdim (2s) z`,
     which is exactly the standing census carry `hFdomEvery` (F2-style Levi domination).  So `hLeviCap`
     should NOT be a separate constant atom — it collapses back into `hFdomEvery`.

  ── RE-CHECK OF THE J4-449 LEVER.  With `Lev` capped only by a Gaussian (not a constant),
     `ProdPtwiseWitness.prodPtwise_of_refinedEnvelope_leviCap` (the CONSTANT-cap route) does NOT apply,
     and the product `dH · Lev` reintroduces the two-Gaussian product
     `gaussDdim (wA·(u−s)) z · gaussDdim (2s) z`, which J4-448 PROVED does NOT collapse to a single
     `gaussDdim (w·(u−s)) z` `s`-uniformly (harmonic-width peak `→ ∞` as `s → 0`).  A near-diagonal
     scaling check (`|z|² ~ s`, so `|z_i| ~ √s`) gives, for the demanded single-Gaussian RHS,
     `LHS/RHS ~ s^{1−n/2} → ∞` for `n ≥ 3`.  Hence `hProdPtwise` (the SINGLE-Gaussian POINTWISE
     product-moment domination) is itself unsatisfiable via the pointwise route for the true `Lev`; the
     `|z_i|`-moment `√τ` gain must be taken UNDER THE INTEGRAL (the J4-447 lever), NOT pointwise.  So
     the J4-449 pointwise split is what needs revisiting — `hProdPtwise` is not a genuine pointwise
     atom, and the `hGint` interval-integrability should be re-grounded on `hFdomEvery` + the
     integral-level moment gain rather than on `{hDHrefined, hLeviCap}`.  This is the Sol #21 task.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS (ns `QIQTH.LeviCapWitness`) — the HONEST cap that DOES exist.

  Since the FULL-gate constant cap is unsound, we land only the TRUE, campaign-floor fact it degrades
  to: the constant cap that genuinely exists on any POSITIVE-time-compact box (`s` bounded away from
  `0`, `z` in a ball) — via `IsCompact.exists_bound_of_continuousOn` against the banked box continuity.
  This makes the gate's boundary explicit: the box constant EXISTS for every `δ > 0` but DIVERGES as
  `δ → 0`, so it cannot be pushed to the full gate `(0,u]`.

    • `leviCap_on_compactBox` — ★ from joint `ContinuousOn` of the Levi `0`-slice on the compact box
      `Icc δ u ×ˢ closedBall 0 R`, a constant cap `|leviSeries E s z 0| ≤ C_L` on that box.

  ⚠  HONESTY FIREWALL.  This brick does NOT discharge `hLeviCap`; it RECORDS that `hLeviCap` is
  unsound as stated and lands only the true positive-time-compact cap.  NO `sorry` (header prose
  excepted), NO `:= True`, NO new axioms, NO existing file edited.  `a₁ = R/6` remains CONDITIONAL on
  the whole convergence-trio + geometric-wiring stack AND on the surviving enumerated carries; the
  `hGint` pointwise atom is HANDED OFF (Sol #21) to be re-grounded on `hFdomEvery` + the integral-level
  moment gain.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ProdPtwiseWitness

open MeasureTheory Filter Set Metric
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.LeviSeries

namespace QIQTH.LeviCapWitness

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `leviCap_on_compactBox` — the honest positive-time-compact Levi cap.
    ############################################################################### -/

/-- **★ `leviCap_on_compactBox` — THE CAP THAT GENUINELY EXISTS (positive-time-compact).**  Given the
    banked joint `ContinuousOn` of the Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on the COMPACT box
    `Icc δ u ×ˢ closedBall 0 R` (supplied by `LeviMTest.leviSeries_boxContOn` for the concrete residual
    `E`, `0 < δ`), there is a single constant `C_L ≥ 0` with
        `|leviSeries E s z 0| ≤ C_L`   for all `s ∈ [δ,u]`, `z ∈ closedBall 0 R`.
    Route: `Icc` and `closedBall` are compact (`Point n = Fin n → ℝ` is a proper space), so the box is
    compact, and `IsCompact.exists_bound_of_continuousOn` yields the bound; `max _ 0` makes it `≥ 0`.

    ⚠ GATE BOUNDARY.  This is the TIGHTEST cap the banked material supports: the constant `C_L` DEPENDS
    on `δ` and DIVERGES as `δ → 0` (the box majorant `gaussDdim δ 0 = (4πδ)^{−n/2} → ∞`).  It therefore
    does NOT extend to the FULL gate `(0,u]×ℝⁿ` — precisely why the census atom `hLeviCap` (a
    `δ`-free, `z`-unbounded constant cap) is UNSATISFIABLE as stated (see the GATE VERDICT header).
    NOT `a₁ = R/6`. -/
theorem leviCap_on_compactBox (E : ℝ → Point n → Point n → ℝ) (δ u R : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      (Set.Icc δ u ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s ∈ Set.Icc δ u, ∀ z ∈ Metric.closedBall (0 : Point n) R,
      |leviSeries E s z 0| ≤ C_L := by
  have hcompact : IsCompact (Set.Icc δ u ×ˢ Metric.closedBall (0 : Point n) R) :=
    (isCompact_Icc).prod (isCompact_closedBall (0 : Point n) R)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs z hz
  have hmem : ((s, z) : ℝ × Point n) ∈ Set.Icc δ u ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mk_mem_prod hs hz
  have hbound := hC (s, z) hmem
  rw [Real.norm_eq_abs] at hbound
  exact le_trans hbound (le_max_left _ _)

end QIQTH.LeviCapWitness

/-! ## THE LEDGER — where the `hGint` floor stands after the J4-450 GATE.

  ── ★★★ GATE VERDICT (binding).  The census atom `hLeviCap` (a TRUE `s,z`-uniform CONSTANT cap on
  `leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0` over the FULL gate `(0,u]×ℝⁿ`) is
  **UNSATISFIABLE AS STATED / NOT SOURCEABLE**:
    · every banked Levi bound (`hFdomEvery`, `leviSeries_dominatedW_le`) is a GAUSSIAN with peak
      `(cs)^{−n/2} → ∞` as `s → 0`; every banked continuity (`leviSeries_boxContOn`) has a
      `τ₀ → 0`-diverging majorant, and the strip `Ioc 0 T × univ` is non-compact at `0`;
    · the finer on-diagonal estimate that would source a constant, `leviSeries s 0 0 ~ O(s^{N−n/2})`,
      requires parametrix order `N ≥ n/2`; the fixed witness has `N = 1`, so the cap FAILS for `n ≥ 3`.
  We DID NOT build a constant `leviCap_at_witness`, and DID NOT wire a `perUCensus_phase8` depending on
  it.  We landed only the true positive-time-compact cap `leviCap_on_compactBox`.

  ── CORRECTED SHAPE (Sol #21).  Replace the constant cap by the ALREADY-BANKED Gaussian envelope
       `∃ C_L ≥ 0, ∀ s ∈ (0,u], ∀ z, |leviSeries s z 0| ≤ C_L · gaussDdim (2s) z`  (= `hFdomEvery`),
  and re-ground the `hGint` interval-integrability on `hFdomEvery` + the INTEGRAL-level `√τ` moment gain
  (the J4-447 lever), NOT on the pointwise split `{hDHrefined, hLeviCap}`.  The J4-449 pointwise split
  is what needs revisiting: with a Gaussian (not constant) `Lev`, the product `dH · Lev` is a genuine
  two-Gaussian product, which J4-448 proved does NOT collapse `s`-uniformly, so `hProdPtwise` is itself
  not a sound pointwise atom.

  ── DONT-UNDERCREDIT FINDINGS.
    • The banked `leviSeries_dominatedW_le` / `leviSeries_gatedWitnessN1_dominated`
      (GatedWitnessPackage) genuinely give ONLY a width-2 Gaussian bound (α = 0, NO compensating
      `t`-power), peak `(8πs)^{−n/2} → ∞`; they cannot source any constant cap.
    • `LeviMTest.leviSeries_boxContOn`/`stripContOn` genuinely establish joint continuity ONLY on
      positive-time-compact boxes with a `gaussDdim τ₀ 0 = (4πτ₀)^{−n/2}` Weierstrass majorant that
      diverges as `τ₀ → 0`; the strip is `Ioc 0 T × univ`, non-compact at `0`.  `leviCap_on_compactBox`
      is the honest, TRUE consequence (`IsCompact.exists_bound_of_continuousOn`), and its constant is
      exactly the one that CANNOT be pushed to `δ = 0`.
    • `hFzero` (`leviSeries s z 0 = 0` for `s ≤ 0`) + the `s → 0⁺` peak blow-up ⟹ the `0`-slice is
      genuinely DISCONTINUOUS at `(0,0)`; there is no continuous extension to `s = 0`, so the
      compactification route to a full-gate constant cap is closed.

  ⚠  J4-450 = a SOUNDNESS GATE on the `hLeviCap` atom (verdict: UNSATISFIABLE-as-stated; not a
  discharge).  This brick does NOT prove `a₁ = R/6`, makes NO claim of unconditionality, and hands the
  pointwise `hGint` atom off to Sol #21 (re-ground on `hFdomEvery` + integral-level moment gain).
-/
section AxiomChecks
open QIQTH.LeviCapWitness
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms leviCap_on_compactBox
end AxiomChecks
