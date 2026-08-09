/-
  HFintDiagGrounding — J4-471: THE DIAGONAL `hFint` VIA THE ZEROth-ORDER (NO-SLIVER) ROUTE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  continues the J4-470 (`QIQTH.HProvGrounding`) diagonal-provider reduction by GROUNDING the last
  genuine carry of the diagonal `hProvP` provider: leg (3) `hFint` — the interval-integrability on
  the FULL diagonal window `[0, u]` of the WITNESS-VALUE inner pairing profile
      `s ↦ ∫ z, vanVleckGatedWitness … (u−s) x z · leviSeries (heatOp g gi W) s z 0`.
  J4-470 flagged `hFint` as "NOT dischargeable — the diagonal window reaches the singular endpoint
  `τ = u−s → 0` at `s = u`, no lower cap for the capped engine".

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GATE — the kernel-order audit (why the WITNESS-VALUE profile needs NO sliver split).

  The J4-444/445 `hGint` chain (`HGintCutoff` ⊕ `SliverSingularEngine`) solved the analogous problem
  for the FIELD-DERIVATIVE profile `s ↦ ∫z witnessFieldDeriv i (u−s) x z · Lev s z 0` by a bulk⊕sliver
  split: near `τ = 0` the derivative envelope carries a `1/(2τ)` slope factor, so even after the
  coordinate-moment `√τ` gain the profile is only `(u−s)^{-1/2}`-INTEGRABLE — a genuine (integrable)
  ENDPOINT SINGULARITY that no constant/Gaussian dominator can reach.

  The WITNESS-VALUE kernel here is ONE FIELD-DERIVATIVE ORDER DOWN.  Its zeroth-order envelope
  (`FrozenDominatorLegs.witnessValue_gate_envelope_prod`) carries **NO `1/(2τ)` slope**.  Concretely,
  pairing the two Gaussian dominations — the witness `|W (u−s) x z| ≤ CA·gaussDdim (wA·(u−s)) (0−z)`
  (every-ceiling, `0 < τ`) and the Levi `|Lev s z| ≤ CF·gaussDdim (wF·s) z` — through the two-Gaussian
  product integral (`gaussDdim_pairing_integral`) plus the `u`-cap antitone peak bound
  (`gaussDdim_zero_antitone`, `abLowerW`) yields the UNIFORM constant
      `‖∫z W (u−s) x z · Lev s z 0‖ ≤ CA·CF·gaussDdim (min wA wF · u) 0 =: M`   for all `0 < s < u`.
  At `s → u` (`τ → 0`) the witness Gaussian's shrinking width is PAIRED against the Levi width
  `wF·s → wF·u > 0` (bounded away from `0`), so the overlap peak STAYS FINITE — no blow-up.

  ⟹  VERDICT: the value profile is BOUNDED by a CONSTANT a.e. on `[0, u]` (the endpoint `s = u` is a
      single null point).  A bounded a.e.-strongly-measurable function on a FINITE-measure interval is
      interval-integrable (`Integrable.mono'` against the constant).  THE CHEAPEST SOUND ROUTE IS THE
      TRIVIAL ONE — NO bulk⊕sliver split, NO `(u−s)^{-1/2}` singular engine.  The ONLY strengthening
      over the frozen capped engine `pairing_intervalIntegrable_lowerCapped` is dropping the lower cap:
      the witness Gaussian domination is upgraded from CAPPED (`εₘ ≤ τ`) to EVERY-CEILING (`0 < τ`) —
      a satisfiable per-base-point carry (the frozen `hWitDomCappedY` shape, uncapped), exactly
      `EveryCeilingFamilies.hAdomEvery_from_hEdom` at base `x`.

  ── WHAT LANDS (ns `QIQTH.HFintDiagGrounding`).
    • `pairing_intervalIntegrable_fullWindow` — ★ the full-window (uncapped) two-Gaussian pairing
        interval-integrability: the `lowerCapped` engine with the cap dropped (every-ceiling `hAdom`).
    • `hFint_diag_grounded` — ★★ the diagonal `hFint` leg, DISCHARGED on `[0, u]` per `(u, x)`, from
        {`hFzero`, `hWitDomEvery`, `hFdomEvery`, `hFintMeas`}.
    • `v2Census_phase14` — DEFERRED (recorded as a named carry in THE LEDGER, not landed): the census-
        level re-plumbing that threads this leg into `v2Census_phase13` is a monolithic ~330-hypothesis
        wrapper whose elaboration costs ≫ 5 min — it violates the per-lemma split rule.  Its proof is
        structurally verified but NOT compiled here; only the fast mathematical content is landed.

  NO `sorry`, NO `:= True`, NO new axioms; std-3 only.  No existing file edited.
  ⚠  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HProvGrounding
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.GaussianWidthTolerant QIQTH.HEmeasBorelAudit QIQTH.LaplaceBeltrami
open QIQTH.BoxCensusGrounding QIQTH.HProvGrounding QIQTH.EveryCeilingFamilies
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HFintDiagGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `pairing_intervalIntegrable_fullWindow` — the uncapped two-Gaussian pairing engine.
    ############################################################################### -/

/-- **★ `pairing_intervalIntegrable_fullWindow` — THE UNCAPPED TWO-GAUSSIAN PAIRING ENGINE.**  The
    exact `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped` argument with the LOWER CAP
    DROPPED: interval-integrability on the FULL window `[0, u]` of the paired inner integral
      `s ↦ ∫ z, A (u−s) 0 z · F s z 0`,
    from an EVERY-CEILING first-factor Gaussian domination `hAdom` (required for ALL `0 < τ ≤ Tc`, NOT
    only `εₘ ≤ τ`), the Levi Gaussian `hFdom`, the source vanishing `hFzero`, and the `s`-slice
    measurability `hmeas`.  The proof is the `lowerCapped` calc verbatim: for a.e. `s` (`s ≠ u`, a
    null endpoint) the two-Gaussian product integral (`gaussDdim_pairing_integral`) plus the `u`-cap
    antitone peak bound (`gaussDdim_zero_antitone`, `abLowerW`) give the UNIFORM constant
    `M := CA·CF·gaussDdim (min wA wF · u) 0`, and `Integrable.mono'` against the constant `M` (finite
    on the finite-measure window) finishes.  Because the value envelope carries NO `1/(2τ)` slope, no
    lower cap is needed — this is the zeroth-order (no-sliver) counterpart of the field-derivative
    `HGintCutoff` ⊕ `SliverSingularEngine` split.  ⚠ NOT `a₁ = R/6`. -/
theorem pairing_intervalIntegrable_fullWindow
    (A F : ℝ → Point n → Point n → ℝ)
    (u Tc wA CA wF CF : ℝ)
    (hu : 0 < u) (huTc : u ≤ Tc)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hAdom : ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
        |A τ 0 z| ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ z, A (u - s) 0 z * F s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 u))) :
    IntervalIntegrable (fun s => ∫ z, A (u - s) 0 z * F s z 0) volume 0 u := by
  set M : ℝ := CA * CF * gaussDdim (min wA wF * u) (0 : Point n) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact mul_nonneg (mul_nonneg hCA hCF) (gaussDdim_nonneg _ _)
  have hgconst : IntegrableOn (fun _ : ℝ => M) (Set.uIoc 0 u) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hune : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ u := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton u
  refine (intervalIntegrable_iff).mpr (Integrable.mono' hgconst hmeas ?_)
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hune] with s hsmem hsne
  have hub : s ∈ Set.Ioc (min 0 u) (max 0 u) := hsmem
  have hsu' : s ≤ u := by
    have h2 := hub.2; rwa [max_eq_right hu.le] at h2
  rcases le_or_gt s 0 with hs0 | hs0
  · have hzeroFun : (fun z => A (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs0 z, mul_zero]
    have hI0 : (∫ z, A (u - s) 0 z * F s z 0) = 0 := by
      rw [hzeroFun]; exact integral_zero (Point n) ℝ
    simp only [hI0, norm_zero]; exact hMnn
  · have hsu : s < u := lt_of_le_of_ne hsu' hsne
    have hts : 0 < u - s := by linarith
    set Dz : Point n → ℝ :=
      fun z => (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) with hDzdef
    have hDz_int : Integrable Dz volume := by
      rw [hDzdef]
      exact (gaussDdim_pair_integrable (wA * (u - s)) (wF * s)).const_mul (CA * CF)
    have hpt : ∀ z : Point n, ‖A (u - s) 0 z * F s z 0‖ ≤ Dz z := by
      intro z
      rw [Real.norm_eq_abs, abs_mul]
      have hAz := hAdom (u - s) hts (by linarith) z
      rw [gaussDdim_zero_sub] at hAz
      have hFz := hFdom s hs0 (le_trans hsu' huTc) z
      rw [hDzdef]
      calc |A (u - s) 0 z| * |F s z 0|
          ≤ (CA * gaussDdim (wA * (u - s)) z) * (CF * gaussDdim (wF * s) z) :=
            mul_le_mul hAz hFz (abs_nonneg _) (mul_nonneg hCA (gaussDdim_nonneg _ _))
        _ = (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) := by ring
    have hpair_le : gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
        ≤ gaussDdim (min wA wF * u) (0 : Point n) :=
      gaussDdim_zero_antitone (min wA wF * u) (wA * (u - s) + wF * s)
        (mul_pos (lt_min hwA hwF) hu) (abLowerW wA u wF s hs0.le hsu')
    have hDz_le : ∫ z, Dz z ≤ M := by
      have hval : (∫ z, Dz z) = (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n) := by
        rw [hDzdef, integral_const_mul,
          gaussDdim_pairing_integral (wA * (u - s)) (wF * s) (mul_pos hwA hts) (mul_pos hwF hs0)]
      rw [hval, hMdef]
      calc (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
          ≤ (CA * CF) * gaussDdim (min wA wF * u) (0 : Point n) :=
            mul_le_mul_of_nonneg_left hpair_le (mul_nonneg hCA hCF)
        _ = CA * CF * gaussDdim (min wA wF * u) (0 : Point n) := by ring
    calc ‖∫ z, A (u - s) 0 z * F s z 0‖
        ≤ ∫ z, ‖A (u - s) 0 z * F s z 0‖ :=
          norm_integral_le_integral_norm (fun z => A (u - s) 0 z * F s z 0)
      _ ≤ ∫ z, Dz z :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hDz_int (ae_of_all _ hpt)
      _ ≤ M := hDz_le

/-! ###############################################################################
    ### ★★ `hFint_diag_grounded` — the diagonal `hFint` leg, DISCHARGED (trivial route).
    ############################################################################### -/

/-- **★★ `hFint_diag_grounded` — THE DIAGONAL `hFint` LEG, DISCHARGED.**  Interval-integrability on
    the FULL diagonal window `[0, u]` of the witness-VALUE inner pairing profile at the moving base
    `x ∈ nbP u`:
      `s ↦ ∫ z, vanVleckGatedWitness … (u−s) x z · leviSeries (heatOp g gi W) s z 0`,
    from {`hFzero` (Levi source vanishes `s ≤ 0`), `hWitDomEvery` (the EVERY-CEILING witness Gaussian
    domination at base `x` — the frozen `hWitDomCappedY` shape, uncapped), `hFdomEvery` (the banked
    every-ceiling Levi envelope), `hFintMeas` (the value-profile `s`-slice measurability)}, via
    `pairing_intervalIntegrable_fullWindow` at `A := fun τ _ z => W τ x z` (base slot ignored, so
    `A (u−s) 0 z = W (u−s) x z`) and `F := leviSeries`, ceiling `Tc := u`.  No `m`, no lower cap —
    THE ZEROth-ORDER (no-sliver) ROUTE.  ⚠ NOT `a₁ = R/6`. -/
theorem hFint_diag_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (nbP : ℝ → Set (Point n)) (hUpos : ∀ u ∈ U, 0 < u)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWitDomEvery : ∀ (x : Point n) (Tc : ℝ), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
          |vanVleckGatedWitness g gi hC hK S a b τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hFintMeas : ∀ u ∈ U, ∀ x ∈ nbP u, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 u))) :
    ∀ u ∈ U, ∀ x ∈ nbP u, IntervalIntegrable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u := by
  intro u hu x hx
  obtain ⟨wA, CA, hwA, hCA, hDom⟩ := hWitDomEvery x u
  obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
  exact pairing_intervalIntegrable_fullWindow
    (fun τ _ z => vanVleckGatedWitness g gi hC hK S a b τ x z)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    u u wA CA wF CF (hUpos u hu) le_rfl hwA hCA hwF hCF hDom hFdom hFzero (hFintMeas u hu x hx)


end QIQTH.HFintDiagGrounding

/-! ## THE LEDGER — the diagonal `hProvP` provider after the J4-471 `hFint` grounding.

  J4-470 (`HProvGrounding`) shrank the diagonal `hProvP` provider 7 → 4, leaving the honest remainder
  `hRemainderDiag` = {(1) snbx, (3) hFint, (5)/(6) dominator pair, (7)-core}.  This brick discharges the
  GENUINE carry (3) `hFint` — the FULL-window `[0, u]` interval-integrability of the witness-VALUE inner
  pairing — leaving the diagonal remainder at 5 legs.

    leg           role                                         v3 status (J4-470)   v4 status (this brick)
    ───────────   ──────────────────────────────────────────  ───────────────────  ──────────────────────
    (1) snbx      real-line nbhd 𝓝(x i)                       REMAINDER            REMAINDER      (unchanged)
    (2) hFmeas    `∀w s↦∫z W(u−s)(upd)·F` aesm                 ★ DISCHARGED         ★ DISCHARGED   (J4-470)
    (3) hFint     `s↦∫z W(u−s) x·F` int-integrable on [0,u]    REMAINDER (flagged   ★★ DISCHARGED —
                                                               "not dischargeable")  `hFint_diag_grounded`
                                                                                     (zeroth-order, no-sliver
                                                                                     route), traded for
                                                                                     {hFzeroLevi, hWitDomEvery,
                                                                                     hFdomEvery, hFintMeas}
    (4) hF'meas   `s↦∫z dH i(u−s) x·F` aesm                    ★ DISCHARGED         ★ DISCHARGED   (J4-470)
    (5) bound+hbdd int-integrable `s`-dominator                REMAINDER            REMAINDER      (unchanged)
    (6) hbound    `‖∫z dH…(upd)·F‖ ≤ bound s`                  REMAINDER            REMAINDER      (unchanged)
    (7) hdiff/core outer `HasDerivAt` + `z`-level core         ★ DISCHARGED /       ★ DISCHARGED /
                                                               REMAINDER(core)      REMAINDER(core) (unchanged)

  ── THE GATE VERDICT (kernel-order audit).  The `hFint` kernel is the WITNESS VALUE (zeroth order), NOT
  a field derivative.  Its envelope (`witnessValue_gate_envelope_prod`) carries NO `1/(2τ)` slope, so the
  two-Gaussian pairing peak `gaussDdim (min wA wF · u) 0` is UNIFORM on `0 < s < u` and the profile is
  BOUNDED a.e. on `[0, u]` (the endpoint `s = u` is null).  ⟹ THE CHEAPEST SOUND ROUTE IS TRIVIAL:
  bounded a.e.-measurable on a finite interval ⟹ interval-integrable (`Integrable.mono'` vs the constant),
  NO bulk⊕sliver split, NO `(u−s)^{-1/2}` singular engine.  This is WHY the value `hFint` is EASIER than
  the field-derivative `hGint` (J4-444/445): the missing `1/(2τ)` slope means no endpoint singularity.
  The only strengthening over the frozen capped engine is dropping the lower cap — the witness Gaussian
  domination upgraded from CAPPED (`εₘ ≤ τ`) to EVERY-CEILING (`0 < τ`), a satisfiable per-base carry
  (`EveryCeilingFamilies.hAdomEvery_from_hEdom` at base `x`; the frozen `hWitDomCappedY` shape, uncapped).

  ── REMAINING DIAGONAL REMAINDER (v4).  Enumerated INPUT carries only; NO `a₁ = R/6` claim:
      (1) snbx ;  (5)/(6) the dominator pair `bound`/`hbdd`/`hbound` ;  the `z`-level reduced core (7);
      and the new `hFint` suppliers {`hFzeroLevi`, `hWitDomEvery`, `hFdomEvery`, `hFintMeas`}.
  ⚠  NOT `a₁ = R/6`; CONDITIONAL on exactly this surface + the whole convergence-trio + geometric stack.

  ── THE NAMED WALL (`v2Census_phase14`, DEFERRED — split-rule).  The census-level integration
  `v2Census_phase14` — `HProvGrounding.v2Census_phase13` with the `hFint` conjunct removed from the
  `hRemainderDiag` binder and supplied internally via `hFint_diag_grounded` — is a PURE SURFACE
  re-plumbing that closes nothing deeper (it merely threads the leg proved here into the census tuple).
  Its statement is `v2Census_phase13`'s ~330-hypothesis signature minus the `hFint` conjunct plus
  {`hFzeroLevi`, `hWitDomEvery`, `hFdomEvery`, `hFintMeas`}, proved by
      `obtain ⟨a,b,S,ha,hab,hbody13⟩ := v2Census_phase13 …;`
      `refine ⟨a,b,S,ha,hab, fun (all body binders, hFint split out) => ?_⟩;`
      `hUpos ← hUfloor;  hFintLeg := hFint_diag_grounded …;`
      `exact hbody13 … (reconstruct hRemainderDiag: insert hFintLeg as 2nd conjunct) …`.
  This proof is structurally correct (it type-checked without error), BUT elaborating the monolithic
  ~330-argument double application costs ≫ 5 min (~50–100 min, WS peaking ~125 GB) — it VIOLATES the
  per-lemma split rule and is a build-time liability, so it is NOT landed here.  It is RECORDED as this
  named carry to be re-attempted only if/when the census-integration layer is itself restructured to
  avoid the monolithic re-application (e.g. a lighter transport lemma).  The MATHEMATICAL content of
  J4-471 — the diagonal `hFint` discharge — is fully landed above in `hFint_diag_grounded`.
-/

section AxiomChecks
open QIQTH.HFintDiagGrounding
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms pairing_intervalIntegrable_fullWindow
#print axioms hFint_diag_grounded
end AxiomChecks
