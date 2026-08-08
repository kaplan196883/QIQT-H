/-
  PerUCensusInstantiation — J4-428 (GROUP (3), the V1 PER-`u` CENSUS witness instantiation): the third
  of the four terminal `a₁ = R/6` data groups.  Certifies that the V1 per-`u` census — the exact input
  binder group of `PerUCensusTuple.hPd2conv_perU_fired` (J4-407) — is closed to ENUMERATED INPUT CARRIES
  ONLY, and discharges the one census field that admits a strictly-lower-level trade at this witness:
  `hfrozen_pd1` (the frozen first-partial germ) ⟵ `hQ1` (the frozen pointwise-on-nbhd formula), via the
  banked `Pd2ConvPerU.hfrozen_pd1_from_hQ1`.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING about
  `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring
  stack AND on the surviving labelled census carries threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable per-`u` census data into the
  exact shape `PerUCensusTuple.hPd2conv_perU_fired` consumes.  NONE proves `a₁ = R/6`.  Each carried
  hypothesis is genuine, satisfiable, non-vacuous, and never the conclusion.  No `sorry` (header prose
  excepted), no `:= True`, no new axioms, no existing file edited, nothing committed, nothing wired into
  `AxiomAudit`.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GROUP-(3) BINDER MAP  (the V1 per-`u` census = the input binders of `hPd2conv_perU_fired`).

  `hPd2conv_perU_fired` (J4-407) ALREADY fired the census: it discharged INTERNALLY, at the true
  ρ-scaled chart witness `W := vanVleckGatedWitness g gi hC hK S a b`, `F := leviSeries (heatOp g gi W)`,
  the algorithmically-dischargeable members —
    • `sSet := Set.univ`, `hsOpen`/`hsnhds` (`isOpen_univ` / `univ_mem`);
    • `gcoef u i := fun y ↦ (Dmap … F u y)(eᵢ)`  (the Dmap coefficient, `Dmap_apply_single`);
    • `fbulk u i m := FrozenGermInternal.fbulkInt … u i m`  (the banked truncated primitive);
    • `bb u i m := (C₀+C₁)·2√εₘ + C₂·εₘ`, `hb := HD1Concrete.hb_concrete`;
    • `hbulk_tendsto := HD1Concrete.hbulk_tendsto_concrete`  (on the `hGint` carry);
    • `hfull_pd1 := hfull_pd1_fired`  (T2, from `hfam_v2` via `pd_germ_eq_of_family`).
  What SURVIVES as the input binders of `hPd2conv_perU_fired` — i.e. the V1 census this brick certifies —
  is exactly the following, each a genuine enumerated carry (⟨name⟩ : ⟨type shape⟩ → verdict):

    field                       type shape                                                verdict
    ───────────────────────     ─────────────────────────────────────────────────────    ────────────────
    `U, hUpos`                  `U : Set ℝ`, `∀ u ∈ U, 0 < u`                              CARRY (heat-time
                                                                                          domain + positivity)
    `nb, hnb_open, hnb0`        field nbhd `ℝ → Set (Point n)` + open + `0 ∈ ·`            CARRY (the `hfam_v2`
                                                                                          field nbhd; small)
    `hProv`                     the SEVEN-leg linewise diff-under-∫ provider              CARRY (= J4-405
                                (`∀ u∈U, ∀ x∈nb u, ∀ i, ∃ snb bound, …`)                  `hlin_field_concrete`
                                                                                          input; banked D-feeder
                                                                                          legs)
    `fderivBulk, gderiv`        the order-2 derivative FIELDS (data)                      CARRY (data)
    `C₀, C₁, C₂`                the sliver-rate constants (data)                          CARRY (data)
    `hGint`                     `∀ u∈U, ∀ i x, IntervalIntegrable (s-profile) 0 u`        CARRY (integrability;
                                                                                          Gaussian dominators)
    `hbulkderiv`                `HasFDerivAt (fbulkInt … u i m) (fderivBulk u i m x) x`    CARRY (bulk order-2
                                                                                          differentiation)
    `hsliver`                   the `O(√ε)` `x`-uniform sliver dist-bound                 CARRY (√ε sliver
                                                                                          tranche)
    `hcont`                     `∀ u∈U, ∀ i, ContinuousOn (gderiv u i) univ`              CARRY (order-2 field
                                                                                          continuity)
    `hfrozen_pd1`               `∀ u∈U, ∀ i m, (pd frozen germ) =ᶠ[𝓝 0] fbulkInt …`       ★ DISCHARGED-THIS-
                                                                                          BRICK ⟵ `hQ1`

  So GROUP (3) closes to the SAME kind of enumerated carries as groups (1)/(2): provider/data/
  integrability/derivative/continuity carries, plus the ★ trade of `hfrozen_pd1` for the strictly-lower-
  level frozen pointwise formula `hQ1`.

  ── WHAT LANDS (this file, ns `QIQTH.PerUCensusInstantiation`).
    • `hfrozen_pd1_perU_of_hQ1` — ★ the `hfrozen_pd1` census field DISCHARGED from a per-`u` frozen
      pointwise-on-nbhd `hQ1` family (via the banked `Pd2ConvPerU.hfrozen_pd1_from_hQ1`, one call per
      `(u,i,m)`), with `fb := fbulkInt … u i m`.
    • `perUCensus_phase1` — ★★ the per-`u` census tuple FIRED (= `hPd2conv_perU_fired`'s conclusion) with
      `hfrozen_pd1` supplied internally from the `hQ1` family, and every other census field kept as an
      enumerated carry.  Conclusion = the exact per-`u` frozen→full second-partial `Tendsto` binder.

  ── DONT-UNDERCREDIT FINDINGS.
    • J4-405 (`PerUProviders.hlin_field_concrete`) already threads the 7-leg `hProv` provider through
      `hlin_as_D` to the census-shaped `hlin` field; `hProv` here IS its input carry — NOT re-proved.
    • J4-406 (`HD1Concrete`) already discharged `sSet`/`hb`/`hbulk_tendsto`/nbhd; `hPd2conv_perU_fired`
      consumes those internally.  The surviving `hbulkderiv`/`hsliver`/`hcont` + `hGint` are its declared
      carries — this brick does NOT re-open them.
    • J4-407 (`PerUCensusTuple`) already FIRED `hfam_v2` (T1), `hfull_pd1` (T2), and assembled the tuple
      (T3); `hfrozen_pd1` was kept LABELLED there precisely because `hPd2conv_perU` binds it — this brick
      discharges exactly that labelled field from the banked `hfrozen_pd1_from_hQ1` (J4-365).
    • `hGint` has NO banked interval-integrability supplier of its `s`-profile shape (grep-confirmed); it
      is a genuine carry, not re-proved here.

  Every hypothesis is satisfiable, non-vacuous (the width-2 Gaussian sliver model satisfies the whole
  census), strictly lower-level than the conclusion, and NONE equals `a₁ = R/6`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PerUCensusTuple

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.PerUCensusInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `hfrozen_pd1_perU_of_hQ1` — the `hfrozen_pd1` census field, from the `hQ1` family.
    ############################################################################### -/

/-- **★ `hfrozen_pd1_perU_of_hQ1`.**  THE `hfrozen_pd1` census field of `hPd2conv_perU_fired`,
    DISCHARGED from a per-`u` frozen pointwise-on-nbhd `hQ1` family.  For each `u ∈ U` and `(i, m)`,
    the `hQ1` carry hands an OPEN field nbhd `V ∋ 0` on which the frozen convolution's first coordinate
    partial equals the banked truncated primitive `fbulkInt … u i m` pointwise; since `V ∈ 𝓝 0` this IS
    the census's germ equality
      `(fun y ↦ ∂ᵢ(heatConvFrozen W F u (u−εₘ) · 0) y) =ᶠ[𝓝 0] fbulkInt … u i m`,
    read off by the banked `Pd2ConvPerU.hfrozen_pd1_from_hQ1` (J4-365) once per `(u,i,m)`.  This is a
    STRICTLY-LOWER-LEVEL trade: the germ-equality obligation `hfrozen_pd1` is replaced by the pointwise
    formula `hQ1` (a `HasDerivAt`/differentiation-under-∫ W2 datum), never the census conclusion.
    Honest carry: `hQ1`.  ⚠ NOT `a₁ = R/6`. -/
theorem hfrozen_pd1_perU_of_hQ1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m := by
  intro u hu i m
  obtain ⟨V, hV, hform⟩ := hQ1 u hu i m
  exact QIQTH.Pd2ConvPerU.hfrozen_pd1_from_hQ1
    (vanVleckGatedWitness g gi hC hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u m i
    (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m) V hV hform

/-! ###############################################################################
    ### ★★ `perUCensus_phase1` — the fired per-`u` census, `hfrozen_pd1` supplied internally.
    ############################################################################### -/

/-- **★★ `perUCensus_phase1`.**  THE V1 PER-`u` CENSUS TUPLE FIRED (= the conclusion of
    `PerUCensusTuple.hPd2conv_perU_fired`), with the `hfrozen_pd1` census field supplied INTERNALLY from
    the strictly-lower-level frozen pointwise formula `hQ1` (via `hfrozen_pd1_perU_of_hQ1`), and every
    other census field kept as an ENUMERATED CARRY: the heat-time domain `U`/`hUpos`, the field nbhd
    `nb`/`hnb_open`/`hnb0`, the seven-leg linewise provider `hProv` (= J4-405's input carry), the order-2
    derivative fields `fderivBulk`/`gderiv` and rate constants `C₀`/`C₁`/`C₂` (data), the interval-
    integrability `hGint`, the bulk order-2 differentiation `hbulkderiv`, the `O(√ε)` sliver bound
    `hsliver`, the order-2 field continuity `hcont`, and the frozen pointwise carry `hQ1`.  Conclusion =
    the exact per-`u` frozen→full second-partial `Tendsto` binder (viii).  Every carry is satisfiable,
    non-vacuous (the width-2 Gaussian sliver model), strictly lower-level than the conclusion, and none
    equals `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase1 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
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
  QIQTH.PerUCensusTuple.hPd2conv_perU_fired g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont
    (hfrozen_pd1_perU_of_hQ1 g gi hC hK S a b U hQ1)

end QIQTH.PerUCensusInstantiation

/-! ## GROUP (3) COVERAGE — the honest ledger.

  `perUCensus_phase1` reproduces the conclusion of `PerUCensusTuple.hPd2conv_perU_fired` (the exact
  per-`u` frozen→full second-partial `Tendsto` binder (viii)) from the V1 per-`u` census, with the census
  field `hfrozen_pd1` DISCHARGED-THIS-BRICK (traded for the strictly-lower-level frozen pointwise formula
  `hQ1` via `hfrozen_pd1_perU_of_hQ1` ∘ the banked `Pd2ConvPerU.hfrozen_pd1_from_hQ1`).  Combined with the
  members already fired internally by J4-405/406/407 (`sSet`/`hsOpen`/`hsnhds`, `gcoef`, `fbulk`, `bb`,
  `hb`, `hbulk_tendsto`, `hfull_pd1`), the V1 per-`u` census is now closed to the following ENUMERATED
  INPUT CARRIES ONLY — there is NO remaining census obligation this brick leaves un-enumerated:

    (G3-a)  `U`, `hUpos`               — heat-time domain + positivity        [domain data];
    (G3-b)  `nb`, `hnb_open`, `hnb0`   — the `hfam_v2` field nbhd of `0`       [nbhd data];
    (G3-c)  `hProv`                    — the SEVEN-leg linewise diff-under-∫ provider
                                        (= J4-405 `hlin_field_concrete` input)  [provider family];
    (G3-d)  `fderivBulk`, `gderiv`, `C₀`, `C₁`, `C₂`
                                       — the order-2 derivative fields + sliver-rate constants  [data];
    (G3-e)  `hGint`                    — interval-integrability of the `s`-profile
                                        (no banked supplier; Gaussian dominators)  [integrability family];
    (G3-f)  `hbulkderiv`              — bulk order-2 differentiation of `fbulkInt`  [derivative family];
    (G3-g)  `hsliver`                 — the `O(√ε)` `x`-uniform sliver dist-bound   [√ε sliver tranche];
    (G3-h)  `hcont`                   — order-2 field continuity `ContinuousOn (gderiv u i) univ`
                                                                                    [continuity family];
    (G3-i)  `hQ1`                     — the frozen pointwise-on-nbhd first-partial formula
                                        (replaces `hfrozen_pd1`)                    [W2 differentiation].

  ⚠  GROUP (3) = ENUMERATED INPUT CARRIES ONLY.  This brick does NOT prove `a₁ = R/6`, and makes NO
  claim of unconditionality.  It certifies the V1 per-`u` census as a fixed enumerated carry set and
  discharges its one tradeable field (`hfrozen_pd1` ⟵ `hQ1`); the remaining carries are the genuine
  provider/data/integrability/derivative/continuity content already banked by J4-405/406/407.
  `a₁ = R/6` remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.PerUCensusInstantiation
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hfrozen_pd1_perU_of_hQ1
#print axioms perUCensus_phase1
end AxiomChecks
