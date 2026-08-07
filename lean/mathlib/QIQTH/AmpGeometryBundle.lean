/-
  QIQTH / HeatResidualBound — AmpGeometryBundle.lean   (J4-398, Sol #17 E1: the amplitude geometry bundle)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file is ONE geometry-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It is the first of the three
  `dataAmp` bricks on the critical path (Sol consult #17, E1): the GEOMETRY BUNDLE of the sliver's
  surviving carries.  The census hard field `hD2Hexpand` inside `AmplitudeDerivativeData` was reduced
  by J4-356 (`SliverAssemblyMatched`) + the J4-352..355 matched-pair bricks to the sliver carries
  {hcubic, hgate, hdisp, hjets, hcenter} + the `L_{A_chart}` Lipschitz data.  This brick lands the
  GEOMETRY members {hcenter, hjets, sliver-hgate}; the quantitative pair {L_A_chart, hcubic} is the
  sibling brick E2 (J4-399), NOT here.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE THREE CARRIES (exact shapes as they appear in the matched-pair assembly).

  • **hcenter** — the SHARED CENTER VALUE `qz 0 = qc 0` of `sliver_term1_full_matched`
    (`h0 : qz 0 = qc 0`), which makes the tail term `A₀·T_τ` cancel EXACTLY between bricks 1 and 2.
    At the concrete van-Vleck chart the z-Gaussian amplitude `qz` and the ρ-scaled chart amplitude
    `qc = rhoRatio·A` agree at the integration centre `z = 0` iff `ρ(τ,0) = 1`.  We LAND this: the
    exact chart Gaussian ratio `rhoRatio g gi hC hK τ 0 = 1` at the centre, hence `qz 0 = qc 0` for
    every amplitude.  Supplier: `chartField_centerValue_base0` (V₀ 0 = 0) + `rncRadialSq_zero`.

  • **sliver-hgate** — the COLLAR / CHART-DOMAIN INCLUSION facts (the census `hgate`: the collar
    support sits inside the bounded gate ball of radius `r₀`, so the off-collar comparison integral
    is over a bounded annulus).  We LAND the radius-shrinking + inequality wrappers: the collar
    regime forces `z ∈ Metric.ball 0 r₀` and the radial control `‖z‖ ≤ rncRadial z`; contrapositive,
    `r₀ ≤ ‖z‖ ⟹ ¬ collarRegime` (the beyond-gate support statement).  Suppliers: the `collarRegime`
    predicate's own `‖z‖ < r₀` conjunct + `norm_le_rncRadial`.

  • **hjets** — the 2-JET DATA (open gate + first/second `i`-jets of the chart + amplitude jets + the
    three centre identities `hVP`/`hPsq`/`hVQ`), the `hjets` field of `amplitudeDataOn_concrete`.
    We CARRY this HONESTLY: the shape is a genuine conjunction assembled from the banked general-base
    jet suppliers (`GeneralBaseJets.chartField_secondJet_general`, `chartField_firstJet_nhds_of_
    contDiffAt`) plus the residual pieces that are NOT yet banked at general base (the GLOBAL `∀ x`
    first-jet form — the field chart is known `C²` only near image points — and the three centre
    identities at general base).  `hjets_assemble` proves the conjunction is a genuine `⟨…⟩` of its
    satisfiable parts (non-vacuous plumbing witness); it does NO new coordinate work.  The residual
    is named in `hjets_residual_carries`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERABLES.
    • `rhoRatio_center`              — ★ hcenter core: `rhoRatio g gi hC hK τ 0 = 1`.
    • `chart_center_amp_match`       — ★ hcenter shape: `A 0 = rhoRatio … τ 0 · A 0` (`qz 0 = qc 0`).
    • `collarRegime_mem_ball`        — ★ sliver-hgate: collar ⟹ `z ∈ Metric.ball 0 r₀`.
    • `collarRegime_radial_control`  — sliver-hgate: collar ⟹ `‖z‖ ≤ rncRadial z ∧ ‖z‖ < r₀`.
    • `not_collarRegime_of_radius`   — ★ sliver-hgate (beyond-gate): `r₀ ≤ ‖z‖ ⟹ ¬ collarRegime`.
    • `HjetsShape` / `hjets_assemble`— hjets exact shape + the genuine conjunction assembler.
    • `hjets_residual_carries`       — the honest residual census for hjets.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable; no existing file edited;
  not wired into QIQTH.lean / AxiomAudit.lean.  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmplitudeDataOnCollar
import QIQTH.ChartJetBounds
import QIQTH.RNCDecay

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.RNCDecay
open scoped Interval Topology

namespace QIQTH.AmpGeometryBundle

open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    MEMBER 1 — hcenter:  the shared centre value `qz 0 = qc 0`  (ρ(τ,0) = 1).
    ############################################################################### -/

/-- **★ hcenter core — `rhoRatio_center`.**  At the integration centre `z = 0`, the exact chart-image
    Gaussian ratio is `1`:  `rhoRatio g gi hC hK τ 0 = 1`.  This is precisely the fact that makes the
    tail term `A₀·T_τ` cancel between the on-collar (`+A₀T_τ`) and off-collar (`−A₀T_τ`) matched-pair
    bricks (`sliver_term1_full_matched`'s `h0 : qz 0 = qc 0`).

    Route (WRAPPER, no new coordinate work): `rhoRatio τ 0 = exp((rncRadialSq 0 −
    rncRadialSq (W₀ 0))/(4τ))`; the centre normalisation `W₀ 0 = 0`
    (`chartField_centerValue_base0`, given `0 ∈ K`) plus `rncRadialSq 0 = 0` collapse the exponent to
    `0`, and `exp 0 = 1`.  ⚠ NOT `a₁ = R/6`. -/
theorem rhoRatio_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (τ : ℝ) :
    rhoRatio g gi hC hK τ 0 = 1 := by
  unfold rhoRatio
  rw [chartField_centerValue_base0 g gi hC hK h0K, rncRadialSq_zero]
  simp

/-- **★ hcenter shape — `chart_center_amp_match`.**  The matched-pair `qz 0 = qc 0` identity for the
    concrete amplitudes.  For any amplitude function `A`, the bare z-Gaussian centre amplitude `A 0`
    equals the ρ-scaled chart centre amplitude `rhoRatio g gi hC hK τ 0 · A 0` — the two agree at the
    integration centre because `ρ(τ,0) = 1` (`rhoRatio_center`).  This is the exact `h0` carry
    consumed by `sliver_term1_full_matched` (`qz 0 := A 0`, `qc 0 := rhoRatio·A 0`).
    ⚠ NOT `a₁ = R/6`. -/
theorem chart_center_amp_match (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (τ : ℝ) (A : Point n → ℝ) :
    A 0 = rhoRatio g gi hC hK τ 0 * A 0 := by
  rw [rhoRatio_center g gi hC hK h0K τ, one_mul]

/-! ###############################################################################
    MEMBER 3 — sliver-hgate:  the collar / chart-domain inclusion (gate support).
    ############################################################################### -/

/-- **★ sliver-hgate — `collarRegime_mem_ball`.**  THE GATE-BALL INCLUSION.  On the collar regime the
    base point `z` sits inside the OPEN gate ball `Metric.ball 0 r₀`.  This is the census `hgate`
    support statement in its cleanest form: the collar support ⊆ the bounded gate ball, so the
    off-collar comparison integral runs over the bounded gate annulus.  Route (WRAPPER): the
    `‖z‖ < r₀` conjunct of `collarRegime`.  ⚠ NOT `a₁ = R/6`. -/
theorem collarRegime_mem_ball {K : Set (Point n)} (r₀ c τ₀ τ : ℝ) (z : Point n)
    (hreg : collarRegime (K := K) r₀ c τ₀ τ z) : z ∈ Metric.ball (0 : Point n) r₀ := by
  obtain ⟨_, _, _, hzr, _⟩ := hreg
  simpa [Metric.mem_ball, dist_zero_right] using hzr

/-- **sliver-hgate — `collarRegime_radial_control`.**  The radial/chart-domain control bundle the
    downstream gate machinery consumes: on the collar regime, `‖z‖ ≤ rncRadial z` (the RNC
    radial-vs-ambient-norm bridge, `norm_le_rncRadial`) AND `‖z‖ < r₀` (the collar bound).  These are
    the two banked inequality facts that place the collar support inside the chart domain / gate ball.
    ⚠ NOT `a₁ = R/6`. -/
theorem collarRegime_radial_control {K : Set (Point n)} (r₀ c τ₀ τ : ℝ) (z : Point n)
    (hreg : collarRegime (K := K) r₀ c τ₀ τ z) :
    ‖z‖ ≤ rncRadial z ∧ ‖z‖ < r₀ := by
  obtain ⟨_, _, _, hzr, _⟩ := hreg
  exact ⟨norm_le_rncRadial z, hzr⟩

/-- **★ sliver-hgate (beyond-gate) — `not_collarRegime_of_radius`.**  THE OFF-GATE / BEYOND-RADIUS
    support statement: if `r₀ ≤ ‖z‖` (the base point lies at or beyond the gate radius) then `z` is
    NOT in the collar regime.  Equivalently, the collar support vanishes beyond the gate radius `r₀`,
    so the comparison integrand's off-collar contribution is confined to the bounded gate annulus.
    Route (WRAPPER): contrapositive of the `‖z‖ < r₀` conjunct.  ⚠ NOT `a₁ = R/6`. -/
theorem not_collarRegime_of_radius {K : Set (Point n)} (r₀ c τ₀ τ : ℝ) (z : Point n)
    (hz : r₀ ≤ ‖z‖) : ¬ collarRegime (K := K) r₀ c τ₀ τ z := by
  rintro ⟨_, _, _, hzr, _⟩
  exact absurd hzr (not_lt.mpr hz)

/-! ###############################################################################
    MEMBER 2 — hjets:  the 2-jet data  (CARRIED honestly: shape + assembler + residual).
    ############################################################################### -/

/-- **hjets shape — `HjetsShape`.**  The EXACT type of the `hjets` field of
    `amplitudeDataOn_concrete`, isolated at a single `(τ, z)` under the collar regime (the outer
    `∀ τ z, collarRegime → …` is the trivial universal closure).  A term of this type supplies the
    open gate (`IsOpen (S z)`, `0 ∈ S z`), an explicit first-jet function `P` (the `fderiv`-column of
    the inverse chart) with the GLOBAL first-jet `HasDerivAt`, a second-jet `Q` with its centre
    `HasDerivAt`, the two amplitude `PdiffAt` jets, and the three centre identities `hVP`/`hPsq`/`hVQ`
    — verbatim the shape fed into `hD2HexpandOn_concrete`.  ⚠ NOT `a₁ = R/6`. -/
def HjetsShape (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) : Prop :=
  IsOpen (S z) ∧ (0 : Point n) ∈ S z ∧
    ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
      (∀ x k, HasDerivAt
        (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i)) ∧
      (∀ k, HasDerivAt
        (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) ∧
      (∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x) ∧
      PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n) ∧
      (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i) ∧
      (∑ k, P 0 k ^ 2 = 1) ∧
      (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0)

/-- **hjets assembler — `hjets_assemble`.**  The genuine (non-vacuous) plumbing witness: `HjetsShape`
    is exactly the conjunction of its satisfiable parts, assembled by `⟨…⟩`.  This proves the shape is
    an honest AND of the banked / carried jet suppliers — NO new coordinate work is done here.

    ROUTE (per conjunct, per Sol #17 E1 — WRAPPER, not new computation):
      • `IsOpen (S z)`, `0 ∈ S z`  — the concrete flow-ball gate openness / centre membership
        (`GateOpennessExport`, `gatedWitness_diag_eval`'s gate hypotheses);
      • the SECOND field jet `Q` + its centre `HasDerivAt`, and the near-`0` first jet — BANKED at
        general base by `GeneralBaseJets.chartField_secondJet_general` /
        `chartField_firstJet_nhds_of_contDiffAt` (from the honest `ContDiffAt ℝ 2 (V_z) 0` carry
        `chartField_contDiffAt_center_general`);
      • the GLOBAL `∀ x` first-jet form — the recognised general-base RESIDUAL (the field chart is
        known `C²` only near image points; the global first-jet existence is CARRIED, see
        `hjets_residual_carries`);
      • the amplitude `PdiffAt` jets — `AmplitudeFamilyDischarge` chart-amplitude `C²` at `0`;
      • the centre identities `hVP`/`hPsq`/`hVQ` — the base-`0` versions are banked
        (`chartField_firstJet_center`, `chartField_centerJet_term_vanishes_base0`); at GENERAL base
        they are the recognised RESIDUAL.
    ⚠ NOT `a₁ = R/6`. -/
theorem hjets_assemble (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hVP : ∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0) :
    HjetsShape g gi hC hK S a b i τ z :=
  ⟨hSopen, h0, P, Q, hV1, hP1, hA1, hA2, hVP, hPsq, hVQ⟩

/-- **hjets residual census — `hjets_residual_carries`.**  The enumerated, satisfiable residual that
    `HjetsShape` still consumes at a GENERAL base `z` (the pieces NOT yet banked at general base).
    A genuine conjunction (non-vacuous), stated abstractly so the census is machine-checkable.

    THE RESIDUAL (each SATISFIABLE, none the conclusion):
      1. `hGlobalJet` — the GLOBAL `∀ x` first-jet form (banked only in a neighbourhood of `0` by
         `chartField_firstJet_nhds_of_contDiffAt`; the global form is the general-base residual);
      2. `hCentreVP`  — the centre identity `hVP` (`∑ (V_z 0)ₖ Pₖ = z i`) at general base;
      3. `hCentrePsq` — the centre normalisation `hPsq` (`∑ Pₖ² = 1`) at general base;
      4. `hCentreVQ`  — the centre-jet contraction `hVQ` (`∑ (V_z 0)ₖ Qₖ = 0`) at general base
         (base-`0` version banked as `chartField_centerJet_term_vanishes_base0`).
    ⚠ NOT `a₁ = R/6`; the hjets member is CONDITIONAL on exactly this residual. -/
def hjets_residual_carries (hGlobalJet hCentreVP hCentrePsq hCentreVQ : Prop) : Prop :=
  hGlobalJet ∧ hCentreVP ∧ hCentrePsq ∧ hCentreVQ

/-- The residual census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem hjets_residual_carries_intro
    {hGlobalJet hCentreVP hCentrePsq hCentreVQ : Prop}
    (h1 : hGlobalJet) (h2 : hCentreVP) (h3 : hCentrePsq) (h4 : hCentreVQ) :
    hjets_residual_carries hGlobalJet hCentreVP hCentrePsq hCentreVQ :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.AmpGeometryBundle

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AmpGeometryBundle.rhoRatio_center
#print axioms QIQTH.AmpGeometryBundle.chart_center_amp_match
#print axioms QIQTH.AmpGeometryBundle.collarRegime_mem_ball
#print axioms QIQTH.AmpGeometryBundle.collarRegime_radial_control
#print axioms QIQTH.AmpGeometryBundle.not_collarRegime_of_radius
#print axioms QIQTH.AmpGeometryBundle.hjets_assemble
#print axioms QIQTH.AmpGeometryBundle.hjets_residual_carries_intro
