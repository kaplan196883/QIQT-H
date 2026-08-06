/-
  OuterCarryRecon — J4-317: the DEFINITIVE classified census of every antecedent of the wide `a₁`
  capstone `ProviderSideExports.wide_a1_R6_interface_discharged_v2`, plus the discharge of the
  derivable base-geometry / normalization (RNC-gauge) carries.  ONE brick of the `a₁ = R/6`
  heat-kernel campaign.  ⚠ NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file carries NO coefficient/geometry CONTENT of its own toward `R/6`.  It
  (a) writes the complete remaining-surface map of the wide capstone, and (b) proves — as small honest
  lemmas at an arbitrary metric with satisfiable hypotheses — that FOUR of the capstone's carried
  base-geometry/normalization inputs are DERIVABLE from OTHER inputs the same capstone already carries.
  No hypothesis is vacuous (`:= True`), unsatisfiable, or equal to any conclusion.  a₁ = R/6 remains
  CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ═══ T0 — THE CLASSIFIED CENSUS of `wide_a1_R6_interface_discharged_v2` ═══
  ══════════════════════════════════════════════════════════════════════════════════════════════════
  The capstone (ProviderSideExports.lean:165-212) has ~25 explicit binders + a 3-arrow returned
  implication.  Reading its COMPILED statement (never restated in Lean here), every antecedent is
  classified into (i)/(ii)/(iii)/(iv).  NO silent omission.

  ── (i) INNER INTERFACE ARROWS — the surviving analytic frontier, each now with a banked GATE slot.
     These are the THREE antecedents of the returned implication (`intro hDuhamel hDConv hCConv`):
       • hDuhamel  — the Duhamel/Levi truncated identity
                       `heatOp g gi (fun u p q => heatConv W (leviSeries …) u p q) t 0 0
                          = leviSeries … t 0 0 + heatConv (heatOp … W) (leviSeries …) t 0 0`.
                     BANKED SLOT: `HDuhamelExportRethread.hDuhamelSlot_AT_GATE` (J4-311), which takes a
                     `TruncatedDuhamelCore g gi (vanVleckGatedWitness …) t` and returns exactly this
                     identity.  Deeper: `truncatedDuhamelCore_AT_GATE_FULL` reduces the Core to the
                     honest UNION pile (F2 regularity, `hFII` tail-integrability, the `hDaLimLU` data
                     census, the single W1-free `hBoundaryLim` slot `EnvelopeWiringLocUnif.
                     hBoundaryLim_DONE`).  W1-poisoned route `hDConv_from_banked` is NEVER cited.
       • hDConv    — `DifferentiableAt ℝ (fun u => heatConv W (leviSeries …) u 0 0) t`.
                     BANKED SLOT: `HDConvGateThreading.hDConvSlot_AT_GATE` (J4-312), taking the
                     differentiation-under-∫ census (`hQ1`, `hFmeas`, `hFint`, `hF'meas`, dominating
                     `bnd`+`hbdd`+`hbound`+`hdiff`, `MemLapFull`, `MemAdjLo/…`) at the concrete gate.
       • hCConv    — `ContDiffAt ℝ 2 (fun p => heatConv W (leviSeries …) t p 0) 0`.
                     BANKED SLOT: `CConvFacadeGate.hCConvSlot_AT_GATE` (J4-313), reducing to the five
                     facade bundles (`CConvMetricData` — DISCHARGED from raw geometry hg/hgiC/hgpos —,
                     `CConvChartGateData`, `CConvSourceData`, `CConvDerivativeData`, `CConvEnvelopeData`)
                     plus the honest still-open L2 carry `hD1 : ContDiffAt ℝ 1 D 0`.
     STATUS in v2:  These three are STILL literal antecedents of the returned implication (the CITED
                    analytic frontier).  The slot theorems above discharge them AT THE CONCRETE GATE
                    but are not yet composed into v2 — that composition is the endgame's next arrows.

  ── (ii) S1 / MEASURABILITY carry.
       • hEmeas    — `∀ (S : Point n → Set (Point n)) (a b : ℝ),
                        tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)`.
                     CONTENT COMPLETE (J4-314→316): the genuine joint strong measurability of the gated
                     `heatOp` at the CONCRETE chosen gate is `ConstRadiusGateExport.
                     constRadius_package_and_S1` (a geometry-only fact modulo `c < δ₀`).
                     ⚠ ARTEFACT VERDICT: the LITERAL `∀ S` form is an over-strong INTERFACE ARTEFACT
                     — it quantifies over pathological (e.g. non-measurable) gates `S` for which the
                     indicator-gated witness is non-measurable, so the `∀ S` statement is NOT globally
                     satisfiable.  The capstone only ever CONSUMES it at the one provider-chosen gate;
                     the honest replacement is the concrete-gate S1 fact.  Retiring the `∀ S` shape in
                     favour of `constRadius_package_and_S1` is a pure interface rethread (no new math).

  ── (iii) ANALYTIC RESIDUE SLOTS — ALL ALREADY INTERNAL in v2 (none carried).  For the record, the
     wide capstone lineage discharged these arrows INTO v2's proof body (ProviderSideExports.lean
     :213-235); each is sourced from the SAME provider-chosen gate `S`:
       • hInter  — tsum/heatConv interchange @ t,0,0.  INTERNAL via `hEboundW_wide_from_geometry_open_inter`
                   (exported field) ⇐ `InterchangeLocalRebase.hInter_from_local_data`.
       • hInt    — `IterConvIntegrableWOn … κ 0 C' t`.  INTERNAL via
                   `iterConvIntegrableWOn_of_bound_baseMeas_trunc` (uses hbound + `hEzeroE_concrete` + hEmeas).
       • hEbound — the `(0,t]` width-`κ` Gaussian bound.  INTERNAL (`hEboundW_widen` of the all-`t`
                   package bound `gatedWitnessN1_package_open`).
       • hEzero  — nonpositive-time vanishing.  INTERNAL (`DataPileWitnessAudit.hEzeroE_concrete`, needs 1≤n).
       • hS0     — `0 ∈ S 0`.  INTERNAL (gate-export `hmemS0 hK0`).
       • hSopen  — `IsOpen (S 0)`.  INTERNAL (gate-export `hopenS0 hK0`).
       • hCH     — spatial-`C²` witness diagonal.  INTERNAL (`hCH_discharge_from_geometry`).
       (Providers banked across J4-206/260-265: DaLimLUConcreteDischarge, TruncatedHIntRethread /
        IterConvIntegrableWOn, WideHIntDischarge, ResidualAssemblyRecon, WideBoundaryLimDischarge.)
     CONCLUSION: in v2 the analytic residue has fully MIGRATED into the three (i) slot providers'
     hypothesis piles; there is no free-standing class-(iii) antecedent left on the capstone.

  ── (iv) BASE GEOMETRY + NORMALIZATION (RNC gauge) + BOOKKEEPING carries.  The capstone's explicit
     binders.  For each: [CARRIED] = genuine irreducible input; [DERIVED HERE] = proved below.
       • hn : 1 ≤ n                                              [CARRIED] dimension bookkeeping.
       • t : ℝ, ht : 0 < t ; κ : ℝ, hκ : 2 ≤ κ                   [CARRIED] window/width bookkeeping.
       • K, hK : IsCompact K, hK0 : 0 ∈ K                        [CARRIED] window data.
       • hChr : christoffel g gi ∈ C^∞                           [CARRIED] genuine smoothness (defines exp).
       • hg   : g_ab ∈ C^∞ ;  hgiC : gi_ab ∈ C^∞                 [CARRIED] genuine smoothness.
       • hgpos: 0 < det (g v)  ∀v                                [CARRIED] genuine positivity.
       • hgsymm: g symmetric                                     [CARRIED] genuine (metric symmetry).
       • hinvF: ∑σ g_aσ gi_σb = δ_ab                             [CARRIED] genuine (gi = g⁻¹).
       • hframeK: g = I on K                                     [CARRIED] RNC frame on the window.
       • hdg0 : ∂_e g_ab (0) = 0                                 [CARRIED] RNC first-derivative gauge.
       • htr  : ∑_a ∂_c∂_d g_aa (0) = -(2/3) Ric_cd              [CARRIED] ★ the Ricci-source COEFFICIENT
                                                                  input (physics; NOT normalization).
       • hsrc : transportOp(…0) ∈ C^∞                            [CARRIED] genuine smoothness.
       • hw   : foldedCoeff … ∈ C^∞                              [CARRIED] genuine smoothness.
       • hg0  : g 0 = I                                          [DERIVED HERE] `hg0_of_hframeK`  ⇐ hframeK, hK0.
       • hgi  : gi 0 = I                                         [DERIVED HERE] `hgi_of_hg0_hinvF` ⇐ hg0, hinvF
                                                                  (⇒ `hgi_of_geometry` ⇐ hframeK,hK0,hinvF).
       • hΓ   : christoffel g gi k i j (0) = 0                   [DERIVED HERE] `hGamma_of_hdg0` ⇐ hdg0.
       • hgnd : IsUnit (matToCLM (g y))  ∀y  (in the §1 provider) [DERIVED HERE] `hgnd_of_hgpos` ⇐ hgpos.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ═══ T1 — DISCHARGES LANDED HERE (all DERIVED; NO `sorry`, NO new axioms; each std-3) ═══
  ══════════════════════════════════════════════════════════════════════════════════════════════════
     • `hg0_of_hframeK`     : hframeK + hK0            ⟹ g 0 = I.                (frame condition at 0∈K.)
     • `hGamma_of_hdg0`     : hdg0                     ⟹ christoffel g gi k i j 0 = 0.
                              (Every bracketed ∂g in the Γ formula vanishes at 0.)
     • `hgi_of_hg0_hinvF`   : hg0 + hinvF             ⟹ gi 0 = I.               (single-index collapse.)
     • `hgi_of_geometry`    : hframeK + hK0 + hinvF    ⟹ gi 0 = I.               (chain of the two above.)
     • `hgnd_of_hgpos`      : hgpos                    ⟹ IsUnit (matToCLM (g y)).  (det>0 ⟹ unit.)
     These CLOSE the four normalization carries as functions of the surviving genuine inputs; the
     capstone's remaining (iv) binders are all genuine smoothness/positivity/symmetry/window data +
     the physics coefficient `htr`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ═══ T2 — THE HONEST REMAINDER (dependency order toward `a1_R6_of_geometry`) ═══
  ══════════════════════════════════════════════════════════════════════════════════════════════════
  After this brick, the surface between `wide_a1_R6_interface_discharged_v2` and a geometry-only
  `a1_R6_of_geometry` is, in order:

    R0 (interface, no math).  Retire the `∀ S` `hEmeas` artefact: replace it by the concrete-gate
        S1 fact `constRadius_package_and_S1`.  Pure rethread.

    R1 (composition, no new math).  Compose the three (i) GATE slots into v2, discharging the returned
        implication's arrows AT THE PROVIDER-CHOSEN GATE:
          hDuhamel ← `hDuhamelSlot_AT_GATE`   (needs a `TruncatedDuhamelCore` at that gate),
          hDConv   ← `hDConvSlot_AT_GATE`     (needs the diff-under-∫ census at that gate),
          hCConv   ← `hCConvSlot_AT_GATE`     (needs the 5 facade bundles + `hD1` at that gate).
        Gap nature: COMPOSITION (threading the provider's `S` through each slot's hypotheses).

    R2 (analytic walls, genuine).  Supply each slot's remaining data pile at the concrete gate:
        • hDuhamel: the `TruncatedDuhamelCore` ⇐ `truncatedDuhamelCore_AT_GATE_FULL` whose residual is
              the `hDaLimLU` loc-unif WALL (`DaLimLUConcreteDischarge` partial) + the F2/`hFII` piles +
              `hBoundaryLim_DONE`.  GAP NATURE: genuine loc-unif analytic wall (`hDaLimLU`).
        • hDConv:  the differentiation-under-∫ family (`hQ1/hFmeas/hFint/hF'meas/hbdd/hbound/hdiff/
              MemLapFull/MemAdjLo`).  GAP NATURE: near-diagonal ODE / dominated-derivative estimates.
        • hCConv:  the four remaining facade bundles + `hD1 : ContDiffAt ℝ 1 D 0` (the L2 carry).
              GAP NATURE: spatial-`C²` chart/source/derivative/envelope estimates + the L2 `D`-regularity.

    R3 (physics coefficient).  `htr : ∑_a ∂_c∂_d g_aa(0) = -(2/3) Ric_cd` — the ONLY non-normalization
        (iv) input; the Riemannian-normal-coordinate 2-jet of the metric.  Deriving it from `Point`-level
        RNC machinery (not carrying it) is the geometric wiring step; currently CARRIED as input.

    Everything else in (iv) is now either genuine irreducible smoothness/positivity/symmetry/window
    data or DISCHARGED here (hg0, hgi, hΓ, hgnd).  a₁ = R/6 stays CONDITIONAL on R2 (+R3).

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable hypotheses.
  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.PullbackNondegFromFDeriv

open QIQTH.Curvature QIQTH.PullbackMetric
open scoped BigOperators

namespace QIQTH.OuterCarryRecon

variable {n : ℕ}

/-! ###############################################################################
    ### T1 — the four derivable base-geometry / normalization carries.
    ############################################################################### -/

/-- **T1 (1) — `hg0_of_hframeK`.**  The origin normalization `g 0 = I` is DERIVED from the RNC frame
    condition `hframeK` (`g = I` on the window `K`) evaluated at `0 ∈ K`.  NOT `a₁ = R/6`. -/
theorem hg0_of_hframeK (g : Point n → Fin n → Fin n → ℝ) {K : Set (Point n)}
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (i j : Fin n) : g (0 : Point n) i j = if i = j then (1 : ℝ) else 0 :=
  hframeK 0 hK0 i j

/-- **T1 (2) — `hGamma_of_hdg0`.**  The RNC Christoffel-vanishing `Γ^k_{ij}(0) = 0` is DERIVED from the
    first-derivative gauge `hdg0` (`∂_e g_{ab}(0) = 0`): every partial derivative of the metric in the
    Christoffel formula is evaluated at `0`, hence vanishes, so the whole (`½ gi·(∂g+∂g−∂g)`) sum is `0`.
    NOT `a₁ = R/6`. -/
theorem hGamma_of_hdg0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (k i j : Fin n) : christoffel g gi k i j (0 : Point n) = 0 := by
  simp only [christoffel]
  have hz : (∑ α, gi (0 : Point n) k α *
      (pd (fun y => g y α j) i (0 : Point n) + pd (fun y => g y α i) j (0 : Point n)
        - pd (fun y => g y i j) α (0 : Point n))) = 0 := by
    apply Finset.sum_eq_zero
    intro α _
    rw [hdg0 α j i, hdg0 α i j, hdg0 i j α]
    ring
  rw [hz, mul_zero]

/-- **T1 (3) — `hgi_of_hg0_hinvF`.**  The inverse-metric origin normalization `gi 0 = I` is DERIVED
    from `hg0` (`g 0 = I`) and the inverse relation `hinvF` (`∑σ g_{aσ} gi_{σb} = δ_{ab}`): at `0` the
    sum collapses on the single index `σ = a`.  NOT `a₁ = R/6`. -/
theorem hgi_of_hg0_hinvF (g gi : Point n → Fin n → Fin n → ℝ)
    (hg0 : ∀ i j, g (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (a b : Fin n) : gi (0 : Point n) a b = if a = b then (1 : ℝ) else 0 := by
  have hsum : (∑ σ, g (0 : Point n) a σ * gi (0 : Point n) σ b) = gi (0 : Point n) a b := by
    rw [Finset.sum_eq_single a]
    · rw [hg0 a a, if_pos rfl, one_mul]
    · intro σ _ hσ
      rw [hg0 a σ, if_neg (fun e => hσ e.symm), zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  rw [← hsum, hinvF 0 a b]

/-- **T1 (4) — `hgi_of_geometry`.**  The chained form: `gi 0 = I` DERIVED directly from the RNC frame
    `hframeK` (+ `0 ∈ K`) and the inverse relation `hinvF`, via `hg0_of_hframeK` then `hgi_of_hg0_hinvF`.
    NOT `a₁ = R/6`. -/
theorem hgi_of_geometry (g gi : Point n → Fin n → Fin n → ℝ) {K : Set (Point n)}
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (a b : Fin n) : gi (0 : Point n) a b = if a = b then (1 : ℝ) else 0 :=
  hgi_of_hg0_hinvF g gi (hg0_of_hframeK g hK0 hframeK) hinvF a b

/-- **T1 (5) — `hgnd_of_hgpos`.**  The everywhere metric nondegeneracy `IsUnit (matToCLM (g y))`
    (the `hgnd` carry of the §1 wide provider) is DERIVED from positive-definiteness-in-the-weak-sense
    `hgpos` (`0 < det (g v)`): a positive determinant is a nonzero scalar, hence a unit, hence the
    matrix — and its `matToCLM` image — is a unit.  NOT `a₁ = R/6`. -/
theorem hgnd_of_hgpos (g : Point n → Fin n → Fin n → ℝ)
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) (y : Point n) :
    IsUnit (matToCLM (fun a b => g y a b)) := by
  rw [isUnit_matToCLM_iff (fun a b => g y a b), Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (hgpos y).ne'

end QIQTH.OuterCarryRecon

/-! ## Axiom checks — every new theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.OuterCarryRecon
#print axioms hg0_of_hframeK
#print axioms hGamma_of_hdg0
#print axioms hgi_of_hg0_hinvF
#print axioms hgi_of_geometry
#print axioms hgnd_of_hgpos
end AxiomChecks
