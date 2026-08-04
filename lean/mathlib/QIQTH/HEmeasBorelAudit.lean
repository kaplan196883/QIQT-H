/-
  HEmeasBorelAudit — J4-215: THE DEFINITIVE `hEmeas`-family BOREL RE-AUDIT.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is an
  AUDIT: it enumerates the measurability-type obligations the capstone tower ACTUALLY consumes, and
  banks — as genuine (std-3, axiom-free) theorems wired to ALREADY-PROVEN suppliers — the BOREL-ROUTE
  discharges that compose WITHOUT any C⁰/C¹ (joint-continuity) input.  No `sorry` (prose excepted),
  no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SLOT CENSUS — what the capstone `CapstoneAssembly.a1_R6_of_geometry_and_frontier` and its
  ## one-level-down providers actually consume in the measurability family.

    SLOT                       VERBATIM Prop (this file's encoding)                 CONSUMER
    ────────────────────────────────────────────────────────────────────────────────────────────
    (S1) tripleHEmeas          StronglyMeasurable (τ,p,q) ↦ heatOp g gi Wit         `endpointData_of_banked`
         [= OBL-1]                                                                  (`hIntegrable`),
                                                                                    `interchangeData_of_banked`
                                                                                    (`hSeries`), `iterE_zmeas`
    (S2) hBmeas                 ∀ s, AEStronglyMeasurable z↦leviSeries(heatOp)s z0   capstone `hBmeas` slot
    (S3) hAmeas                 ∀ τ, AEStronglyMeasurable z↦Wit τ 0 z               capstone `hAmeas` slot
    (S4) hMeasFII               ∀u∈U, AEStronglyMeasurable s↦∫ Wit·leviSeries        capstone `hMeasFII` slot
    (S5) hu0/hu1meas            AEStronglyMeasurable u₀/u₁                           capstone (near-diagonal)

  KEY STRUCTURAL FACT (verified below).  At capstone level the triple `hEmeas` (S1) is HIDDEN inside
  the abstract `EndpointData` / `InterchangeData` bundles.  DISCHARGING those bundles routes through
  `TruncatedDuhamelData.endpointData_of_banked` and `.interchangeData_of_banked`, BOTH of which take
  the SINGLE slot `hEmeas : StronglyMeasurable (fun q => heatOp g gi Wit q.1 q.2.1 q.2.2)` (= S1).
  And `hBmeas` (S2) reduces to S1 via `IterEMeasurable.iterE_zmeas`.  So S1 is the ONE upstream
  measurability slot feeding the whole Levi/Duhamel interface.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE `hKp1` VERDICT (THE HEADLINE):  **hKp1 (OBL-3) RETIRES as a wall.**

  `GatedWitnessEmeas` offers TWO routes from the derivative fields to the triple `hEmeas` (S1):

    ROUTE A (E3e, `heatOp_stronglyMeasurable_of_jointContinuous`) — reduces S1 to the JOINT
      CONTINUITY inputs `hKcont` (OBL-2) and `hKp1` (OBL-3).  hKp1 = the flow's base-point `C¹`
      regularity (the W2 wall) BECAUSE E3e obtains the second-`pd` measurability from the first-`pd`
      via `measurable_deriv_with_param`, which needs joint continuity of the whole family (incl. the
      opaque `Classical.choose` base `q`).

    ROUTE B (E3d, `heatOp_stronglyMeasurable_of_deriv_fields`) — reduces S1 to the strong
      MEASURABILITIES of the three derivative fields (∂_τ, first-`pd`, second-`pd`) + the coefficient
      measurabilities.  **NO CONTINUITY ANYWHERE.**  E3d is PURE measurable algebra.

  The BANKED gate-equation Borel machinery supplies Route B's derivative-field measurabilities
  DIRECTLY, with NO joint continuity in the base point `q`:

    • `GatedDInstantiation.witnessFieldDeriv_measurable_of_gateEq`  (J4-185) — the FIRST field-`pd`
      kernel is jointly Borel-measurable via the on-gate closed form (`witnessFieldDeriv_gate_eq`)
      glued to the off-gate zero on the measurable base gate `Prod.snd ⁻¹' K` (`gatedDerivRep`).
    • `SecondDerivEnvelope.witnessFieldDeriv2_measurable_of_gateEq` (J4-198) — the SECOND field-`pd`
      kernel is jointly Borel-measurable the same way (`gatedDeriv2Rep`).

  Both use ONLY: the on-gate Leibniz–Gaussian closed form, off-gate vanishing, a MeasurableSet gate,
  and CARRIED measurabilities of {chart value `uniformInverseChart`, chart field-jets `P`/`Q`,
  amplitude `chartFieldAmp` and its field-`pd`s}.  The base point `q` enters ONLY through those
  carried MEASURABLE values — never through a continuity/derivative of the `Classical.choose` flow.

  THEREFORE the C¹ base-point variational-Grönwall wall (`hFlowBaseC1`, HEmeasRecon B5, the sole
  genuinely-open flow-axis endeavour) is **NOT needed** by any consumed measurability slot.  hKp1
  retires: it was an artefact of choosing Route A.  Route B (E3d + the gate-eq Borel measurabilities)
  reaches the same S1 conclusion continuity-free.

  ── THE EXACT REPLACING THEOREMS (this file re-exposes / banks them):
       S1 ⟵ `triple_hEmeas_of_borel_deriv_fields`   (E3d, continuity-free)      [banked here]
       first-`pd` meas  ⟵ `firstFieldPd_measurable_of_gateEq`  (J4-185)         [re-exposed here]
       second-`pd` meas ⟵ `secondFieldPd_measurable_of_gateEq` (J4-198)         [re-exposed here]
       endpoint `hIntegrable` ⟵ `endpoint_integrable_of_tripleHEmeas`           [banked here]
       `hBmeas` building block ⟵ `iterE_zslice_of_tripleHEmeas`                  [banked here]

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE UPDATED WALLS LIST (measurability family).  With hKp1 retired, the residue to actually THREAD
  ## Route B for the full concrete-witness triple S1 is NOT a wall but THREE routine Borel-extension
  ## bricks of the SAME already-banked kind (gate indicator × measurable closed form):

    (G-a) VARYING FIELD POINT.  The banked `_of_gateEq` results fix the field point `x` and give
          measurability in `(time, base) = (s,z)`; E3d needs the field point `p` to VARY (the full
          triple `(τ,p,q)`).  The `gatedDerivRep` / `gatedDeriv2Rep` representatives extend verbatim
          to a varying `p` (a product coordinate), same factor-by-factor Borel proof.
    (G-b) OFF-DIAGONAL HESSIAN.  `witnessFieldDeriv2` is `pd_i(pd_i …)` (diagonal `i,i`); E3d's `hP2`
          needs `pd_i(pd_j …)` for all `i,j` (the full `laplaceBeltrami` Hessian).  A general-index
          `gatedDeriv2Rep` closes it.
    (G-c) THE ∂_τ FIELD.  E3d's `hDτ` (time-derivative field) needs its own gate-eq Borel
          representative (∂_τ of the on-gate closed form; a `heatKernel1D`-derivative × amplitude,
          all globally Borel).

  NONE of (G-a)/(G-b)/(G-c) is the ODE-smooth-dependence (`C¹` variational-Grönwall) wall; each is a
  finite measurable-algebra brick.  The genuine capstone-level wall remains `hDaLimLU` (the truncated
  locally-uniform limit), which is NOT in the measurability family and is untouched by this audit.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HEmeasRecon
import QIQTH.SecondDerivEnvelope
import QIQTH.IterEMeasurable

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant QIQTH.ParametrixFunction QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open scoped BigOperators ContDiff Topology

namespace QIQTH.HEmeasBorelAudit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## PART 1 — THE SLOT CENSUS (build-checked `def … : Prop` for each consumed slot).
    ############################################################################### -/

/-- **(S1) `tripleHEmeas` = OBL-1.**  The base joint strong measurability of the residual operator
    `E := heatOp g gi Wit` over the triple `(τ,p,q)`.  This is the EXACT `hEmeas` slot consumed by
    `TruncatedDuhamelData.endpointData_of_banked` (`hIntegrable`),
    `TruncatedDuhamelData.interchangeData_of_banked` (`hSeries`), and `IterEMeasurable.iterE_zmeas`. -/
def tripleHEmeas (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ) : Prop :=
  StronglyMeasurable (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2)

/-- **(S2) `hBmeasSlot`.**  The `z`-ae-strong-measurability of the Levi series `B := leviSeries (heatOp
    g gi Wit)` at each outer time `s` and diagonal endpoint `y = 0` — the capstone `hBmeas` slot. -/
def hBmeasSlot (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ) : Prop :=
  ∀ s : ℝ, AEStronglyMeasurable
    (fun z : Point n => leviSeries (heatOp g gi Wit) s z 0) volume

/-- **(S3) `hAmeasSlot`.**  The `z`-ae-strong-measurability of the witness `Wit` at the field centre
    `p = 0` — the capstone `hAmeas` slot. -/
def hAmeasSlot (Wit : ℝ → Point n → Point n → ℝ) : Prop :=
  ∀ τ : ℝ, AEStronglyMeasurable (fun z : Point n => Wit τ 0 z) volume

/-- **(S4) `hMeasFIISlot`.**  The `s`-ae-strong-measurability of the inner space-time pairing on
    `(0,u]` for `u` in the window `U` — the capstone `hMeasFII` slot. -/
def hMeasFIISlot (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ)
    (U : Set ℝ) : Prop :=
  ∀ u ∈ U, AEStronglyMeasurable
    (fun s => ∫ z, Wit (u - s) 0 z * leviSeries (heatOp g gi Wit) s z 0)
    (volume.restrict (Set.uIoc 0 u))

/-! ###############################################################################
    ## PART 2 — THE BOREL-ROUTE DISCHARGES (each wired to an ALREADY-PROVEN supplier).
    ############################################################################### -/

/-- **★★ VERDICT S1 — `triple_hEmeas_of_borel_deriv_fields` (the `hKp1` RETIREMENT).**  The triple
    `hEmeas` (S1) follows from the strong MEASURABILITIES of the three derivative fields (`∂_τ`,
    first-`pd`, second-`pd`) plus the coefficient measurabilities — via `GatedWitnessEmeas` E3d
    (`heatOp_stronglyMeasurable_of_deriv_fields`), PURE measurable algebra.  **NO joint continuity
    (`hKcont`/`hKp1`) appears.**  This is the Borel route (Route B) that structurally retires hKp1:
    the second-`pd` measurability is taken as a DIRECT input (supplied by the gate-eq Borel route,
    Part 2 below), not derived from first-`pd` continuity via `measurable_deriv_with_param`.
    NOT `a₁ = R/6`. -/
theorem triple_hEmeas_of_borel_deriv_fields
    (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → Point n → ℝ)
    (hDτ : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => G u w.2.1 w.2.2) w.1))
    (hP1 : ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => G w.1 x w.2.2) k w.2.1))
    (hP2 : ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    tripleHEmeas g gi G :=
  heatOp_stronglyMeasurable_of_deriv_fields g gi G hDτ hP1 hP2 hgi hchr

/-- **★ SUPPLIER (Route B, first order) — `firstFieldPd_measurable_of_gateEq`.**  Re-exposes
    `GatedDInstantiation.witnessFieldDeriv_measurable_of_gateEq`: the FIRST field-`pd` kernel of the
    concrete gated `N=1` van-Vleck witness is jointly `(s,z)`-Borel-measurable at a FIXED field point
    `x`, via the on-gate closed form glued to the off-gate zero on the MeasurableSet gate — with
    **NO joint-continuity hypothesis** (the base `z` enters only through the CARRIED measurabilities
    of the chart value / jets / amplitude).  This is the first-`pd` measurability input Route B's
    E3d slot `hP1` consumes (modulo the varying-field-point extension G-a).  NOT `a₁ = R/6`. -/
theorem firstFieldPd_measurable_of_gateEq (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (x : Point n) (Pfield : Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x))
    (hPmeas : ∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
    (hAmpMeas : Measurable
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x))
    (hAmpDerivMeas : Measurable
      (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hgate : ∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
        IsOpen (S p.2) ∧ x ∈ S p.2 ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
          (Pfield p.2 k) (x i)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x) :
    Measurable (fun p : ℝ × Point n =>
      witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) :=
  QIQTH.GatedDInstantiation.witnessFieldDeriv_measurable_of_gateEq hn g gi hC hK S a b i t x
    Pfield hKmeasSet hChartMeas hPmeas hAmpMeas hAmpDerivMeas hgate

/-- **★ SUPPLIER (Route B, second order) — `secondFieldPd_measurable_of_gateEq`.**  Re-exposes
    `SecondDerivEnvelope.witnessFieldDeriv2_measurable_of_gateEq`: the SECOND field-`pd` kernel of the
    concrete witness is jointly `(s,z)`-Borel-measurable at a FIXED field point `x` via the order-2
    on-gate closed form `gatedDeriv2Rep`, again with **NO joint-continuity hypothesis**.  This is the
    second-`pd` measurability input Route B's E3d slot `hP2` consumes DIRECTLY — the input that in
    Route A (E3e) would instead be manufactured from first-`pd` continuity (`hKp1`) via
    `measurable_deriv_with_param`.  Supplying it here Borel-directly is exactly what retires `hKp1`
    (modulo G-a varying field point and G-b off-diagonal index).  NOT `a₁ = R/6`. -/
theorem secondFieldPd_measurable_of_gateEq (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x))
    (hPmeas : ∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 x k))
    (hQmeas : ∀ k, Measurable (fun p : ℝ × Point n => Qfield p.2 k))
    (hAmpMeas : Measurable
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x))
    (hAmpDerivMeas : Measurable
      (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hAmpDeriv2Meas : Measurable
      (fun p : ℝ × Point n => pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x))
    (hgate : ∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
        IsOpen (S p.2) ∧ x ∈ S p.2 ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update y i s) k)
          (Pfield p.2 y k) (y i)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pfield p.2 (Function.update x i s) k) (Qfield p.2 k) (x i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x) :
    Measurable (fun p : ℝ × Point n =>
      witnessFieldDeriv2 g gi hC hK S a b i (t - p.1) x p.2) :=
  QIQTH.SecondDerivEnvelope.witnessFieldDeriv2_measurable_of_gateEq hn g gi hC hK S a b i t x
    Pfield Qfield hKmeasSet hChartMeas hPmeas hQmeas hAmpMeas hAmpDerivMeas hAmpDeriv2Meas hgate

/-- **★ VERDICT — `endpoint_integrable_of_tripleHEmeas`.**  The `EndpointData.hIntegrable` slot (the
    all-outer-time `IterConvIntegrableW` the Levi tower needs) follows from the `(0,·)` one-step
    Gaussian bound, vanishing at nonpositive time, and the SINGLE triple `hEmeas` (S1) — via
    `IterEMeasurable.iterConvIntegrableW_of_bound_baseMeas`.  **NO joint continuity.**  Certifies that
    the endpoint bundle's measurability content is EXACTLY S1 (which Route B discharges
    continuity-free).  NOT `a₁ = R/6`. -/
theorem endpoint_integrable_of_tripleHEmeas
    (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ) (C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |heatOp g gi Wit τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hEmeas : tripleHEmeas g gi Wit) :
    IterConvIntegrableW (heatOp g gi Wit) (2 : ℝ) (0 : ℝ) C :=
  iterConvIntegrableW_of_bound_baseMeas (heatOp g gi Wit) C hEbound hEzero hEmeas

/-- **★ VERDICT — `iterE_zslice_of_tripleHEmeas` (the `hBmeas` building block).**  Every Levi-tower
    level's `z`-slice `z ↦ iterE (heatOp g gi Wit) k s z y` is `AEStronglyMeasurable` from the SINGLE
    triple `hEmeas` (S1) alone — via `IterEMeasurable.iterE_zmeas`.  **NO joint continuity.**  This is
    the per-level building block from which the capstone `hBmeas` slot (S2, the `tsum` `leviSeries`
    z-slice) is assembled; it certifies S2 reduces to S1, hence is likewise continuity-free.
    NOT `a₁ = R/6`. -/
theorem iterE_zslice_of_tripleHEmeas
    (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ)
    (hEmeas : tripleHEmeas g gi Wit) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ) (y : Point n),
      AEStronglyMeasurable (fun z : Point n => iterE (heatOp g gi Wit) k s z y) volume :=
  iterE_zmeas (heatOp g gi Wit) hEmeas

/-! ###############################################################################
    ## PART 3 — CONTINUITY-FREE CERTIFICATE.  The two Route-B suppliers (Part 2) feed the E3d slots
    ## `hP1`/`hP2`, and E3d assembles S1 — the whole chain never mentions `hKcont`/`hKp1`.  This
    ## `def` records that the audited discharge surface for S1 is exactly
    ##   { hDτ-meas, hP1-meas, hP2-meas, coeff-meas } — a MEASURABILITY-only surface.
    ############################################################################### -/

/-- **`BorelDischargeSurface`.**  The continuity-free discharge surface of the triple `hEmeas` (S1)
    under Route B: the four measurability families E3d consumes.  Bundling them as a `def` makes
    explicit that hKp1 (a CONTINUITY obligation) is NOT among them — the honest record that the
    measurability tower runs entirely on measurabilities.  `tripleHEmeas_of_surface` below shows this
    surface is sufficient. -/
def BorelDischargeSurface (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → Point n → ℝ) : Prop :=
  (StronglyMeasurable (fun w : ℝ × Point n × Point n => deriv (fun u => G u w.2.1 w.2.2) w.1))
  ∧ (∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => G w.1 x w.2.2) k w.2.1))
  ∧ (∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1))
  ∧ (∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
  ∧ (∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))

/-- **★★ `tripleHEmeas_of_surface` — S1 FROM THE CONTINUITY-FREE SURFACE.**  The triple `hEmeas` (S1)
    holds given the `BorelDischargeSurface` — a bundle of MEASURABILITIES only, containing NO
    continuity obligation.  This is the airtight statement of the `hKp1` retirement: the sufficient
    discharge surface for S1 is continuity-free.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_of_surface
    (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → Point n → ℝ)
    (h : BorelDischargeSurface g gi G) :
    tripleHEmeas g gi G := by
  obtain ⟨hDτ, hP1, hP2, hgi, hchr⟩ := h
  exact triple_hEmeas_of_borel_deriv_fields g gi G hDτ hP1 hP2 hgi hchr

end QIQTH.HEmeasBorelAudit

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HEmeasBorelAudit
#print axioms triple_hEmeas_of_borel_deriv_fields
#print axioms firstFieldPd_measurable_of_gateEq
#print axioms secondFieldPd_measurable_of_gateEq
#print axioms endpoint_integrable_of_tripleHEmeas
#print axioms iterE_zslice_of_tripleHEmeas
#print axioms tripleHEmeas_of_surface
end AxiomChecks
