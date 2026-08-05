/-
  WideHIntDischarge — J4-261: the wide `hInt` (IterConvIntegrableW) composition, at the discharged
  residual's width `κ ≥ 2`.  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`;
  proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file banks the `hInt` composition for the WIDE capstone
  `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_hEboundW_discharged` (J4-260, which internalized the
  residual `hEboundW_le` slot at any width `κ ≥ 2`).  It carries no coefficient/geometry content of its
  own; it is pure integrability plumbing on top of banked machinery.

  ── WHAT `hInt` IS.  The wide capstone still carries, as an inner hypothesis of its returned
     implication, the slot
        `hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness …)) κ 0 C'`,
     the width-`κ` per-step / Levi-tower integrability family the Duhamel assembly consumes.  Unfolding
     `IterConvIntegrableW E κ 0 C` (ParametrixHEboundWiring): for every level `k ≥ 1` and every OUTER
     time `t > 0`, five interval / z integrability facts about the actual convolution integrand
     `E (t−s) x z · iterE E k s z y` and the width-`κ` model.

  ── THE PRODUCER.  `WidthAdapters.iterConvIntegrableW_of_bound_baseMeas_wide` proves
     `IterConvIntegrableW E κ 0 C` from three inputs:
        (i)  the ONE-STEP width-`κ` residual bound `hEbound : ∀ τ p q, 0 < τ →
             |E τ p q| ≤ C · baseKernelW κ 0 τ p q`   — an ALL-POSITIVE-TIME bound at a FIXED `C`;
        (ii) the vanishing at nonpositive time `hEzero : ∀ τ ≤ 0, ∀ p q, E τ p q = 0`;
        (iii) the joint strong measurability `hEmeas : StronglyMeasurable (τ,p,q) ↦ E …`  (= the S1
             triple `HEmeasBorelAudit.tripleHEmeas`).

  ── WHAT THIS FILE DISCHARGES.  For `E = heatOp g gi (vanVleckGatedWitness …)`:
        • (ii) `hEzero` is DISCHARGED FROM GEOMETRY (needs `1 ≤ n`) by
          `DataPileWitnessAudit.hEzeroE_concrete`;
        • (iii) `hEmeas` is the S1 triple, reducible to the continuity-free
          `HEmeasBorelAudit.BorelDischargeSurface` (variant `hInt_wide_of_surface`), or supplied
          directly by the `Gc`-route `GcConsumerMirror.tripleHEmeas_Gc`;
        • (i) the ONE-STEP all-τ fixed-`C` residual bound is CARRIED.
     Target: `hInt_wide_from_geometry` — the capstone's `hInt` slot at width `κ`, with `hEzero`
     discharged from geometry, the S1 triple and the one-step bound carried.

  ── ⚠ THE HONEST RESIDUAL / SHAPE MISMATCH (bankable intel).  The one-step bound the producer needs is
     an ALL-τ bound at a FIXED constant `C`.  The residual provider that the wide capstone actually
     uses — `ResidualAssemblyRecon.hEboundW_wide_from_geometry`, sourced from
     `EboundWiringHD1.hEboundW_from_geometry` / `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final`
     — supplies only
        `∀ τ p q, 0 < τ → τ ≤ t → |heatOp …| ≤ (C·(1+t)·√(κ/2)ⁿ) · baseKernelW κ 0 τ p q`,
     a bound RESTRICTED to `τ ≤ t`, whose valid constant `C·(1+t)` is AFFINE in the cutoff time.
     Extending to all `τ > 0` (by taking the cutoff `= τ`) gives `C·(1+τ)·G` — an AFFINE-in-τ
     coefficient — which admits NO fixed-constant Gaussian majorant for all `τ` (a linear `(1+τ)`
     prefactor cannot be absorbed by any Gaussian width change: width only rescales the exponent, not
     the `τ^{-n/2}` prefactor scaling).  Hence the geometry residual bound does NOT feed the producer at
     the capstone's constant `C'`, and the `hInt` slot is NOT internalizable into the capstone from
     geometry alone.  The obstruction is the τ-RANGE / affine constant of the residual coefficient, NOT
     the gate — the gate `(a,b,S)` threads fine (both providers share the provider-chosen gate).  The
     genuinely-open input is the ALL-τ FIXED-CONSTANT one-step residual bound; this file makes that the
     sole carried content and discharges everything else.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the conclusion.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthAdapters
import QIQTH.DataPileWitnessAudit
import QIQTH.HEmeasBorelAudit
import QIQTH.ResidualAssemblyRecon

open MeasureTheory
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.WidthAdapters QIQTH.HEmeasBorelAudit QIQTH.DataPileWitnessAudit
open scoped BigOperators Topology ContDiff

namespace QIQTH.WideHIntDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### T1 — the wide `hInt` composition: `hEzero` from geometry, one-step bound + S1 carried.
    ############################################################################### -/

/-- **★★ J4-261 (T1) — `hInt_wide_from_geometry`.**  The wide capstone's `hInt` slot
    `IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness …)) κ 0 C` (width `κ`, `0 < κ`), produced
    by `WidthAdapters.iterConvIntegrableW_of_bound_baseMeas_wide` with:
      • the vanishing at nonpositive time DISCHARGED FROM GEOMETRY (needs `1 ≤ n`) via
        `DataPileWitnessAudit.hEzeroE_concrete`;
      • the ONE-STEP all-τ fixed-`C` width-`κ` residual bound `hEbound` CARRIED;
      • the S1 joint strong measurability `hEmeas` (`= HEmeasBorelAudit.tripleHEmeas`) CARRIED.
    ⚠ HONEST RESIDUAL: `hEbound` is an ALL-τ bound at a FIXED `C`; the geometry residual provider
    `ResidualAssemblyRecon.hEboundW_wide_from_geometry` supplies only the `τ ≤ t` / affine-`C·(1+t)`
    version, which does NOT feed this slot at the capstone's constant (see the file header).  So this
    brick reduces `hInt` to (all-τ one-step bound + S1) and discharges `hEzero`; it does NOT close the
    slot from geometry alone.  NOT `a₁ = R/6`. -/
theorem hInt_wide_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (κ C : ℝ) (hκ : 0 < κ)
    (hEbound : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hEmeas : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)) :
    IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ (0 : ℝ) C :=
  iterConvIntegrableW_of_bound_baseMeas_wide
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ C hκ hEbound
    (hEzeroE_concrete g gi hChr hK S a b hn) hEmeas

/-! ###############################################################################
    ### T2 — the surface variant: S1 reduced to the continuity-free `BorelDischargeSurface`.
    ############################################################################### -/

/-- **★ J4-261 (T2) — `hInt_wide_of_surface`.**  Same as T1 but the S1 triple `hEmeas` is reduced to
    the CONTINUITY-FREE `HEmeasBorelAudit.BorelDischargeSurface` (the four measurability families:
    `∂_τ`, first and second field-`pd`, `gi`, `christoffel`) via `HEmeasBorelAudit.tripleHEmeas_of_surface`.
    Records that the whole `hInt` discharge runs on measurabilities + the one carried all-τ residual
    bound + `1 ≤ n` — no joint continuity anywhere.  NOT `a₁ = R/6`. -/
theorem hInt_wide_of_surface (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (κ C : ℝ) (hκ : 0 < κ)
    (hEbound : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hsurf : BorelDischargeSurface g gi (vanVleckGatedWitness g gi hChr hK S a b)) :
    IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ (0 : ℝ) C :=
  hInt_wide_from_geometry g gi hChr hK S a b hn κ C hκ hEbound
    (tripleHEmeas_of_surface g gi (vanVleckGatedWitness g gi hChr hK S a b) hsurf)

/-! ###############################################################################
    ### T3 — the abstract width-`κ` `hInt` producer (any kernel `E`, geometry-agnostic re-export).
    ############################################################################### -/

/-- **★ J4-261 (T3) — `iterConvIntegrableW_wide`.**  The geometry-agnostic re-export of the wide
    producer, ABSTRACT in the kernel `E`: from the width-`κ` (`0 < κ`) all-τ fixed-`C` one-step bound,
    the nonpositive-time vanishing, and the S1 joint strong measurability, the full
    `IterConvIntegrableW E κ 0 C` family holds.  This is the honest "slot shape" the wide capstone's
    `hInt` needs; T1/T2 specialize it to `E = heatOp g gi (vanVleckGatedWitness …)` and discharge
    `hEzero` from geometry.  NOT `a₁ = R/6`. -/
theorem iterConvIntegrableW_wide (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    IterConvIntegrableW E κ (0 : ℝ) C :=
  iterConvIntegrableW_of_bound_baseMeas_wide E κ C hκ hEbound hEzero hEmeas

end QIQTH.WideHIntDischarge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WideHIntDischarge
#print axioms hInt_wide_from_geometry
#print axioms hInt_wide_of_surface
#print axioms iterConvIntegrableW_wide
end AxiomChecks

/-!
  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE STRETCH (step 3) — WHY `wide_a1_R6_residual_closed` DOES NOT LAND, precisely.
  ══════════════════════════════════════════════════════════════════════════════════════════════════

  The wide capstone `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_hEboundW_discharged` binds a SINGLE
  constant `C'` and consumes BOTH residual slots at it:
      hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t → |heatOp …| ≤ C' · baseKernelW κ 0 τ p q      (discharged)
      hInt        : IterConvIntegrableW (heatOp …) κ 0 C'                                  (this slot)
  where `C' = C·(1+t)·√(κ/2)ⁿ` is the constant the residual provider chooses.

  To internalize `hInt` from geometry via T1/T3 one would have to supply the ALL-τ fixed-`C'` one-step
  bound `∀ τ p q, 0 < τ → |heatOp …| ≤ C' · baseKernelW κ 0 τ p q`.  The ONLY geometric provider is the
  `τ ≤ t` bound (constant `C·(1+t')` at cutoff `t'`).  Extending it to all `τ` forces the AFFINE
  coefficient `C·(1+τ)`, which has no fixed-`C'` Gaussian majorant (a linear `(1+τ)` prefactor survives
  every Gaussian width change).  So the all-τ fixed-`C'` bound is neither provided nor known to be
  satisfiable at `C'`; carrying it would risk an UNSATISFIABLE hypothesis (firewall violation).  The
  stretch is therefore STOPPED here — the mismatch is intrinsic to the residual coefficient's affine
  time-dependence, not to the gate.  Reducing `hInt` to (all-τ one-step bound + S1 + `1 ≤ n`) — with
  `hEzero` discharged — is the honest maximal bank, and pinpoints the ALL-τ FIXED-CONSTANT one-step
  residual bound as the exact remaining input.

  NOT `a₁ = R/6`.
-/
