/-
  TruncHIntFromGeometry — J4-665: the TRUNCATED Duhamel-split integrability carry with `hEzero`
  DISCHARGED FROM GEOMETRY.  ONE brick of gap (i) of the post-K1 `a₁ = R/6` residue list.  NOT
  `a₁ = R/6`; proves NOTHING new about `R/6` (R/6 stays a labelled carrier).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — GAP (i) INCREMENT ONLY.  This file advances gap (i) of the post-K1 list (the
  Duhamel-split integrability carry = the `hInt : IterConvIntegrableW`/`…WOn` per-step integrability
  family the Levi/Duhamel Neumann assembly consumes).  It does NOT touch gaps (ii)–(v) (fat-K carrier
  piles, capstone co-instantiation at the whitened witness, prior analytic piles, R/6-itself), and it
  does NOT make `a₁ = R/6` unconditional.

  ── CONTEXT.  The honest (non-vacuous) truncated route to `hInt` is
     `TruncatedHIntRethread.iterConvIntegrableWOn_of_affine_trunc` (J4-262): from the AFFINE `τ ≤ T₀`
     one-step residual bound (coefficient `C·(1+τ)`, the exact `hpkgBound` shape the flat AND curved
     capstones carry), the nonpositive-time vanishing `hEzero`, and the S1 joint strong measurability,
     it delivers the truncated per-step integrability family `IterConvIntegrableWOn E κ 0 (C·(1+T₀)) T₀`
     at the FIXED constant `C·(1+T₀)` — dissolving the affine obstruction J4-261 pinned (the all-τ
     fixed-constant bound is UNSATISFIABLE; the small-time truncation makes the linear `(1+τ)` prefactor
     a fixed constant `(1+T₀)`).  That producer, however, still CARRIES `hEzero` as a hypothesis.

     The pre-existing `hEzero`-from-geometry discharge (`WideHIntDischarge.hInt_wide_from_geometry`,
     J4-261) is only on the NON-truncated wide route, which is blocked by the very affine-obstruction
     firewall the truncation exists to dissolve.  So on the honest (truncated) route, `hEzero` was
     still a live carry.

  ── WHAT THIS FILE DISCHARGES.  For `E = heatOp g gi (vanVleckGatedWitness …)` at ANY metric `(g,gi)`,
     the nonpositive-time vanishing `hEzero` is DISCHARGED FROM GEOMETRY (needs only `1 ≤ n`) by
     `DataPileWitnessAudit.hEzeroE_concrete`.  Composing it with the truncated affine producer gives:

       `hIntOn_affine_from_geometry` — the truncated Duhamel integrability family for the gated-witness
       heat operator, with `hEzero` discharged from geometry, carrying ONLY the (satisfiable, non-vacuous)
       affine `τ ≤ T₀` one-step bound + the S1 joint strong measurability.

     Then `curved_hIntOn_affine_from_geometry` specializes it to the CURVED (constant-curvature `κ<0`,
     genuinely `Ric ≠ 0`) witness metric `(curvedRNCMetric κ, curvedRNCInv κ)`, with the Christoffel
     smoothness supplied by the proven `CurvedA1CenterAmp.curvedRNC_hChr` (NOT carried).  This is the
     FIRST time the truncated Duhamel-split integrability carry has `hEzero` discharged from geometry
     at a genuinely-curved witness — the honest gap-(i) increment.

  ── WHAT STAYS CARRIED (honest residue of gap (i), satisfiable, never the conclusion):
       • the affine `τ ≤ T₀` one-step residual bound `hAff` (the `hpkgBound` shape; provided from
         geometry by `EboundWiringHD1.hEboundW_from_geometry` at width 2, `C·(1+t)`, gate-existential);
       • the S1 joint strong measurability `tripleHEmeas` (the `HEmeasBorelAudit` Borel surface).
     Both are non-vacuous, satisfiable-by-design interface facts — never `a₁ = R/6`.

  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.  Every carried
  hypothesis is satisfiable, non-vacuous, and NEVER equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TruncatedHIntRethread
import QIQTH.DataPileWitnessAudit
import QIQTH.HEmeasBorelAudit
import QIQTH.CurvedA1CenterAmp

open MeasureTheory
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.TruncatedHIntRethread QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open scoped BigOperators Topology ContDiff

namespace QIQTH.TruncHIntFromGeometry

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### T1 — the truncated `hInt` (`IterConvIntegrableWOn`), `hEzero` DISCHARGED from geometry.
    ############################################################################### -/

/-- **★★ J4-665 (T1) — `hIntOn_affine_from_geometry`.**  The truncated Duhamel-split integrability
    family `IterConvIntegrableWOn (heatOp g gi (vanVleckGatedWitness …)) κ 0 (C·(1+T₀)) T₀` for the
    gated-witness heat operator at ANY metric `(g,gi)`, produced by
    `TruncatedHIntRethread.iterConvIntegrableWOn_of_affine_trunc` with:
      • the nonpositive-time vanishing `hEzero` DISCHARGED FROM GEOMETRY (needs `1 ≤ n`) via
        `DataPileWitnessAudit.hEzeroE_concrete`;
      • the AFFINE `τ ≤ T₀` one-step width-`κ` residual bound `hAff` (the `hpkgBound` shape) CARRIED;
      • the S1 joint strong measurability `tripleHEmeas` CARRIED.
    This is the honest (non-vacuous, affine-obstruction-free) truncated route with `hEzero` closed from
    geometry — the increment the pre-existing `WideHIntDischarge.hInt_wide_from_geometry` (J4-261) could
    only make on the firewall-blocked NON-truncated wide route.  NOT `a₁ = R/6`. -/
theorem hIntOn_affine_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (κ C T₀ : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * (1 + τ) * baseKernelW κ (0 : ℝ) τ p q)
    (hEmeas : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)) :
    IterConvIntegrableWOn (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
      κ (0 : ℝ) (C * (1 + T₀)) T₀ :=
  iterConvIntegrableWOn_of_affine_trunc
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ C T₀ hκ hC hAff
    (hEzeroE_concrete g gi hChr hK S a b hn) hEmeas

/-! ###############################################################################
    ### T2 — the CURVED (constant-curvature `κ<0`) witness: `hChr` supplied, `hEzero` from geometry.
    ############################################################################### -/

/-- **★★ J4-665 (T2) — `curved_hIntOn_affine_from_geometry`.**  T1 specialized to the genuinely-curved
    (constant-curvature `κ < 0`, `Ric ≠ 0`) witness metric `(curvedRNCMetric κ, curvedRNCInv κ)`, with
    the Christoffel smoothness supplied (NOT carried) by the proven `CurvedA1CenterAmp.curvedRNC_hChr`.
    The truncated Duhamel-split integrability family for the curved-witness heat operator, with
    `hEzero` discharged from geometry, carrying ONLY the affine `τ ≤ T₀` one-step bound + the S1 Borel
    surface (both satisfiable-by-design).  The first gap-(i) increment carried into the curved-witness
    regime.  NOT `a₁ = R/6` (R/6 stays a labelled carrier; gaps (ii)–(v) untouched). -/
theorem curved_hIntOn_affine_from_geometry (κ : ℝ) (hκneg : κ < 0)
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) (lam C T₀ : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκneg.le) hK S a b) τ p q|
          ≤ C * (1 + τ) * baseKernelW lam (0 : ℝ) τ p q)
    (hEmeas : tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκneg.le) hK S a b)) :
    IterConvIntegrableWOn
      (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκneg.le) hK S a b))
      lam (0 : ℝ) (C * (1 + T₀)) T₀ :=
  hIntOn_affine_from_geometry (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκneg.le) hK S a b hn lam C T₀ hlam hC hAff hEmeas

end QIQTH.TruncHIntFromGeometry

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.TruncHIntFromGeometry
#print axioms hIntOn_affine_from_geometry
#print axioms curved_hIntOn_affine_from_geometry
end AxiomChecks
