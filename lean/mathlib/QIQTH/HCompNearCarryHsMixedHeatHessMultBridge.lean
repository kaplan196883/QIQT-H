/-
  HCompNearCarryHsMixedHeatHessMultBridge — J4-1011: the G3-gate identification (Sol `gpt-5.6-sol`,
  high, 2026-08-23) linking `HCompNearCarryKPrimeBaseFieldCoV`'s (J4-1010) LITERAL `Bfac` term1 scalar
  `hsMixed` to `HeatHessianMomentCancellation`'s (J4-998) abstract `heatHessMult` multiplier.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## BACKGROUND.  A staged sympy audit (cp902, no commit) found that `nb`'s `Bfac` 4-term sum
  (`HCompNearCarryKPrimeBaseFieldCoV.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`, J4-1010)
  carries ALL of `kPrime`'s singular `1/τ`/`1/τ²` structure in ONE term (`hsMixed·A`, "term1"), and
  Sol independently confirmed a genuine n-D Gaussian second-moment cancellation is available for
  exactly this shape via `HeatHessMoment.integral_heatHessMult_eq_zero` (J4-998).  Sol staged the
  wiring into THREE risk-ranked gates: G3 (LOWEST — is `hsMixed` literally/algebraically
  `heatHessMult`'s multiplier for the literal `Fin n`-indexed `PI`/`PJ`?), G2 (boundary-term control
  on the actual bounded integration domain `S'`), G1 (HIGHEST — the cancellation must be exposed
  BEFORE any `|·|`/triangle-inequality step).  THIS FILE is G3 ONLY.

  ## THE G3 FINDING (sympy-verified FIRST, `docs/qg_roadmap/rnc_sympy/
  hcomp_g3_hsmixed_heathessmult_identity.py`, general symbolic dot-product algebra): `hsMixed` is
  **NOT** literally `heatHessMult`'s bare scalar multiplier.  It differs by an EXACT, non-vanishing
  additive correction term:
      `hsMixed(τ,U,PI,PJ,Q) = heatHessMult_scalar(τ,PI,PJ,U) − ⟨U,Q⟩/(2τ)`,
  i.e. (restoring the `gaussDdim` factor, `heatHessMult` already includes it):
      `hsMixed(τ,U,PI,PJ,Q) · G_τ(U) = heatHessMult τ PI PJ U − (⟨U,Q⟩/(2τ)) · G_τ(U)`.
  The naive identity `hsMixed = heatHessMult_scalar` is FALSE in general — sympy confirms the residual
  is exactly `−⟨U,Q⟩/(2τ)`, nonzero whenever `Q ≠ 0` (the generic case: `Q` is `hJetQ`'s i-directional
  jet-derivative of the `PJ` direction field at `x`, a genuine second-order chart datum, not an
  artifact).  This is a PURE ALGEBRAIC (ring) identity — no positivity, no integration, no chart
  hypotheses needed; it holds for ALL `τ, U, PI, PJ, Q : Point n / ℝ`.

  `integral_heatHessMult_eq_zero` therefore does NOT directly kill `term1`: after this bridge, term1
  = `heatHessMult(...) · A − (leftover ⟨U,Q⟩/(2τ)·G_τ(U)) · A`.  The `heatHessMult` piece is now
  wired to J4-998's exact-zero mechanism (subject to G2's domain/boundary caveat); the leftover
  `⟨U,Q⟩/(2τ)·G_τ(U)` piece is a FIRST-MOMENT shape (`∫ v, ⟨v,Q⟩·G_τ(v) = 0` when `Q` is independent
  of the integration variable, by `gaussianFirstMoment_oneD`-type oddness) — Sol flags this is
  amenable to the SAME class of trick but is genuinely SEPARATE, still-open infrastructure (not
  supplied here), and its own domain/CoV bookkeeping (the integration variable is `z`, with
  `U = uniformInverseChart … z x`, not a bare Gaussian variable — the `z ↦ U` change of variables
  needed to invoke first-moment vanishing is exactly G2's territory).

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  G3 IDENTIFICATION ONLY — a standalone algebraic bridge lemma, NOT composed with
  `integral_heatHessMult_eq_zero`, NOT integrated, NOT wired into `hcomp`.  It does NOT discharge `nb`,
  `hCConv`, or any part of `hcomp`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion (the identity is a nontrivial
  rearrangement exposing a nonzero correction term, not a restatement of either side), no existing
  file edited.  G2 (boundary control on `S'`) and G1 (pre-`|·|` exposure ordering) are EXPLICITLY
  DEFERRED — not attempted here.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeBaseFieldCoV
import QIQTH.HeatHessianMomentCancellation

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryHsMixedHeatHessMultBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### G3 BRICK — the generic scalar identification (parameter-free of `kPrime`).
    ############################################################################### -/

/-- **★ `hsMixed_eq_heatHessMult_sub_firstMomentCorrection` — the G3 IDENTIFICATION.**  For ANY
    `τ U PI PJ Q : … ℝ / Point n` (no positivity, no chart, no integration hypotheses — pure algebra),
    the literal `Bfac` `hsMixed` scalar (as it appears, undivided by `gaussDdim`, in
    `HCompNearCarryKPrimeBaseFieldCoV.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`'s term1)
    equals `HeatHessMoment.heatHessMult τ PI PJ U` MINUS an explicit, generally NONZERO first-moment
    correction `(⟨U,Q⟩/(2τ)) · G_τ(U)`:
        `(⟨U,PI⟩⟨U,PJ⟩/(4τ²) − (⟨PI,PJ⟩ + ⟨U,Q⟩)/(2τ)) · G_τ(U)
            = heatHessMult τ PI PJ U − (⟨U,Q⟩/(2τ)) · G_τ(U)`.
    Sympy-verified (`docs/qg_roadmap/rnc_sympy/hcomp_g3_hsmixed_heathessmult_identity.py`) BEFORE this
    Lean statement.  The naive `hsMixed = heatHessMult`'s bare scalar is FALSE — this lemma is the
    PRECISE correction, not a restatement.  NOT `a₁ = R/6`. -/
theorem hsMixed_eq_heatHessMult_sub_firstMomentCorrection
    (τ : ℝ) (U PI PJ Q : Point n) :
    (((∑ k, U k * PI k) * (∑ k, U k * PJ k) / (4 * τ ^ 2)
          - ((∑ k, PI k * PJ k) + (∑ k, U k * Q k)) / (2 * τ)))
        * gaussDdim τ U
      = QIQTH.HeatHessMoment.heatHessMult τ PI PJ U
          - (∑ k, U k * Q k) / (2 * τ) * gaussDdim τ U := by
  simp only [QIQTH.HeatHessMoment.heatHessMult]
  ring

/-! ###############################################################################
    ### G3 BRICK — the literal `kPrime`/`Bfac` specialization (matches BRICK 1 exactly).
    ############################################################################### -/

/-- **★★ `kPrime_term1_eq_heatHessMult_sub_firstMomentCorrection_mul_amp` — the G3 DELIVERABLE.**  The
    LITERAL `term1 := hsMixed·A` piece of `Bfac`, exactly as it occurs inside
    `HCompNearCarryKPrimeBaseFieldCoV.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`'s conclusion
    (same `PI x`, `PJ x`, `Q`, `U := uniformInverseChart g gi hC hK z x`, `A := chartFieldAmp … z x`,
    `τ := t − s` — NO new hypotheses beyond what BRICK 1 already carries), equals
    `(heatHessMult (t−s) (PI x) (PJ x) U − (⟨U,Q⟩/(2(t−s)))·G_τ(U)) · A`:
        `G_τ(U) · (hsMixed · A) = (heatHessMult (t−s) (PI x) (PJ x) U − (⟨U,Q⟩/(2(t−s)))·G_τ(U)) · A`.
    This is the literal `Fin n`-indexed identification G3 asked for — `heatHessMult`'s directions
    instantiated at the ACTUAL chart-Jacobian jet fields `PI x`/`PJ x` `Bfac` uses, not a hand-picked
    scalar toy.  Composing this with `integral_heatHessMult_eq_zero` (J4-998) and disposing of the
    leftover first-moment correction term is EXPLICITLY DEFERRED to G2/G1 — NOT attempted here.
    NOT `a₁ = R/6`. -/
theorem kPrime_term1_eq_heatHessMult_sub_firstMomentCorrection_mul_amp
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (t s : ℝ) (x z : Point n)
    (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ) :
    gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
        * (((∑ k, uniformInverseChart g gi hC hK z x k * PI x k)
                * (∑ k, uniformInverseChart g gi hC hK z x k * PJ x k) / (4 * (t - s) ^ 2)
              - ((∑ k, PI x k * PJ x k)
                  + (∑ k, uniformInverseChart g gi hC hK z x k * Q k)) / (2 * (t - s)))
              * chartFieldAmp g gi hC hK a b (t - s) z x)
      = (QIQTH.HeatHessMoment.heatHessMult (t - s) (PI x) (PJ x)
              (uniformInverseChart g gi hC hK z x)
            - (∑ k, uniformInverseChart g gi hC hK z x k * Q k) / (2 * (t - s))
                * gaussDdim (t - s) (uniformInverseChart g gi hC hK z x))
          * chartFieldAmp g gi hC hK a b (t - s) z x := by
  simp only [QIQTH.HeatHessMoment.heatHessMult]
  ring

end QIQTH.HCompNearCarryHsMixedHeatHessMultBridge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryHsMixedHeatHessMultBridge
#print axioms hsMixed_eq_heatHessMult_sub_firstMomentCorrection
#print axioms kPrime_term1_eq_heatHessMult_sub_firstMomentCorrection_mul_amp
end AxiomChecks
