/-
  CurvedA1Hsrc — J4-594: discharging the `hsrc` carrier (Seeley–DeWitt transport-source smoothness)
  of the CENTER-GAUGE curved a₁ = R/6 capstone `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (draining the curved capstone's carried residuals).  The non-vacuous curved capstone (J4-587)
  carries a family of residual analytic/regularity inputs, drained one-by-one via banked generic engines
  (hmassone J4-588→591; hInnerCont J4-592; hOffCollarTail J4-593).  THIS brick attacks `hsrc`, the exact
  binder
      `hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
        (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)
          (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) 0))`
  i.e. the assertion that the DeWitt transport SOURCE `T u₀` — the operator
  `transportOp Θ g gi` applied to the base DeWitt coefficient `u₀ = transportCoeff T 0` — is `C^∞`.

  ── ★★ VERDICT (J4-594): `hsrc` is FULLY DISCHARGEABLE from banked smoothness machinery, NO new
     analytic input.  Two observations collapse it to composition of PROVED `ContDiff` facts.
       (1) `transportCoeff T 0 = (fun _ => 1)` DEFINITIONALLY (`ParametrixFunction.transportCoeff_zero`):
           the base DeWitt coefficient `u₀` is the constant `1`, which is `C^∞` (`contDiff_const`).
       (2) `transportOp (vanVleck g) g gi` PRESERVES `C^∞` (`TransportOpSmoothness.transportOp_preserves_contDiff`,
           banked J4-174 Part A — the van-Vleck prefactors `Θ^{±½}` are `C^∞` where `det g > 0`, and
           `Δ_g` maps `C^∞ → C^∞`), for the curved witness's metric carries
             • `curvedRNCMetric_contDiff`  (`g^K_{ij}` is `C^∞`, polynomial),
             • `curvedRNCInv_contDiff`     (`gi^K_{ij}` is `C^∞`, `K ≤ 0`, denom `≥ 1 > 0`),
             • `curvedRNCMetric_hgpos`     (`det g^K > 0`, `K ≤ 0`).
     The banked `transportOp_preserves_contDiff` delivers `C^∞` at the ANALYTIC level `⊤ = ω` of the
     toolchain's `WithTop ℕ∞`; `hsrc` only asks for the WEAKER `∞`-level (`(∞ : WithTop ℕ∞) ≤ ⊤`), so
     `ContDiff.of_le le_top` closes it.  ⚠ NOTE: the honest ANALYTIC WALL of `TransportOpSmoothness`
     (why the FULL `hu`-tower `hSolve` is not closed at ω) is about the RAY-INTEGRAL SOLVE
     `radialTransportSolve`; `hsrc` involves NO solve — only ONE transport-source application to the
     CONSTANT `u₀`, whose smoothness is a pure composition.  So there is no residual analytic gap here.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hsrc_at_gate` — ★★ the EXACT `hsrc` shape of the center-gauge curved capstone, PROVED
      for the curved witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`).  Fully discharges the `hsrc` binder.
    • `curved_hsrc_satisfiable` — ★ the NON-VACUITY certificate.  For `κ < 0`, `n ≥ 2`: `hsrc` holds
      WHILE `g^K` is GENUINELY CURVED (`∃ w, 1 < det g^K(w)`), so the discharged smoothness is NOT
      secretly the flat metric's — the transport source of a genuinely curved metric IS `C^∞`.

  ⚠ HONEST a₁ FRAMING.  `a₁ = R/6` remains CONDITIONAL.  This brick removes ONLY the `hsrc` carrier
  from the center-gauge curved capstone's residual family; the capstone still owes the OTHER carried
  residuals (census/measurability/domination, the convergence trio, `hmassone`'s pre-`ρ` carriers
  `hGgate`/`hSupp`, `hInnerCont`'s `hContDom`, the on-collar chart-jet bundle `hjets`).  `hsrc` is
  genuinely TRUE for `g^K` (the curved metric is `C^∞`, `det g^K > 0`, and van-Vleck / Laplace–Beltrami
  preserve smoothness), DERIVED from PROVED machinery — NOT axiomatized, NOT the `a₁` conclusion, and
  the `R/6` value is unaffected.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous/conclusion-in-disguise hypothesis,
  no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.TransportOpSmoothness
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.CurvedA1HmassoneBound

open QIQTH.Curvature
open QIQTH.TransportOpSmoothness QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open scoped ContDiff

namespace QIQTH.CurvedA1Hsrc

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **★★ `curved_hsrc_at_gate` — the `hsrc` carrier of the center-gauge curved capstone, DISCHARGED.**
    The Seeley–DeWitt transport SOURCE `T u₀ = transportOp (vanVleck g^K) g^K gi^K (transportCoeff T 0)`
    is `C^∞` for the curved witness `g^K = curvedRNCMetric κ` (`κ ≤ 0`).  Since `transportCoeff T 0`
    is the CONSTANT `u₀ ≡ 1` (`transportCoeff_zero`, `C^∞` by `contDiff_const`) and the banked
    `transportOp_preserves_contDiff` maps `C^∞ → C^∞` (using the metric carries
    `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff` / `curvedRNCMetric_hgpos`) at the analytic
    level `⊤`, the weaker `∞`-level target follows by `ContDiff.of_le le_top`.  This is the EXACT
    `hsrc` binder of `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center`.  NOT `a₁ = R/6`. -/
theorem curved_hsrc_at_gate (κ : ℝ) (hκ : κ ≤ 0) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ)
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ)
          (curvedRNCInv κ)) 0)) := by
  -- the base DeWitt coefficient `u₀ = transportCoeff T 0 ≡ 1` is `C^∞`.
  have hf : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) 0) := by
    rw [transportCoeff_zero]
    exact contDiff_const
  -- the transport source preserves `C^∞` (banked, at the analytic level `⊤`).
  have hTsrc : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ)
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ)
          (curvedRNCInv κ)) 0)) :=
    transportOp_preserves_contDiff (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun a b => curvedRNCInv_contDiff κ hκ a b)
      (curvedRNCMetric_hgpos κ hκ)
      _ hf
  -- `∞ ≤ ⊤`, so the `∞`-level target follows.
  exact hTsrc.of_le le_top

/-- **★ `curved_hsrc_satisfiable` — NON-VACUITY certificate for the discharged `hsrc`.**  For `κ < 0`
    and `n ≥ 2`, the transport-source smoothness `hsrc` holds WHILE `g^K` is GENUINELY CURVED — there
    is `w` with `1 < det g^K(w)` (`det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` for `‖w‖ > 0`, `K < 0`).  So
    the discharged smoothness is NOT the flat metric's degenerate case: the transport source of a
    genuinely curved metric IS `C^∞`.  NOT `a₁ = R/6`. -/
theorem curved_hsrc_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ)
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ)
          (curvedRNCInv κ)) 0))
      ∧ ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  ⟨curved_hsrc_at_gate κ hκ.le,
    (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2⟩

end QIQTH.CurvedA1Hsrc

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1Hsrc

#print axioms curved_hsrc_at_gate
#print axioms curved_hsrc_satisfiable

end AxiomChecks
