/-
  CurvedWidth43QuadBridge — J4-675 (route-β first brick of the curved width-3/2 hEdom campaign).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE ROUTE VERDICT THIS BRICK LANDS ON (α vs β).

  The width-3/2 `hEdom` slot the labelled capstone consumes demands EXACTLY `gaussDdim (3/2·τ)`.  Two
  candidate ambient transfers of the banked CURVED INTRINSIC width-3/2 defect
  (`CurvedIntrinsicWidth32.curvedRNC_intrinsic_width32_defect`, J4-672) were on the table:

    (α)  the PURE-GAUSSIAN (1+δ) transfer.  Compose the intrinsic width `w_i = 3/2` with the banked
         `(1+δ)` shrunk-radius displacement (`WidthParametricGoodGate.uniformFlowExp_hdisp_ball_delta`,
         J4-673 (b)) through the width-parametric merge (`gatedWitnessN1_hEboundW_le_of_good_W`, J4-673
         (a)).  The ambient width lands at `w_i·(1+δ) = (3/2)(1+δ) > 3/2` STRICTLY (δ>0).  To reach the
         demanded `gaussDdim (3/2·τ)` one would need `gaussDdim ((3/2)(1+δ)τ) ≤ C·gaussDdim (3/2·τ)` — a
         WIDER Gaussian dominated by a NARROWER one — which is FALSE: the ratio
         `gaussDdim (Wτ) v / gaussDdim (wτ) v = √(W/w)ⁿ · exp(‖v‖²·(1/w−1/W)/(4τ))` with `W>w` DIVERGES
         as `‖v‖→∞` (`1/w > 1/W`).  The banked width-widening lemma
         `WidthMarginEngine.rncRadialSq_pow_mul_gaussDdim_le_width` is stated with `c < d` (SOURCE
         narrower than target); the (1+δ) route puts the source on the WRONG side.  ⟹ (α) CANNOT reach
         the intrinsic floor 3/2 exactly.  **WRONG ROUTE.**

    (β)  the WIDTH-4/3 QUADRATIC-PREFACTOR transfer.  The banked bridge
         `HrawPreCollapse.hEdom_of_quadPoly_residual_width` takes an ambient bound at width `w₀ = 4/3
         < 3/2` carrying a QUADRATIC prefactor `((r²/τ)² + r²/τ + 1)` and produces the width-3/2 `hEdom`
         with `E₁ = 0`.  Mechanism (quoted from its proof, HrawPreCollapse.lean:127–201): the `m=0,1,2`
         width absorptions `rncRadialSq_pow_mul_gaussDdim_le_width` (with `c = 4/3 < d = 3/2`) eat the
         `1`, `r²/τ`, `(r²/τ)²` polynomial terms into constants × `gaussDdim (3/2·τ)`, because the
         SOURCE width 4/3 is BELOW the target 3/2 (the exponential margin `exp(−r²(1/(4/3)−1/(3/2))/4τ)`
         beats every polynomial power).  This is the direction that WORKS.  **RIGHT ROUTE.**

  So the campaign target is NOT the pure-Gaussian ambient transfer (α); it is the CURVED width-4/3
  QUADRATIC-prefactor on-gate carry.  Crucially, the entire route-β bridge machinery
  (`hEdom_vanVleck_of_hgate` and its core `HrawPreCollapse.hEdom_concrete_final`,
  `hEdom_of_quadPoly_residual_width`, `chartTransfer_quad`) is **metric-agnostic** — it is quantified over
  arbitrary `g gi K S H` — so it applies to the genuinely-curved witness `g^K = curvedRNCMetric κ`
  (κ<0) with ZERO new geometry.  The surviving wall is producing the CURVED on-gate width-4/3 QUADRATIC
  carry `hgate` (the honest, satisfiable labelled input — the flat tower carries the same object; see
  HrawPreCollapse.lean:30–31,62–66).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE (route-β brick 1).

    • `curvedRNC_hEdom_of_width43_quad` — ★★ the CURVED route-β bridge: from the on-gate ambient
      width-4/3 QUADRATIC carry at the genuinely-curved van-Vleck gated witness
      `vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) …`, produce the width-3/2 `hEdom`
      ∃-shape (`gaussDdim (3/2·τ)`) the labelled capstone consumes.  This is
      `LabelledRethreadV2.hEdom_vanVleck_of_hgate` INSTANTIATED at the curved metric — the honest
      route-β analogue of J4-672's re-run of the intrinsic producer at `curvedRNCMetric`.  It isolates
      the surviving curved wall to EXACTLY the curved width-4/3 quadratic on-gate `hgate`.
    • `curvedRNC_width43_quad_curved_satisfiable` — the SATISFIABILITY GATE re-export
      (`Ric(0) ≠ 0` at `κ ≠ 0`, `n ≥ 2`): the bridge is instantiated at a GENUINELY curved metric, not
      the flat `δ`.  Non-vacuous.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and it does NOT discharge the surviving curved
  width-4/3 quadratic on-gate carry `hgate` — it CONSUMES `hgate` as an honest, satisfiable, NAMED
  labelled input and threads it through the metric-agnostic quadratic bridge to the width-3/2 `hEdom`.
  `hgate` is NOT the conclusion (width-4/3 QUADRATIC on the gate vs the width-3/2 affine ∃-shape
  everywhere).  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  conclusion-in-disguise, no existing file edited, nothing committed.
-/
import QIQTH.LabelledRethreadV2
import QIQTH.CurvedIntrinsicWidth32

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness
open QIQTH.CurvedRNCGaugeBundle QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.FlatHeatEquation
open scoped BigOperators

namespace QIQTH.CurvedWidth43QuadBridge

variable {n : ℕ}

/-- **★★ J4-675 (route-β brick 1) — `curvedRNC_hEdom_of_width43_quad`.**  THE CURVED ROUTE-β BRIDGE.
    From the ON-GATE ambient width-`4/3` QUADRATIC carry at the genuinely-curved van-Vleck gated witness
    `H_G := vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK S a b`,
        `hgate : ∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g^K gi^K H_G τ p q|
              ≤ P·(((r²/τ)² + r²/τ + 1)·gaussDdim ((4/3)·τ) (p−q))`   (`r² = rncRadialSq (p−q)`),
    the width-3/2 `hEdom` ∃-shape follows:
        `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ>0, ∀ p q,
            |heatOp g^K gi^K H_G τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`.

    This is `LabelledRethreadV2.hEdom_vanVleck_of_hgate` INSTANTIATED at `g := curvedRNCMetric κ`,
    `gi := curvedRNCInv κ` — the honest route-β analogue of J4-672's re-run of the intrinsic width-3/2
    producer at the curved metric.  The width-4/3-QUADRATIC → width-3/2-PURE reduction is the metric-
    agnostic `m=0,1,2` width absorption (source width `4/3 < 3/2`, the RIGHT direction), NOT the failed
    pure-Gaussian `(1+δ)` inflation (route α, which lands at `(3/2)(1+δ) > 3/2`).  It isolates the
    surviving curved wall to EXACTLY the curved width-4/3 quadratic on-gate `hgate`.  ⚠ NOT `a₁ = R/6`. -/
theorem curvedRNC_hEdom_of_width43_quad
    (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK S a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK S a b) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
  QIQTH.LabelledRethreadV2.hEdom_vanVleck_of_hgate
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK S a b P hP hgate

/-- **★ J4-675 (satisfiability gate) — CURVED, NOT SECRETLY FLAT.**  The witness underlying the route-β
    bridge is genuinely curved: for `κ ≠ 0` and `n ≥ 2` the diagonal metric-Hessian trace (`Ric(0)`) is
    nonzero.  So `curvedRNC_hEdom_of_width43_quad` is instantiated at a genuinely curved metric
    (`κ < 0` ⊂ `κ ≠ 0`), NOT the flat `δ`.  Non-vacuous.  NOT `a₁ = R/6`. -/
theorem curvedRNC_width43_quad_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedWidth43QuadBridge

section AxiomChecks
open QIQTH.CurvedWidth43QuadBridge
#print axioms curvedRNC_hEdom_of_width43_quad
#print axioms curvedRNC_width43_quad_curved_satisfiable
end AxiomChecks
