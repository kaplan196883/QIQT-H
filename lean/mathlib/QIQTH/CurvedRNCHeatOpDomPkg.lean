import QIQTH.CurvedRNCPosDef
import QIQTH.ConstRadiusGateExport
import QIQTH.CoeffBoundsN1
import QIQTH.CoeffU1Fix
import QIQTH.ParametrixHEboundWiring
import QIQTH.ConvApproximants
import QIQTH.A1R6CoreAtGate

/-!
# J4-536 — the CONCRETE curved heatOp width-2 Gaussian domination (`hpkgBound` + `hAdomHeat`)

The `a₁ = R/6` curved-signature capstone
`A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary` consumes, in its SECTION C and
SECTION G analytic piles, the two heat-operator (defect-kernel) Gaussian dominations for the concrete
gated van-Vleck witness on the constant-radius flow-ball gate:

```
hpkgBound : ∀ t' τ p q, 0 < τ → τ ≤ t' →
    |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
      ≤ (C·(1+t'))·baseKernelW 2 0 τ p q                                   -- all-t' width-2 bound
hAdomHeat : ∀ τ, 0 < τ → τ ≤ T → ∀ z,
    |heatOp g gi (vanVleckGatedWitness … (constGate … c) a b) τ 0 z|
      ≤ CA·gaussDdim (wA·τ) (0 − z)                                        -- frozen p=0 window slice
```

where `heatOp g gi K τ x y = ∂_τ K − Δ_g K` is the parametrix DEFECT kernel (`TrueHeatKernel.heatOp`).
This brick lands BOTH, for the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`,
`Ric(0) = (n−1)Kδ ≠ 0`), on the singleton gate seed `Kset = {0}` (the RNC centre — the ONLY base
point at which `g^K = δ`, which is exactly `hframeK`'s demand for the coefficient route).

## Route — every step banked

The gated van-Vleck witness unfolds definitionally (`ConvApproximants.vanVleckGatedWitness`) to
`gatedKernel {0} (constGate …) (globalCutoffParametrixWitnessN 1 (vanVleck g^K) (transportCoeff …)
a b (uniformInverseChart …))`.  The **banked concrete constant-radius `hEboundW_le` producer**
`ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST` delivers EXACTLY the all-`t'` width-2
Gaussian defect bound for that gated kernel on the flow-ball gate `fun z ↦ exp_z '' ball 0 c =
constGate g^K gi^K hChr hK c` — given the geometry/gauge data and the two amplitude-coefficient
bounds `hCoeffU0`/`hCoeffLin1`.  For `g^K` those bounds are DISCHARGED exactly as in the flat capstone
`gatedWitnessN1_hEboundW_le_vanVleck_final`:

* `hCoeffU0` ⟸ `HeatResidualBound.hCoeffU0_vanVleck` (the shifted-van-Vleck `O(r²)` zeroth bound);
* `hCoeffLin1` ⟸ `HeatResidualBound.uniformCoeffLinear_bound` (the `O(r)` first bound).

All curved geometry/gauge inputs are the banked members: `curvedRNCMetric_contDiff` (`hg`),
`curvedRNCMetric_symm` (`hgsymm`), `curvedRNCMetric_hinvF` (`hinvF`), `curvedRNCMetric_zero`
(`hg0`/`hframeK` on `{0}`), `curvedRNCMetric_pd_zero` (`hdg0`), and — the nondegeneracy `hgnd` —
`CurvedRNCPosDef.curvedRNCMetric_det_pos` (`det g^K > 0`, `K ≤ 0`) through `isUnit_matToCLM_iff`.  The
frozen `hAdomHeat` is the `p = 0`, `q = z`, `t' = T` slice of `hpkgBound`, with the width-2 base
kernel rewritten to the Gaussian by `ParametrixHEboundWiring.baseKernelW_zero_apply`
(`baseKernelW 2 0 τ p q = gaussDdim (2τ) (p − q)`).

## Honest scope

`K < 0` is genuinely curved (`curvedRNCMetric_ricci_trace_diag_ne`; satisfiability re-exported below)
and lies in the `K ≤ 0` global-inverse range — NOT secretly flat.  The ONLY carried residuals are the
mainline-standard Christoffel smoothness `hChr` and the all-`k` van-Vleck folded smoothness `hw`; the
coefficient bounds and nondegeneracy are DISCHARGED internally.  This closes the two heatOp defect
dominations that Section C (`hpkgBound`) and Section G (`hAdomHeat`) of the capstone consume.  It does
**not** derive the coefficient: `a₁ = R/6` still needs the rest of the heatOp/Levi/error-kernel
domination pile, the Duhamel assembly, and the coefficient extraction, and remains CONDITIONAL and
effectively FLAT-ONLY.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.GaussGaugeToHgauge
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef QIQTH.PullbackMetric
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ConstRadiusGateExport
open QIQTH.GaussianWidthTolerant QIQTH.A1R6CoreAtGate
open scoped BigOperators

namespace QIQTH.CurvedRNCHeatOpDomPkg

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-536 — `curvedRNC_heatOp_dom_pkg`.**  THE CONCRETE CURVED heatOp DEFECT-KERNEL width-2
    GAUSSIAN DOMINATION.  For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`), given
    ONLY the mainline Christoffel smoothness `hChr` and the amplitude-smoothness carry `hw`, there are
    gate parameters `0 < a < b < c` and a constant `C ≥ 0` such that the gated van-Vleck witness on the
    constant-radius flow-ball gate `constGate g^K gi^K hChr isCompact_singleton c` (seed `Kset = {0}`)
    satisfies BOTH:

    * `hpkgBound` (all `t'`): `∀ t' τ p q, 0 < τ → τ ≤ t' →
        |heatOp g^K gi^K (vanVleckGatedWitness …) τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`;
    * `hAdomHeat` (frozen `p = 0` window): `∀ τ ∈ (0,T], ∀ z,
        |heatOp g^K gi^K (vanVleckGatedWitness …) τ 0 z| ≤ (C·(1+T))·gaussDdim (2τ) (0 − z)`.

    Both are the EXACT capstone binders (Section C `hpkgBound`, Section G `hAdomHeat`).  The bound is
    produced by the banked `gatedWitnessN1_hEboundW_le_lin_CONST`, with `hgnd` discharged via
    `curvedRNCMetric_det_pos` and the two coefficient bounds via `hCoeffU0_vanVleck` +
    `uniformCoeffLinear_bound`; `hAdomHeat` is the `p=0` slice of `hpkgBound` (`baseKernelW_zero_apply`).
    NOT `a₁ = R/6`. -/
theorem curvedRNC_heatOp_dom_pkg
    (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
          (curvedRNCMetric K) (curvedRNCInv K))) k : Point n → ℝ))
    (T : ℝ) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      (∀ (t' : ℝ), ∀ (τ : ℝ), ∀ (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric K) (curvedRNCInv K)
            (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) ∧
      (∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp (curvedRNCMetric K) (curvedRNCInv K)
            (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b) τ (0 : Point n) z|
          ≤ (C * (1 + T)) * gaussDdim (2 * τ) (0 - z)) := by
  classical
  -- ── the geometry / gauge members for `g^K` (all banked).
  have hg : ∀ (a b : Fin n), ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => curvedRNCMetric K y a b) :=
    fun a b => curvedRNCMetric_contDiff K a b
  have hgsymm : ∀ (y : Point n) a b, curvedRNCMetric K y a b = curvedRNCMetric K y b a :=
    fun y a b => curvedRNCMetric_symm K y a b
  have hinvF : ∀ (y : Point n) a b,
      (∑ σ, curvedRNCMetric K y a σ * curvedRNCInv K y σ b) = if a = b then (1 : ℝ) else 0 :=
    fun y a b => curvedRNCMetric_hinvF K hK.le y a b
  have hg0 : ∀ i j, curvedRNCMetric K (0 : Point n) i j = if i = j then (1 : ℝ) else 0 :=
    fun i j => curvedRNCMetric_zero K i j
  have hdg0 : ∀ a b e, pd (fun y => curvedRNCMetric K y a b) e (0 : Point n) = 0 :=
    fun a b e => curvedRNCMetric_pd_zero K a b e
  -- ── nondegeneracy `hgnd` from `det g^K > 0` (`K ≤ 0`).
  have hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => curvedRNCMetric K y a b)) := by
    intro y
    rw [isUnit_matToCLM_iff (fun a b => curvedRNCMetric K y a b), Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (curvedRNCMetric_det_pos K hK.le y).ne'
  -- ── the singleton-seed frame condition (`g^K = δ` at the RNC centre `0`).
  have hframeK : ∀ q ∈ ({(0 : Point n)} : Set (Point n)), ∀ i j,
      curvedRNCMetric K q i j = (if i = j then (1 : ℝ) else 0) := by
    intro q hq i j
    rw [Set.mem_singleton_iff.mp hq]; exact hg0 i j
  -- ── the two amplitude-coefficient bounds (as in the flat `_vanVleck_final`).
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck (curvedRNCMetric K) (curvedRNCInv K) hg hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K))
      (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound (curvedRNCMetric K) (curvedRNCInv K) hg hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric K))
      (fun j => transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
        (curvedRNCMetric K) (curvedRNCInv K)) (j + 1)) (hw 1)
  set ρc : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρc := lt_min hρ0 hρ1
  -- ── the banked CONCRETE constant-radius width-2 defect bound.
  obtain ⟨a, b, C, c, ha, hab, hCnn, hbc, hbound, -, -, -⟩ :=
    gatedWitnessN1_hEboundW_le_lin_CONST (curvedRNCMetric K) (curvedRNCInv K) hg hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric K))
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
        (curvedRNCMetric K) (curvedRNCInv K)))
      hw ρc C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
  refine ⟨a, b, C, c, ha, hab, hCnn, hbc, ?_, ?_⟩
  · -- hpkgBound: the all-`t'` width-2 bound (vanVleckGatedWitness/constGate = gatedKernel, defeq).
    intro t' τ p q hτ hτle
    exact hbound t' τ p q hτ hτle
  · -- hAdomHeat: the frozen `p = 0`, `q = z`, `t' = T` slice; `baseKernelW 2 0 → gaussDdim`.
    intro τ hτ hτle z
    have h := hbound T τ (0 : Point n) z hτ hτle
    rw [baseKernelW_zero_apply] at h
    exact h

/-- **★ J4-536 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The witness `g^K` underlying the
    concrete heatOp defect domination is genuinely curved: for `K ≠ 0` and `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) is nonzero.  So the domination is inhabited by a genuinely curved
    metric (`K < 0` ⊂ `K ≠ 0`), NOT the flat `δ`.  Curved-inhabited.  NOT `a₁ = R/6`. -/
theorem curvedRNC_heatOp_dom_pkg_curved_satisfiable (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne K hK hn c

end QIQTH.CurvedRNCHeatOpDomPkg

section AxiomChecks
open QIQTH.CurvedRNCHeatOpDomPkg
#print axioms curvedRNC_heatOp_dom_pkg
#print axioms curvedRNC_heatOp_dom_pkg_curved_satisfiable
end AxiomChecks
