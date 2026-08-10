import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.TransportOpSmoothness

/-!
# J4-532 — discharging the transport-coefficient moduli carry `hMod` for `g^K`

`QIQTH.CurvedRNCBaseWitnessDom.curvedRNC_baseWitness_dom` (J4-531) assembled the first curved
base-witness Gaussian domination for `g^K = curvedRNCMetric K` (`K ≤ 0`) modulo TWO carried
geometric hypotheses:

* `hMod`   — the transport-coefficient modulus bound `|∑ₖ uₖ(w)·τᵏ| ≤ C_u`;
* `hPhase` — the Gaussian-phase transfer `gaussDdim τ w ≤ C_φ · gaussDdim (λτ) z`.

This brick discharges **`hMod`** for the order-1 parametrix (`N = 1`, `Finset.range 2`).  The
transport sum is
```
∑ k ∈ Finset.range 2, uₖ(w)·τᵏ  =  u₀(w)·1 + u₁(w)·τ  =  1 + u₁(w)·τ ,
```
using `u₀ ≡ 1` (`transportCoeff_zero`, definitional) and
`u₁ = transportCoeff (transportOp (vanVleck g^K) g^K gi^K) 1
    = radialTransportSolve 1 (transportOp (vanVleck g^K) g^K gi^K u₀)`.

**How `u₁` is bounded.**  `u₁` is CONTINUOUS: its ray-integral source `transportOp (vanVleck g^K)
g^K gi^K (fun _ ↦ 1)` is `C^∞` (`TransportOpSmoothness.transportOp_preserves_contDiff`, from the
banked `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff` / `curvedRNCMetric_hgpos`), so the solve
`radialTransportSolve 1 (·)` is `C¹` (`TransportOpSmoothness.radialTransportSolve_contDiff_one`),
hence continuous.  On any COMPACT `Wset` a continuous function is bounded
(`IsCompact.exists_bound_of_continuousOn`): `|u₁(w)| ≤ M`.  Then
`|1 + u₁(w)·τ| ≤ 1 + |M|·|τmax| =: C_u` for `0 ≤ τ ≤ τmax`.

## Honest scope

`K < 0` is genuinely curved (`Ric(0) = (n−1)Kδ ≠ 0`); `C_u = 1 + |M|·|τmax| ≥ 1 > 0` is finite and
the domain is inhabited (any nonempty compact, e.g. a closed ball), so the bound is NOT vacuous.

⚠ The `hMod` binder of `curvedRNC_baseWitness_dom` quantifies `∀ z τ` UNGUARDED, with
`w := uniformInverseChart g^K gi^K hChr hKset z 0`.  `uniformInverseChart` is a `.choose` (no
continuity), so the chart-image over ALL `z` is not honestly contained in any compact `Wset` — the
same far-reach obstruction catalogued in `GeomPTransportAssess` (Part A).  Hence the moduli bound is
delivered over an arbitrary compact `Wset`: it discharges `hMod` POINTWISE for every `z` whose
chart-image lands in `Wset` (i.e. on the chart's finite reach, where the gate is supported).  The
only residual to the literal unguarded binder is that far-reach range fact — NOT a new gap.  This is
one of ~30–40 curved heat-kernel dominations and does **not** derive the coefficient.  `a₁ = R/6`
remains CONDITIONAL and effectively FLAT-ONLY; after this brick the base-witness domination is modulo
ONLY the phase transfer `hPhase`.
-/

open QIQTH.Curvature QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialTransport
open QIQTH.TransportOpSmoothness
open scoped BigOperators

namespace QIQTH.CurvedRNCModuliBound

variable {n : ℕ}

/-- **★ `curvedRNC_moduli_bound` — the order-1 transport-coefficient modulus bound for `g^K`.**
    For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`), any compact base-point set
    `Wset`, and any time cap `τmax`, there is a FINITE `C_u > 0` with
    ```
    |∑ k ∈ Finset.range 2, uₖ(w)·τᵏ| ≤ C_u    for all w ∈ Wset, 0 ≤ τ ≤ τmax,
    ```
    where `uₖ = transportCoeff (transportOp (vanVleck g^K) g^K gi^K) k`.  The `k = 0` term is `1`
    (`u₀ ≡ 1`, `transportCoeff_zero`); the `k = 1` term is `u₁(w)·τ`, and `u₁` — being continuous
    (its `C^∞` transport source `transportOp (vanVleck g^K) g^K gi^K 1` solved by the `C¹`
    ray-integral) — is bounded by some `M` on the compact `Wset`.  So `C_u := 1 + |M|·|τmax|`
    discharges the `hMod` carry of `curvedRNC_baseWitness_dom` on the chart's reach.  NOT `a₁ = R/6`. -/
theorem curvedRNC_moduli_bound (K : ℝ) (hK : K < 0)
    {Wset : Set (Point n)} (hWset : IsCompact Wset) (τmax : ℝ) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ w ∈ Wset, ∀ τ : ℝ, 0 ≤ τ → τ ≤ τmax →
      |∑ k ∈ Finset.range 2,
          transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
              (curvedRNCMetric K) (curvedRNCInv K)) k w * τ ^ k| ≤ Cu := by
  -- Banked smoothness of `g^K`, `gi^K`, and det-positivity (the geometric inputs of the source).
  have hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCMetric K y a b) :=
    fun a b => curvedRNCMetric_contDiff K a b
  have hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCInv K y a b) :=
    fun a b => curvedRNCInv_contDiff K hK.le a b
  have hgpos : ∀ v : Point n, 0 < Matrix.det (curvedRNCMetric K v) :=
    curvedRNCMetric_hgpos K hK.le
  -- The `u₁` source `T u₀ = transportOp (vanVleck g^K) g^K gi^K 1` is `C^∞`.
  have hTu0 : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K)
        (fun _ => (1 : ℝ))) :=
    transportOp_preserves_contDiff (curvedRNCMetric K) (curvedRNCInv K) hg hgi hgpos
      (fun _ => (1 : ℝ)) contDiff_const
  -- Hence `u₁ = radialTransportSolve 1 (T u₀)` is `C¹`, in particular continuous.
  have hu1cont : Continuous
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
        (curvedRNCInv K)) 1) :=
    (radialTransportSolve_contDiff_one 1
      (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K)
        (fun _ => (1 : ℝ))) hTu0).continuous
  -- Bound `|u₁|` on the compact `Wset`.
  obtain ⟨M, hM⟩ := hWset.exists_bound_of_continuousOn
    (f := transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
      (curvedRNCInv K)) 1) hu1cont.continuousOn
  refine ⟨1 + |M| * |τmax|, by positivity, ?_⟩
  intro w hw τ hτ0 hτmax
  have hMw : |transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
        (curvedRNCInv K)) 1 w| ≤ M := by
    have h := hM w hw; rwa [Real.norm_eq_abs] at h
  -- Collapse the order-1 transport sum: `u₀ ≡ 1`, so `∑ = 1 + u₁(w)·τ`.
  have hsum : ∑ k ∈ Finset.range 2,
        transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
          (curvedRNCInv K)) k w * τ ^ k
      = 1 + transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
          (curvedRNCInv K)) 1 w * τ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, transportCoeff_zero]
    simp only [pow_zero, mul_one, one_mul, pow_one]
  rw [hsum]
  calc |1 + transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
          (curvedRNCInv K)) 1 w * τ|
      ≤ |(1 : ℝ)| + |transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
          (curvedRNCInv K)) 1 w * τ| := abs_add_le _ _
    _ = 1 + |transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
          (curvedRNCInv K)) 1 w| * τ := by rw [abs_one, abs_mul, abs_of_nonneg hτ0]
    _ ≤ 1 + |M| * |τmax| := by
        have h1 : |transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
            (curvedRNCInv K)) 1 w| ≤ |M| := le_trans hMw (le_abs_self M)
        have h2 : τ ≤ |τmax| := le_trans hτmax (le_abs_self τmax)
        have h3 : |transportCoeff (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K)
            (curvedRNCInv K)) 1 w| * τ ≤ |M| * |τmax| :=
          mul_le_mul h1 h2 hτ0 (abs_nonneg M)
        linarith

end QIQTH.CurvedRNCModuliBound

section AxiomChecks
open QIQTH.CurvedRNCModuliBound
#print axioms curvedRNC_moduli_bound
end AxiomChecks
