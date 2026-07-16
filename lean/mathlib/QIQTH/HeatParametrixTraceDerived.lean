/-
  HeatParametrixTraceDerived — the P2 capstone: the parametrix diagonal heat-trace `a₁` coefficient
  `= (1/6)∫R` with the `t¹`-coefficient's `u₁ = τ/6` DERIVED from the transport recursion, not
  carried as a bare `scalarR/6` label.

  WHAT IS BUILT HERE (the honest boundary — read it).
  `QIQTH.HeatParametrixTrace.parametrixDiagTrace_a1` gives the parametrix diagonal heat trace under
  the two DeWitt diagonal normalizations `ud₀(x,x) = 1` and `ud₁(x,x) = R(x)/6`, where the `R/6`
  was a labelled *carried* hypothesis.  This file replaces that carried label at each sample point:
  feeding a family `T : ι → TransportRecursion n` of Minakshisundaram–DeWitt transport recursions
  (one per sample point `pt i = (T i).x₀`) and the key hypothesis that the trace's `ud₁` at each
  sample point EQUALS the transport recursion's own `u₁` there, we DERIVE `ud₁(pt i) = τ_i/6` from
  `QIQTH.HeatTransportRecursion.TransportRecursion.u1_diag_eq_tau_div_six` (itself derived by
  applying `Δ_g` to the van-Vleck 2-jet `u0Quad = (1/12)Ric`).  The resulting `t¹` coefficient is

      W₁ = (1/6) · Σ_i τ_i · w(pt i)  =  (1/6) · Σ_i (tr Ric at pt i) · w(pt i)  =  (1/6)·∫R,

  the Seeley–DeWitt `a₁ = (1/6)∫R` heat-trace coefficient, with `R/6` now DERIVED from the
  transport recursion at each sample point rather than carried as a bare label.  The sphere witness
  `sphereParametrixTraceA1` exhibits it at NONZERO curvature (`τ = 2`), so it is not vacuous.

  ⚠ HONEST SCOPE (unchanged from the rest of the P2 line; this only removes the `R/6` *label*):
    • it is STILL the PARAMETRIX trace, NOT the true `Tr e^{−tΔ}` — that needs the Levi/Duhamel
      construction (kernel existence + error control), the analytic wall absent from every proof
      assistant;
    • the "trace integral" is a FINITE-SAMPLE `Finset` sum with a carried volume density `w`, NOT
      the measure-theoretic Riemannian-volume integral over the manifold;
    • the transport recursion's own diagonal recursion `udiag_rec` (the diagonal collapse
      `(k+1)u_{k+1}(x₀) = Δ_g u_k(x₀)`) is CARRIED as a structure field — the off-diagonal
      radial-ODE derivation is the wall.
  So this is NOT the general `a₁ = R/6` for the true kernel, and NOT numerical-`G`.  What it DOES
  add over `parametrixDiagTrace_a1`: the `t¹` coefficient's `u₁ = τ/6` is now derived from the
  transport recursion at each sample point (via `u1_diag_eq_tau_div_six`), not carried.
  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.HeatParametrixTrace
import QIQTH.HeatTransportRecursion

open Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.HeatParametrixTrace QIQTH.HeatTransportRecursion QIQTH.DeWittDiagonal

namespace QIQTH.HeatParametrixTraceDerived

variable {n : ℕ} {ι : Type*}

set_option maxHeartbeats 800000

/-! ### #1 — the derived-`u₁` parametrix diagonal heat trace `a₁ = (1/6)∫R`. -/

/-- **#1 — the parametrix diagonal heat-trace `a₁` coefficient with `u₁ = τ/6` DERIVED.**

    Feed a family `T : ι → TransportRecursion n` (one transport recursion per sample point) with
    the sample points `pt i = (T i).x₀` (`hpt`), the volume density `w`, and diagonal Seeley
    coefficients `ud`.  The two inputs are:
      * `hud0` — the DeWitt normalization `ud₀(pt i) = 1` (carried, as before);
      * `hud1_derived` — the KEY: the trace's `ud₁` at each sample point equals the transport
        recursion's own `u₁` there, `ud₁(pt i) = (T i).u 1 (pt i)`.
    Using `(T i).u1_diag_eq_tau_div_six` (which DERIVES `(T i).u 1 (T i).x₀ = τ_i/6` from `Δ_g` on
    the van-Vleck 2-jet), the `t¹` coefficient becomes `(1/6)·Σ_i τ_i·w(pt i)`:

      Tr H_N(t) = (4πt)^{−d/2} · (Vol + (1/6)·(Σ_i τ_i·w(pt i))·t + Σ_{2≤k≤N} W_k·t^k),

    with `Vol = Σ_i w(pt i)` and `τ_i = (T i).jet.tau` the scalar curvature at `pt i`.  Here the
    `R/6` of the `a₁ = (1/6)∫R` heat-trace coefficient is DERIVED from the transport recursion at
    each sample point, not carried as a bare `scalarR/6` label.

    ⚠ Parametrix-level, finite-sample, with the transport recursion's `udiag_rec` itself carried:
    NOT the true kernel trace `Tr e^{−tΔ}` (Levi/Duhamel), and NOT the general `a₁ = R/6`. -/
theorem parametrixDiagTrace_a1_derived (N : ℕ) (T : ι → TransportRecursion n)
    (ud : ℕ → Point n → ℝ) (w : Point n → ℝ) (s : Finset ι) (pt : ι → Point n) (t : ℝ)
    (hN : 1 ≤ N) (hpt : ∀ i, pt i = (T i).x₀)
    (hud0 : ∀ i, ud 0 (pt i) = 1)
    (hud1_derived : ∀ i, ud 1 (pt i) = (T i).u 1 (pt i)) :
    parametrixDiagTrace N ud w s pt t
      = (heatKernel1D t 0) ^ n
        * ((∑ i ∈ s, w (pt i))
            + (1 / 6) * (∑ i ∈ s, (T i).jet.tau * w (pt i)) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), diagTraceCoeff ud w s pt k * t ^ k) := by
  -- Derive `ud₁(pt i) = τ_i/6` from the transport recursion at each sample point.
  have hud1 : ∀ i, ud 1 (pt i) = (T i).jet.tau / 6 := by
    intro i
    rw [hud1_derived i, hpt i]
    exact (T i).u1_diag_eq_tau_div_six
  rw [parametrixDiagTrace_expansion N ud w s pt t]
  congr 1
  have hW0 : diagTraceCoeff ud w s pt 0 = ∑ i ∈ s, w (pt i) := by
    unfold diagTraceCoeff
    apply Finset.sum_congr rfl
    intro i _
    rw [hud0 i, one_mul]
  have hW1 : diagTraceCoeff ud w s pt 1
      = (1 / 6) * ∑ i ∈ s, (T i).jet.tau * w (pt i) := by
    unfold diagTraceCoeff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hud1 i]; ring
  rw [sum_range_split_two (fun k => diagTraceCoeff ud w s pt k * t ^ k) N hN]
  simp only [pow_zero, mul_one, pow_one, hW0, hW1]

/-! ### #2 — `τ = tr Ric`, so the `a₁` coefficient is manifestly `(1/6)·∫ tr Ric`. -/

/-- **#2 (connective) — `τ = tr Ric`.** The transport-recursion jet's scalar curvature `τ` is the
    trace of its Ricci tensor (`NormalCoordJet.tau_eq_trace`). -/
theorem transportJetTau_eq_trace_Ric (T : TransportRecursion n) :
    T.jet.tau = ∑ a, T.jet.Ric a a :=
  T.jet.tau_eq_trace

/-- **#2′ — the `a₁` coefficient in manifest `tr Ric` form.** Rewriting each `τ_i` as `tr Ric` at
    `pt i`, the `t¹` coefficient of the derived parametrix trace is `(1/6)·Σ_i (Σ_a Ric_aa)·w(pt i)`
    — the integrated scalar curvature `(1/6)∫R` displayed as `(1/6)∫ tr Ric`. -/
theorem parametrixDiagTrace_a1_derived_trace_Ric (N : ℕ) (T : ι → TransportRecursion n)
    (ud : ℕ → Point n → ℝ) (w : Point n → ℝ) (s : Finset ι) (pt : ι → Point n) (t : ℝ)
    (hN : 1 ≤ N) (hpt : ∀ i, pt i = (T i).x₀)
    (hud0 : ∀ i, ud 0 (pt i) = 1)
    (hud1_derived : ∀ i, ud 1 (pt i) = (T i).u 1 (pt i)) :
    parametrixDiagTrace N ud w s pt t
      = (heatKernel1D t 0) ^ n
        * ((∑ i ∈ s, w (pt i))
            + (1 / 6) * (∑ i ∈ s, (∑ a, (T i).jet.Ric a a) * w (pt i)) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), diagTraceCoeff ud w s pt k * t ^ k) := by
  rw [parametrixDiagTrace_a1_derived N T ud w s pt t hN hpt hud0 hud1_derived]
  have hcoeff : (∑ i ∈ s, (T i).jet.tau * w (pt i))
      = ∑ i ∈ s, (∑ a, (T i).jet.Ric a a) * w (pt i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [transportJetTau_eq_trace_Ric (T i)]
  rw [hcoeff]

/-! ### #3 — the sphere witness (`τ = 2`, nonzero curvature, non-vacuous). -/

/-- The trace's diagonal Seeley coefficients for the sphere witness: `ud₀ ≡ 1` (the DeWitt
    normalization — note the transport recursion's own `u₀` is the van-Vleck 2-jet, which VANISHES
    at the center, so `ud₀` is normalized separately), and for `k ≥ 1` the transport recursion's
    own coefficients (so `ud₁` at the center is `sphereTransportRecursion.u 1 = 1/3 = τ/6`). -/
noncomputable def sphereTraceUd : ℕ → Point 2 → ℝ :=
  fun k => if k = 0 then (fun _ => 1) else sphereTransportRecursion.u k

/-- **#3 — the sphere witness.** The derived-`u₁` parametrix diagonal heat trace over a finite
    sample `s` of unit-2-sphere center points, at `N = 1`.  The `a₁` (`t¹`) coefficient is
    `(1/6)·Σ_i 2·w(x₀)` with the `2 = τ = tr Ric` DERIVED from the sphere transport recursion — a
    NONZERO-curvature, non-vacuous instance of `parametrixDiagTrace_a1_derived`. -/
theorem sphereParametrixTraceA1 {ι : Type*} (s : Finset ι) (w : Point 2 → ℝ) (t : ℝ) :
    parametrixDiagTrace 1 sphereTraceUd w s (fun _ => sphereTransportRecursion.x₀) t
      = (heatKernel1D t 0) ^ 2
        * ((∑ i ∈ s, w sphereTransportRecursion.x₀)
            + (1 / 6) * (∑ i ∈ s, 2 * w sphereTransportRecursion.x₀) * t) := by
  rw [parametrixDiagTrace_a1_derived 1 (fun _ : ι => sphereTransportRecursion) sphereTraceUd w s
        (fun _ => sphereTransportRecursion.x₀) t le_rfl (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl)]
  have htau : (sphereTransportRecursion.jet.tau : ℝ) = 2 := rfl
  simp only [show (1 : ℕ) + 1 = 2 from rfl, Finset.Ico_self, Finset.sum_empty, add_zero, htau]

end QIQTH.HeatParametrixTraceDerived
