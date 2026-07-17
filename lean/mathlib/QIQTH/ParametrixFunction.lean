/-
  ParametrixFunction — J4 of the Jacobi/van-Vleck campaign: the ASSEMBLY brick.

  Phase J4 (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md).  The previous bricks built the three
  ingredients of the Minakshisundaram–Pleijel / Seeley–DeWitt off-diagonal parametrix

      H_N(t,x,y) = (4πt)^{−d/2} e^{−r²/4t} · Θ(x,y)^{−1/2} · Σ_{k≤N} u_k(x,y) · t^k

  in Riemann normal coordinates centred at `y`:
    * J1 — the van-Vleck–Morette determinant `Θ = (√det g̃)⁻¹`   (`QIQTH.VanVleck.vanVleck`);
    * J2 — the RNC radial coordinate `r² = ‖v‖²`                 (`QIQTH.RadialDistance.rncRadialSq`);
    * J3 — the transport-ODE solution operator `radialTransportSolve k f = ∫₀¹ s^{k−1} f(s•v) ds`,
           which SOLVES the DeWitt radial transport ODE `(k + r∂_r) u_k = f`
           (`QIQTH.RadialTransport.radialTransportSolve_transport_eq`).

  This file ASSEMBLES those into (1) the concrete off-diagonal transport coefficients
  `transportCoeff T : ℕ → Point n → ℝ` — the DeWitt recursion `u_{k+1} = radialTransportSolve
  (k+1) (T u_k)`, driven by a CARRIED transport-source operator `T` — proving each `u_k` satisfies
  the transport recursion `(k+1 + r∂_r) u_{k+1} = T u_k`; and (2) the parametrix FUNCTION, obtained
  by instantiating the existing ansatz `QIQTH.HeatParametrixAnsatz.heatParametrix` with `Θ := vanVleck G`
  and `u := transportCoeff T`, plus its diagonal value.

  ⚠ HONEST SCOPE (binding).  This is the J4 ASSEMBLY.  The transport-SOURCE operator `T` (the
  DeWitt operator `Θ^{−1/2} Δ_g (Θ^{1/2} ·)`) is CARRIED ABSTRACTLY here — wiring its concrete
  `Δ_g`/van-Vleck form and computing the residual `(∂_t − Δ_g) H_N` is J5's analytic job; deriving
  `u_1(0) = R/6` from the Seeley–DeWitt recursion is J6 (the Riemannian-heat-kernel wall).  The
  `ContDiff`/`det G 0 = 1` hypotheses are carried EXACTLY as the source lemmas (J1/J3) demand —
  genuine, load-bearing, non-vacuous.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.VanVleck
import QIQTH.RadialDistance
import QIQTH.RadialTransport
import QIQTH.HeatParametrixAnsatz

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RadialTransport QIQTH.VanVleck
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.HeatKernelA1

namespace QIQTH.ParametrixFunction

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### #1 — the concrete off-diagonal transport coefficients `u_k` via J3.

The DeWitt heat coefficients built by the radial transport engine.  `T : (Point n → ℝ) → (Point n → ℝ)`
is the CARRIED transport-source operator (`T u_{k−1}` = the DeWitt source, abstractly `Θ^{−1/2}Δ_g(Θ^{1/2}·)`;
its concrete wiring is J5).  The recursion is `u_0 ≡ 1`, `u_{k+1} = radialTransportSolve (k+1) (T u_k)`. -/
noncomputable def transportCoeff (T : (Point n → ℝ) → (Point n → ℝ)) : ℕ → Point n → ℝ
  | 0 => fun _ => 1
  | (k + 1) => radialTransportSolve (k + 1) (T (transportCoeff T k))

/-- **`u_0 ≡ 1`** — the base DeWitt coefficient (definitional). -/
theorem transportCoeff_zero (T : (Point n → ℝ) → (Point n → ℝ)) :
    transportCoeff T 0 = (fun _ => (1 : ℝ)) := rfl

/-- The recursion unfolding: `u_{k+1} = radialTransportSolve (k+1) (T u_k)` (definitional). -/
theorem transportCoeff_succ (T : (Point n → ℝ) → (Point n → ℝ)) (k : ℕ) :
    transportCoeff T (k + 1) = radialTransportSolve (k + 1) (T (transportCoeff T k)) := rfl

/-- **THE J4 payoff (#1) — the DeWitt transport recursion for the concrete off-diagonal `u_k`.**
    For every `k`, GIVEN the genuine smoothness `ContDiff ℝ ⊤ (T u_k)` of the transport source demanded
    by J3's Leibniz/IBP steps, the coefficient `u_{k+1} = transportCoeff T (k+1)` satisfies the radial
    transport ODE `(k+1 + r∂_r) u_{k+1} = T u_k`:

      (k+1) · u_{k+1}(v) + radialDeriv(u_{k+1})(v) = (T u_k)(v).

    This is exactly J3's `radialTransportSolve_transport_eq` at level `k+1`, transported onto the
    recursively-defined coefficient family. -/
theorem transportCoeff_succ_transport_eq (T : (Point n → ℝ) → (Point n → ℝ)) (k : ℕ)
    (hf : ContDiff ℝ ⊤ (T (transportCoeff T k))) (v : Point n) :
    ((k : ℝ) + 1) * transportCoeff T (k + 1) v
      + radialDeriv (transportCoeff T (k + 1)) v = T (transportCoeff T k) v := by
  have h := radialTransportSolve_transport_eq (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    (T (transportCoeff T k)) hf v
  rw [transportCoeff_succ]
  rw [Nat.cast_add, Nat.cast_one] at h
  exact h

/-! ### #2 — the parametrix FUNCTION (reusing the existing ansatz).

We instantiate the built ansatz `QIQTH.HeatParametrixAnsatz.heatParametrix` — whose convention
(`Θ : Point n → ℝ`, `u : ℕ → Point n → ℝ`, and `H_N = gaussDdim t v · Θ(v)^{−1/2} · Σ_{k≤N} u_k(v)·t^k`)
matches ours exactly — with `Θ := vanVleck G` (J1) and `u := transportCoeff T` (J3).  The flat Gaussian
`gaussDdim t v` carries the RNC radial factor `e^{−r²/4t}` with `r² = ‖v‖²` (J2's `rncRadialSq`). -/
noncomputable def heatParametrixFn (N : ℕ) (G : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t : ℝ) (v : Point n) : ℝ :=
  heatParametrix N (vanVleck G) (transportCoeff T) t v

/-- Unfolding: `heatParametrixFn` is the ansatz `heatParametrix` at `Θ := vanVleck G`,
    `u := transportCoeff T` (definitional). -/
theorem heatParametrixFn_eq (N : ℕ) (G : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t : ℝ) (v : Point n) :
    heatParametrixFn N G T t v = heatParametrix N (vanVleck G) (transportCoeff T) t v := rfl

/-- **The explicit product form of the parametrix function.**
    `H_N(t,v) = gaussDdim t v · (vanVleck G v)^{−1/2} · Σ_{k≤N} (transportCoeff T k v)·t^k`. -/
theorem heatParametrixFn_apply (N : ℕ) (G : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t : ℝ) (v : Point n) :
    heatParametrixFn N G T t v
      = gaussDdim t v * (vanVleck G v) ^ (-(1 : ℝ) / 2)
        * ∑ k ∈ Finset.range (N + 1), transportCoeff T k v * t ^ k := rfl

/-! ### #3 — the diagonal value at the RNC centre `v = 0`. -/

/-- **#3 — the parametrix function on the diagonal.**  At the RNC centre `v = 0`, where the van-Vleck
    determinant is `Θ(0) = 1` (J1's `vanVleck_zero`, GIVEN `det g̃(0) = 1`), the `Θ^{−1/2}` factor is
    `1`, so

      H_N(t,0) = gaussDdim t 0 · Σ_{k≤N} u_k(0)·t^k .

    (`gaussDdim t 0 = (√(4πt))⁻ⁿ` is the `(4πt)^{−d/2}` prefactor, `heatParametrix_diagonal`.) -/
theorem heatParametrixFn_diagonal (N : ℕ) (G : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t : ℝ) (hG0 : Matrix.det (G 0) = 1) :
    heatParametrixFn N G T t (0 : Point n)
      = gaussDdim t (0 : Point n)
        * ∑ k ∈ Finset.range (N + 1), transportCoeff T k (0 : Point n) * t ^ k := by
  rw [heatParametrixFn_eq]
  exact heatParametrix_diagonal N (vanVleck G) (transportCoeff T) t (vanVleck_zero G hG0)

/-- **#3 — the diagonal expansion with the DeWitt prefactor.**
    `H_N(t,0) = (√(4πt))⁻ⁿ · Σ_{k≤N} u_k(0)·t^k` — the `(4πt)^{−d/2}` heat-trace prefactor times the
    DeWitt polynomial in `t`, with `u_0(0) = 1`. -/
theorem heatParametrixFn_diagonal_expansion (N : ℕ) (G : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t : ℝ) (hG0 : Matrix.det (G 0) = 1) :
    heatParametrixFn N G T t (0 : Point n)
      = (heatKernel1D t 0) ^ n
        * ∑ k ∈ Finset.range (N + 1), transportCoeff T k (0 : Point n) * t ^ k := by
  rw [heatParametrixFn_eq]
  exact heatParametrix_diagonal_expansion N (vanVleck G) (transportCoeff T) t (vanVleck_zero G hG0)

/-- **#3 — the diagonal `a₁`-coefficient structure of the assembled parametrix.**  For `N ≥ 1`, using the
    concrete `u_0(0) = transportCoeff T 0 0 = 1` (J3 base) and carrying the DeWitt normalization
    `u_1(0) = R/6` as a labelled hypothesis (J6, not derived here):

      H_N(t,0) = (4πt)^{−d/2} · (1 + (R/6)·t + Σ_{2≤k≤N} u_k(0)·t^k).

    This is the leading short-time structure the heat trace `Tr e^{−tΔ}` consumes; the `R/6` is the
    labelled `a₁` input (the Seeley–DeWitt wall, J6). -/
theorem heatParametrixFn_diagonal_a1 (N : ℕ) (G : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ)) (t R : ℝ) (hG0 : Matrix.det (G 0) = 1) (hN : 1 ≤ N)
    (hu1 : transportCoeff T 1 (0 : Point n) = R / 6) :
    heatParametrixFn N G T t (0 : Point n)
      = (heatKernel1D t 0) ^ n
        * (1 + (R / 6) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1), transportCoeff T k (0 : Point n) * t ^ k) := by
  rw [heatParametrixFn_eq]
  refine heatParametrix_diagonal_a1 N (vanVleck G) (transportCoeff T) t R
    (vanVleck_zero G hG0) hN ?_ hu1
  rw [transportCoeff_zero]

end QIQTH.ParametrixFunction
