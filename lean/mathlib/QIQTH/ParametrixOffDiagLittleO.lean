/-
  ParametrixOffDiagLittleO — the CAPSTONE of the M5 off-diagonal `O(1/t)` cancellation:  the FULL
  general-`v` statement `totalRadialO1_coeff(v) = o(‖v‖²)` near the RNC centre.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE.  The three centre-only faces of the off-diagonal `O(1/t)` cancellation —
      • VALUE   (c5, `totalRadialO1_coeff_center_vanishes`):     `coeff(0) = 0`,
      • GRADIENT (c6, `totalRadialO1_coeff_center_grad_vanishes`): `∂_e coeff(0) = 0`,
      • HESSIAN (c7, `totalRadialO1_coeff_center_hessian_vanishes`): `∂_a∂_b coeff(0) = 0`,
  are here PROMOTED to a single UNIFORM-near-centre statement by feeding them into the general-`v`
  second-order Peano (little-`o`) Taylor expansion (T1, `RNCExpansion.pd_taylor_two_peano`):

      `totalRadialO1_coeff g gi Θ u  =o[𝓝 0]  (fun v => ‖v‖²)`    (`totalRadialO1_coeff_isLittleO`).

  Since the `C²` Taylor polynomial of `coeff` at the centre is `coeff(0) + ∂coeff(0)·v + ½∂²coeff(0)[v,v]`
  and ALL THREE coefficient jets vanish (c5/c6/c7), the second-order Taylor polynomial is identically
  `0`, so `coeff(v) = coeff(v) − 0 = o(‖v‖²)`.  This closes the off-diagonal cancellation to curvature
  order UNIFORMLY (not merely at `v = 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HYPOTHESES (all genuine, load-bearing — NONE vacuous).
  • `hcoeffC2` is ASSEMBLED here (not carried) from the constituents' smoothness `hgiC`/`hC`/`hw0`
    via `ContDiff.add`/`.mul`/`.sub`/`.sum` + `radialDeriv`/`contDiff_pd`.
  • Value (c5), gradient (c6) discharged directly from the RNC gauge `hgi0`/`hdgi0`/`hΓ0` + smoothness
    + the van-Vleck flatness datum `hw0flat` (`∂w₀(0)=0`).
  • Hessian (c7) discharged by wiring `totalRadialO1_coeff_center_hessian_vanishes` — whose van-Vleck
    2-jet datum is stated over the FILE-PRIVATE field `coeffA` and therefore cannot be named across the
    module boundary.  It is supplied instead through the PUBLIC curvature converter
    `coeffA_center_hessian` (`∂_a∂_b A(0) = ⅓Ric − ½(∂Γ-divergence)`), so the van-Vleck 2-jet is
    carried in EXPLICIT Ricci form `hw0hessRicci` — the same `sqrtdet_pd_pd`-class datum as the
    transport equation, at Hessian order.  This is why the full normal-coordinate metric gauge suite
    (`hg`/`hg0`/`hdg0`/`hsymm`/`hinv`/`hgauge`) is carried: it is exactly what the public converter
    needs.  All of it is the SAME normal-coordinate gauge the √det chain carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  SCOPE.  This is the general-`v` off-diagonal `O(1/t)` cancellation to CURVATURE ORDER, uniform near
  the RNC centre.  It inherits the van-Vleck 2-jet + RNC gauge.  It is NOT the full all-orders
  general-`v` `= 0` (the exact transport identity, ROUTE (b), remains absent), and it is NOT
  `a₁ = R/6` (M6 parametrix convergence remains).  No `sorry`, no new axioms, no vacuous hypotheses.
  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1.
-/
import Mathlib
import QIQTH.RNCTaylorPeano
import QIQTH.ParametrixResidualO1Total
import QIQTH.ParametrixOffDiagCancellation
import QIQTH.ParametrixHessianCancellation

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCExpansion
open QIQTH.HeatResidualBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ THE CAPSTONE — the FULL general-`v` off-diagonal `O(1/t)` cancellation to curvature order.**
    Near the RNC centre the assembled leading `O(1/t)` coefficient is `o(‖v‖²)`:
        `totalRadialO1_coeff g gi Θ u  =o[𝓝 0]  (fun v => ‖v‖²)` .
    Promotes the centre-only value (c5) / gradient (c6) / Hessian (c7) cancellations to a single
    uniform-near-centre little-`o`, via the general-`v` second-order Peano Taylor expansion (T1).
    The `C²` Taylor polynomial of `coeff` at the centre is identically `0` (all three jets vanish),
    so `coeff(v) = o(‖v‖²)`.  Inherits the van-Vleck 2-jet (`hw0flat`, `hw0hessRicci`) + the RNC gauge.
    NOT the exact general-`v` transport identity, NOT `a₁ = R/6`. -/
theorem totalRadialO1_coeff_isLittleO
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw0 : ContDiff ℝ ⊤ (foldedCoeff Θ u 0))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0) :
    (fun v => totalRadialO1_coeff g gi Θ u v) =o[nhds (0 : Point n)] (fun v => ‖v‖ ^ 2) := by
  -- ══ VALUE face (c5). ══
  have hval : totalRadialO1_coeff g gi Θ u (0 : Point n) = 0 :=
    totalRadialO1_coeff_center_vanishes g gi Θ u (fun i => by rw [hgi0 i i]; simp)
  -- ══ GRADIENT face (c6). ══
  have hgrad : ∀ e, pd (fun v => totalRadialO1_coeff g gi Θ u v) e (0 : Point n) = 0 :=
    fun e => totalRadialO1_coeff_center_grad_vanishes g gi Θ u hgiC hC hw0 hgi0 hdgi0 hΓ0 hw0flat e
  -- ══ HESSIAN face (c7), wired through the PUBLIC curvature converter (private `coeffA` unnameable). ══
  have hhess : ∀ a b, pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) b y) a (0 : Point n)
      = 0 := by
    intro a b
    refine totalRadialO1_coeff_center_hessian_vanishes g gi Θ u hgiC hC hw0 hgi0 hdgi0 hΓ0 ?_ a b
    intro a' b'
    rw [coeffA_center_hessian g gi hg hgiC hC hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge a' b']
    linear_combination hw0hessRicci a' b'
  -- ══ ContDiff of the assembled coefficient (assembled, not carried). ══
  have hTerm2 : ContDiff ℝ ⊤ (fun v : Point n => radialDeriv (foldedCoeff Θ u 0) v) := by
    have hrw : (fun v : Point n => radialDeriv (foldedCoeff Θ u 0) v)
        = (fun v => ∑ i, v i * pd (foldedCoeff Θ u 0) i v) := rfl
    rw [hrw]
    exact ContDiff.sum fun i _ => (coord_contDiff i).mul (contDiff_pd (foldedCoeff Θ u 0) hw0 i)
  have hT1 : ContDiff ℝ ⊤ (fun v : Point n =>
      ((1 / 2) * (∑ i, (gi v i i - 1))
          - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
        * foldedCoeff Θ u 0 v) :=
    ((contDiff_const.mul (ContDiff.sum fun i _ => (hgiC i i).sub contDiff_const)).sub
      (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun k _ =>
        ((hgiC i j).mul (hC k i j)).mul (coord_contDiff k)))).mul hw0
  have hT3 : ContDiff ℝ ⊤ (fun v : Point n =>
      (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd (foldedCoeff Θ u 0) j v + v j * pd (foldedCoeff Θ u 0) i v))) :=
    contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      ((hgiC i j).sub contDiff_const).mul
        (((coord_contDiff i).mul (contDiff_pd (foldedCoeff Θ u 0) hw0 j)).add
          ((coord_contDiff j).mul (contDiff_pd (foldedCoeff Θ u 0) hw0 i))))
  have hcoeffCD : ContDiff ℝ ⊤ (fun v => totalRadialO1_coeff g gi Θ u v) :=
    (hT1.add hTerm2).add hT3
  have hf : ContDiffAt ℝ 2 (fun v => totalRadialO1_coeff g gi Θ u v) 0 :=
    hcoeffCD.contDiffAt.of_le le_top
  -- ══ Feed the general-`v` second-order Peano Taylor (T1); the polynomial is identically 0. ══
  have hpeano := QIQTH.RNCExpansion.pd_taylor_two_peano
    (fun v => totalRadialO1_coeff g gi Θ u v) hf
  refine hpeano.congr_left (fun x => ?_)
  have h1 : (∑ i, pd (fun v => totalRadialO1_coeff g gi Θ u v) i 0 * x i) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hgrad i]; ring
  have h2 : (∑ i, ∑ j, pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) j y) i 0
      * x i * x j) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hhess i j]; ring
  show totalRadialO1_coeff g gi Θ u x - totalRadialO1_coeff g gi Θ u 0
      - (∑ i, pd (fun v => totalRadialO1_coeff g gi Θ u v) i 0 * x i)
      - (1 / 2) * ∑ i, ∑ j, pd (fun y => pd (fun v => totalRadialO1_coeff g gi Θ u v) j y) i 0
          * x i * x j
      = totalRadialO1_coeff g gi Θ u x
  rw [hval, h1, h2]; ring

end QIQTH.HeatResidualBound
