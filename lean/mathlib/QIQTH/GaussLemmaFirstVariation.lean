/-
  GaussLemmaFirstVariation — the FIRST-VARIATION / energy-conservation content of the Gauss lemma
  for the geodesic exponential map, toward discharging `hGauss` (brick J4-341, the hGauss derivation
  campaign of the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one of the four labelled inputs of `a1_R6_from_labelled`
  (J4-340), and this campaign works toward discharging it for the exp-pullback normal-form metric.
  This file delivers the RADIAL LEG of that program (the metric-compatible energy identity along a
  geodesic).  Nothing here builds normal coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  R0 — THE COMPLETE BANK INVENTORY (exp-map / geodesic / variational machinery)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Notation.  `Point n = Fin n → ℝ`.  Ambient metric `g : Point n → Fin n → Fin n → ℝ`, inverse `gi`.
  `christoffel g gi μ ν ρ x = ½ gⁱ(μα)(∂_ν g_{αρ}+∂_ρ g_{αν}−∂_α g_{νρ})` (`QIQTH.Curvature`).
  `pd f i x = ∂ᵢ f` (coordinate partial).

  (1) THE EXPONENTIAL MAP is a confinement `Classical.choose` (opaque body; reason only via the
      spec lemmas):
        • `expMap g gi hC p v = (expTube g gi hC p v 1).1`  (`QIQTH.ExpMap` :748).
        • `expTube g gi hC p v : ℝ → Point n × Point n` is the confined geodesic PHASE curve; its
          defining property is `expTube_spec` (:766): for `‖v‖ ≤ expRho`,
            `expTube p v 0 = (p, v)`  ∧
            `∀ t ∈ Ioo (-2) 2, HasDerivAt (expTube p v) (geodesicField g gi (expTube p v t)) t`  ∧
            confinement `‖expTube p v t − (p,0)‖ ≤ expConst·‖v‖` on `[0,1]`.
        • `expRho`, `expConst`, `expTube` are `[irreducible]` — banked reasoning is through
          `expTube_spec` only (the DEFEQ lesson).
        • Banked value-jets: `hasStrictFDerivAt_expMap` (S5, D exp_p(0)=id), `expMap_contDiffOn_four`
          (exp ∈ C⁴ UNCONDITIONAL, J4-5f), `expMap_contDiffOn_three`.

  (2) THE GEODESIC ODE **is banked** as the defining property of the flow (NOT a research unknown):
        • `geodesicField g gi (x,v) = (v, fun i => -∑ⱼ∑ₖ Γⁱⱼₖ(x) vʲ vᵏ)`  (`QIQTH.Geodesic` :37).
          This IS the first-order form of `γ̈ + Γ(γ̇,γ̇) = 0`.
        • `geodesic_local_existence` / `geodesic_local_unique` (Picard–Lindelöf + Grönwall).
        • The exp-tube `expTube_spec` gives `HasDerivAt (expTube p v) (geodesicField …) t` — i.e. the
          geodesic ODE is a usable HasDerivAt property along the exp curve.  Position/velocity split
          via `.fst`/`.snd` CLM composition (pattern at `ExpMap.lean:1027-1037`).

  (3) THE JACOBI / VARIATIONAL MACHINERY:
        • `jacobiOperator` (`QIQTH.JacobiEquation` :80); `geodesicField_fderiv_eq_jacobiOperator`
          (the linearization = Jacobi eqn for the differential); `jacobiVariation_secondOrder`,
          `riemann_at_center`, `riemannDeviation_at_center`.
        • `expJacobianMat_eq_flow` (`ExpJacobianFlow`), `expMatrixJacobi_flow` (`ExpMatrixJacobi`),
          `frameJacobi_matrix_ode` / `geodesic_raychaudhuri` (`GeodesicRaychaudhuri`).
        • These carry the matrix Jacobi/variational ODE + the Raychaudhuri det equation, but NO
          symplectic/Wronskian Gauss identity and NO `g(J,γ̇) = const` transverse conservation.

  (4) THE RADIAL / VAN-VLECK FACTS:
        • `radialDeriv f v = ∑ᵢ vⁱ ∂ᵢ f` (Euler field `r∂_r`); `radialDeriv_quadraticForm`
          (`r∂_r` of a quadratic form = twice its value); `sqrtdet_taylorModel_radialDeriv_ricci`,
          the directional van-Vleck 2-jet.  `JacobianRadial`: `expJacobianDet_pos_nhds` etc.
        • These solved the RADIAL ODE for `√det g̃`; the geodesic ENERGY identity
          `g_{γ(t)}(γ̇,γ̇) = const` was NOT previously banked (it is the deliverable G1 here).

  (5) METRIC COMPATIBILITY **is banked** (`QIQTH.Curvature`) — the analytic crux for energy
      conservation:
        • `christoffel_lower` (:312): `∑σ g_{σν} Γ^σ_{λμ} = ½(∂_λ g_{νμ}+∂_μ g_{νλ}−∂_ν g_{λμ})`
          (the inverse metric in Γ cancelled by the lowering).
        • `metric_compat` (:333): `∇_λ g_{μν} = 0`; `christoffel_symm` (torsion-freeness).
      These need ONLY `g` symmetric + `gi` its inverse (algebraic; no metric smoothness).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THREE-BRICK SUPPORT VERDICT (per Sol's decomposition):
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • Brick (1) FIRST-VARIATION GAUSS IDENTITY `g_{exp(v)}(dexp·v, dexp·w) = g₀(v,w)`:
       RADIAL half (`w = v`, i.e. energy `g_{γ(t)}(γ̇,γ̇) = |v|²_g`) is SUPPORTED NOW — banked
       `christoffel_lower` + `expTube_spec`.  THIS FILE DERIVES IT (G1a/G1b/G1c below).
       TRANSVERSE half (`w ⊥ v`, Jacobi `g(J,γ̇)=const`) is NOT banked — needs the symplectic /
       Gauss-lemma conservation `d/dt g(J,γ̇)=0` which the Jacobi machinery in (3) does not carry.
   • Brick (2) COORDINATE CONVERSION `∑ⱼ g̃_ij v^j = v^i`:  NOT reachable without the transverse
       half + the homogeneity `D exp_p(v)·v = γ̇(1)` (geodesic rescaling).  Named residue only.
   • Brick (3) FRAME/RECENTER TRANSPORT to the capstone `g`:  downstream of (2); not reachable now.

  DELIVERED (fully derived, axiom-free, no `sorry`):
   • G1a `geodesic_energy_deriv_eq_zero` — the ALGEBRAIC HEART: along a geodesic the total
       t-derivative of the energy quadratic form vanishes IDENTICALLY (pure metric-compatibility
       algebra from `christoffel_lower`; no ODE, no smoothness).
   • G1b `energy_hasDerivAt_along_geodesic` — the pointwise chain-rule derivative of the energy
       along ANY integral curve of `geodesicField`, and `energy_hasDerivAt_zero` combining with G1a
       ⟹ `HasDerivAt E 0 t`.
   • G1c `geodesic_energy_conservation` — integrating: `g_{exp_p v}(γ̇(1),γ̇(1)) = g_p(v,v)` for the
       banked exp-tube (energy conservation, the radial Gauss identity).

  NAMED RESIDUES (honest, not attempted here): the transverse Jacobi conservation, the coordinate
  form `∑ⱼ g̃_ij v^j = v^i`, and the frame/recenter transport (bricks (2),(3) and the transverse
  half of (1)).  See the campaign map in the final report.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap

namespace QIQTH.GaussLemmaFirstVariation

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open Finset

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### G1a — the algebraic heart: the geodesic energy derivative vanishes identically.

For a geodesic `γ` with velocity `u = γ̇` and acceleration `acc = γ̈ = −Γ(γ)(u,u)`, the total
`t`-derivative of the energy `E = ∑_{a,b} g_{ab}(γ) u^a u^b` is
  `∑_{a,b} [ (∑_c ∂_c g_{ab}·u^c)·u^a u^b + g_{ab}(acc^a u^b + u^a acc^b) ] = 0`.
This is PURE metric-compatibility algebra: the `∂g` (radial) term is cancelled by the christoffel
(acceleration) term after lowering `∑_a g_{ab} Γ^a_{de} = ½(∂_d g_{be}+∂_e g_{bd}−∂_b g_{de})`
(`christoffel_lower`) and reindexing the three symmetric triple sums.  No smoothness, no ODE. -/
theorem geodesic_energy_deriv_eq_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (u acc : Fin n → ℝ)
    (hacc : ∀ a, acc a = -∑ d, ∑ e, christoffel g gi a d e x * u d * u e) :
    (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c x * u c) * u a * u b
              + g x a b * acc a * u b + g x a b * u a * acc b)) = 0 := by
  classical
  -- The canonical fully-symmetric triple sum.
  -- A := radial term, B := acceleration term (first slot), C := acceleration term (second slot).
  -- T1,T2,T3 := the three lowered-christoffel triple sums.
  -- Claim: A = M, C = B, B = −½(T1+T2−T3), and T1 = T2 = T3 = M.  Then A + B + C = M − M = 0.
  -- ── A = M ────────────────────────────────────────────────────────────────────────────────
  have hA : (∑ a, ∑ b, (∑ c, pd (fun y => g y a b) c x * u c) * u a * u b)
      = ∑ i, ∑ j, ∑ k, pd (fun y => g y i j) k x * u i * u j * u k := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  -- ── C = B ────────────────────────────────────────────────────────────────────────────────
  have hCB : (∑ a, ∑ b, g x a b * u a * acc b) = (∑ a, ∑ b, g x a b * acc a * u b) := by
    rw [show (∑ a, ∑ b, g x a b * u a * acc b)
          = ∑ a, ∑ b, g x b a * u a * acc b from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hsymm x a b]))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  -- ── the three lowered-christoffel triple sums equal M ─────────────────────────────────────
  have hT2 : (∑ b, ∑ d, ∑ e, pd (fun y => g y b d) e x * u b * u d * u e)
      = ∑ i, ∑ j, ∑ k, pd (fun y => g y i j) k x * u i * u j * u k := rfl
  have hT1 : (∑ b, ∑ d, ∑ e, pd (fun y => g y b e) d x * u b * u d * u e)
      = ∑ i, ∑ j, ∑ k, pd (fun y => g y i j) k x * u i * u j * u k := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun d _ => by ring))
  have hT3 : (∑ b, ∑ d, ∑ e, pd (fun y => g y d e) b x * u b * u d * u e)
      = ∑ i, ∑ j, ∑ k, pd (fun y => g y i j) k x * u i * u j * u k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun b _ => by ring))
  -- ── B = −½(T1+T2−T3) via christoffel_lower ────────────────────────────────────────────────
  -- per-`b` reduction: `∑_a g_{ab} acc_a · u_b = −½ ∑_d ∑_e (P1+P2−P3)_{bde} u_b u_d u_e`.
  have hstep : ∀ b : Fin n, (∑ a, g x a b * acc a * u b)
      = -((1 / 2) * ∑ d, ∑ e,
            (pd (fun y => g y b e) d x + pd (fun y => g y b d) e x - pd (fun y => g y d e) b x)
              * u b * u d * u e) := by
    intro b
    -- factor out `u b`
    rw [← Finset.sum_mul]
    -- substitute the acceleration
    rw [show (∑ a, g x a b * acc a)
          = ∑ a, g x a b * (-∑ d, ∑ e, christoffel g gi a d e x * u d * u e) from
        Finset.sum_congr rfl (fun a _ => by rw [hacc a])]
    -- `∑_a g_{ab} · (−∑_d∑_e Γ u u) = −∑_d∑_e (∑_a g_{ab} Γ) u_d u_e`
    rw [show (∑ a, g x a b * (-∑ d, ∑ e, christoffel g gi a d e x * u d * u e))
          = -∑ d, ∑ e, (∑ a, g x a b * christoffel g gi a d e x) * (u d * u e) from ?_]
    · -- apply christoffel_lower to the inner `∑_a`
      rw [show (∑ d, ∑ e, (∑ a, g x a b * christoffel g gi a d e x) * (u d * u e))
            = ∑ d, ∑ e,
                ((1 / 2) * (pd (fun y => g y b e) d x + pd (fun y => g y b d) e x
                    - pd (fun y => g y d e) b x)) * (u d * u e) from
          Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => by
            rw [christoffel_lower g gi hsymm x hinv b d e]))]
      -- pull `u b` inside and reorder factors
      rw [neg_mul]
      refine congrArg Neg.neg ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    · -- the reorder `∑_a g (−∑_d∑_e Γ u u) = −∑_d∑_e (∑_a g Γ) u_d u_e`
      rw [show (∑ a, g x a b * (-∑ d, ∑ e, christoffel g gi a d e x * u d * u e))
            = ∑ a, -∑ d, ∑ e, g x a b * christoffel g gi a d e x * (u d * u e) from
          Finset.sum_congr rfl (fun a _ => by
            rw [mul_neg, Finset.mul_sum]
            refine congrArg Neg.neg (Finset.sum_congr rfl (fun d _ => ?_))
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun e _ => by ring))]
      rw [Finset.sum_neg_distrib]
      refine congrArg Neg.neg ?_
      -- reorder `∑_a ∑_d ∑_e → ∑_d ∑_e ∑_a` and factor
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.sum_mul]
  -- assemble B = −½(T1+T2−T3)
  have hB : (∑ a, ∑ b, g x a b * acc a * u b)
      = -((1 / 2) * ((∑ b, ∑ d, ∑ e, pd (fun y => g y b e) d x * u b * u d * u e)
                    + (∑ b, ∑ d, ∑ e, pd (fun y => g y b d) e x * u b * u d * u e)
                    - (∑ b, ∑ d, ∑ e, pd (fun y => g y d e) b x * u b * u d * u e))) := by
    rw [Finset.sum_comm]
    rw [show (∑ b, ∑ a, g x a b * acc a * u b)
          = ∑ b, -((1 / 2) * ∑ d, ∑ e,
              (pd (fun y => g y b e) d x + pd (fun y => g y b d) e x - pd (fun y => g y d e) b x)
                * u b * u d * u e) from Finset.sum_congr rfl (fun b _ => hstep b)]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    refine congrArg (fun z => -((1 / 2) * z)) ?_
    -- distribute (P1+P2−P3) across the triple sum
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- final linear combination
  have hsplit :
      (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c x * u c) * u a * u b
                + g x a b * acc a * u b + g x a b * u a * acc b))
      = (∑ a, ∑ b, (∑ c, pd (fun y => g y a b) c x * u c) * u a * u b)
        + (∑ a, ∑ b, g x a b * acc a * u b)
        + (∑ a, ∑ b, g x a b * u a * acc b) := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit, hA, hCB, hB, hT1, hT2, hT3]
  ring

/-! ### G1b — the pointwise chain-rule derivative of the energy along an integral curve.

For any curve `Y` solving the geodesic ODE `Y' t = geodesicField g gi (Y t)` (e.g. the exp-tube),
and any `C¹` ambient metric, the energy `E s = ∑_{a,b} g_{ab}((Y s).1)·(Y s).2^a·(Y s).2^b` is
differentiable at `t` with the explicit product-rule derivative (radial term + the two acceleration
slots).  Combined with G1a this derivative is `0`. -/
theorem energy_hasDerivAt_along_geodesic
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, Differentiable ℝ (fun y => g y a b))
    (Y : ℝ → Point n × Point n) {t : ℝ}
    (hYd : HasDerivAt Y (geodesicField g gi (Y t)) t) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (Y s).1 a b * (Y s).2 a * (Y s).2 b)
      (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * (Y t).2 a * (Y t).2 b
                + g (Y t).1 a b * (geodesicField g gi (Y t)).2 a * (Y t).2 b
                + g (Y t).1 a b * (Y t).2 a * (geodesicField g gi (Y t)).2 b)) t := by
  classical
  -- position derivative `γ̇ = velocity`
  have hpos : HasDerivAt (fun s => (Y s).1) ((Y t).2) t := by
    simpa [geodesicField] using
      (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t hYd
  -- velocity derivative `u̇ = acceleration`
  have hvel : HasDerivAt (fun s => (Y s).2) ((geodesicField g gi (Y t)).2) t := by
    simpa using
      (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t hYd
  have hu : ∀ a, HasDerivAt (fun s => (Y s).2 a) ((geodesicField g gi (Y t)).2 a) t := by
    intro a
    simpa using (ContinuousLinearMap.proj a).hasFDerivAt.comp_hasDerivAt t hvel
  -- metric-along-curve derivative via the chain rule `d/dt g_{ab}(γ) = ∑_c ∂_c g_{ab}·γ̇^c`
  have hgab : ∀ a b, HasDerivAt (fun s => g (Y s).1 a b)
      (∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) t := by
    intro a b
    have hcomp := ((hg a b).differentiableAt (x := (Y t).1)).hasFDerivAt.comp_hasDerivAt t hpos
    rwa [fderiv_apply_eq_sum_pd (fun y => g y a b) (Y t).1 ((Y t).2)
        ((hg a b).differentiableAt)] at hcomp
  -- per-`(a,b)` product-rule summand
  have hsummand : ∀ a b, HasDerivAt (fun s => g (Y s).1 a b * (Y s).2 a * (Y s).2 b)
      ((∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * (Y t).2 a * (Y t).2 b
        + g (Y t).1 a b * (geodesicField g gi (Y t)).2 a * (Y t).2 b
        + g (Y t).1 a b * (Y t).2 a * (geodesicField g gi (Y t)).2 b) t := by
    intro a b
    have h := ((hgab a b).mul (hu a)).mul (hu b)
    convert h using 1
    simp only [Pi.mul_apply]
    ring
  have h := HasDerivAt.sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
    HasDerivAt.sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin n))) => hsummand a b))
  have hfun : (fun s => ∑ a, ∑ b, g (Y s).1 a b * (Y s).2 a * (Y s).2 b)
      = (∑ a ∈ Finset.univ, ∑ b ∈ Finset.univ,
          fun s => g (Y s).1 a b * (Y s).2 a * (Y s).2 b) := by
    funext s; simp only [Finset.sum_apply]
  rw [hfun]; exact h

/-- **G1b (zero form).**  Along a geodesic of the (symmetric, invertible) metric, the energy has
    derivative `0` — G1a discharges the derivative computed by `energy_hasDerivAt_along_geodesic`. -/
theorem energy_hasDerivAt_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, Differentiable ℝ (fun y => g y a b))
    (Y : ℝ → Point n × Point n) {t : ℝ}
    (hYd : HasDerivAt Y (geodesicField g gi (Y t)) t) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (Y s).1 a b * (Y s).2 a * (Y s).2 b) 0 t := by
  have hzero :
      (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * (Y t).2 a * (Y t).2 b
                + g (Y t).1 a b * (geodesicField g gi (Y t)).2 a * (Y t).2 b
                + g (Y t).1 a b * (Y t).2 a * (geodesicField g gi (Y t)).2 b)) = 0 :=
    geodesic_energy_deriv_eq_zero g gi hsymm (Y t).1 (hinv (Y t).1) (Y t).2
      ((geodesicField g gi (Y t)).2) (fun a => rfl)
  simpa [hzero] using energy_hasDerivAt_along_geodesic g gi hg Y hYd

/-! ### G1c — energy conservation (the radial Gauss identity). -/

/-- **G1c — geodesic energy conservation.**  For the banked exp-tube through `(p, v)` (with
    `‖v‖ ≤ expRho`), the energy is conserved from `t = 0` to `t = 1`:
      `g_{exp_p v}(γ̇(1), γ̇(1)) = g_p(v, v)`.
    This is the RADIAL half of the first-variation Gauss identity (the `w = v` contraction).
    ⚠ NOT `a₁ = R/6`; NOT the transverse Jacobi conservation; NOT the coordinate form. -/
theorem geodesic_energy_conservation
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, Differentiable ℝ (fun y => g y a b))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) :
    (∑ a, ∑ b, g (expMap g gi hC p v) a b
        * (expTube g gi hC p v 1).2 a * (expTube g gi hC p v 1).2 b)
      = ∑ a, ∑ b, g p a b * v a * v b := by
  classical
  set Y : ℝ → Point n × Point n := expTube g gi hC p v with hYdef
  obtain ⟨hY0, hYd, -⟩ := expTube_spec g gi hC p v hv
  -- the energy along the tube
  set E : ℝ → ℝ := fun s => ∑ a, ∑ b, g (Y s).1 a b * (Y s).2 a * (Y s).2 b with hEdef
  -- Icc/Ico 0 1 ⊆ Ioo (-2) 2
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- `E` has derivative `0` on `(-2, 2)`
  have hE0 : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt E 0 s := fun s hs =>
    energy_hasDerivAt_zero g gi hsymm hinv hg Y (hYd s hs)
  have hcont : ContinuousOn E (Set.Icc (0 : ℝ) 1) := fun x hx =>
    (hE0 x (hsub hx)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt E 0 (Set.Ici x) x := fun x hx =>
    (hE0 x (hsub (Set.Ico_subset_Icc_self hx))).hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv 1 (Set.right_mem_Icc.mpr (by norm_num))
  -- unpack `E 1 = E 0`
  have h1 : E 1 = ∑ a, ∑ b, g (expMap g gi hC p v) a b
      * (expTube g gi hC p v 1).2 a * (expTube g gi hC p v 1).2 b := by
    simp only [hEdef, hYdef, expMap]
  have h0 : E 0 = ∑ a, ∑ b, g p a b * v a * v b := by
    simp only [hEdef, hYdef, hY0]
  rw [← h1, ← h0]
  exact hconst

end QIQTH.GaussLemmaFirstVariation
