/-
  GaussLemmaHomogeneity — the EULER-HOMOGENEITY + JACOBI-INSTANTIATION legs of the Gauss lemma
  for the geodesic exponential map, toward discharging `hGauss` (brick J4-344 of the hGauss
  derivation campaign of the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one of the four labelled inputs of `a1_R6_from_labelled`, and this
  campaign works toward discharging it for the exp-pullback normal-form metric.  This file delivers
  two legs of that program:
    • H1 — the EULER HOMOGENEITY `D exp_p(v)·v = γ̇_v(1)` (the radial derivative of the exponential
      map along a ray is the terminal geodesic velocity), from the banked ray-vs-geodesic identity.
    • H2 — the JACOBI-INSTANTIATION BRIDGE: the pure pd-calculus algebra turning the RAW second-order
      variational ODE `ξ'' = −jacobiOperator` into the COVARIANT Riemann form `∇∇J = −R(J,γ̇)γ̇`, i.e.
      the exact `hJac` shape consumed by `RiemannFirstPairAntisym.hvanish_from_antisym`.
  Nothing here builds normal coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE BANKED STATE THIS BUILDS ON
  ─────────────────────────────────────────────────────────────────────────────────────────────
  • `ExpJacobianRescale`: `expMap_smul_eq_expTube` (`exp_p(s•v) = (expTube p v s).1` for `‖v‖ ≤ expRho`,
    `|s| ≤ 1`) and `hasDerivAt_expMap_smul_ray` (`∂_t exp_p(t•v)|_s = (expTube p v s).2` for `|s| < 1`).
  • `ExpMap`: `hasFDerivAt_expMap` (`HasFDerivAt exp_p L v` for `‖v‖ < expRho`).
  • `JacobiEquation`: `jacobiOperator` (the RAW variational acceleration coefficient) and
    `jacobiVariation_secondOrder` (`ξ'' = −jacobiOperator`, UNCONDITIONAL given the first-order system).
  • `Curvature`: `christoffel` (`Γ`, symmetric in the lower pair via `christoffel_symm`), `riemann`
    (`R^ρ_{σμν} = ∂_μΓ^ρ_{νσ} − ∂_νΓ^ρ_{μσ} + ∑_l(Γ^ρ_{μl}Γ^l_{νσ} − Γ^ρ_{νl}Γ^l_{μσ})`).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED (fully derived, axiom-free, no `sorry`):
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • H1a `exp_euler_homogeneity_interior` — `fderiv exp_p (s•v) v = (expTube p v s).2` for `‖v‖ < expRho`,
       `|s| < 1` (the ray chain-rule: `D exp_p` at the scaled point applied to `v` = the geodesic
       velocity at parameter `s`).  UNCONDITIONAL.
   • H1b `exp_euler_homogeneity` — `fderiv exp_p v v = (expTube p v 1).2` for `‖v‖ < expRho` (the
       endpoint `s = 1`, the classical Euler homogeneity `D exp_p(v)·v = γ̇_v(1)`), via the within-`Iic`
       derivative uniqueness at the boundary parameter.  UNCONDITIONAL.
   • H2 `jacobi_covariant_ode` — the RAW→COVARIANT Jacobi bridge: given the raw second-order variational
       ODE `Jpp = −jacobiOperator` (`hJODE`, banked as `jacobiVariation_secondOrder`), the covariant field
       `cJ = J' + Γ(u,J)` and its product-rule `t`-derivative `cJp` (`hcJ`, `hcJp`; satisfied by the
       actual flow-derivative Jacobi field), the second covariant derivative equals `−R(J,u)u`:
       `cJp^a + ∑ Γ^a_{cd} u^c cJ^d = −∑ R^a_{σep} u^σ J^e u^p` — the EXACT `hJac` shape of
       `RiemannFirstPairAntisym.hvanish_from_antisym`.  Pure `Γ`/`∂Γ` pointwise algebra: the `J'`
       (first-derivative) terms cancel by `Γ`-lower-symmetry, the `∂Γ` terms antisymmetrize to the
       Riemann derivative part, the `ΓΓ` terms match the Riemann `ΓΓ` part.

  ⚠ NOT a₁ = R/6.  H1 is unconditional; H2's `hcJ`/`hcJp`/`hJODE` are the satisfiable instantiation
  data of the actual flow-derivative field (the differentiation step, a separate downstream brick).
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.JacobiEquation
import QIQTH.ExpJacobianRescale
import QIQTH.RiemannFirstPairAntisym

namespace QIQTH.GaussLemmaHomogeneity

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open Finset

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### H1a — the interior Euler homogeneity `D exp_p(s•v)·v = γ̇_v(s)`. -/

/-- **H1a — the interior ray homogeneity.**  For `‖v‖ < expRho` and `|s| < 1`, the Fréchet
    derivative of the exponential map at the scaled point `s•v`, applied to `v`, equals the geodesic
    velocity at parameter `s`:  `D exp_p(s•v)·v = (expTube p v s).2 = γ̇_v(s)`.
    Chain rule on `t ↦ exp_p(t•v) = exp_p ∘ (·•v)` (`hasFDerivAt_expMap`) matched against the banked
    ray velocity `hasDerivAt_expMap_smul_ray` via `HasDerivAt.unique`.  ⚠ NOT a₁ = R/6. -/
theorem exp_euler_homogeneity_interior
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s : ℝ} (hs : |s| < 1) :
    fderiv ℝ (expMap g gi hC p) (s • v) v = (expTube g gi hC p v s).2 := by
  -- `‖s•v‖ < expRho` since `|s| ≤ 1`.
  have hsv : ‖s • v‖ < expRho g gi hC p := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |s| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ < expRho g gi hC p := hv
  obtain ⟨Φ, -, -, hFD⟩ := hasFDerivAt_expMap g gi hC p (s • v) hsv
  have hsmul : HasDerivAt (fun t : ℝ => t • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have hchain := hFD.comp_hasDerivAt s hsmul
  have hray := hasDerivAt_expMap_smul_ray g gi hC p v hv.le hs
  have huniq := hchain.unique hray
  rw [hFD.fderiv]
  exact huniq

/-! ### H1b — the endpoint Euler homogeneity `D exp_p(v)·v = γ̇_v(1)`. -/

/-- **H1b — the Euler homogeneity (endpoint).**  For `‖v‖ < expRho`, the Fréchet derivative of the
    exponential map at `v` applied to `v` equals the terminal geodesic velocity:
      `D exp_p(v)·v = (expTube p v 1).2 = γ̇_v(1)`.
    The classical Euler homogeneity of the exponential map.  Because the ray identity
    `exp_p(t•v) = (expTube p v t).1` holds only for `|t| ≤ 1`, the parameter `1` is a right endpoint;
    the derivative there is identified through the within-`Iic 1` uniqueness of derivatives (the
    two-sided chain-rule derivative `D exp_p(v)·v`, restricted to `Iic 1`, agrees with the geodesic
    velocity computed from the left).  ⚠ NOT a₁ = R/6. -/
theorem exp_euler_homogeneity
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) :
    fderiv ℝ (expMap g gi hC p) v v = (expTube g gi hC p v 1).2 := by
  obtain ⟨Φ, -, -, hFD⟩ := hasFDerivAt_expMap g gi hC p v hv
  -- two-sided chain-rule derivative of the ray `t ↦ exp_p(t•v)` at `1`.
  have hFD1 : HasFDerivAt (expMap g gi hC p)
      (expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) ((1 : ℝ) • v) := by
    rw [one_smul]; exact hFD
  have hsmul : HasDerivAt (fun t : ℝ => t • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hchain := hFD1.comp_hasDerivAt (1 : ℝ) hsmul
  have hcompeq : (expMap g gi hC p ∘ fun t : ℝ => t • v)
      = fun t => expMap g gi hC p (t • v) := rfl
  rw [hcompeq] at hchain
  have hchainW := hchain.hasDerivWithinAt (s := Set.Iic (1 : ℝ))
  -- geodesic-velocity within-derivative from the left.
  obtain ⟨-, hYd, -⟩ := expTube_spec g gi hC p v hv.le
  have h1mem : (1 : ℝ) ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hpos : HasDerivAt (fun u => (expTube g gi hC p v u).1) ((expTube g gi hC p v 1).2) 1 := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt 1
      (hYd 1 h1mem)
    simpa [geodesicField] using this
  have hposW := hpos.hasDerivWithinAt (s := Set.Iic (1 : ℝ))
  -- the ray identity holds on a left-neighbourhood of `1` within `Iic 1`.
  have hev : (fun t : ℝ => expMap g gi hC p (t • v))
      =ᶠ[nhdsWithin 1 (Set.Iic (1 : ℝ))] (fun t => (expTube g gi hC p v t).1) := by
    have h1 : Set.Ioo (-1 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have h2 : Set.Ioo (-1 : ℝ) 2 ∈ nhdsWithin 1 (Set.Iic (1 : ℝ)) := nhdsWithin_le_nhds h1
    filter_upwards [h2, self_mem_nhdsWithin] with t ht htIic
    have htle : |t| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], htIic⟩
    exact expMap_smul_eq_expTube g gi hC p v hv.le htle
  have hgeoW : HasDerivWithinAt (fun t : ℝ => expMap g gi hC p (t • v))
      ((expTube g gi hC p v 1).2) (Set.Iic (1 : ℝ)) 1 :=
    hposW.congr_of_eventuallyEq hev
      (expMap_smul_eq_expTube g gi hC p v hv.le (by rw [abs_one]))
  -- uniqueness of within-`Iic 1` derivatives.
  have hu : UniqueDiffWithinAt ℝ (Set.Iic (1 : ℝ)) 1 :=
    uniqueDiffOn_Iic 1 1 Set.self_mem_Iic
  have e1 := hchainW.derivWithin hu
  have e2 := hgeoW.derivWithin hu
  rw [hFD.fderiv]
  exact e1.symm.trans e2

/-! ### H2 — the raw→covariant Jacobi bridge.

  The classical identity `∇∇J = −R(J,γ̇)γ̇` from the RAW second-order variational ODE
  `J'' = −jacobiOperator`.  With `u = γ̇`, `J` the Jacobi field, `J'` its ordinary derivative, and the
  covariant derivative `cJ = ∇_u J = J' + Γ(u,J)`, the second covariant derivative
  `∇_u cJ = cJ' + Γ(u,cJ)` (with `cJ'` the product-rule `t`-derivative under `u' = −Γ(u,u)`) equals
  `−R(J,u)u`.  Purely pointwise `Γ`/`∂Γ` algebra:
    • the `J'` (first-derivative) terms cancel by `Γ`-lower-symmetry (`christoffel_symm`),
    • the `∂Γ` terms antisymmetrize into the Riemann derivative part,
    • the `ΓΓ` terms match the Riemann `ΓΓ` part.
  Split into index-permutation helpers and four "bridge" lemmas, one per monomial class. -/

/-- Rotate a triple sum: outermost index to innermost. -/
private theorem sum3_rot (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ j, ∑ k, ∑ i, F i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- Swap the 1st and 4th indices of a quadruple sum. -/
private theorem sum4_swap14 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, ∑ e, ∑ f, F c d e f) = ∑ f, ∑ d, ∑ e, ∑ c, F c d e f := by
  calc (∑ c, ∑ d, ∑ e, ∑ f, F c d e f)
      = ∑ d, ∑ c, ∑ e, ∑ f, F c d e f := Finset.sum_comm
    _ = ∑ d, ∑ e, ∑ c, ∑ f, F c d e f := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ e, ∑ f, ∑ c, F c d e f := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ d, ∑ f, ∑ e, ∑ c, F c d e f := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ f, ∑ d, ∑ e, ∑ c, F c d e f := Finset.sum_comm

/-- Block-swap a quadruple sum: `(c,d,e,f) → (e,f,c,d)`. -/
private theorem sum4_blockswap (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, ∑ e, ∑ f, F c d e f) = ∑ e, ∑ f, ∑ c, ∑ d, F c d e f := by
  have h1 : (∑ c, ∑ d, ∑ e, ∑ f, F c d e f) = ∑ c, ∑ e, ∑ f, ∑ d, F c d e f := by
    refine Finset.sum_congr rfl fun c _ => ?_
    exact sum3_rot (fun d e f => F c d e f)
  rw [h1]
  exact sum3_rot (fun c e f => ∑ d, F c d e f)

/-- **Bridge A1** — the `∂Γ·J·u·u` term of `−jacobiOperator` equals the first Riemann derivative
    contraction `∑ ∂_e Γ^a_{pσ} u^σ J^e u^p`. -/
private theorem gaussHom_A1 (g gi : Point n → Fin n → Fin n → ℝ)
    (x u J : Point n) (a : Fin n) :
    (∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi a j k z) l x * J l) * u j * u k)
    = ∑ σ, ∑ e, ∑ p, pd (fun z => christoffel g gi a p σ z) e x * u σ * J e * u p := by
  have hflat : (∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi a j k z) l x * J l) * u j * u k)
      = ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi a j k z) l x * J l * u j * u k := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hflat, sum3_rot (fun j k l => pd (fun z => christoffel g gi a j k z) l x * J l * u j * u k)]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun p _ => by ring

/-- **Bridge B1** — the `∂Γ·u·u·J` term of `cJ'` equals the second Riemann derivative contraction
    `∑ ∂_p Γ^a_{eσ} u^σ J^e u^p`.  Uses `Γ`-lower-symmetry. -/
private theorem gaussHom_B1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x u J : Point n) (a : Fin n) :
    (∑ c, ∑ d, (∑ l, pd (fun z => christoffel g gi a c d z) l x * u l) * u c * J d)
    = ∑ σ, ∑ e, ∑ p, pd (fun z => christoffel g gi a e σ z) p x * u σ * J e * u p := by
  have hflat : (∑ c, ∑ d, (∑ l, pd (fun z => christoffel g gi a c d z) l x * u l) * u c * J d)
      = ∑ c, ∑ d, ∑ l, pd (fun z => christoffel g gi a c d z) l x * u l * u c * J d := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hflat]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [show (fun z => christoffel g gi a c d z) = (fun z => christoffel g gi a d c z) from
      funext fun z => christoffel_symm g gi hsymm a c d z]
  ring

/-- **Bridge B2** — the `ΓΓ·u·u·J` term of `cJ'` (from the acceleration `u' = −Γ(u,u)`) equals the
    first Riemann `ΓΓ` contraction `∑_l Γ^a_{el} Γ^l_{pσ} u^σ J^e u^p`.  Uses `Γ`-lower-symmetry. -/
private theorem gaussHom_B2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x u J : Point n) (a : Fin n) :
    (∑ c, ∑ d, christoffel g gi a c d x
        * (∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d)
    = ∑ σ, ∑ e, ∑ p,
        (∑ l, christoffel g gi a e l x * christoffel g gi l p σ x) * u σ * J e * u p := by
  have hflatL : (∑ c, ∑ d, christoffel g gi a c d x
        * (∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d)
      = ∑ c, ∑ d, ∑ e, ∑ f,
          christoffel g gi a c d x * christoffel g gi c e f x * u e * u f * J d := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => by ring
  have hflatR : (∑ σ, ∑ e, ∑ p,
        (∑ l, christoffel g gi a e l x * christoffel g gi l p σ x) * u σ * J e * u p)
      = ∑ σ, ∑ e, ∑ p, ∑ l,
          christoffel g gi a e l x * christoffel g gi l p σ x * u σ * J e * u p := by
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [hflatL, hflatR,
      sum4_swap14 (fun c d e f =>
        christoffel g gi a c d x * christoffel g gi c e f x * u e * u f * J d)]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ => ?_
  rw [christoffel_symm g gi hsymm a l e]
  ring

/-- **Bridge C2** — the `ΓΓ·u·u·J` term of the `∇`-correction `Γ(u,cJ)` equals the second Riemann
    `ΓΓ` contraction `∑_l Γ^a_{pl} Γ^l_{eσ} u^σ J^e u^p`.  Uses `Γ`-lower-symmetry. -/
private theorem gaussHom_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x u J : Point n) (a : Fin n) :
    (∑ c, ∑ d, christoffel g gi a c d x * u c
        * (∑ e, ∑ f, christoffel g gi d e f x * u e * J f))
    = ∑ σ, ∑ e, ∑ p,
        (∑ l, christoffel g gi a p l x * christoffel g gi l e σ x) * u σ * J e * u p := by
  have hflatL : (∑ c, ∑ d, christoffel g gi a c d x * u c
        * (∑ e, ∑ f, christoffel g gi d e f x * u e * J f))
      = ∑ c, ∑ d, ∑ e, ∑ f,
          christoffel g gi a c d x * christoffel g gi d e f x * u c * u e * J f := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => by ring
  have hflatR : (∑ σ, ∑ e, ∑ p,
        (∑ l, christoffel g gi a p l x * christoffel g gi l e σ x) * u σ * J e * u p)
      = ∑ σ, ∑ e, ∑ p, ∑ l,
          christoffel g gi a p l x * christoffel g gi l e σ x * u σ * J e * u p := by
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [hflatL, hflatR,
      sum4_blockswap (fun c d e f =>
        christoffel g gi a c d x * christoffel g gi d e f x * u c * u e * J f)]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun l _ => ?_
  rw [christoffel_symm g gi hsymm l σ e]
  ring

/-! ### H2 — the assembly: the raw variational ODE gives the covariant Jacobi (Riemann) equation. -/

/-- **H2 — `jacobi_covariant_ode`.**  The RAW→COVARIANT Jacobi bridge.  Let `u = γ̇`, `J` the Jacobi
    field with ordinary derivative `Jp = J'` and second derivative `Jpp = J''` satisfying the RAW
    second-order variational ODE `Jpp = −jacobiOperator g gi x u J Jp` (`hJODE`, banked as
    `jacobiVariation_secondOrder`).  Let `cJ = ∇_u J = J' + Γ(u,J)` (`hcJ`) and `cJp` its product-rule
    `t`-derivative under the geodesic acceleration `u' = −Γ(u,u)` (`hcJp`).  Then the second covariant
    derivative equals `−R(J,u)u`:
      `cJp^a + ∑_{c,d} Γ^a_{cd} u^c cJ^d = −∑_{σ,e,p} R^a_{σep} u^σ J^e u^p`.
    This is EXACTLY the `hJac` shape consumed by
    `RiemannFirstPairAntisym.hvanish_from_antisym`, discharging (for the actual flow-derivative field,
    whose data satisfy `hcJ`/`hcJp`/`hJODE`) the covariant Jacobi equation from the raw variational one.
    Purely pointwise `Γ`/`∂Γ` algebra (metric symmetry via `christoffel_symm`); no ODE, no smoothness.

    ⚠ HONESTY.  NOT a₁ = R/6.  `hJODE` is banked; `hcJ` is the definition of the covariant derivative;
    `hcJp` is the product-rule instantiation of `cJ`'s `t`-derivative, satisfied by the actual Jacobi
    field (the differentiation step is a separate downstream brick).  Here the ALGEBRAIC bridge is
    unconditional given those satisfiable data. -/
theorem jacobi_covariant_ode
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (x u J Jp Jpp : Point n)
    (hJODE : ∀ a, Jpp a = -jacobiOperator g gi x u J Jp a)
    (cJ cJp : Fin n → ℝ)
    (hcJ : ∀ d, cJ d = Jp d + ∑ c, ∑ e, christoffel g gi d c e x * u c * J e)
    (hcJp : ∀ a, cJp a = Jpp a
        + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l x * u l) * u c * J d
              + christoffel g gi a c d x
                  * (-∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d
              + christoffel g gi a c d x * u c * Jp d)) :
    ∀ a, cJp a + ∑ c, ∑ d, christoffel g gi a c d x * u c * cJ d
       = -(∑ σ, ∑ e, ∑ p, riemann g gi a σ e p x * u σ * J e * u p) := by
  intro a
  -- Split the ∇-correction `∑ Γ u cJ` into the `Jp` part (C1) and the `ΓΓ` part (C2).
  have hcorr : (∑ c, ∑ d, christoffel g gi a c d x * u c * cJ d)
      = (∑ c, ∑ d, christoffel g gi a c d x * u c * Jp d)
        + (∑ c, ∑ d, christoffel g gi a c d x * u c
              * (∑ e, ∑ f, christoffel g gi d e f x * u e * J f)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hcJ d]; ring
  rw [hcJp a, hJODE a, hcorr]
  simp only [jacobiOperator]
  -- Split the `−jacobiOperator` triple sum into its three atoms (A1, A2, A3).
  have hspA : (∑ j, ∑ k, ((∑ l, pd (fun z => christoffel g gi a j k z) l x * J l) * u j * u k
        + christoffel g gi a j k x * Jp j * u k + christoffel g gi a j k x * u j * Jp k))
      = (∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi a j k z) l x * J l) * u j * u k)
        + (∑ j, ∑ k, christoffel g gi a j k x * Jp j * u k)
        + (∑ j, ∑ k, christoffel g gi a j k x * u j * Jp k) := by
    simp only [Finset.sum_add_distrib]
  -- Split the `cJ'` extras triple sum into its three atoms (B1, B2, B3).
  have hspB : (∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l x * u l) * u c * J d
        + christoffel g gi a c d x
            * (-∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d
        + christoffel g gi a c d x * u c * Jp d))
      = (∑ c, ∑ d, (∑ l, pd (fun z => christoffel g gi a c d z) l x * u l) * u c * J d)
        + (∑ c, ∑ d, christoffel g gi a c d x
            * (-∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d)
        + (∑ c, ∑ d, christoffel g gi a c d x * u c * Jp d) := by
    simp only [Finset.sum_add_distrib]
  rw [hspA, hspB]
  -- Pull the acceleration's minus out of the ΓΓ atom (B2).
  have hB2neg : (∑ c, ∑ d, christoffel g gi a c d x
        * (-∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d)
      = -(∑ c, ∑ d, christoffel g gi a c d x
            * (∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d) := by
    have h1 : (∑ c, ∑ d, christoffel g gi a c d x
          * (-∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d)
        = ∑ c, ∑ d, -(christoffel g gi a c d x
            * (∑ e, ∑ f, christoffel g gi c e f x * u e * u f) * J d) :=
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    rw [h1]
    simp only [Finset.sum_neg_distrib]
  rw [hB2neg]
  -- Split the RHS Riemann contraction into the four Riemann atoms (T1, T2, G1, G2).
  have hRHS : (∑ σ, ∑ e, ∑ p, riemann g gi a σ e p x * u σ * J e * u p)
      = (∑ σ, ∑ e, ∑ p, pd (fun z => christoffel g gi a p σ z) e x * u σ * J e * u p)
        - (∑ σ, ∑ e, ∑ p, pd (fun z => christoffel g gi a e σ z) p x * u σ * J e * u p)
        + (∑ σ, ∑ e, ∑ p,
            (∑ l, christoffel g gi a e l x * christoffel g gi l p σ x) * u σ * J e * u p)
        - (∑ σ, ∑ e, ∑ p,
            (∑ l, christoffel g gi a p l x * christoffel g gi l e σ x) * u σ * J e * u p) := by
    have h4 : ((∑ σ, ∑ e, ∑ p, pd (fun z => christoffel g gi a p σ z) e x * u σ * J e * u p)
        - (∑ σ, ∑ e, ∑ p, pd (fun z => christoffel g gi a e σ z) p x * u σ * J e * u p)
        + (∑ σ, ∑ e, ∑ p,
            (∑ l, christoffel g gi a e l x * christoffel g gi l p σ x) * u σ * J e * u p)
        - (∑ σ, ∑ e, ∑ p,
            (∑ l, christoffel g gi a p l x * christoffel g gi l e σ x) * u σ * J e * u p))
        = ∑ σ, ∑ e, ∑ p,
            (pd (fun z => christoffel g gi a p σ z) e x * u σ * J e * u p
             - pd (fun z => christoffel g gi a e σ z) p x * u σ * J e * u p
             + (∑ l, christoffel g gi a e l x * christoffel g gi l p σ x) * u σ * J e * u p
             - (∑ l, christoffel g gi a p l x * christoffel g gi l e σ x) * u σ * J e * u p) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [h4]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun p _ => ?_
    simp only [riemann, Finset.sum_sub_distrib]
    ring
  rw [hRHS, gaussHom_A1 g gi x u J a, gaussHom_B1 g gi hsymm x u J a,
      gaussHom_B2 g gi hsymm x u J a, gaussHom_C2 g gi hsymm x u J a]
  -- Kinetic cancellation: the two `Γ·Jp·u` atoms coincide by `Γ`-lower-symmetry.
  have hkin : (∑ j, ∑ k, christoffel g gi a j k x * Jp j * u k)
      = (∑ j, ∑ k, christoffel g gi a j k x * u j * Jp k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [christoffel_symm g gi hsymm a k j]; ring
  linarith [hkin]

end QIQTH.GaussLemmaHomogeneity

