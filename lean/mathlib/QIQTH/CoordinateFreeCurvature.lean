/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Coordinate-free curvature of a Koszul connection

Builds the abstract COORDINATE-FREE curvature of a Koszul connection on a module: vector fields as
`Derivation R A A`, bracket = commutator, curvature `F(X,Y) = ∇_X∇_Y − ∇_Y∇_X − ∇_{⁅X,Y⁆}`, with the key
theorem that `F(X,Y)` is `A`-LINEAR (`curvature_smul`) — so curvature is a genuine TENSOR
(`curvatureTensor : M →ₗ[A] M`), coordinate-free BY CONSTRUCTION (no charts, no components), plus antisymmetry
and biadditivity, and a flat-connection non-vacuity witness (curvature 0). ⚠ HONEST (binding): this is the
ABSTRACT ALGEBRAIC coordinate-free curvature — the tensorial skeleton that the smooth-manifold Riemann tensor
instantiates. It is NOT the smooth-manifold Riemann curvature tensor itself: that additionally requires the
tangent bundle of a smooth manifold, a Riemannian metric, and the Levi-Civita connection (metric-compatible +
torsion-free), which are Mathlib-WIP (#36036/#36845) and are NOT built here. So this breaks the coordinate-free
curvature wall at the ALGEBRAIC level, not the smooth-manifold-analytic level. Also NOT the general curved heat
kernel (parametrix wall). NOT the conjecture, NOT the strong principle, NOT QG.
-/

namespace QIQTH.CoordinateFreeCurvature

variable {R A M : Type*}
  [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- A Koszul connection: an `R`-linear assignment of an `R`-linear endomorphism `cd X = ∇_X` to each
vector field `X` (a `Derivation R A A`), additive in `X`, satisfying the Leibniz rule in the module slot. -/
structure KoszulConnection (R A M : Type*)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] where
  /-- The covariant derivative along a vector field, as an `R`-linear endomorphism of sections. -/
  cd : Derivation R A A → (M →ₗ[R] M)
  /-- Additivity in the vector-field slot. -/
  cd_add : ∀ X Y, cd (X + Y) = cd X + cd Y
  /-- Leibniz rule: `∇_X (a • m) = (X a) • m + a • ∇_X m`. -/
  leibniz : ∀ (X : Derivation R A A) (a : A) (m : M), cd X (a • m) = (X a) • m + a • cd X m

namespace KoszulConnection

/-- The curvature endomorphism `F(X,Y) = ∇_X∇_Y − ∇_Y∇_X − ∇_{⁅X,Y⁆}`, coordinate-free by construction. -/
def curvature (cn : KoszulConnection R A M) (X Y : Derivation R A A) : M →ₗ[R] M :=
  cn.cd X ∘ₗ cn.cd Y - cn.cd Y ∘ₗ cn.cd X - cn.cd ⁅X, Y⁆

theorem curvature_apply (cn : KoszulConnection R A M) (X Y : Derivation R A A) (m : M) :
    cn.curvature X Y m = cn.cd X (cn.cd Y m) - cn.cd Y (cn.cd X m) - cn.cd ⁅X, Y⁆ m := by
  simp only [curvature, LinearMap.sub_apply, LinearMap.comp_apply]

/-- ★ TENSORIALITY: the curvature `F(X,Y)` is `A`-linear in the module argument — the first-order
cross terms cancel between the two double-derivative terms and against the bracket term. This is what
makes curvature a genuine tensor. -/
theorem curvature_smul (cn : KoszulConnection R A M) (X Y : Derivation R A A) (a : A) (m : M) :
    cn.curvature X Y (a • m) = a • cn.curvature X Y m := by
  simp only [curvature_apply, cn.leibniz, map_add, Derivation.commutator_apply,
    sub_smul, smul_sub]
  abel

/-- The curvature packaged as an `A`-linear endomorphism — the genuine coordinate-free curvature TENSOR. -/
def curvatureTensor (cn : KoszulConnection R A M) (X Y : Derivation R A A) : M →ₗ[A] M where
  toFun := cn.curvature X Y
  map_add' := (cn.curvature X Y).map_add
  map_smul' := by intro a m; simpa using cn.curvature_smul X Y a m

@[simp] theorem curvatureTensor_apply (cn : KoszulConnection R A M) (X Y : Derivation R A A) (m : M) :
    cn.curvatureTensor X Y m = cn.curvature X Y m := rfl

/-- The covariant derivative along the zero vector field is zero (from additivity). -/
theorem cd_zero (cn : KoszulConnection R A M) : cn.cd 0 = 0 := by
  have h := cn.cd_add 0 0
  rw [add_zero] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

/-- The covariant derivative negates with the vector field (from additivity). -/
theorem cd_neg (cn : KoszulConnection R A M) (X : Derivation R A A) :
    cn.cd (-X) = - cn.cd X := by
  have h := cn.cd_add X (-X)
  rw [add_neg_cancel, cn.cd_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Antisymmetry in the vector-field slots. -/
theorem curvature_antisymm (cn : KoszulConnection R A M) (X Y : Derivation R A A) :
    cn.curvature X Y = - cn.curvature Y X := by
  ext m
  have hb : (⁅Y, X⁆ : Derivation R A A) = -⁅X, Y⁆ := by rw [← lie_skew X Y, neg_neg]
  simp only [curvature_apply, LinearMap.neg_apply, hb, cn.cd_neg, LinearMap.neg_apply]
  abel

/-- The curvature vanishes on the diagonal (bracket of a field with itself is zero). -/
theorem curvature_self (cn : KoszulConnection R A M) (X : Derivation R A A) :
    cn.curvature X X = 0 := by
  ext m
  simp only [curvature_apply, lie_self, cn.cd_zero, LinearMap.zero_apply, sub_self]

/-- Biadditivity in the first vector-field slot. -/
theorem curvature_add_left (cn : KoszulConnection R A M) (X Y Z : Derivation R A A) :
    cn.curvature (X + Y) Z = cn.curvature X Z + cn.curvature Y Z := by
  ext m
  simp only [curvature_apply, cn.cd_add, LinearMap.add_apply, add_lie, map_add]
  abel

/-- Biadditivity in the second vector-field slot. -/
theorem curvature_add_right (cn : KoszulConnection R A M) (X Y Z : Derivation R A A) :
    cn.curvature X (Y + Z) = cn.curvature X Y + cn.curvature X Z := by
  ext m
  simp only [curvature_apply, cn.cd_add, LinearMap.add_apply, lie_add, map_add]
  abel

end KoszulConnection

/-- Non-vacuity witness: the flat (trivial) connection on `A` itself, `∇_X = X` (the derivation as an
`R`-linear map). Its Leibniz rule is the derivation Leibniz rule. -/
def flatConnection : KoszulConnection R A A where
  cd X := X.toLinearMap
  cd_add X Y := by ext a; simp
  leibniz X a m := by
    show X.toLinearMap (a • m) = (X a) • m + a • X.toLinearMap m
    simp only [Derivation.coeFn_coe, smul_eq_mul, Derivation.leibniz]
    ring

/-- The flat connection has zero curvature — the curvature genuinely computes. -/
theorem flatConnection_curvature (X Y : Derivation R A A) :
    (flatConnection : KoszulConnection R A A).curvature X Y = 0 := by
  ext a
  simp only [KoszulConnection.curvature_apply, flatConnection, Derivation.coeFn_coe,
    Derivation.commutator_apply, LinearMap.zero_apply]
  abel

end QIQTH.CoordinateFreeCurvature
