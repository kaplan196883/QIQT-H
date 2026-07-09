/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE INTRINSIC SPHERE — the great-circle metric, with the non-flatness a THEOREM (brick S1, sphere track)

The unit sphere `S² ⊂ ℝ³` carrying its INTRINSIC (great-circle / geodesic) metric
`dist p q = angle p q = arccos ⟪p, q⟫`, packaged as a compact metric space
(`IntrinsicSphere`), with its curvature made a THEOREM: the intrinsic sphere admits **no
distance-preserving map into ANY real inner-product space**
(`sphere_no_isometric_embedding_into_inner`).

This is the program's first **smooth curved space**.  The cone (`ConeMetric.lean`) is flat
away from the apex — all its curvature is concentrated at one point.  The round sphere is
curved EVERYWHERE (constant sectional curvature `+1`).  What is FORMALIZED here, however, is
the metric space and the no-flat-embedding OBSTRUCTION — **not** a Riemann/sectional-curvature
tensor computation (Mathlib has no computed curvature tensor for the sphere; the midpoint
obstruction is the honest formalizable surrogate, and it is strictly weaker than "curvature
`= +1`" but strictly stronger than nothing: no flat — indeed no inner-product — model exists).

## The metric

`dist p q := InnerProductGeometry.angle p.vec q.vec` on unit vectors.  Symmetry and
`dist_self` are elementary; the triangle inequality is Mathlib's
`InnerProductGeometry.angle_le_angle_add_angle` (the spherical triangle inequality); point
separation is the `arccos ⟪p,q⟫ = 0 ⟹ ⟪p,q⟫ = 1 ⟹ ‖p − q‖² = 0` cosine route.  The
CHORD↔ANGLE bridge (`chord_eq`, `chord_le_angle`, `angle_le_pi_div_two_mul_chord`:
`chord = 2 sin(θ/2)` and `chord ≤ θ ≤ (π/2)·chord`) makes the identity map a bi-Lipschitz
equivalence with the ambient chord metric — giving compactness now, and the finite-net
estimates for the GH-approximation brick S2 later.

## The non-flatness theorem (the FOURTH use of the unique-midpoint invariant)

In an inner-product space, a metric midpoint is UNIQUE and affine
(`QIQTH.IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint` — the same invariant that
killed the L¹ plane, the tripod, and the cone).  On the intrinsic sphere the antipodal poles
`±e₂` are at distance `π`, and EVERY equator point is a metric midpoint (`e₀` and `e₁` are
both at distance `π/2` from both poles, yet at distance `π/2 > 0` from each other).  An
isometric embedding would collapse `e₀` and `e₁` — contradiction.

## Scope firewall (MANDATORY)

The sphere and its geometry are **INPUTS** — a chosen target space, transported into the
formal system; nothing here is EMERGENCE of a sphere from quantum data.  The formalized
"non-flatness" is the midpoint obstruction, NOT a formalized curvature tensor.  The
GH-approximation of the sphere by finite clouds is brick S2, not this file.  NOT GR, NOT
numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QIQTH.IsotropyNoGo

namespace QIQTH.SphereMetric

open InnerProductGeometry
open scoped RealInnerProductSpace

/-! ## The carrier — a TYPE SYNONYM for the unit sphere

The subtype `{x // ‖x‖ = 1}` already carries the ambient CHORD metric; the intrinsic
great-circle metric needs a fresh type (the `ScaledStencil` pattern — a plain `def` blocks
instance leakage). -/

/-- **The intrinsic sphere** — the unit sphere of `ℝ³` as a bare type, to be equipped with
the great-circle (angle) metric rather than the inherited chord metric. -/
def IntrinsicSphere : Type := {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ = 1}

namespace IntrinsicSphere

/-- View an intrinsic-sphere point in the underlying subtype. -/
def toSub (p : IntrinsicSphere) : {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ = 1} := p

/-- Make an intrinsic-sphere point from a unit vector. -/
def ofVec (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) : IntrinsicSphere :=
  (⟨x, hx⟩ : {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ = 1})

/-- The underlying unit vector of an intrinsic-sphere point. -/
def vec (p : IntrinsicSphere) : EuclideanSpace ℝ (Fin 3) := (toSub p).1

@[simp] lemma vec_ofVec (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    (ofVec x hx).vec = x := rfl

/-- Every intrinsic-sphere point is a unit vector. -/
lemma norm_vec (p : IntrinsicSphere) : ‖p.vec‖ = 1 := (toSub p).2

/-- Unit vectors are nonzero (needed for `angle_self`). -/
lemma vec_ne_zero (p : IntrinsicSphere) : p.vec ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [p.norm_vec]; exact one_ne_zero)

/-- Two intrinsic-sphere points with the same vector are equal (`vec` is injective). -/
@[ext] lemma ext {p q : IntrinsicSphere} (h : p.vec = q.vec) : p = q := Subtype.ext h

lemma vec_injective : Function.Injective vec := fun _ _ h => ext h

/-- The north pole `e₂`. -/
noncomputable def northPole : IntrinsicSphere := ofVec (EuclideanSpace.single 2 1) (by simp)

instance : Nonempty IntrinsicSphere := ⟨northPole⟩

end IntrinsicSphere

open IntrinsicSphere

/-! ## The great-circle metric -/

/-- **The intrinsic (great-circle) metric on the sphere**: `dist p q = angle p q =
arccos ⟪p, q⟫`.  The triangle inequality is Mathlib's spherical triangle inequality
`InnerProductGeometry.angle_le_angle_add_angle`; separation is the cosine route
(`angle = 0 ⟹ ⟪p,q⟫ = 1 ⟹ ‖p − q‖² = 2 − 2⟪p,q⟫ = 0`). -/
noncomputable instance instMetricSpaceIntrinsicSphere : MetricSpace IntrinsicSphere where
  dist p q := InnerProductGeometry.angle p.vec q.vec
  dist_self p := angle_self p.vec_ne_zero
  dist_comm p q := angle_comm p.vec q.vec
  dist_triangle p q r := angle_le_angle_add_angle p.vec q.vec r.vec
  eq_of_dist_eq_zero := by
    intro p q h
    have h0 : InnerProductGeometry.angle p.vec q.vec = 0 := h
    have hinner : ⟪p.vec, q.vec⟫ = 1 := by
      have hc := cos_angle p.vec q.vec
      rw [h0, Real.cos_zero, p.norm_vec, q.norm_vec] at hc
      simpa using hc.symm
    have hns : ‖p.vec - q.vec‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, p.norm_vec, q.norm_vec, hinner]; ring
    have hsub : p.vec - q.vec = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero).symm.symm |>.mp hns)
    exact IntrinsicSphere.ext (sub_eq_zero.mp hsub)

/-- The intrinsic distance, unfolded: it IS the vector angle. -/
lemma dist_eq_angle (p q : IntrinsicSphere) :
    dist p q = InnerProductGeometry.angle p.vec q.vec := rfl

/-- Great-circle distances never exceed `π` (antipodes are the diameter). -/
lemma dist_le_pi (p q : IntrinsicSphere) : dist p q ≤ Real.pi :=
  angle_le_pi p.vec q.vec

/-- The cosine of the intrinsic distance is the inner product (unit vectors). -/
lemma cos_dist (p q : IntrinsicSphere) :
    Real.cos (dist p q) = ⟪p.vec, q.vec⟫ := by
  have hc := cos_angle p.vec q.vec
  rw [p.norm_vec, q.norm_vec] at hc
  rw [dist_eq_angle]
  simpa using hc

/-! ## The chord↔angle bridge

`chord² = 2 − 2 cos θ`, `chord = 2 sin (θ/2)`, and the two-sided Lipschitz comparison
`chord ≤ θ ≤ (π/2)·chord` — the identity map between the chord sphere and the intrinsic
sphere is bi-Lipschitz.  This yields compactness below and the S2 net estimates later. -/

/-- The quadratic cosine bound `1 − cos δ ≤ δ²/2` (via `sin²(δ/2) ≤ (δ/2)²`; restated from
`ConeMetric.lean`, where it is private). -/
private lemma one_sub_cos_le_half_sq (δ : ℝ) : 1 - Real.cos δ ≤ δ ^ 2 / 2 := by
  have h1 : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (δ / 2)
    rwa [show 2 * (δ / 2) = δ by ring] at h
  have h2 : Real.sin (δ / 2) ^ 2 ≤ (δ / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := δ / 2)
    have h3 := mul_self_le_mul_self (abs_nonneg _) h
    rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at h3
  nlinarith [h1, h2]

/-- **The chord–angle identity, squared**: `‖p − q‖² = 2 − 2 cos (dist p q)` (law of cosines
on unit vectors). -/
lemma chord_sq_eq (p q : IntrinsicSphere) :
    ‖p.vec - q.vec‖ ^ 2 = 2 - 2 * Real.cos (dist p q) := by
  rw [cos_dist, norm_sub_sq_real, p.norm_vec, q.norm_vec]; ring

/-- **The chord–angle identity**: `‖p − q‖ = 2 sin (dist p q / 2)` (the half-angle formula;
the sine is nonnegative since `dist/2 ∈ [0, π/2]`). -/
lemma chord_eq (p q : IntrinsicSphere) :
    ‖p.vec - q.vec‖ = 2 * Real.sin (dist p q / 2) := by
  have hcos : Real.cos (dist p q) = 1 - 2 * Real.sin (dist p q / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (dist p q / 2)
    rwa [show 2 * (dist p q / 2) = dist p q by ring] at h
  have hsq : ‖p.vec - q.vec‖ ^ 2 = (2 * Real.sin (dist p q / 2)) ^ 2 := by
    rw [chord_sq_eq, hcos]; ring
  have hsin : 0 ≤ Real.sin (dist p q / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (div_nonneg dist_nonneg (by norm_num))
      (by linarith [dist_le_pi p q, Real.pi_pos])
  calc ‖p.vec - q.vec‖ = Real.sqrt (‖p.vec - q.vec‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((2 * Real.sin (dist p q / 2)) ^ 2) := by rw [hsq]
    _ = 2 * Real.sin (dist p q / 2) :=
        Real.sqrt_sq (mul_nonneg (by norm_num) hsin)

/-- **Chord ≤ angle**: the straight-line chord is shorter than the great-circle arc
(`2 sin(θ/2) ≤ θ`, via `1 − cos θ ≤ θ²/2`). -/
lemma chord_le_angle (p q : IntrinsicSphere) : ‖p.vec - q.vec‖ ≤ dist p q := by
  have hsq : ‖p.vec - q.vec‖ ^ 2 ≤ dist p q ^ 2 := by
    have h := one_sub_cos_le_half_sq (dist p q)
    rw [chord_sq_eq]; linarith
  calc ‖p.vec - q.vec‖ = Real.sqrt (‖p.vec - q.vec‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (dist p q ^ 2) := Real.sqrt_le_sqrt hsq
    _ = dist p q := Real.sqrt_sq dist_nonneg

/-- **Angle ≤ (π/2)·chord**: the reverse comparison, from Jordan's inequality
`sin x ≥ (2/π)x` on `[0, π/2]` (`Real.mul_le_sin`) applied to the half-angle.  The identity
map chord-sphere → intrinsic sphere is `π/2`-Lipschitz. -/
lemma angle_le_pi_div_two_mul_chord (p q : IntrinsicSphere) :
    dist p q ≤ Real.pi / 2 * ‖p.vec - q.vec‖ := by
  have h0 : 0 ≤ dist p q := dist_nonneg
  have hπ : dist p q ≤ Real.pi := dist_le_pi p q
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := hπ0.ne'
  have hj : 2 / Real.pi * (dist p q / 2) ≤ Real.sin (dist p q / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have key : dist p q ≤ Real.pi * Real.sin (dist p q / 2) := by
    have h := mul_le_mul_of_nonneg_left hj hπ0.le
    have hid : Real.pi * (2 / Real.pi * (dist p q / 2)) = dist p q := by
      field_simp
    calc dist p q = Real.pi * (2 / Real.pi * (dist p q / 2)) := hid.symm
      _ ≤ Real.pi * Real.sin (dist p q / 2) := h
  rw [chord_eq]
  calc dist p q ≤ Real.pi * Real.sin (dist p q / 2) := key
    _ = Real.pi / 2 * (2 * Real.sin (dist p q / 2)) := by ring

/-! ## Compactness

The identity map from the (compact, since `ℝ³` is proper) chord sphere is `π/2`-Lipschitz
onto the intrinsic sphere by the bridge, so the intrinsic sphere is compact. -/

/-- The identity map from the ambient CHORD sphere (`Metric.sphere 0 1`, subtype metric) to
the intrinsic sphere. -/
def fromChordSphere (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    IntrinsicSphere :=
  ofVec x.1 (mem_sphere_zero_iff_norm.mp x.2)

lemma fromChordSphere_surjective : Function.Surjective fromChordSphere := fun p =>
  ⟨⟨p.vec, mem_sphere_zero_iff_norm.mpr p.norm_vec⟩, IntrinsicSphere.ext rfl⟩

/-- The chord-to-intrinsic identity map is `π/2`-Lipschitz (`angle ≤ (π/2)·chord`). -/
lemma fromChordSphere_lipschitz :
    LipschitzWith (Real.pi / 2).toNNReal fromChordSphere := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hcoe : ((Real.pi / 2).toNNReal : ℝ) = Real.pi / 2 :=
    Real.coe_toNNReal _ (by positivity)
  rw [hcoe, Subtype.dist_eq, dist_eq_norm]
  exact angle_le_pi_div_two_mul_chord (fromChordSphere x) (fromChordSphere y)

/-- **The intrinsic sphere is a COMPACT metric space** — the continuous image of the compact
chord sphere under the (Lipschitz) identity map. -/
instance instCompactSpaceIntrinsicSphere : CompactSpace IntrinsicSphere := by
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr fromChordSphere_surjective, ← Set.image_univ]
  exact IsCompact.image isCompact_univ fromChordSphere_lipschitz.continuous

/-! ## The non-flatness THEOREM -/

section NoEmbedding

/-- Distinct standard basis directions are orthogonal. -/
private lemma inner_single_single_ne {i j : Fin 3} (h : i ≠ j) :
    ⟪(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      EuclideanSpace.single j (1 : ℝ)⟫ = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp [h]

/-- Orthogonal unit vectors are at intrinsic distance `π/2`. -/
private lemma dist_ofVec_of_inner_eq_zero {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫ = 0) :
    dist (ofVec x hx) (ofVec y hy) = Real.pi / 2 := by
  rw [dist_eq_angle, vec_ofVec, vec_ofVec]
  exact (inner_eq_zero_iff_angle_eq_pi_div_two x y).mp hxy

/-- Antipodal points are at intrinsic distance `π`. -/
private lemma dist_ofVec_antipodal {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ‖x‖ = 1) (hx' : ‖-x‖ = 1) :
    dist (ofVec x hx) (ofVec (-x) hx') = Real.pi := by
  rw [dist_eq_angle, vec_ofVec, vec_ofVec]
  exact angle_self_neg_of_nonzero
    (norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero))

private lemma norm_single_one (i : Fin 3) :
    ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by simp

private lemma norm_neg_single_one (i : Fin 3) :
    ‖(-(EuclideanSpace.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by simp

/-- **THE SPHERE IS NOT FLAT — no isometric embedding into any inner-product space.**
There is NO distance-preserving map from the intrinsic sphere into any real inner-product
(Euclidean/Riemannian-flat) space, in any dimension.  The FOURTH use of the unique-midpoint
invariant: the poles `±e₂` are at distance `π`, and BOTH equator points `e₀`, `e₁` are metric
midpoints (each at distance `π/2` from both poles); in an inner-product space the metric
midpoint is unique and affine (`inner_metric_midpoint_eq_affine_midpoint`), so `f e₀ = f e₁`
— contradicting `dist e₀ e₁ = π/2 > 0`. -/
theorem sphere_no_isometric_embedding_into_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : IntrinsicSphere → E)
    (hf : ∀ p q : IntrinsicSphere, dist (f p) (f q) = dist p q) : False := by
  -- the four witnesses: poles N = e₂, S = −e₂ and equator points A = e₀, B = e₁
  set N : IntrinsicSphere := ofVec (EuclideanSpace.single 2 1) (norm_single_one 2) with hN
  set S : IntrinsicSphere :=
    ofVec (-(EuclideanSpace.single 2 1)) (norm_neg_single_one 2) with hS
  set A : IntrinsicSphere := ofVec (EuclideanSpace.single 0 1) (norm_single_one 0) with hA
  set B : IntrinsicSphere := ofVec (EuclideanSpace.single 1 1) (norm_single_one 1) with hB
  -- the six intrinsic distances
  have hNS : dist N S = Real.pi := dist_ofVec_antipodal _ _
  have hNA : dist N A = Real.pi / 2 :=
    dist_ofVec_of_inner_eq_zero _ _ (inner_single_single_ne (by decide))
  have hNB : dist N B = Real.pi / 2 :=
    dist_ofVec_of_inner_eq_zero _ _ (inner_single_single_ne (by decide))
  have hAS : dist A S = Real.pi / 2 := by
    rw [hA, hS, dist_eq_angle, vec_ofVec, vec_ofVec]
    refine (inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp ?_
    rw [inner_neg_right, inner_single_single_ne (by decide : (0 : Fin 3) ≠ 2), neg_zero]
  have hBS : dist B S = Real.pi / 2 := by
    rw [hB, hS, dist_eq_angle, vec_ofVec, vec_ofVec]
    refine (inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp ?_
    rw [inner_neg_right, inner_single_single_ne (by decide : (1 : Fin 3) ≠ 2), neg_zero]
  have hAB : dist A B = Real.pi / 2 :=
    dist_ofVec_of_inner_eq_zero _ _ (inner_single_single_ne (by decide))
  -- transport along f and apply midpoint uniqueness twice
  have hfNS : dist (f N) (f S) = 2 * (Real.pi / 2) := by rw [hf, hNS]; ring
  have hfNA : dist (f N) (f A) = Real.pi / 2 := by rw [hf, hNA]
  have hfAS : dist (f A) (f S) = Real.pi / 2 := by rw [hf, hAS]
  have hfNB : dist (f N) (f B) = Real.pi / 2 := by rw [hf, hNB]
  have hfBS : dist (f B) (f S) = Real.pi / 2 := by rw [hf, hBS]
  have hmidA := QIQTH.IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint hfNA hfAS hfNS
  have hmidB := QIQTH.IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint hfNB hfBS hfNS
  have hfAB : f A = f B := hmidA.trans hmidB.symm
  have h0 : dist (f A) (f B) = 0 := by rw [hfAB, dist_self]
  rw [hf, hAB] at h0
  exact Real.pi_div_two_pos.ne' h0

end NoEmbedding

end QIQTH.SphereMetric
