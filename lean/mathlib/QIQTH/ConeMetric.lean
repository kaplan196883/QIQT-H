/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE CONE — concentrated positive curvature as a metric space, with the curvature a THEOREM
(brick B2a)

Brick B2a of the CURVATURE track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`, Track B
continuation).  The tripod (`QIQTH/TripodGH.lean`) gave the first non-Euclidean limit — a
CAT(0) branch point, i.e. a tree singularity.  This file builds the opposite sign: the
**Euclidean cone `Cone θ` of total angle `θ ≤ 2π`**, whose apex carries the *deficit angle*
`2π − θ` — the textbook model of CONCENTRATED POSITIVE CURVATURE (a conical singularity, the
2D analogue of a cosmic string / point mass in 3D gravity).

* Points: the apex (`none`) plus polar pairs `some (r, φ)` with radius `r ∈ (0,1]` and angle
  `φ : AddCircle θ` (the circle of circumference `θ`).
* Metric: the **law of cosines** `lawCos r₁ r₂ δ = √(r₁² + r₂² − 2r₁r₂ cos δ)` at the angular
  distance `δ = ‖φ₁ − φ₂‖`.  Because the `AddCircle θ` norm is pinned at `δ ≤ θ/2 ≤ π`, the
  law-of-cosines formula needs **no case split** (no "path through the apex" branch): for
  `δ ≤ π` the straight chord is always optimal.  The triangle inequality is proved by the
  genuine two-case geometry (`lawCos_triangle`): angles summing `≤ π` unfold isometrically
  into the plane (the planar law-of-cosines identity + the Euclidean triangle inequality);
  angles summing `> π` route through the apex (`lawCos a b δ ≥ a − b cos δ` twice).
* `Cone θ` is a compact metric space (`instCompactSpaceCone`): it is the Lipschitz image of
  the compact cylinder `[0,1] × AddCircle θ` under the polar-coordinate map `fromPolar`.

## The curvature is a THEOREM, not prose

`cone_no_isometric_embedding_into_inner`: for every `θ < 2π` the cone admits NO
distance-preserving map into ANY real inner-product space.  The invariant is the SAME
unique-metric-midpoint argument as `QIQTH/IsotropyNoGo.lean` and the tripod: the two unit
radii at angles `0` and `θ/2` have TWO distinct metric midpoints — the points at radius
`cos (θ/4)` on the two bisecting angles `θ/4` and `θ/4 + θ/2` (the second bisects *the other
way around* the cone, which is where the deficit angle bites: for `θ < 2π` the two bisectors
are genuinely distinct points at distance `sin (θ/2) > 0`, while in the flat plane `θ = 2π`
they merge).  In an inner-product space the metric midpoint is unique and affine
(`inner_metric_midpoint_eq_affine_midpoint`), so both would collapse — contradiction.  This
makes "the apex carries genuine positive curvature" a machine-checked statement: the metric
space is not flat, in ANY dimension.

## Scope firewall (HONEST)

* **The curvature is CONCENTRATED** — an Alexandrov cone point (positive curvature in the
  comparison sense at the apex), NOT a smooth Riemann tensor, NOT a curved surface atlas,
  NOT a Riemannian manifold.  Away from the apex the cone is flat.
* **`θ` and the whole geometry are INPUTS** — this file transports a chosen deficit angle
  into a verified metric space; nothing is emergent.
* The Gromov–Hausdorff approximation by finite graph clouds is brick B2b (the intrinsic
  graph-geodesic version near a bending apex is the cited frontier), not this file.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.IsotropyNoGo
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace QIQTH.ConeMetric

open scoped NNReal

/-! ## Part 0 — the law-of-cosines chord function and its toolkit -/

/-- **The law-of-cosines chord length**: the distance between two points at radii `a`, `b`
and angular separation `δ`, as if laid out in the Euclidean plane. -/
noncomputable def lawCos (a b δ : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos δ)

/-- The chord length, unfolded. -/
lemma lawCos_def (a b δ : ℝ) :
    lawCos a b δ = Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos δ) := rfl

private lemma radicand_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (δ : ℝ) :
    0 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos δ := by
  nlinarith [Real.cos_le_one δ, sq_nonneg (a - b), mul_nonneg ha hb]

private lemma lawCos_comm (a b δ : ℝ) : lawCos a b δ = lawCos b a δ := by
  rw [lawCos_def, lawCos_def]
  congr 1
  ring

private lemma lawCos_neg (a b δ : ℝ) : lawCos a b (-δ) = lawCos a b δ := by
  rw [lawCos_def, lawCos_def, Real.cos_neg]

private lemma lawCos_self (a : ℝ) : lawCos a a 0 = 0 := by
  rw [lawCos_def, Real.cos_zero,
    show a ^ 2 + a ^ 2 - 2 * a * a * 1 = 0 by ring, Real.sqrt_zero]

/-- (F3) Monotonicity in the angle on `[0, π]`: a wider angle gives a longer chord. -/
private lemma lawCos_mono {a b δ δ' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ0 : 0 ≤ δ) (hδ'π : δ' ≤ Real.pi) (hδδ' : δ ≤ δ') :
    lawCos a b δ ≤ lawCos a b δ' := by
  rw [lawCos_def, lawCos_def]
  apply Real.sqrt_le_sqrt
  have hcos : Real.cos δ' ≤ Real.cos δ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hδ'π hδδ'
  nlinarith [mul_nonneg ha hb, hcos]

/-- (F5) The apex bound: the chord never exceeds the route through the apex. -/
private lemma lawCos_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (δ : ℝ) :
    lawCos a b δ ≤ a + b := by
  have h1 : a ^ 2 + b ^ 2 - 2 * a * b * Real.cos δ ≤ (a + b) ^ 2 := by
    nlinarith [Real.neg_one_le_cos δ, mul_nonneg ha hb]
  calc lawCos a b δ ≤ Real.sqrt ((a + b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = a + b := Real.sqrt_sq (by positivity)

/-- (F6) The projection lower bound: `a − b cos δ ≤ lawCos a b δ` (unconditionally). -/
private lemma le_lawCos (a b δ : ℝ) : a - b * Real.cos δ ≤ lawCos a b δ := by
  rcases le_or_gt (a - b * Real.cos δ) 0 with h | h
  · exact h.trans (Real.sqrt_nonneg _)
  · rw [lawCos_def]
    have hrad : (a - b * Real.cos δ) ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos δ := by
      nlinarith [Real.sin_sq δ, sq_nonneg (b * Real.sin δ), sq_nonneg b]
    calc a - b * Real.cos δ
        = Real.sqrt ((a - b * Real.cos δ) ^ 2) := (Real.sqrt_sq h.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt hrad

/-- (F2) Vanishing chord with positive radii and `δ ∈ [0, π]` forces equal radii and
zero angle. -/
private lemma lawCos_eq_zero_imp {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (h : lawCos a b δ = 0) : a = b ∧ δ = 0 := by
  have hπ := Real.pi_pos
  have hrad0 : a ^ 2 + b ^ 2 - 2 * a * b * Real.cos δ = 0 := by
    have hle := Real.sqrt_eq_zero'.mp h
    have hge := radicand_nonneg ha.le hb.le δ
    linarith
  have hc1 : Real.cos δ ≤ 1 := Real.cos_le_one δ
  have hsq : (a - b) ^ 2 ≤ 0 := by nlinarith [mul_pos ha hb]
  have h0 : (a - b) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have hab : a = b := sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
  subst hab
  have h2 : 2 * (a * a) * (1 - Real.cos δ) = 0 := by linear_combination hrad0
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by positivity)
  · have hc : Real.cos δ = 1 := by linarith
    have hδeq : δ = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hc
    exact ⟨rfl, hδeq⟩

/-- (F4) **The planar identity**: the chord at angle `α − β` IS the Euclidean distance
between the planar points `(a cos α, a sin α)` and `(b cos β, b sin β)`. -/
private lemma lawCos_eq_planar (a b α β : ℝ) :
    lawCos a b (α - β) = Real.sqrt ((a * Real.cos α - b * Real.cos β) ^ 2
      + (a * Real.sin α - b * Real.sin β) ^ 2) := by
  rw [lawCos_def]
  congr 1
  rw [Real.cos_sub]
  linear_combination (-a ^ 2) * Real.sin_sq_add_cos_sq α
    + (-b ^ 2) * Real.sin_sq_add_cos_sq β

/-- The Euclidean triangle inequality in coordinates, via `EuclideanSpace ℝ (Fin 2)`. -/
private lemma planar_triangle (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) :
    Real.sqrt ((x₁ - x₃) ^ 2 + (y₁ - y₃) ^ 2)
      ≤ Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2)
        + Real.sqrt ((x₂ - x₃) ^ 2 + (y₂ - y₃) ^ 2) := by
  have key : ∀ a b c d : ℝ,
      dist (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) !₂[c, d]
        = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
    intro a b c d
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
  have h := dist_triangle (!₂[x₁, y₁] : EuclideanSpace ℝ (Fin 2)) !₂[x₂, y₂] !₂[x₃, y₃]
  rwa [key, key, key] at h

/-- The quadratic cosine bound `1 − cos δ ≤ δ²/2` (via `sin² (δ/2) ≤ (δ/2)²`). -/
private lemma one_sub_cos_le_half_sq (δ : ℝ) : 1 - Real.cos δ ≤ δ ^ 2 / 2 := by
  have h1 : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (δ / 2)
    rwa [show 2 * (δ / 2) = δ by ring] at h
  have h2 : Real.sin (δ / 2) ^ 2 ≤ (δ / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := δ / 2)
    have h3 := mul_self_le_mul_self (abs_nonneg _) h
    rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at h3
  nlinarith [h1, h2]

/-- The Lipschitz-type bound for radii in `[0,1]`: `lawCos r r' δ ≤ |r − r'| + δ`. -/
private lemma lawCos_le_abs_add {r r' δ : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hr' : 0 ≤ r') (hr'1 : r' ≤ 1) (hδ : 0 ≤ δ) :
    lawCos r r' δ ≤ |r - r'| + δ := by
  have h1 := one_sub_cos_le_half_sq δ
  have h2' : 0 ≤ r * r' := mul_nonneg hr hr'
  have h2 : r * r' ≤ 1 := by nlinarith
  have h3 : 0 ≤ |r - r'| * δ := mul_nonneg (abs_nonneg _) hδ
  have h4 : |r - r'| ^ 2 = (r - r') ^ 2 := sq_abs _
  have hrad : r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos δ ≤ (|r - r'| + δ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 h2',
      mul_le_mul_of_nonneg_right h2 (sq_nonneg δ), h3, h4]
  calc lawCos r r' δ ≤ Real.sqrt ((|r - r'| + δ) ^ 2) := Real.sqrt_le_sqrt hrad
    _ = |r - r'| + δ := Real.sqrt_sq (by positivity)

/-- **THE CHORD TRIANGLE INEQUALITY.**  For nonnegative radii and angles in `[0, π]` with
`δ₁₃ ≤ δ₁₂ + δ₂₃`, the law-of-cosines chords satisfy the triangle inequality.  Two cases:
angles summing `≤ π` unfold isometrically into the Euclidean plane (the planar identity F4
plus the planar triangle inequality); angles summing `> π` route through the apex
(`cos δ₁₂ + cos δ₂₃ ≤ 0`, then the projection bound F6 twice and the apex bound F5). -/
theorem lawCos_triangle {r₁ r₂ r₃ δ₁₂ δ₂₃ δ₁₃ : ℝ}
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃)
    (_h₁₂0 : 0 ≤ δ₁₂) (_h₂₃0 : 0 ≤ δ₂₃) (h₁₃0 : 0 ≤ δ₁₃)
    (h₁₂π : δ₁₂ ≤ Real.pi) (h₂₃π : δ₂₃ ≤ Real.pi) (_h₁₃π : δ₁₃ ≤ Real.pi)
    (htri : δ₁₃ ≤ δ₁₂ + δ₂₃) :
    lawCos r₁ r₃ δ₁₃ ≤ lawCos r₁ r₂ δ₁₂ + lawCos r₂ r₃ δ₂₃ := by
  rcases le_or_gt (δ₁₂ + δ₂₃) Real.pi with hsum | hsum
  · -- planar case: lay the three radii out at angles 0, δ₁₂, δ₁₂ + δ₂₃
    have e12 : lawCos r₁ r₂ δ₁₂
        = Real.sqrt ((r₁ * Real.cos 0 - r₂ * Real.cos δ₁₂) ^ 2
          + (r₁ * Real.sin 0 - r₂ * Real.sin δ₁₂) ^ 2) := by
      rw [← lawCos_eq_planar r₁ r₂ 0 δ₁₂, show (0 : ℝ) - δ₁₂ = -δ₁₂ by ring, lawCos_neg]
    have e23 : lawCos r₂ r₃ δ₂₃
        = Real.sqrt ((r₂ * Real.cos δ₁₂ - r₃ * Real.cos (δ₁₂ + δ₂₃)) ^ 2
          + (r₂ * Real.sin δ₁₂ - r₃ * Real.sin (δ₁₂ + δ₂₃)) ^ 2) := by
      rw [← lawCos_eq_planar r₂ r₃ δ₁₂ (δ₁₂ + δ₂₃),
        show δ₁₂ - (δ₁₂ + δ₂₃) = -δ₂₃ by ring, lawCos_neg]
    have e13 : lawCos r₁ r₃ (δ₁₂ + δ₂₃)
        = Real.sqrt ((r₁ * Real.cos 0 - r₃ * Real.cos (δ₁₂ + δ₂₃)) ^ 2
          + (r₁ * Real.sin 0 - r₃ * Real.sin (δ₁₂ + δ₂₃)) ^ 2) := by
      rw [← lawCos_eq_planar r₁ r₃ 0 (δ₁₂ + δ₂₃),
        show (0 : ℝ) - (δ₁₂ + δ₂₃) = -(δ₁₂ + δ₂₃) by ring, lawCos_neg]
    calc lawCos r₁ r₃ δ₁₃ ≤ lawCos r₁ r₃ (δ₁₂ + δ₂₃) :=
          lawCos_mono h₁ h₃ h₁₃0 hsum htri
      _ = Real.sqrt ((r₁ * Real.cos 0 - r₃ * Real.cos (δ₁₂ + δ₂₃)) ^ 2
          + (r₁ * Real.sin 0 - r₃ * Real.sin (δ₁₂ + δ₂₃)) ^ 2) := e13
      _ ≤ Real.sqrt ((r₁ * Real.cos 0 - r₂ * Real.cos δ₁₂) ^ 2
            + (r₁ * Real.sin 0 - r₂ * Real.sin δ₁₂) ^ 2)
          + Real.sqrt ((r₂ * Real.cos δ₁₂ - r₃ * Real.cos (δ₁₂ + δ₂₃)) ^ 2
            + (r₂ * Real.sin δ₁₂ - r₃ * Real.sin (δ₁₂ + δ₂₃)) ^ 2) :=
          planar_triangle _ _ _ _ _ _
      _ = lawCos r₁ r₂ δ₁₂ + lawCos r₂ r₃ δ₂₃ := by rw [← e12, ← e23]
  · -- apex case: the two cosines cannot both be positive
    have hcos : Real.cos δ₂₃ ≤ -Real.cos δ₁₂ := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith : (0 : ℝ) ≤ Real.pi - δ₁₂) h₂₃π (by linarith)
      rwa [Real.cos_pi_sub] at h
    have hA := le_lawCos r₁ r₂ δ₁₂
    have hB := le_lawCos r₃ r₂ δ₂₃
    rw [lawCos_comm r₃ r₂] at hB
    have hC := lawCos_le_add h₁ h₃ δ₁₃
    nlinarith [hA, hB, hC,
      mul_nonneg h₂ (by linarith : (0 : ℝ) ≤ -(Real.cos δ₁₂ + Real.cos δ₂₃))]

/-! ## Part 1 — the cone and its distance -/

/-- **The cone of total angle `θ`**: the apex (`none`) plus polar points `some (r, φ)` at
radius `r ∈ (0, 1]` and angle `φ` on the circle of circumference `θ`. -/
def Cone (θ : ℝ) : Type := Option (Set.Ioc (0 : ℝ) 1 × AddCircle θ)

/-- **The cone metric**: apex to `(r, φ)` costs `r`; two polar points are at the law-of-
cosines chord distance at their angular separation `‖φ₁ − φ₂‖ ≤ θ/2`. -/
noncomputable def coneDist (θ : ℝ) : Cone θ → Cone θ → ℝ
  | none, none => 0
  | none, some q => q.1.1
  | some p, none => p.1.1
  | some p, some q => lawCos p.1.1 q.1.1 ‖p.2 - q.2‖

@[simp] lemma coneDist_none_none (θ : ℝ) : coneDist θ none none = 0 := rfl

@[simp] lemma coneDist_none_some (θ : ℝ) (r : Set.Ioc (0 : ℝ) 1) (φ : AddCircle θ) :
    coneDist θ none (some (r, φ)) = r.1 := rfl

@[simp] lemma coneDist_some_none (θ : ℝ) (r : Set.Ioc (0 : ℝ) 1) (φ : AddCircle θ) :
    coneDist θ (some (r, φ)) none = r.1 := rfl

@[simp] lemma coneDist_some_some (θ : ℝ) (r₁ r₂ : Set.Ioc (0 : ℝ) 1)
    (φ₁ φ₂ : AddCircle θ) :
    coneDist θ (some (r₁, φ₁)) (some (r₂, φ₂)) = lawCos r₁.1 r₂.1 ‖φ₁ - φ₂‖ := rfl

/-- **The polar-coordinate map** from the closed cylinder: radius `0` collapses to the
apex, positive radii map to the corresponding polar point. -/
noncomputable def fromPolar (θ : ℝ) (p : Set.Icc (0 : ℝ) 1 × AddCircle θ) : Cone θ :=
  if h : p.1.1 = 0 then none
  else some (⟨p.1.1, lt_of_le_of_ne p.1.2.1 (Ne.symm h), p.1.2.2⟩, p.2)

lemma fromPolar_of_eq (θ : ℝ) {p : Set.Icc (0 : ℝ) 1 × AddCircle θ} (h : p.1.1 = 0) :
    fromPolar θ p = none := dif_pos h

lemma fromPolar_of_ne (θ : ℝ) {p : Set.Icc (0 : ℝ) 1 × AddCircle θ} (h : p.1.1 ≠ 0) :
    fromPolar θ p
      = some (⟨p.1.1, lt_of_le_of_ne p.1.2.1 (Ne.symm h), p.1.2.2⟩, p.2) := dif_neg h

/-- The polar map is onto: the apex comes from radius `0`, everything else from itself. -/
lemma fromPolar_surjective (θ : ℝ) : Function.Surjective (fromPolar θ) := by
  intro x
  rcases x with _ | ⟨r, φ⟩
  · exact ⟨(⟨0, Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩, 0), fromPolar_of_eq θ rfl⟩
  · exact ⟨(⟨r.1, Set.mem_Icc.mpr ⟨r.2.1.le, r.2.2⟩⟩, φ),
      fromPolar_of_ne θ (ne_of_gt r.2.1)⟩

/-- The uniform Lipschitz-type bound for the polar map, covering the apex cases: the cone
distance is at most the radius gap plus the angle gap. -/
lemma coneDist_fromPolar_le (θ : ℝ) (p q : Set.Icc (0 : ℝ) 1 × AddCircle θ) :
    coneDist θ (fromPolar θ p) (fromPolar θ q) ≤ |p.1.1 - q.1.1| + ‖p.2 - q.2‖ := by
  rcases eq_or_ne p.1.1 0 with hp | hp <;> rcases eq_or_ne q.1.1 0 with hq | hq
  · rw [fromPolar_of_eq θ hp, fromPolar_of_eq θ hq, coneDist_none_none]
    positivity
  · rw [fromPolar_of_eq θ hp, fromPolar_of_ne θ hq]
    show q.1.1 ≤ |p.1.1 - q.1.1| + ‖p.2 - q.2‖
    have habs : |p.1.1 - q.1.1| = q.1.1 := by
      rw [hp, zero_sub, abs_neg, abs_of_nonneg q.1.2.1]
    have hn := norm_nonneg (p.2 - q.2)
    linarith
  · rw [fromPolar_of_ne θ hp, fromPolar_of_eq θ hq]
    show p.1.1 ≤ |p.1.1 - q.1.1| + ‖p.2 - q.2‖
    have habs : |p.1.1 - q.1.1| = p.1.1 := by
      rw [hq, sub_zero, abs_of_nonneg p.1.2.1]
    have hn := norm_nonneg (p.2 - q.2)
    linarith
  · rw [fromPolar_of_ne θ hp, fromPolar_of_ne θ hq]
    show lawCos p.1.1 q.1.1 ‖p.2 - q.2‖ ≤ |p.1.1 - q.1.1| + ‖p.2 - q.2‖
    exact lawCos_le_abs_add p.1.2.1 p.1.2.2 q.1.2.1 q.1.2.2 (norm_nonneg _)

instance instNonemptyCone (θ : ℝ) : Nonempty (Cone θ) := ⟨none⟩

/-! ## Part 2 — the metric space structure (needs `0 < θ ≤ 2π`) -/

section Metric

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)]

/-- The angular distance on `AddCircle θ` is pinned at `θ/2 ≤ π` — this is what makes the
single-formula law-of-cosines metric correct with no case split. -/
private lemma angNorm_le_pi (x : AddCircle θ) : ‖x‖ ≤ Real.pi := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have hθ2π : θ ≤ 2 * Real.pi := Fact.out
  have h : ‖x‖ ≤ |θ| / 2 := AddCircle.norm_le_half_period θ hθ0.ne'
  rw [abs_of_pos hθ0] at h
  linarith

omit [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] in
private lemma coneDist_self (x : Cone θ) : coneDist θ x x = 0 := by
  rcases x with _ | ⟨r, φ⟩
  · rfl
  · rw [coneDist_some_some, sub_self, norm_zero, lawCos_self]

omit [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] in
private lemma coneDist_comm (x y : Cone θ) : coneDist θ x y = coneDist θ y x := by
  rcases x with _ | ⟨r₁, φ₁⟩ <;> rcases y with _ | ⟨r₂, φ₂⟩
  · rfl
  · rfl
  · rfl
  · rw [coneDist_some_some, coneDist_some_some, lawCos_comm, norm_sub_rev]

private lemma coneDist_triangle (x y z : Cone θ) :
    coneDist θ x z ≤ coneDist θ x y + coneDist θ y z := by
  rcases x with _ | ⟨r₁, φ₁⟩ <;> rcases y with _ | ⟨r₂, φ₂⟩ <;> rcases z with _ | ⟨r₃, φ₃⟩
  · simp
  · simp
  · -- apex to apex via a polar point
    simp only [coneDist_none_none, coneDist_none_some, coneDist_some_none]
    linarith [r₂.2.1]
  · -- apex to polar via a polar point: F6 with cos ≤ 1
    simp only [coneDist_none_some, coneDist_some_some]
    have h6 := le_lawCos r₃.1 r₂.1 ‖φ₂ - φ₃‖
    rw [lawCos_comm] at h6
    nlinarith [h6, Real.cos_le_one ‖φ₂ - φ₃‖, r₂.2.1]
  · simp
  · -- polar to polar via the apex: F5
    simp only [coneDist_some_none, coneDist_none_some, coneDist_some_some]
    exact lawCos_le_add r₁.2.1.le r₃.2.1.le _
  · -- polar to apex via a polar point: F6 with cos ≤ 1
    simp only [coneDist_some_none, coneDist_some_some]
    nlinarith [le_lawCos r₁.1 r₂.1 ‖φ₁ - φ₂‖, Real.cos_le_one ‖φ₁ - φ₂‖, r₂.2.1]
  · -- the main case: the chord triangle inequality at the AddCircle angular distances
    simp only [coneDist_some_some]
    have htri : ‖φ₁ - φ₃‖ ≤ ‖φ₁ - φ₂‖ + ‖φ₂ - φ₃‖ := by
      have he : φ₁ - φ₃ = (φ₁ - φ₂) + (φ₂ - φ₃) := by abel
      rw [he]
      exact norm_add_le _ _
    exact lawCos_triangle r₁.2.1.le r₂.2.1.le r₃.2.1.le
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (angNorm_le_pi θ _) (angNorm_le_pi θ _) (angNorm_le_pi θ _) htri

private lemma coneDist_eq_zero_imp : ∀ {x y : Cone θ}, coneDist θ x y = 0 → x = y := by
  intro x y h
  rcases x with _ | ⟨r₁, φ₁⟩ <;> rcases y with _ | ⟨r₂, φ₂⟩
  · rfl
  · rw [coneDist_none_some] at h
    exact absurd h (ne_of_gt r₂.2.1)
  · rw [coneDist_some_none] at h
    exact absurd h (ne_of_gt r₁.2.1)
  · rw [coneDist_some_some] at h
    obtain ⟨hr, hδ⟩ := lawCos_eq_zero_imp r₁.2.1 r₂.2.1 (norm_nonneg _)
      (angNorm_le_pi θ _) h
    have hφ : φ₁ = φ₂ := sub_eq_zero.mp (norm_eq_zero.mp hδ)
    rw [Subtype.ext hr, hφ]

/-- **The cone is a metric space** under the law-of-cosines metric — no case split needed
because the `AddCircle θ` angular distance is pinned at `θ/2 ≤ π`. -/
noncomputable instance instMetricSpaceCone : MetricSpace (Cone θ) where
  dist := coneDist θ
  dist_self := coneDist_self θ
  dist_comm := coneDist_comm θ
  dist_triangle := coneDist_triangle θ
  eq_of_dist_eq_zero := coneDist_eq_zero_imp θ

/-- The cone distance, unfolded. -/
lemma dist_eq_coneDist (x y : Cone θ) : dist x y = coneDist θ x y := rfl

/-! ## Part 3 — compactness via the polar-coordinate map -/

/-- **The polar map is `2`-Lipschitz** from the product-metric cylinder
`[0,1] × AddCircle θ` (whose distance is the max of the radius and angle gaps). -/
lemma lipschitz_fromPolar : LipschitzWith 2 (fromPolar θ) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h1 : |p.1.1 - q.1.1| ≤ dist p q := by
    have hle : dist p.1 q.1 ≤ dist p q := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    rwa [Subtype.dist_eq, Real.dist_eq] at hle
  have h2 : ‖p.2 - q.2‖ ≤ dist p q := by
    have hle : dist p.2 q.2 ≤ dist p q := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    rwa [dist_eq_norm] at hle
  calc dist (fromPolar θ p) (fromPolar θ q)
      = coneDist θ (fromPolar θ p) (fromPolar θ q) := rfl
    _ ≤ |p.1.1 - q.1.1| + ‖p.2 - q.2‖ := coneDist_fromPolar_le θ p q
    _ ≤ dist p q + dist p q := add_le_add h1 h2
    _ = (2 : ℝ≥0) * dist p q := by push_cast; ring

/-- **The cone is compact**: the Lipschitz image of the compact cylinder
`[0,1] × AddCircle θ`. -/
instance instCompactSpaceCone : CompactSpace (Cone θ) := by
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr (fromPolar_surjective θ), ← Set.image_univ]
  exact isCompact_univ.image (lipschitz_fromPolar θ).continuous

/-! ## Part 4 — THE CURVATURE THEOREM -/

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The `AddCircle θ` norm of a coercion difference with representative in `[-θ/2, θ/2]`. -/
private lemma angNorm_sub_coe (x y : ℝ) (h : |x - y| ≤ θ / 2) :
    ‖((x : ℝ) : AddCircle θ) - ((y : ℝ) : AddCircle θ)‖ = |x - y| := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  rw [← QuotientAddGroup.mk_sub]
  exact (AddCircle.norm_coe_eq_abs_iff θ hθ0.ne').mpr (by rwa [abs_of_pos hθ0])

/-- **THE CURVATURE THEOREM.**  For every deficit angle (`θ < 2π`) the cone admits NO
distance-preserving map into ANY real inner-product space: the apex is a genuine
concentrated-positive-curvature obstruction.  The invariant is the SAME unique-midpoint
argument as `IsotropyNoGo`/`TripodGH`: the two unit radii at angles `0` and `θ/2` have TWO
distinct metric midpoints — the radius-`cos (θ/4)` points on the two bisectors `θ/4` and
`3θ/4` (the second bisects the other way around the cone; they are `sin (θ/2) > 0` apart,
merging only in the flat plane `θ = 2π`).  In an inner-product space both would have to be
the affine midpoint `½(f P₁ + f P₂)` — contradiction. -/
theorem cone_no_isometric_embedding_into_inner (hθlt : θ < 2 * Real.pi)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Cone θ → E) (hf : ∀ p q : Cone θ, dist (f p) (f q) = dist p q) : False := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- side conditions
  have hc0 : 0 < Real.cos (θ / 4) :=
    Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  have hc1 : Real.cos (θ / 4) ≤ 1 := Real.cos_le_one _
  have hone : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_Ioc.mpr ⟨one_pos, le_rfl⟩
  have hcmem : Real.cos (θ / 4) ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_Ioc.mpr ⟨hc0, hc1⟩
  have hs4 : 0 < Real.sin (θ / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2 : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the exact chord values
  have hL1 : lawCos 1 1 (θ / 2) = 2 * Real.sin (θ / 4) := by
    have hs := Real.sin_half_eq_sqrt (x := θ / 2) (by linarith) (by linarith)
    rw [show θ / 2 / 2 = θ / 4 by ring] at hs
    rw [lawCos_def,
      show (1 : ℝ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 * Real.cos (θ / 2)
        = 2 ^ 2 * ((1 - Real.cos (θ / 2)) / 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← hs]
  have hL2 : lawCos 1 (Real.cos (θ / 4)) (θ / 4) = Real.sin (θ / 4) := by
    rw [lawCos_def,
      show (1 : ℝ) ^ 2 + Real.cos (θ / 4) ^ 2
          - 2 * 1 * Real.cos (θ / 4) * Real.cos (θ / 4)
        = 1 - Real.cos (θ / 4) ^ 2 by ring,
      ← Real.sin_sq, Real.sqrt_sq hs4.le]
  have hL2' : lawCos (Real.cos (θ / 4)) 1 (θ / 4) = Real.sin (θ / 4) := by
    rw [lawCos_comm]
    exact hL2
  have hL3 : lawCos (Real.cos (θ / 4)) (Real.cos (θ / 4)) (θ / 2) = Real.sin (θ / 2) := by
    have h1 := Real.cos_two_mul_eq_one_sub (θ / 4)
    rw [show 2 * (θ / 4) = θ / 2 by ring] at h1
    have h2 := Real.sin_two_mul (θ / 4)
    rw [show 2 * (θ / 4) = θ / 2 by ring] at h2
    rw [lawCos_def,
      show Real.cos (θ / 4) ^ 2 + Real.cos (θ / 4) ^ 2
          - 2 * Real.cos (θ / 4) * Real.cos (θ / 4) * Real.cos (θ / 2)
        = (2 * Real.sin (θ / 4) * Real.cos (θ / 4)) ^ 2 by rw [h1]; ring,
      ← h2, Real.sqrt_sq hs2.le]
  -- the angular distances (all representatives reduced into [-θ/2, θ/2])
  have hn12 : ‖((0 : ℝ) : AddCircle θ) - ((θ / 2 : ℝ) : AddCircle θ)‖ = θ / 2 := by
    have habs : |(0 : ℝ) - θ / 2| = θ / 2 := by
      rw [zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < θ / 2)]
    rw [angNorm_sub_coe θ 0 (θ / 2) (by rw [habs]), habs]
  have hn1M : ‖((0 : ℝ) : AddCircle θ) - ((θ / 4 : ℝ) : AddCircle θ)‖ = θ / 4 := by
    have habs : |(0 : ℝ) - θ / 4| = θ / 4 := by
      rw [zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < θ / 4)]
    rw [angNorm_sub_coe θ 0 (θ / 4) (by rw [habs]; linarith), habs]
  have hnM2 : ‖((θ / 4 : ℝ) : AddCircle θ) - ((θ / 2 : ℝ) : AddCircle θ)‖ = θ / 4 := by
    have habs : |(θ / 4 : ℝ) - θ / 2| = θ / 4 := by
      rw [show (θ / 4 : ℝ) - θ / 2 = -(θ / 4) by ring, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < θ / 4)]
    rw [angNorm_sub_coe θ (θ / 4) (θ / 2) (by rw [habs]; linarith), habs]
  have hshift : ((3 * θ / 4 : ℝ) : AddCircle θ) = ((-(θ / 4) : ℝ) : AddCircle θ) := by
    rw [show (3 * θ / 4 : ℝ) = -(θ / 4) + θ by ring, QuotientAddGroup.mk_add,
      AddCircle.coe_period, add_zero]
  have hn1M' : ‖((0 : ℝ) : AddCircle θ) - ((3 * θ / 4 : ℝ) : AddCircle θ)‖ = θ / 4 := by
    rw [hshift]
    have habs : |(0 : ℝ) - -(θ / 4)| = θ / 4 := by
      rw [zero_sub, neg_neg, abs_of_pos (by linarith : (0 : ℝ) < θ / 4)]
    rw [angNorm_sub_coe θ 0 (-(θ / 4)) (by rw [habs]; linarith), habs]
  have hnM'2 : ‖((3 * θ / 4 : ℝ) : AddCircle θ) - ((θ / 2 : ℝ) : AddCircle θ)‖
      = θ / 4 := by
    have habs : |(3 * θ / 4 : ℝ) - θ / 2| = θ / 4 := by
      rw [show (3 * θ / 4 : ℝ) - θ / 2 = θ / 4 by ring,
        abs_of_pos (by linarith : (0 : ℝ) < θ / 4)]
    rw [angNorm_sub_coe θ (3 * θ / 4) (θ / 2) (by rw [habs]; linarith), habs]
  have hnMM' : ‖((θ / 4 : ℝ) : AddCircle θ) - ((3 * θ / 4 : ℝ) : AddCircle θ)‖
      = θ / 2 := by
    have habs : |(θ / 4 : ℝ) - 3 * θ / 4| = θ / 2 := by
      rw [show (θ / 4 : ℝ) - 3 * θ / 4 = -(θ / 2) by ring, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < θ / 2)]
    rw [angNorm_sub_coe θ (θ / 4) (3 * θ / 4) (by rw [habs]), habs]
  -- the five distances feeding the double-midpoint argument
  have hd1M : dist (f (some (⟨1, hone⟩, ((0 : ℝ) : AddCircle θ))))
      (f (some (⟨Real.cos (θ / 4), hcmem⟩, ((θ / 4 : ℝ) : AddCircle θ))))
      = Real.sin (θ / 4) := by
    rw [hf]
    show lawCos 1 (Real.cos (θ / 4))
      ‖((0 : ℝ) : AddCircle θ) - ((θ / 4 : ℝ) : AddCircle θ)‖ = Real.sin (θ / 4)
    rw [hn1M, hL2]
  have hdM2 : dist (f (some (⟨Real.cos (θ / 4), hcmem⟩, ((θ / 4 : ℝ) : AddCircle θ))))
      (f (some (⟨1, hone⟩, ((θ / 2 : ℝ) : AddCircle θ)))) = Real.sin (θ / 4) := by
    rw [hf]
    show lawCos (Real.cos (θ / 4)) 1
      ‖((θ / 4 : ℝ) : AddCircle θ) - ((θ / 2 : ℝ) : AddCircle θ)‖ = Real.sin (θ / 4)
    rw [hnM2, hL2']
  have hd12 : dist (f (some (⟨1, hone⟩, ((0 : ℝ) : AddCircle θ))))
      (f (some (⟨1, hone⟩, ((θ / 2 : ℝ) : AddCircle θ)))) = 2 * Real.sin (θ / 4) := by
    rw [hf]
    show lawCos 1 1 ‖((0 : ℝ) : AddCircle θ) - ((θ / 2 : ℝ) : AddCircle θ)‖
      = 2 * Real.sin (θ / 4)
    rw [hn12, hL1]
  have hd1M' : dist (f (some (⟨1, hone⟩, ((0 : ℝ) : AddCircle θ))))
      (f (some (⟨Real.cos (θ / 4), hcmem⟩, ((3 * θ / 4 : ℝ) : AddCircle θ))))
      = Real.sin (θ / 4) := by
    rw [hf]
    show lawCos 1 (Real.cos (θ / 4))
      ‖((0 : ℝ) : AddCircle θ) - ((3 * θ / 4 : ℝ) : AddCircle θ)‖ = Real.sin (θ / 4)
    rw [hn1M', hL2]
  have hdM'2 : dist
      (f (some (⟨Real.cos (θ / 4), hcmem⟩, ((3 * θ / 4 : ℝ) : AddCircle θ))))
      (f (some (⟨1, hone⟩, ((θ / 2 : ℝ) : AddCircle θ)))) = Real.sin (θ / 4) := by
    rw [hf]
    show lawCos (Real.cos (θ / 4)) 1
      ‖((3 * θ / 4 : ℝ) : AddCircle θ) - ((θ / 2 : ℝ) : AddCircle θ)‖ = Real.sin (θ / 4)
    rw [hnM'2, hL2']
  -- the two bisector points are sin(θ/2) apart in the cone …
  have hdMM' : @dist (Cone θ) _
      (some (⟨Real.cos (θ / 4), hcmem⟩, ((θ / 4 : ℝ) : AddCircle θ)))
      (some (⟨Real.cos (θ / 4), hcmem⟩, ((3 * θ / 4 : ℝ) : AddCircle θ)))
      = Real.sin (θ / 2) := by
    show lawCos (Real.cos (θ / 4)) (Real.cos (θ / 4))
      ‖((θ / 4 : ℝ) : AddCircle θ) - ((3 * θ / 4 : ℝ) : AddCircle θ)‖ = Real.sin (θ / 2)
    rw [hnMM', hL3]
  -- … but both are metric midpoints of (P₁, P₂), hence share the affine-midpoint image
  have hm := IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint hd1M hdM2 hd12
  have hm' := IsotropyNoGo.inner_metric_midpoint_eq_affine_midpoint hd1M' hdM'2 hd12
  have hMeq : f (some (⟨Real.cos (θ / 4), hcmem⟩, ((θ / 4 : ℝ) : AddCircle θ)))
      = f (some (⟨Real.cos (θ / 4), hcmem⟩, ((3 * θ / 4 : ℝ) : AddCircle θ))) :=
    hm.trans hm'.symm
  have h0 : Real.sin (θ / 2) = 0 := by
    rw [← hdMM', ← hf, hMeq, dist_self]
  exact absurd h0 (ne_of_gt hs2)

end Metric

end QIQTH.ConeMetric
