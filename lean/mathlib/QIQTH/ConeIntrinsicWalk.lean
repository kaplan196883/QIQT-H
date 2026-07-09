/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE INTRINSIC CONE WALK — the unfolded-segment walk: connectivity and the hop-metric
upper bound (brick K2, the crux)

Brick K2 of the INTRINSIC-CONE track
(`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`).  Brick K1
(`QIQTH/ConeIntrinsicGraph.lean`) built the geometric graph `coneGraph θ n ρ` on the polar
grid and the trivial lower bound `coneDist ≤ ρ · hopcount`, leaving `Reachable` as a
hypothesis.  This brick discharges it with an EXPLICIT walk and proves the matching upper
bound — the hard half of the K3 pinching.

## The geometry (honest description)

The walk follows the cone GEODESIC by **unfolding** the sector between the two points into
the Euclidean plane: for polar points `P = (r₁, φ₁)` and `Q = (r₂, φ₂)` at angular
separation `s = ‖φ₂ − φ₁‖ ≤ θ/2 < π`, the law-of-cosines metric of `Cone θ` IS the planar
distance between `r₁` (on the real axis) and `r₂·e^{is}`, so the straight segment

    seg t = (1−t)·r₁ + t·r₂·e^{is}       (t ∈ [0,1], in ℂ)

is an isometric picture of the cone geodesic.  Waypoints `seg (j/k)` are pulled back
through polar coordinates (`Complex.arg`), giving cone points
`(‖seg t‖, φ₁ + arg (seg t))`.  **THE SECTOR LEMMA** (`seg_arg_nonneg` + `seg_arg_le`) is
what makes this work: the segment stays inside the closed convex sector of aperture
`s < π`, so `arg (seg t) ∈ [0, s]` throughout — the branch cut of `arg` is never
approached, and the pullback is distance-NONEXPANDING (angle differences on `AddCircle θ`
only shrink, and the law-of-cosines chord is monotone in the angle on `[0, π]`).  Each
waypoint then snaps to the polar grid via the B2b net (cost `2·mesh θ n` per hop), and the
lazy-chain walk builder from the isotropy campaign (`StencilWalk.walk_of_lazy_chain`)
assembles the walk.  Apex-adjacent pairs use the same machinery degenerately: a RADIAL
chain at fixed angle.

**`θ < 2π` (a genuine deficit angle) is REQUIRED** for the polar/polar case: it pins the
angular separation at `s ≤ θ/2 < π`, so the unfolded segment misses the apex.  At `θ = 2π`
antipodal pairs would have segments running exactly through the origin, where `arg` (and
the geodesic) degenerates.

## The K2 theorems

* `coneWalk_exists` — the explicit walk, `length ≤ ⌈dist x y / (ρ − 2·mesh θ n)⌉₊`;
* `coneGraph_reachable` — connectivity of the intrinsic cone graph for `ρ > 2·mesh θ n`
  (discharges brick K1's `Reachable` hypothesis, so `dist_le_rho_mul_dist` fires
  unconditionally);
* `coneGraph_dist_le` — the matching UPPER bound on the hop metric:
  `hopdist ≤ coneDist/(ρ − 2·mesh) + 1`.

## Scope firewall (HONEST)

* **The cone geometry is INSERTED through the adjacency rule** (`dist x y ≤ ρ`, the cone
  metric) — nothing about the cone is emergent from combinatorics; the combinatorics
  RECOVERS a geometry that was put in by hand.
* **`θ` is an INPUT** — a chosen deficit angle, not derived.
* **The curvature is CONCENTRATED** — an Alexandrov cone point, NOT a smooth Riemann
  tensor, NOT a Riemannian manifold.  Away from the apex the cone is flat.
* NOT GR, NOT numerical-G, NOT QG.  The GH capstone (hop metric → cone in the
  Gromov–Hausdorff sense) is brick K3.  No axioms, no `sorry`.
-/
import QIQTH.ConeIntrinsicGraph
import QIQTH.StencilWalk
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Trigonometric

namespace QIQTH.ConeIntrinsicWalk

open QIQTH.ConeMetric QIQTH.ConeGH QIQTH.ConeIntrinsicGraph

/-! ## Part 0 — the `lawCos` toolkit (B2a's private lemmas restated) and the two bridges -/

private lemma lawCos_comm (a b δ : ℝ) : lawCos a b δ = lawCos b a δ := by
  rw [lawCos_def, lawCos_def]
  congr 1
  ring

private lemma lawCos_neg (a b δ : ℝ) : lawCos a b (-δ) = lawCos a b δ := by
  rw [lawCos_def, lawCos_def, Real.cos_neg]

private lemma lawCos_abs (a b δ : ℝ) : lawCos a b |δ| = lawCos a b δ := by
  rcases abs_choice δ with h | h
  · rw [h]
  · rw [h, lawCos_neg]

/-- (F3, restated from B2a) Monotonicity in the angle on `[0, π]`. -/
private lemma lawCos_mono {a b δ δ' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ0 : 0 ≤ δ) (hδ'π : δ' ≤ Real.pi) (hδδ' : δ ≤ δ') :
    lawCos a b δ ≤ lawCos a b δ' := by
  rw [lawCos_def, lawCos_def]
  apply Real.sqrt_le_sqrt
  have hcos : Real.cos δ' ≤ Real.cos δ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hδ'π hδδ'
  nlinarith [mul_nonneg ha hb, hcos]

/-- Zero angle: the chord is the radius gap (the radial-chain step formula). -/
private lemma lawCos_zero_angle (a b : ℝ) : lawCos a b 0 = |a - b| := by
  rw [lawCos_def, Real.cos_zero, mul_one,
    show a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- (F4, restated from B2a) The planar identity in coordinates. -/
private lemma lawCos_eq_planar (a b α β : ℝ) :
    lawCos a b (α - β) = Real.sqrt ((a * Real.cos α - b * Real.cos β) ^ 2
      + (a * Real.sin α - b * Real.sin β) ^ 2) := by
  rw [lawCos_def]
  congr 1
  rw [Real.cos_sub]
  linear_combination (-a ^ 2) * Real.sin_sq_add_cos_sq α
    + (-b ^ 2) * Real.sin_sq_add_cos_sq β

/-- **Round minimality**: `round t` is the closest integer to `t`. -/
private lemma abs_sub_round_le (t : ℝ) (m : ℤ) : |t - round t| ≤ |t - (m : ℝ)| := by
  rcases eq_or_ne m (round t) with rfl | hne
  · exact le_rfl
  · have h1 : (1 : ℤ) ≤ |round t - m| :=
      Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hne))
    have h1' : (1 : ℝ) ≤ |((round t : ℤ) : ℝ) - (m : ℝ)| := by exact_mod_cast h1
    have h2 : |t - ((round t : ℤ) : ℝ)| ≤ 1 / 2 := abs_sub_round t
    have h3 : |((round t : ℤ) : ℝ) - (m : ℝ)|
        ≤ |((round t : ℤ) : ℝ) - t| + |t - (m : ℝ)| := abs_sub_le _ _ _
    have h4 : |((round t : ℤ) : ℝ) - t| = |t - ((round t : ℤ) : ℝ)| := abs_sub_comm _ _
    linarith

/-- **The ℂ law of cosines**: the distance between two points in polar form is the
law-of-cosines chord at the angle difference — the bridge between the cone metric and the
complex plane where the unfolded segment lives. -/
lemma norm_sub_polar (a b α β : ℝ) :
    ‖(a : ℂ) * Complex.exp ((α : ℂ) * Complex.I)
      - (b : ℂ) * Complex.exp ((β : ℂ) * Complex.I)‖ = lawCos a b (α - β) := by
  have hre : ((a : ℂ) * Complex.exp ((α : ℂ) * Complex.I)
      - (b : ℂ) * Complex.exp ((β : ℂ) * Complex.I)).re
      = a * Real.cos α - b * Real.cos β := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have him : ((a : ℂ) * Complex.exp ((α : ℂ) * Complex.I)
      - (b : ℂ) * Complex.exp ((β : ℂ) * Complex.I)).im
      = a * Real.sin α - b * Real.sin β := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  rw [Complex.norm_def, Complex.normSq_apply, hre, him, lawCos_eq_planar]
  congr 1
  ring

/-! ## Part 1 — the unfolded segment and THE SECTOR LEMMA -/

/-- **The unfolded segment**: the straight planar segment from `r₁` (angle `0`) to
`r₂·e^{is}` (angle `s`), the isometric picture of the cone geodesic between two polar
points once their sector is unfolded into `ℂ`. -/
noncomputable def seg (r₁ r₂ s t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * (r₁ : ℂ)
    + ((t : ℝ) : ℂ) * ((r₂ : ℂ) * Complex.exp ((s : ℂ) * Complex.I))

private lemma seg_re (r₁ r₂ s t : ℝ) :
    (seg r₁ r₂ s t).re = (1 - t) * r₁ + t * (r₂ * Real.cos s) := by
  simp only [seg, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

private lemma seg_im (r₁ r₂ s t : ℝ) :
    (seg r₁ r₂ s t).im = t * (r₂ * Real.sin s) := by
  simp only [seg, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

private lemma seg_zero (r₁ r₂ s : ℝ) : seg r₁ r₂ s 0 = (r₁ : ℂ) := by
  unfold seg
  push_cast
  ring

private lemma seg_one (r₁ r₂ s : ℝ) :
    seg r₁ r₂ s 1 = (r₂ : ℂ) * Complex.exp ((s : ℂ) * Complex.I) := by
  unfold seg
  push_cast
  ring

/-- The segment is affine: differences scale linearly in the parameter. -/
private lemma seg_sub (r₁ r₂ s u v : ℝ) :
    seg r₁ r₂ s u - seg r₁ r₂ s v
      = ((u - v : ℝ) : ℂ) * ((r₂ : ℂ) * Complex.exp ((s : ℂ) * Complex.I) - (r₁ : ℂ)) := by
  unfold seg
  push_cast
  ring

/-- The unfolded chord is the law-of-cosines distance (endpoint form of `norm_sub_polar`). -/
private lemma norm_chord (r₁ r₂ s : ℝ) :
    ‖(r₂ : ℂ) * Complex.exp ((s : ℂ) * Complex.I) - (r₁ : ℂ)‖ = lawCos r₁ r₂ s := by
  have h := norm_sub_polar r₂ r₁ s 0
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, sub_zero] at h
  rw [h, lawCos_comm]

/-- For `s ∈ [0, π)` and positive radii the segment misses the origin — the apex is never
crossed (this is where `s < π`, i.e. `θ < 2π`, is load-bearing). -/
private lemma seg_ne_zero {r₁ r₂ s t : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hs0 : 0 ≤ s) (hsπ : s < Real.pi) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    seg r₁ r₂ s t ≠ 0 := by
  intro h
  have hre : (1 - t) * r₁ + t * (r₂ * Real.cos s) = 0 := by
    rw [← seg_re r₁ r₂ s t, h, Complex.zero_re]
  have him : t * (r₂ * Real.sin s) = 0 := by
    rw [← seg_im r₁ r₂ s t, h, Complex.zero_im]
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- s = 0: a convex combination of two positives cannot vanish
    rw [← hs, Real.cos_zero, mul_one] at hre
    rcases eq_or_lt_of_le ht0 with ht | ht
    · rw [← ht] at hre
      norm_num at hre
      linarith
    · have h1 : 0 < t * r₂ := mul_pos ht hr₂
      have h2 : 0 ≤ (1 - t) * r₁ := mul_nonneg (by linarith) hr₁.le
      linarith
  · -- 0 < s < π: the imaginary part forces t = 0, then the real part is r₁ > 0
    have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs hsπ
    have ht' : t = 0 := by
      by_contra htne
      have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
      have : 0 < t * (r₂ * Real.sin s) := mul_pos htpos (mul_pos hr₂ hsin)
      linarith
    rw [ht'] at hre
    norm_num at hre
    linarith

/-- The segment stays inside the closed unit disc when both radii are `≤ 1`. -/
private lemma seg_norm_le_one {r₁ r₂ t : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1)
    (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1) (s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖seg r₁ r₂ s t‖ ≤ 1 := by
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have hA : ‖((1 - t : ℝ) : ℂ) * (r₁ : ℂ)‖ = (1 - t) * r₁ := by
    rw [← Complex.ofReal_mul, Complex.norm_of_nonneg (mul_nonneg h1t hr₁0)]
  have hB : ‖((t : ℝ) : ℂ) * ((r₂ : ℂ) * Complex.exp ((s : ℂ) * Complex.I))‖
      = t * r₂ := by
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_of_nonneg ht0, Complex.norm_of_nonneg hr₂0]
  have hle : ‖seg r₁ r₂ s t‖ ≤ (1 - t) * r₁ + t * r₂ := by
    rw [← hA, ← hB]
    exact norm_add_le _ _
  have hA1 : (1 - t) * r₁ ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left hr₁1 h1t
  have hB1 : t * r₂ ≤ t * 1 := mul_le_mul_of_nonneg_left hr₂1 ht0
  linarith

/-- The segment norm lands in `(0, 1]` — the radius coordinate of a valid cone point. -/
private lemma seg_norm_mem {r₁ r₂ s t : ℝ} (h₁ : r₁ ∈ Set.Ioc (0 : ℝ) 1)
    (h₂ : r₂ ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 ≤ s) (hsπ : s < Real.pi)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖seg r₁ r₂ s t‖ ∈ Set.Ioc (0 : ℝ) 1 :=
  Set.mem_Ioc.mpr ⟨norm_pos_iff.mpr (seg_ne_zero h₁.1 h₂.1 hs0 hsπ ht0 ht1),
    seg_norm_le_one h₁.1.le h₁.2 h₂.1.le h₂.2 s ht0 ht1⟩

/-- **THE SECTOR LEMMA, lower half**: the segment never leaves the upper half-plane, so its
argument is nonnegative. -/
lemma seg_arg_nonneg {r₂ s t : ℝ} (r₁ : ℝ) (hr₂ : 0 ≤ r₂) (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi) (ht0 : 0 ≤ t) : 0 ≤ Complex.arg (seg r₁ r₂ s t) := by
  rw [Complex.arg_nonneg_iff, seg_im]
  exact mul_nonneg ht0 (mul_nonneg hr₂ (Real.sin_nonneg_of_nonneg_of_le_pi hs0 hsπ))

/-- **THE SECTOR LEMMA, upper half (the heart of K2)**: the segment stays inside the closed
sector of aperture `s`, so its argument never exceeds `s`.  Proof: rotate by `e^{−is}`; the
rotated point `(1−t)·r₁·e^{−is} + t·r₂` has imaginary part `−(1−t)·r₁·sin s ≤ 0`, while the
polar identity writes the same imaginary part as `‖seg t‖·sin (arg (seg t) − s)`; with
`arg (seg t) − s ∈ (−π, π)` (here `s < π` bites) a nonpositive sine forces
`arg (seg t) ≤ s`.  The branch cut of `arg` is never approached. -/
lemma seg_arg_le {r₁ r₂ s t : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hs0 : 0 ≤ s) (hsπ : s < Real.pi) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Complex.arg (seg r₁ r₂ s t) ≤ s := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- s = 0: the segment is a positive real, arg = 0
    rw [← hs]
    have hpos : 0 < (1 - t) * r₁ + t * r₂ := by
      rcases eq_or_lt_of_le ht0 with ht | ht
      · rw [← ht]
        simpa using hr₁
      · have h1 : 0 < t * r₂ := mul_pos ht hr₂
        have h2 : 0 ≤ (1 - t) * r₁ := mul_nonneg (by linarith) hr₁.le
        linarith
    have hseg : seg r₁ r₂ 0 t = (((1 - t) * r₁ + t * r₂ : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [seg_re, Complex.ofReal_re, Real.cos_zero, mul_one]
      · rw [seg_im, Complex.ofReal_im, Real.sin_zero, mul_zero, mul_zero]
    rw [hseg, Complex.arg_ofReal_of_nonneg hpos.le]
  · -- 0 < s < π: the rotation argument
    by_contra hcon
    push Not at hcon
    have hzne : seg r₁ r₂ s t ≠ 0 := seg_ne_zero hr₁ hr₂ hs0 hsπ ht0 ht1
    have hznorm : 0 < ‖seg r₁ r₂ s t‖ := norm_pos_iff.mpr hzne
    have hargπ : Complex.arg (seg r₁ r₂ s t) ≤ Real.pi := Complex.arg_le_pi _
    have hsin_s : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 hsπ.le
    -- the rotated point, imaginary part computed directly from re/im
    have him1 : (seg r₁ r₂ s t * Complex.exp (((-s : ℝ) : ℂ) * Complex.I)).im
        = -((1 - t) * (r₁ * Real.sin s)) := by
      rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Real.cos_neg, Real.sin_neg, seg_re, seg_im]
      ring
    -- the same imaginary part via the polar identity
    have him2 : (seg r₁ r₂ s t * Complex.exp (((-s : ℝ) : ℂ) * Complex.I)).im
        = ‖seg r₁ r₂ s t‖ * Real.sin (Complex.arg (seg r₁ r₂ s t) - s) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (seg r₁ r₂ s t)]
      rw [mul_assoc, ← Complex.exp_add,
        show ((Complex.arg (seg r₁ r₂ s t) : ℝ) : ℂ) * Complex.I
            + ((-s : ℝ) : ℂ) * Complex.I
          = ((Complex.arg (seg r₁ r₂ s t) - s : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    have hsin_le : Real.sin (Complex.arg (seg r₁ r₂ s t) - s) ≤ 0 := by
      have hle : ‖seg r₁ r₂ s t‖ * Real.sin (Complex.arg (seg r₁ r₂ s t) - s) ≤ 0 := by
        rw [← him2, him1]
        have h1 : 0 ≤ (1 - t) * (r₁ * Real.sin s) :=
          mul_nonneg (by linarith) (mul_nonneg hr₁.le hsin_s)
        linarith
      by_contra hpos
      push Not at hpos
      nlinarith [mul_pos hznorm hpos]
    -- but s < arg ≤ π puts arg − s in (0, π), where the sine is positive
    have h1 : 0 < Complex.arg (seg r₁ r₂ s t) - s := by linarith
    have h2 : Complex.arg (seg r₁ r₂ s t) - s < Real.pi := by linarith
    have h3 := Real.sin_pos_of_pos_of_lt_pi h1 h2
    linarith

/-- The argument at the far endpoint is exactly `s` (for `s ∈ [0, π)`). -/
private lemma seg_one_arg {r₂ s : ℝ} (hr₂ : 0 < r₂) (hs0 : 0 ≤ s) (hsπ : s < Real.pi)
    (r₁ : ℝ) : Complex.arg (seg r₁ r₂ s 1) = s := by
  have hπ := Real.pi_pos
  rw [seg_one, Complex.exp_mul_I, Complex.arg_real_mul _ hr₂,
    Complex.arg_cos_add_sin_mul_I (Set.mem_Ioc.mpr ⟨by linarith, hsπ.le⟩)]

/-! ## Part 2A — the circle toolkit (needs `0 < θ`) -/

section Angle

variable (θ : ℝ) [Fact (0 < θ)]

/-- **Round minimality on the circle**: the quotient norm never exceeds the absolute value
of any representative — pulling an angle difference back to `ℝ` can only grow it. -/
lemma norm_coe_le_abs (x : ℝ) : ‖((x : ℝ) : AddCircle θ)‖ ≤ |x| := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  rw [AddCircle.norm_eq]
  have hkey := abs_sub_round_le (θ⁻¹ * x) 0
  rw [Int.cast_zero, sub_zero] at hkey
  have he : x - (round (θ⁻¹ * x) : ℤ) * θ = θ * (θ⁻¹ * x - (round (θ⁻¹ * x) : ℤ)) := by
    have hx : θ * (θ⁻¹ * x) = x := by
      rw [← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul]
    rw [mul_sub, hx]
    ring
  rw [he, abs_mul, abs_of_pos hθ0]
  have habs : |θ⁻¹ * x| = θ⁻¹ * |x| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hθ0)]
  calc θ * |θ⁻¹ * x - ((round (θ⁻¹ * x) : ℤ) : ℝ)| ≤ θ * |θ⁻¹ * x| :=
        mul_le_mul_of_nonneg_left hkey hθ0.le
    _ = |x| := by rw [habs, ← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul]

/-- **The minimal representative**: every angle class has a real lift whose absolute value
IS the circle norm (via `AddCircle.norm_eq` at the `[0, θ)` representative). -/
private lemma exists_norm_rep (ψ : AddCircle θ) :
    ∃ s : ℝ, ((s : ℝ) : AddCircle θ) = ψ ∧ |s| = ‖ψ‖ := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ((a : ℝ) : AddCircle θ) = ψ :=
    ⟨(AddCircle.equivIco θ 0 ψ : ℝ), AddCircle.coe_equivIco⟩
  refine ⟨a - (round (θ⁻¹ * a) : ℤ) * θ, ?_, ?_⟩
  · have hz : (((round (θ⁻¹ * a) : ℤ) * θ : ℝ) : AddCircle θ) = 0 :=
      (AddCircle.coe_eq_zero_iff θ).mpr ⟨round (θ⁻¹ * a), by rw [zsmul_eq_mul]⟩
    rw [QuotientAddGroup.mk_sub, hz, sub_zero, ha]
  · rw [← ha, AddCircle.norm_eq]

/-- **THE NONEXPANSION LEMMA**: the cone-side law-of-cosines distance between two pulled-back
waypoints is at most the planar distance between the segment points.  The sector lemma pins
both arguments in `[0, s] ⊆ [0, π)`, so the `AddCircle` angle gap is `≤ |Δ arg| ≤ s < π`
(round minimality), the chord is monotone there (F3), and the planar identity closes. -/
private lemma lawCos_seg_le {r₁ r₂ s : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hs0 : 0 ≤ s) (hsπ : s < Real.pi) {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lawCos ‖seg r₁ r₂ s u‖ ‖seg r₁ r₂ s v‖
        ‖((Complex.arg (seg r₁ r₂ s u) : ℝ) : AddCircle θ)
          - ((Complex.arg (seg r₁ r₂ s v) : ℝ) : AddCircle θ)‖
      ≤ ‖seg r₁ r₂ s u - seg r₁ r₂ s v‖ := by
  have hαu0 : 0 ≤ Complex.arg (seg r₁ r₂ s u) := seg_arg_nonneg r₁ hr₂.le hs0 hsπ.le hu0
  have hαus : Complex.arg (seg r₁ r₂ s u) ≤ s := seg_arg_le hr₁ hr₂ hs0 hsπ hu0 hu1
  have hαv0 : 0 ≤ Complex.arg (seg r₁ r₂ s v) := seg_arg_nonneg r₁ hr₂.le hs0 hsπ.le hv0
  have hαvs : Complex.arg (seg r₁ r₂ s v) ≤ s := seg_arg_le hr₁ hr₂ hs0 hsπ hv0 hv1
  have habs : |Complex.arg (seg r₁ r₂ s u) - Complex.arg (seg r₁ r₂ s v)| ≤ s :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hcirc : ‖((Complex.arg (seg r₁ r₂ s u) : ℝ) : AddCircle θ)
      - ((Complex.arg (seg r₁ r₂ s v) : ℝ) : AddCircle θ)‖
      ≤ |Complex.arg (seg r₁ r₂ s u) - Complex.arg (seg r₁ r₂ s v)| := by
    rw [← QuotientAddGroup.mk_sub]
    exact norm_coe_le_abs θ _
  have hmono := lawCos_mono (a := ‖seg r₁ r₂ s u‖) (b := ‖seg r₁ r₂ s v‖)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (le_trans habs hsπ.le) hcirc
  have heq : lawCos ‖seg r₁ r₂ s u‖ ‖seg r₁ r₂ s v‖
      |Complex.arg (seg r₁ r₂ s u) - Complex.arg (seg r₁ r₂ s v)|
      = ‖seg r₁ r₂ s u - seg r₁ r₂ s v‖ := by
    rw [lawCos_abs, ← norm_sub_polar ‖seg r₁ r₂ s u‖ ‖seg r₁ r₂ s v‖
        (Complex.arg (seg r₁ r₂ s u)) (Complex.arg (seg r₁ r₂ s v)),
      Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]
  exact hmono.trans (le_of_eq heq)

end Angle

/-! ## Part 2B — the chains and the pullback walk -/

/-- The radial-chain radius `(min (max 1 i) k)/k · R` is a valid cone radius. -/
private lemma radial_mem {k i : ℕ} (hk : 0 < k) (R : Set.Ioc (0 : ℝ) 1) :
    ((min (max 1 i) k : ℕ) : ℝ) / (k : ℝ) * R.1 ∈ Set.Ioc (0 : ℝ) 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hm1 : 1 ≤ min (max 1 i) k := by omega
  have hmk : min (max 1 i) k ≤ k := min_le_right _ _
  have hm1R : (1 : ℝ) ≤ ((min (max 1 i) k : ℕ) : ℝ) := by exact_mod_cast hm1
  have hmkR : ((min (max 1 i) k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hdiv0 : 0 < ((min (max 1 i) k : ℕ) : ℝ) / (k : ℝ) := div_pos (by linarith) hkR
  have hdiv1 : ((min (max 1 i) k : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkR]
    exact hmkR
  refine Set.mem_Ioc.mpr ⟨mul_pos hdiv0 R.2.1, ?_⟩
  calc ((min (max 1 i) k : ℕ) : ℝ) / (k : ℝ) * R.1 ≤ 1 * 1 :=
        mul_le_mul hdiv1 R.2.2 R.2.1.le zero_le_one
    _ = 1 := one_mul 1

section Walk

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] (n : ℕ) (ρ : ℝ)

/-- The cone distance between two pulled-back segment waypoints (any valid radius
packaging) is at most the planar distance — `lawCos_seg_le` in `Cone θ` form. -/
private lemma dist_seg_pts_le {r₁ r₂ s : ℝ} (h₁ : r₁ ∈ Set.Ioc (0 : ℝ) 1)
    (h₂ : r₂ ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 ≤ s) (hsπ : s < Real.pi)
    (φ₁ : AddCircle θ) {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (Pu Pv : Set.Ioc (0 : ℝ) 1) (hPu : Pu.1 = ‖seg r₁ r₂ s u‖)
    (hPv : Pv.1 = ‖seg r₁ r₂ s v‖) :
    @dist (Cone θ) _ (some (Pu, φ₁ + ((Complex.arg (seg r₁ r₂ s u) : ℝ) : AddCircle θ)))
        (some (Pv, φ₁ + ((Complex.arg (seg r₁ r₂ s v) : ℝ) : AddCircle θ)))
      ≤ ‖seg r₁ r₂ s u - seg r₁ r₂ s v‖ := by
  rw [dist_eq_coneDist, coneDist_some_some, hPu, hPv]
  have hang : (φ₁ + ((Complex.arg (seg r₁ r₂ s u) : ℝ) : AddCircle θ))
      - (φ₁ + ((Complex.arg (seg r₁ r₂ s v) : ℝ) : AddCircle θ))
      = ((Complex.arg (seg r₁ r₂ s u) : ℝ) : AddCircle θ)
        - ((Complex.arg (seg r₁ r₂ s v) : ℝ) : AddCircle θ) := by
    abel
  rw [hang]
  exact lawCos_seg_le θ h₁.1 h₂.1 hs0 hsπ hu0 hu1 hv0 hv1

/-- **The unfolded-segment chain** between two polar points, oriented so that the angle gap
has a NONNEGATIVE minimal representative `s ∈ [0, π)`: `k` waypoints on the planar segment,
pulled back through `Complex.arg`, each consecutive pair at cone distance `≤ D/k`. -/
private lemma chain_some_some (R₁ R₂ : Set.Ioc (0 : ℝ) 1) (φ₁ φ₂ : AddCircle θ)
    {s : ℝ} (hs0 : 0 ≤ s) (hsπ : s < Real.pi)
    (hrep : ((s : ℝ) : AddCircle θ) = φ₂ - φ₁) (hnorm : ‖φ₂ - φ₁‖ = s)
    {k : ℕ} (hk : 0 < k) :
    ∃ c : ℕ → Cone θ, c 0 = (some (R₁, φ₁) : Cone θ) ∧ c k = some (R₂, φ₂) ∧
      ∀ i, i < k → dist (c i) (c (i + 1))
        ≤ @dist (Cone θ) _ (some (R₁, φ₁)) (some (R₂, φ₂)) / k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ht0 : ∀ i : ℕ, 0 ≤ ((min i k : ℕ) : ℝ) / (k : ℝ) := fun i => by positivity
  have ht1 : ∀ i : ℕ, ((min i k : ℕ) : ℝ) / (k : ℝ) ≤ 1 := fun i => by
    rw [div_le_one hkR]
    exact_mod_cast min_le_right i k
  refine ⟨fun i => some (⟨‖seg R₁.1 R₂.1 s (((min i k : ℕ) : ℝ) / (k : ℝ))‖,
      seg_norm_mem R₁.2 R₂.2 hs0 hsπ (ht0 i) (ht1 i)⟩,
    φ₁ + ((Complex.arg (seg R₁.1 R₂.1 s (((min i k : ℕ) : ℝ) / (k : ℝ))) : ℝ)
      : AddCircle θ)), ?_, ?_, ?_⟩
  · -- start: t = 0, the segment sits at r₁ on the real axis, arg = 0
    have htz : ((min 0 k : ℕ) : ℝ) / (k : ℝ) = 0 := by
      rw [min_eq_left (Nat.zero_le k), Nat.cast_zero, zero_div]
    have h1 : ‖seg R₁.1 R₂.1 s (((min 0 k : ℕ) : ℝ) / (k : ℝ))‖ = R₁.1 := by
      rw [htz, seg_zero, Complex.norm_of_nonneg R₁.2.1.le]
    have h2 : φ₁ + ((Complex.arg (seg R₁.1 R₂.1 s (((min 0 k : ℕ) : ℝ) / (k : ℝ))) : ℝ)
        : AddCircle θ) = φ₁ := by
      rw [htz, seg_zero, Complex.arg_ofReal_of_nonneg R₁.2.1.le]
      simp
    exact congrArg some (Prod.ext (Subtype.ext h1) h2)
  · -- end: t = 1, the segment sits at r₂·e^{is}, arg = s, and ↑s = φ₂ − φ₁
    have htk : ((min k k : ℕ) : ℝ) / (k : ℝ) = 1 := by
      rw [min_self, div_self hkR.ne']
    have h1 : ‖seg R₁.1 R₂.1 s (((min k k : ℕ) : ℝ) / (k : ℝ))‖ = R₂.1 := by
      rw [htk, seg_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_of_nonneg R₂.2.1.le]
    have h2 : φ₁ + ((Complex.arg (seg R₁.1 R₂.1 s (((min k k : ℕ) : ℝ) / (k : ℝ))) : ℝ)
        : AddCircle θ) = φ₂ := by
      rw [htk, seg_one_arg R₂.2.1 hs0 hsπ R₁.1, hrep]
      abel
    exact congrArg some (Prod.ext (Subtype.ext h1) h2)
  · -- steps: nonexpansion + the affine segment step ‖seg tᵢ − seg tᵢ₊₁‖ = D/k
    intro i hik
    beta_reduce
    have hD : @dist (Cone θ) _ (some (R₁, φ₁)) (some (R₂, φ₂)) = lawCos R₁.1 R₂.1 s := by
      rw [dist_eq_coneDist, coneDist_some_some, norm_sub_rev, hnorm]
    refine le_trans (dist_seg_pts_le θ R₁.2 R₂.2 hs0 hsπ φ₁ (ht0 i) (ht1 i)
      (ht0 (i + 1)) (ht1 (i + 1)) _ _ rfl rfl) ?_
    rw [seg_sub, norm_mul]
    have hdiff : ((min i k : ℕ) : ℝ) / (k : ℝ) - ((min (i + 1) k : ℕ) : ℝ) / (k : ℝ)
        = -(1 / (k : ℝ)) := by
      rw [min_eq_left hik.le, min_eq_left (by omega : i + 1 ≤ k)]
      push_cast
      ring
    have hn1 : ‖((((min i k : ℕ) : ℝ) / (k : ℝ)
        - ((min (i + 1) k : ℕ) : ℝ) / (k : ℝ) : ℝ) : ℂ)‖ = 1 / (k : ℝ) := by
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / (k : ℝ))]
    rw [hn1, norm_chord, hD]
    exact le_of_eq (by ring)

/-- **The radial chain** from the apex out to a polar point: same angle throughout, radii
`(i/k)·R`, each hop of cone length exactly `R/k` (`lawCos` at zero angle). -/
private lemma chain_none_some (R : Set.Ioc (0 : ℝ) 1) (φ : AddCircle θ) {k : ℕ}
    (hk : 0 < k) :
    ∃ c : ℕ → Cone θ, c 0 = (none : Cone θ) ∧ c k = some (R, φ) ∧
      ∀ i, i < k → dist (c i) (c (i + 1))
        ≤ @dist (Cone θ) _ none (some (R, φ)) / k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hD : @dist (Cone θ) _ none (some (R, φ)) = R.1 := by
    rw [dist_eq_coneDist, coneDist_none_some]
  refine ⟨fun i => if i = 0 then none
      else some (⟨((min (max 1 i) k : ℕ) : ℝ) / (k : ℝ) * R.1, radial_mem hk R⟩, φ),
    if_pos rfl, ?_, ?_⟩
  · -- endpoint: at i = k the radius is exactly R
    beta_reduce
    have hval : ((min (max 1 k) k : ℕ) : ℝ) / (k : ℝ) * R.1 = R.1 := by
      rw [(by omega : min (max 1 k) k = k), div_self hkR.ne', one_mul]
    rw [if_neg hk.ne']
    exact congrArg some (Prod.ext (Subtype.ext hval) rfl)
  · intro i hik
    beta_reduce
    by_cases h0 : i = 0
    · -- first hop: apex to the innermost shell, cost R/k
      subst h0
      rw [if_pos rfl, if_neg (by omega : ¬(0 + 1 = 0)), dist_eq_coneDist,
        coneDist_none_some, hD]
      show ((min (max 1 (0 + 1)) k : ℕ) : ℝ) / (k : ℝ) * R.1 ≤ R.1 / (k : ℝ)
      rw [(by omega : min (max 1 (0 + 1)) k = 1), Nat.cast_one]
      exact le_of_eq (by ring)
    · -- interior hop: same angle, radius gap R/k
      rw [if_neg h0, if_neg (by omega : ¬(i + 1 = 0)), dist_eq_coneDist,
        coneDist_some_some, sub_self, norm_zero, lawCos_zero_angle, hD]
      show |((min (max 1 i) k : ℕ) : ℝ) / (k : ℝ) * R.1
          - ((min (max 1 (i + 1)) k : ℕ) : ℝ) / (k : ℝ) * R.1| ≤ R.1 / (k : ℝ)
      rw [(by omega : min (max 1 i) k = i), (by omega : min (max 1 (i + 1)) k = i + 1)]
      have hkey : ((i : ℕ) : ℝ) / (k : ℝ) * R.1 - (((i + 1 : ℕ)) : ℝ) / (k : ℝ) * R.1
          = -(R.1 / (k : ℝ)) := by
        push_cast
        ring
      rw [hkey, abs_neg, abs_of_pos (div_pos R.2.1 hkR)]

/-- Chains reverse: flip the index, keep the per-hop bound. -/
private lemma chain_reverse {p q : Cone θ} {k : ℕ} {B : ℝ}
    (h : ∃ c : ℕ → Cone θ, c 0 = p ∧ c k = q ∧
      ∀ i, i < k → dist (c i) (c (i + 1)) ≤ B) :
    ∃ c : ℕ → Cone θ, c 0 = q ∧ c k = p ∧
      ∀ i, i < k → dist (c i) (c (i + 1)) ≤ B := by
  obtain ⟨c, hc0, hck, hstep⟩ := h
  refine ⟨fun i => c (k - i), ?_, ?_, fun i hik => ?_⟩
  · show c (k - 0) = q
    rw [Nat.sub_zero]
    exact hck
  · show c (k - k) = p
    rw [Nat.sub_self]
    exact hc0
  · show dist (c (k - i)) (c (k - (i + 1))) ≤ B
    have h2 : k - i = (k - (i + 1)) + 1 := by omega
    rw [dist_comm, h2]
    exact hstep _ (by omega)

/-- **THE CHAIN LEMMA**: between ANY two cone points there is a `k`-step chain with per-hop
cone distance `≤ dist p q / k` — the geodesic subdivided.  Four cases: apex/apex trivial,
apex/polar radial (both orientations by reversal), polar/polar by the unfolded segment
(oriented via the minimal representative, reversed if it is negative).  `θ < 2π` enters
exactly here: it pins the angular gap `s ≤ θ/2 < π` for the sector lemma. -/
private lemma cone_chain_exists (hθlt : θ < 2 * Real.pi) (p q : Cone θ) {k : ℕ}
    (hk : 0 < k) :
    ∃ c : ℕ → Cone θ, c 0 = p ∧ c k = q ∧
      ∀ i, i < k → dist (c i) (c (i + 1)) ≤ dist p q / k := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  rcases p with _ | ⟨R₁, φ₁⟩ <;> rcases q with _ | ⟨R₂, φ₂⟩
  · -- apex to apex
    refine ⟨fun _ => none, rfl, rfl, fun i _ => ?_⟩
    simp
  · -- apex out to a polar point: the radial chain
    exact chain_none_some θ R₂ φ₂ hk
  · -- polar point in to the apex: the radial chain, reversed
    obtain ⟨c, hc0, hck, hstep⟩ := chain_reverse θ (chain_none_some θ R₁ φ₁ hk)
    refine ⟨c, hc0, hck, fun i hik => ?_⟩
    rw [dist_comm (α := Cone θ) (some (R₁, φ₁)) none]
    exact hstep i hik
  · -- polar to polar: the unfolded segment, oriented by the minimal representative
    obtain ⟨s₀, hrep, habs⟩ := exists_norm_rep θ (φ₂ - φ₁)
    have hs₀π : |s₀| < Real.pi := by
      rw [habs]
      have h := AddCircle.norm_le_half_period θ hθ0.ne' (x := φ₂ - φ₁)
      rw [abs_of_pos hθ0] at h
      linarith
    rcases le_or_gt 0 s₀ with hs₀ | hs₀
    · have hπ : s₀ < Real.pi := by rwa [abs_of_nonneg hs₀] at hs₀π
      exact chain_some_some θ R₁ R₂ φ₁ φ₂ hs₀ hπ hrep
        (by rw [← habs, abs_of_nonneg hs₀]) hk
    · have hπ : -s₀ < Real.pi := by rwa [abs_of_neg hs₀] at hs₀π
      have hrep' : ((-s₀ : ℝ) : AddCircle θ) = φ₁ - φ₂ := by
        rw [QuotientAddGroup.mk_neg, hrep, neg_sub]
      have hnorm' : ‖φ₁ - φ₂‖ = -s₀ := by
        rw [norm_sub_rev, ← habs, abs_of_neg hs₀]
      obtain ⟨c, hc0, hck, hstep⟩ := chain_reverse θ
        (chain_some_some θ R₂ R₁ φ₂ φ₁ (by linarith) hπ hrep' hnorm' hk)
      refine ⟨c, hc0, hck, fun i hik => ?_⟩
      rw [dist_comm (α := Cone θ) (some (R₁, φ₁)) (some (R₂, φ₂))]
      exact hstep i hik

/-- **Snap and walk**: a `k`-step cone chain with hops `≤ ρ − 2·mesh` between the images of
two grid points snaps to the grid (B2b net, cost `mesh` per endpoint of each hop) and
yields a graph walk of length `≤ k` via the lazy-chain builder. -/
private lemma walk_of_cone_chain {x y : PolarGrid θ n} {k : ℕ} (hk : 0 < k)
    (c : ℕ → Cone θ) (hc0 : c 0 = gridToCone θ n x) (hck : c k = gridToCone θ n y)
    (hstep : ∀ i, i < k → dist (c i) (c (i + 1)) ≤ ρ - 2 * mesh θ n) :
    ∃ w : (coneGraph θ n ρ).Walk x y, w.length ≤ k := by
  classical
  have hmesh := mesh_pos θ n
  -- the snapped grid chain: endpoints exact, interior via the net
  have hex : ∃ g : ℕ → PolarGrid θ n, g 0 = x ∧ g k = y ∧
      ∀ i, i ≤ k → dist (c i) (gridToCone θ n (g i)) ≤ mesh θ n := by
    refine ⟨fun i => if i = 0 then x else if k ≤ i then y
      else Classical.choose (cone_net_mesh θ n (c i)), if_pos rfl, ?_, ?_⟩
    · beta_reduce
      rw [if_neg hk.ne', if_pos le_rfl]
    · intro i hik
      beta_reduce
      by_cases h0 : i = 0
      · subst h0
        rw [if_pos rfl, hc0, dist_self]
        exact hmesh.le
      · by_cases hki : k ≤ i
        · have hik' : i = k := le_antisymm hik hki
          subst hik'
          rw [if_neg h0, if_pos le_rfl, hck, dist_self]
          exact hmesh.le
        · rw [if_neg h0, if_neg hki]
          exact Classical.choose_spec (cone_net_mesh θ n (c i))
  obtain ⟨g, hg0, hgk, hgd⟩ := hex
  have hchain : ∀ i, i < k → g i = g (i + 1) ∨ (coneGraph θ n ρ).Adj (g i) (g (i + 1)) := by
    intro i hik
    by_cases heq : g i = g (i + 1)
    · exact Or.inl heq
    · refine Or.inr ((coneGraph_adj θ n ρ _ _).mpr ⟨heq, ?_⟩)
      rw [polarGrid_dist_def]
      have h1 := hgd i hik.le
      have h2 := hgd (i + 1) hik
      rw [dist_comm] at h1
      calc dist (gridToCone θ n (g i)) (gridToCone θ n (g (i + 1)))
          ≤ dist (gridToCone θ n (g i)) (c i) + dist (c i) (c (i + 1))
            + dist (c (i + 1)) (gridToCone θ n (g (i + 1))) := dist_triangle4 _ _ _ _
        _ ≤ mesh θ n + (ρ - 2 * mesh θ n) + mesh θ n :=
            add_le_add (add_le_add h1 (hstep i hik)) h2
        _ = ρ := by ring
  obtain ⟨w, hw⟩ := QIQTH.StencilWalk.walk_of_lazy_chain g k hchain
  exact ⟨w.copy hg0 hgk, by rw [SimpleGraph.Walk.length_copy]; exact hw⟩

/-! ## Part 3 — THE K2 THEOREMS -/

/-- **THE K2 WALK (explicit construction).**  For `ρ > 2·mesh θ n` and any two grid points,
the snapped unfolded-segment (or radial) chain is a walk in `coneGraph θ n ρ` of length at
most `⌈dist x y / (ρ − 2·mesh θ n)⌉₊`.  Needs `θ < 2π` (genuine deficit) so that the
polar/polar sector has aperture `< π`. -/
theorem coneWalk_exists (hθlt : θ < 2 * Real.pi) (hρ : 2 * mesh θ n < ρ)
    (x y : PolarGrid θ n) :
    ∃ w : (coneGraph θ n ρ).Walk x y,
      w.length ≤ ⌈dist x y / (ρ - 2 * mesh θ n)⌉₊ := by
  have hρ2 : 0 < ρ - 2 * mesh θ n := by linarith
  by_cases hxy : x = y
  · subst hxy
    exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩
  · have hD : 0 < dist x y := dist_pos.mpr hxy
    set k := ⌈dist x y / (ρ - 2 * mesh θ n)⌉₊ with hkdef
    have hk : 0 < k := Nat.ceil_pos.mpr (div_pos hD hρ2)
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    obtain ⟨c, hc0, hck, hstep⟩ := cone_chain_exists θ hθlt
      (gridToCone θ n x) (gridToCone θ n y) hk
    have hDk : dist (gridToCone θ n x) (gridToCone θ n y) / (k : ℝ)
        ≤ ρ - 2 * mesh θ n := by
      rw [← polarGrid_dist_def, div_le_iff₀ hkR]
      have hle := Nat.le_ceil (dist x y / (ρ - 2 * mesh θ n))
      rw [← hkdef] at hle
      have h2 := mul_le_mul_of_nonneg_right hle hρ2.le
      rw [div_mul_cancel₀ _ hρ2.ne'] at h2
      rwa [mul_comm ((k : ℕ) : ℝ) (ρ - 2 * mesh θ n)] at h2
    exact walk_of_cone_chain θ n ρ hk c hc0 hck
      fun i hik => (hstep i hik).trans hDk

/-- **CONNECTIVITY (K2).**  For `ρ > 2·mesh θ n` and `θ < 2π` the intrinsic cone graph is
connected — discharges the `Reachable` hypothesis of brick K1's `dist_le_rho_mul_dist`. -/
theorem coneGraph_reachable (hθlt : θ < 2 * Real.pi) (hρ : 2 * mesh θ n < ρ)
    (x y : PolarGrid θ n) : (coneGraph θ n ρ).Reachable x y := by
  obtain ⟨w, -⟩ := coneWalk_exists θ n ρ hθlt hρ x y
  exact w.reachable

/-- **THE K2 THEOREM (hop-metric upper bound).**  For `ρ > 2·mesh θ n` and `θ < 2π`,
`hopdist x y ≤ coneDist x y / (ρ − 2·mesh θ n) + 1` — the companion to K1's lower bound
`coneDist ≤ ρ · hopdist`; together they pinch the hop metric between two multiples of the
cone metric, the two-sided comparability the K3 GH capstone consumes. -/
theorem coneGraph_dist_le (hθlt : θ < 2 * Real.pi) (hρ : 2 * mesh θ n < ρ)
    (x y : PolarGrid θ n) :
    (((coneGraph θ n ρ).dist x y : ℕ) : ℝ) ≤ dist x y / (ρ - 2 * mesh θ n) + 1 := by
  obtain ⟨w, hw⟩ := coneWalk_exists θ n ρ hθlt hρ x y
  have hd : (coneGraph θ n ρ).dist x y ≤ ⌈dist x y / (ρ - 2 * mesh θ n)⌉₊ :=
    le_trans (SimpleGraph.dist_le w) hw
  have hρ2 : 0 < ρ - 2 * mesh θ n := by linarith
  have hnn : 0 ≤ dist x y / (ρ - 2 * mesh θ n) := div_nonneg dist_nonneg hρ2.le
  have hceil : (⌈dist x y / (ρ - 2 * mesh θ n)⌉₊ : ℝ)
      < dist x y / (ρ - 2 * mesh θ n) + 1 := Nat.ceil_lt_add_one hnn
  have hcast : (((coneGraph θ n ρ).dist x y : ℕ) : ℝ)
      ≤ (⌈dist x y / (ρ - 2 * mesh θ n)⌉₊ : ℝ) := by exact_mod_cast hd
  linarith

end Walk

end QIQTH.ConeIntrinsicWalk
