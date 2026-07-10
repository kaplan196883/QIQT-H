/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# CONE FLATNESS ⟺ θ = 2π — the smooth-at-the-Hawking-temperature theorem
(brick E2, Hawking–Euclidean campaign)

Brick E2 of the HAWKING–EUCLIDEAN campaign (`docs/qg_roadmap/HAWKING_EUCLIDEAN_PLAN.md`).
Brick B2a (`QIQTH/ConeMetric.lean`) proved the NO-embedding theorem: for every deficit
angle `θ < 2π` the cone `Cone θ` admits no distance-preserving map into any real
inner-product space (`cone_no_isometric_embedding_into_inner`).  This file proves the
exact CONVERSE and packages the pair as an iff:

* `coneToDisk_isometry` — at `θ = 2π` the polar map `(r, φ) ↦ r·e^{i·rep φ}` (apex `↦ 0`)
  IS a distance-preserving map `Cone (2π) → ℂ`;
* `range_coneToDisk` — its image is exactly the closed unit disk: the `2π`-cone IS the
  flat disk, isometrically;
* `cone_flat_iff` — **`Cone θ` embeds isometrically in `ℂ` ⟺ `θ = 2π`** (for
  `0 < θ ≤ 2π`).  The forward direction for an ARBITRARY real inner-product space `E` is
  the already-named theorem `cone_no_isometric_embedding_into_inner`; `ℂ` is the canonical
  two-dimensional witness, so the iff is stated there.

The geometric mechanism: the two bisector midpoints of the no-embedding argument are
`sin (θ/2)` apart, which vanishes precisely at `θ = 2π` — the two midpoints merge, the
obstruction dies, and the disk unrolls flat.

## THE DICTIONARY (interpretation, honestly labelled)

In Euclidean gravity the near-horizon `(r, τ_E)` section of a static black-hole (or
Rindler) metric is a two-dimensional cone of total angle `θ = κβ`, where `κ` is the
surface gravity and `β` the period of Euclidean time.  Smoothness of the Euclidean
section ⟺ no conical singularity ⟺ `θ = 2π` ⟺ `β = 2π/κ` — the **Hawking–Unruh inverse
temperature** (Gibbons–Hawking 1977).  This file supplies the GEOMETRIC half of that
statement as a machine-checked iff: flat ⟺ `θ = 2π`.  The algebraic face — the boost
modular flow satisfies the KMS condition at exactly `2π` (`QIQTH/BoostKMS.lean`) — is the
modular twin; pairing the two is brick E3.

## Scope firewall (MANDATORY, HONEST)

* **The geometry is the theorem; the temperature is a dictionary.**  The identification
  `θ = κβ` and the reading "flat ⟺ Hawking temperature" are INTERPRETATION, cited to the
  literature (Gibbons–Hawking), NOT a formalized field-theory derivation.
* **`θ` and `β` are INPUTS** — chosen parameters, not derived.
* **Wick rotation loses causal structure** — the Euclidean section is not the Lorentzian
  spacetime; the Lorentzian ladder is a separate cited plan.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.ConeIntrinsicWalk
import Mathlib.Analysis.InnerProductSpace.Basic

namespace QIQTH.ConeFlat

open QIQTH.ConeMetric QIQTH.ConeIntrinsicWalk

/-! ## Part 0 — the concrete-angle instances: `Cone (2π)` gets its metric space -/

instance : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨by have h := Real.pi_pos; linarith⟩

instance : Fact ((2 * Real.pi : ℝ) ≤ 2 * Real.pi) := ⟨le_refl _⟩

/-! ## Part 1 — the key cosine identity: the `AddCircle (2π)` norm is invisible to `cos` -/

/-- **The key cosine identity**: the cosine of the circle norm of a class in
`AddCircle (2π)` equals the cosine of any real representative — `cos` is even and
`2π`-periodic, which is exactly what the quotient norm forgets. -/
lemma cos_norm_addCircle_two_pi (x : ℝ) :
    Real.cos ‖((x : ℝ) : AddCircle (2 * Real.pi))‖ = Real.cos x := by
  rw [AddCircle.norm_eq, Real.cos_abs, Real.cos_sub_int_mul_two_pi]

/-- The law-of-cosines chord only sees the cosine of the angle, so at total angle `2π` the
circle-norm angular distance and the raw real angle give the SAME chord. -/
lemma lawCos_norm_eq (a b x : ℝ) :
    lawCos a b ‖((x : ℝ) : AddCircle (2 * Real.pi))‖ = lawCos a b x := by
  rw [lawCos_def, lawCos_def, cos_norm_addCircle_two_pi]

/-! ## Part 2 — the isometry `Cone (2π) → ℂ` and its image, the closed unit disk -/

/-- The canonical `[0, 2π)` real representative of an angle class (via
`AddCircle.equivIco`, so no quotient-lift well-definedness is ever needed). -/
noncomputable def rep (φ : AddCircle (2 * Real.pi)) : ℝ :=
  (AddCircle.equivIco (2 * Real.pi) 0 φ : ℝ)

/-- The representative represents: coercing `rep φ` back to the circle returns `φ`. -/
lemma rep_coe (φ : AddCircle (2 * Real.pi)) :
    ((rep φ : ℝ) : AddCircle (2 * Real.pi)) = φ :=
  AddCircle.coe_equivIco

/-- **The unrolling map**: the apex goes to the origin, the polar point `(r, φ)` goes to
`r·e^{i·rep φ}` — the cone of full angle `2π` laid flat onto the complex plane. -/
noncomputable def coneToDisk : Cone (2 * Real.pi) → ℂ
  | none => 0
  | some p => (p.1.1 : ℂ) * Complex.exp ((rep p.2 : ℂ) * Complex.I)

@[simp] lemma coneToDisk_none : coneToDisk none = 0 := rfl

@[simp] lemma coneToDisk_some (r : Set.Ioc (0 : ℝ) 1) (φ : AddCircle (2 * Real.pi)) :
    coneToDisk (some (r, φ)) = (r.1 : ℂ) * Complex.exp ((rep φ : ℂ) * Complex.I) := rfl

/-- **THE FLATNESS ISOMETRY**: at total angle `2π` the unrolling map is distance-
preserving — the law-of-cosines cone metric IS the planar metric (the ℂ law of cosines
`norm_sub_polar` on one side, the key cosine identity on the other). -/
theorem coneToDisk_isometry : Isometry coneToDisk := by
  refine Isometry.of_dist_eq fun p q => ?_
  rcases p with _ | ⟨r₁, φ₁⟩ <;> rcases q with _ | ⟨r₂, φ₂⟩
  · rw [coneToDisk_none, dist_self, dist_eq_coneDist, coneDist_none_none]
  · rw [coneToDisk_none, coneToDisk_some, dist_eq_coneDist, coneDist_none_some,
      Complex.dist_eq, zero_sub, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_of_nonneg r₂.2.1.le]
  · rw [coneToDisk_some, coneToDisk_none, dist_eq_coneDist, coneDist_some_none,
      Complex.dist_eq, sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_of_nonneg r₁.2.1.le]
  · rw [coneToDisk_some, coneToDisk_some, Complex.dist_eq, norm_sub_polar,
      dist_eq_coneDist, coneDist_some_some,
      show φ₁ - φ₂ = ((rep φ₁ - rep φ₂ : ℝ) : AddCircle (2 * Real.pi)) by
        rw [QuotientAddGroup.mk_sub, rep_coe, rep_coe],
      lawCos_norm_eq]

/-- **The image is the closed unit disk**: the `2π`-cone is not merely flat — it is,
isometrically, the standard closed disk `{z : ‖z‖ ≤ 1}` in the plane. -/
theorem range_coneToDisk : Set.range coneToDisk = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [Set.mem_range, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨p, rfl⟩
    rcases p with _ | ⟨r, φ⟩
    · rw [coneToDisk_none, norm_zero]
      exact zero_le_one
    · rw [coneToDisk_some, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_of_nonneg r.2.1.le]
      exact r.2.2
  · intro hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨none, coneToDisk_none⟩
    · -- `rep (arg z)` and `arg z` represent the same class: they differ by `n·2π`
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp
        (show ((rep ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))
            - Complex.arg z : ℝ) : AddCircle (2 * Real.pi)) = 0 by
          rw [QuotientAddGroup.mk_sub, rep_coe, sub_self])
      rw [zsmul_eq_mul] at hn
      refine ⟨some (⟨‖z‖, Set.mem_Ioc.mpr ⟨norm_pos_iff.mpr hz0, hz⟩⟩,
        ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))), ?_⟩
      rw [coneToDisk_some]
      have hrep : rep ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))
          = Complex.arg z + (n : ℝ) * (2 * Real.pi) := by linarith
      rw [hrep]
      have hexp : Complex.exp (((Complex.arg z + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
            * Complex.I)
          = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
        rw [show (((Complex.arg z + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
            = (Complex.arg z : ℂ) * Complex.I
              + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
          Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [hexp, Complex.norm_mul_exp_arg_mul_I]

/-- **The `2π`-cone embeds**: existence packaging of the flatness isometry — the exact
input the capstone iff consumes. -/
theorem cone_two_pi_embeds :
    ∃ f : Cone (2 * Real.pi) → ℂ,
      ∀ p q : Cone (2 * Real.pi), dist (f p) (f q) = dist p q :=
  ⟨coneToDisk, fun p q => coneToDisk_isometry.dist_eq p q⟩

/-! ## Part 3 — THE CAPSTONE IFF: flat ⟺ θ = 2π -/

section Capstone

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)]

/-- **THE FLATNESS CRITERION (capstone).**  For `0 < θ ≤ 2π` the cone of total angle `θ`
admits a distance-preserving map into the plane `ℂ` **iff `θ = 2π`** — the conical
singularity is absent exactly when the full angle is there.

Forward: any deficit (`θ < 2π`) triggers the no-embedding theorem
`cone_no_isometric_embedding_into_inner` (which holds for EVERY real inner-product space;
`ℂ` is the canonical 2D witness).  Backward: the unrolling isometry `coneToDisk`.

Via the Euclidean-gravity dictionary (INTERPRETATION, see the header): with `θ = κβ` this
is "the Euclidean section is smooth ⟺ `β = 2π/κ`", i.e. the Hawking–Unruh temperature is
the unique smooth period — Gibbons–Hawking, cited not derived. -/
theorem cone_flat_iff :
    (∃ f : Cone θ → ℂ, ∀ p q : Cone θ, dist (f p) (f q) = dist p q)
      ↔ θ = 2 * Real.pi := by
  constructor
  · rintro ⟨f, hf⟩
    by_contra hne
    exact cone_no_isometric_embedding_into_inner θ
      (lt_of_le_of_ne (Fact.out : θ ≤ 2 * Real.pi) hne) f hf
  · rintro rfl
    exact cone_two_pi_embeds

end Capstone

end QIQTH.ConeFlat
