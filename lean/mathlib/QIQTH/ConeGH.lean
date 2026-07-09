/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE CONE GH LIMIT — finite polar-grid clouds converge to the concentrated-positive-curvature
cone (brick B2b, curvature-track capstone)

Brick B2b of the CURVATURE track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`, Track B
continuation).  Brick B2a (`QIQTH/ConeMetric.lean`) built the Euclidean cone `Cone θ` of total
angle `θ ≤ 2π` as a compact metric space whose CONCENTRATED POSITIVE CURVATURE (deficit angle
`2π − θ` at the apex) is a THEOREM, not prose: for `θ < 2π` the cone admits no isometric
embedding into any real inner-product space (`cone_no_isometric_embedding_into_inner`).  This
file completes the brick by exhibiting that curved space as a **Gromov–Hausdorff limit of
finite point clouds**: the polar grids `PolarGrid θ n` — the apex plus `(n+1)·(n+2)` points at
radii `k/(n+1)` (`k = 1, …, n+1`) and angles `j·θ/(n+2)` (`j = 0, …, n+1`) — satisfy

    toGHSpace (PolarGrid θ n) ⟶ toGHSpace (Cone θ)      (`polarGrid_toGHSpace_tendsto_cone`)

via the quantitative bound
`ghDist (PolarGrid θ n) (Cone θ) ≤ 1/(n+1) + θ/(2(n+2))` (`ghDist_polarGrid_le`): the grid
embedding `gridToCone` is an EXACT isometry (`gridToCone_isometry`, the grid carries the
pullback metric) whose image is a `(1/(n+1) + θ/(2(n+2)))`-net of the cone (`cone_net`,
riding B2a's Lipschitz bound `coneDist_fromPolar_le` — radius rounds by ceiling exactly as
the tripod's stars, angle rounds wrap-aware on `AddCircle θ` exactly as the torus lattice).
This is the program's first POSITIVE-curvature GH limit: after the flat cube/torus and the
CAT(0) tripod, the finite-cloud machine now reaches a space with a genuine curvature
obstruction of the opposite sign.

## Scope firewall (HONEST)

* **The finite clouds carry the INDUCED (pullback) metric** — they are exact isometric
  samples of the cone, like the tripod's subdivided stars — **NOT an intrinsic graph-geodesic
  (hop-count) metric: the intrinsic rounding-walk construction near the bending apex (where
  geodesics are no longer straight in any single chart) is the CITED frontier, not
  attempted here.**
* **The curvature is CONCENTRATED** — an Alexandrov cone point, NOT a smooth Riemann tensor,
  NOT a curved surface atlas, NOT a Riemannian manifold.  Away from the apex the cone is flat.
* **`θ` and the whole geometry are INPUTS** — this file transports a chosen deficit angle to
  a GH limit of finite clouds; nothing is emergent.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.ConeMetric
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Semiring

namespace QIQTH.ConeGH

open QIQTH.ConeMetric Filter Topology

/-! ## Part 1 — the finite polar grid

The apex (`none`) plus `(n+1)·(n+2)` polar-grid points `some (k, j)`: radius index
`k ∈ {1, …, n+1}` (a nonzero `Fin (n+2)`, the tripod encoding) and angle index
`j ∈ ZMod (n+2)` (the cyclic wrap, the torus encoding).  The parameter `θ` is phantom in the
raw type — it enters through the metric, which is pulled back from `Cone θ`. -/

set_option linter.unusedVariables false in
/-- **The finite polar grid**: the apex (`none`) plus points `some (k, j)` at radius
`k/(n+1)` (`k = 1, …, n+1`) and angle `j·θ/(n+2)` (`j ∈ ZMod (n+2)`, wrap-around).  `θ` is
phantom in the raw type; it parametrizes the pullback metric below. -/
def PolarGrid (θ : ℝ) (n : ℕ) : Type :=
  Option ({k : Fin (n + 2) // k ≠ 0} × ZMod (n + 2))

instance instNonemptyPolarGrid (θ : ℝ) (n : ℕ) : Nonempty (PolarGrid θ n) := ⟨none⟩

instance instFinitePolarGrid (θ : ℝ) (n : ℕ) : Finite (PolarGrid θ n) :=
  inferInstanceAs (Finite (Option ({k : Fin (n + 2) // k ≠ 0} × ZMod (n + 2))))

/-- The radius `k/(n+1) ∈ (0,1]` of the `k`-th radial shell (the tripod `starParam`
pattern). -/
noncomputable def gridRadius (n : ℕ) (k : {k : Fin (n + 2) // k ≠ 0}) : Set.Ioc (0 : ℝ) 1 :=
  ⟨(k.1.1 : ℝ) / ((n : ℝ) + 1), by
    have hk0 : 0 < k.1.1 :=
      Nat.pos_of_ne_zero fun h0 => k.2 (Fin.ext (by rw [h0, Fin.val_zero]))
    have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    constructor
    · exact div_pos (by exact_mod_cast hk0) hc
    · rw [div_le_one hc]
      have hkle : k.1.1 ≤ n + 1 := Nat.lt_succ_iff.mp k.1.2
      exact_mod_cast hkle⟩

@[simp] lemma gridRadius_val (n : ℕ) (k : {k : Fin (n + 2) // k ≠ 0}) :
    (gridRadius n k).1 = (k.1.1 : ℝ) / ((n : ℝ) + 1) := rfl

/-! ## Part 2 — the embedding into the cone and the pullback metric -/

section Grid

variable (θ : ℝ)

/-- The angle `j·θ/(n+2)` on the circle of circumference `θ` of the `j`-th angular ray. -/
noncomputable def gridAngle (n : ℕ) (j : ZMod (n + 2)) : AddCircle θ :=
  (((j.val : ℝ) * θ / ((n : ℝ) + 2) : ℝ) : AddCircle θ)

/-- The grid angle, unfolded. -/
lemma gridAngle_def (n : ℕ) (j : ZMod (n + 2)) :
    gridAngle θ n j = (((j.val : ℝ) * θ / ((n : ℝ) + 2) : ℝ) : AddCircle θ) := rfl

/-- **The grid embedding** into the cone: apex to apex, `(k, j)` to the polar point at
radius `k/(n+1)` and angle `j·θ/(n+2)`. -/
noncomputable def gridToCone (n : ℕ) : PolarGrid θ n → Cone θ
  | none => none
  | some (k, j) => some (gridRadius n k, gridAngle θ n j)

@[simp] lemma gridToCone_none (n : ℕ) : gridToCone θ n none = none := rfl

@[simp] lemma gridToCone_some (n : ℕ) (k : {k : Fin (n + 2) // k ≠ 0})
    (j : ZMod (n + 2)) :
    gridToCone θ n (some (k, j)) = some (gridRadius n k, gridAngle θ n j) := rfl

/-- Integer multiples of the period vanish on the circle. -/
private lemma coe_nat_mul_period (q : ℕ) : (((q : ℝ) * θ : ℝ) : AddCircle θ) = 0 :=
  (AddCircle.coe_eq_zero_iff θ).mpr ⟨(q : ℤ), by rw [zsmul_eq_mul]; push_cast; ring⟩

/-- **The wrap bridge**: the grid angle of the mod-`(n+2)` cast of ANY natural `m` is the
class of `m·θ/(n+2)` — the cyclic cast absorbs whole turns (`m ↦ m % (n+2)` shifts the
representative by an integer multiple of `θ`). -/
private lemma gridAngle_natCast (n m : ℕ) :
    gridAngle θ n ((m : ℕ) : ZMod (n + 2))
      = (((m : ℝ) * θ / ((n : ℝ) + 2) : ℝ) : AddCircle θ) := by
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [gridAngle_def, ZMod.val_natCast]
  have hcast : (m : ℝ)
      = ((n : ℝ) + 2) * ((m / (n + 2) : ℕ) : ℝ) + ((m % (n + 2) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) (Nat.div_add_mod m (n + 2)).symm
  have hreal : (m : ℝ) * θ / ((n : ℝ) + 2)
      = ((m % (n + 2) : ℕ) : ℝ) * θ / ((n : ℝ) + 2) + ((m / (n + 2) : ℕ) : ℝ) * θ := by
    rw [hcast]
    field_simp
    ring
  rw [hreal, QuotientAddGroup.mk_add, coe_nat_mul_period θ (m / (n + 2)), add_zero]

end Grid

section Metric

variable (θ : ℝ) [Fact (0 < θ)]

/-- The `n+2` grid angles are pairwise distinct: their representatives `j·θ/(n+2)` all lie
in the fundamental half-open interval `[0, θ)`, where the coercion to `AddCircle θ` is
injective. -/
lemma gridAngle_injective (n : ℕ) : Function.Injective (gridAngle θ n) := by
  intro j j' h
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hmem : ∀ i : ZMod (n + 2),
      (i.val : ℝ) * θ / ((n : ℝ) + 2) ∈ Set.Ico (0 : ℝ) (0 + θ) := by
    intro i
    rw [zero_add]
    refine Set.mem_Ico.mpr
      ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg _) hθ0.le) hn2.le, ?_⟩
    rw [div_lt_iff₀ hn2]
    have hv : (i.val : ℝ) < (n : ℝ) + 2 := by exact_mod_cast ZMod.val_lt i
    nlinarith [mul_lt_mul_of_pos_right hv hθ0]
  have heq : (j.val : ℝ) * θ / ((n : ℝ) + 2) = (j'.val : ℝ) * θ / ((n : ℝ) + 2) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem j) (hmem j')).mp h
  rw [mul_div_assoc, mul_div_assoc] at heq
  have hval : (j.val : ℝ) = (j'.val : ℝ) :=
    mul_right_cancel₀ (div_pos hθ0 hn2).ne' heq
  exact ZMod.val_injective _ (by exact_mod_cast hval)

lemma gridToCone_injective (n : ℕ) : Function.Injective (gridToCone θ n) := by
  intro x y h
  rcases x with _ | ⟨k, j⟩ <;> rcases y with _ | ⟨l, j'⟩
  · rfl
  · rw [gridToCone_none, gridToCone_some] at h
    have h' : (none : Option (Set.Ioc (0 : ℝ) 1 × AddCircle θ))
        = some (gridRadius n l, gridAngle θ n j') := h
    simp at h'
  · rw [gridToCone_some, gridToCone_none] at h
    have h' : (some (gridRadius n k, gridAngle θ n j)
        : Option (Set.Ioc (0 : ℝ) 1 × AddCircle θ)) = none := h
    simp at h'
  · rw [gridToCone_some, gridToCone_some] at h
    have h' : (some (gridRadius n k, gridAngle θ n j)
        : Option (Set.Ioc (0 : ℝ) 1 × AddCircle θ))
        = some (gridRadius n l, gridAngle θ n j') := h
    have hpair : (gridRadius n k, gridAngle θ n j) = (gridRadius n l, gridAngle θ n j') :=
      Option.some.inj h'
    have hrad : gridRadius n k = gridRadius n l := congrArg Prod.fst hpair
    have hang : gridAngle θ n j = gridAngle θ n j' := congrArg Prod.snd hpair
    have hval : (k.1.1 : ℝ) / ((n : ℝ) + 1) = (l.1.1 : ℝ) / ((n : ℝ) + 1) :=
      congrArg Subtype.val hrad
    have hc : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (k.1.1 : ℝ) = (l.1.1 : ℝ) := by
      have h3 := congrArg (fun r : ℝ => r * ((n : ℝ) + 1)) hval
      simpa only [div_mul_cancel₀ _ hc] using h3
    have hk : k = l := Subtype.ext (Fin.ext (by exact_mod_cast h2))
    have hj : j = j' := gridAngle_injective θ n hang
    rw [hk, hj]

/-- The `AddCircle θ` norm of a coercion difference with representative within `θ/2` (the
B2a route, restated locally). -/
private lemma angNorm_sub_coe (x y : ℝ) (h : |x - y| ≤ θ / 2) :
    ‖((x : ℝ) : AddCircle θ) - ((y : ℝ) : AddCircle θ)‖ = |x - y| := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  rw [← QuotientAddGroup.mk_sub]
  exact (AddCircle.norm_coe_eq_abs_iff θ hθ0.ne').mpr (by rwa [abs_of_pos hθ0])

variable [Fact (θ ≤ 2 * Real.pi)]

/-- **The pullback metric**: the polar grid carries the cone-restricted distance (the exact
tripod pattern — the finite cloud is an isometric SAMPLE of the cone, not an intrinsic
graph-geodesic space; see the scope firewall). -/
noncomputable instance instMetricSpacePolarGrid (n : ℕ) : MetricSpace (PolarGrid θ n) where
  dist x y := dist (gridToCone θ n x) (gridToCone θ n y)
  dist_self x := dist_self (gridToCone θ n x)
  dist_comm x y := dist_comm (gridToCone θ n x) (gridToCone θ n y)
  dist_triangle x y z :=
    dist_triangle (gridToCone θ n x) (gridToCone θ n y) (gridToCone θ n z)
  eq_of_dist_eq_zero := by
    intro x y h
    exact gridToCone_injective θ n (eq_of_dist_eq_zero h)

/-- The polar-grid distance, unfolded. -/
lemma polarGrid_dist_def {n : ℕ} (x y : PolarGrid θ n) :
    dist x y = dist (gridToCone θ n x) (gridToCone θ n y) := rfl

/-- **The grid embedding is an EXACT isometry** (the grid metric is the pullback). -/
theorem gridToCone_isometry (n : ℕ) : Isometry (gridToCone θ n) :=
  Isometry.of_dist_eq fun _ _ => rfl

instance instCompactSpacePolarGrid (n : ℕ) : CompactSpace (PolarGrid θ n) :=
  Finite.compactSpace

/-! ## Part 3 — the grid is a `(1/(n+1) + θ/(2(n+2)))`-net of the cone

Radius rounds by ceiling `k = ⌈r(n+1)⌉` exactly as the tripod net; angle takes the `[0, θ)`
representative (`AddCircle.equivIco`) and rounds wrap-aware to the nearest of `n+2` rays,
the mod-`(n+2)` cast absorbing the wrap exactly as the torus net. -/

/-- The cone distance from a polar point to an embedded grid point is at most the radius gap
plus the angle gap — B2a's public Lipschitz bound `coneDist_fromPolar_le`, routed through
`fromPolar`. -/
private lemma dist_some_grid_le (n : ℕ) (r : Set.Ioc (0 : ℝ) 1) (φ : AddCircle θ)
    (k : {k : Fin (n + 2) // k ≠ 0}) (j : ZMod (n + 2)) :
    @dist (Cone θ) _ (some (r, φ)) (gridToCone θ n (some (k, j)))
      ≤ |r.1 - (gridRadius n k).1| + ‖φ - gridAngle θ n j‖ := by
  have key := coneDist_fromPolar_le θ
    ((⟨r.1, r.2.1.le, r.2.2⟩, φ) : Set.Icc (0 : ℝ) 1 × AddCircle θ)
    ((⟨(gridRadius n k).1, (gridRadius n k).2.1.le, (gridRadius n k).2.2⟩,
      gridAngle θ n j) : Set.Icc (0 : ℝ) 1 × AddCircle θ)
  rw [fromPolar_of_ne θ (ne_of_gt r.2.1),
    fromPolar_of_ne θ (ne_of_gt (gridRadius n k).2.1)] at key
  exact key

/-- **The net lemma.**  Every point of the cone is within `1/(n+1) + θ/(2(n+2))` of an
embedded grid point: the apex maps to the apex; a polar point `(r, φ)` rounds its radius up
to the shell `k = ⌈r(n+1)⌉` (error `≤ 1/(n+1)`) and its angle wrap-aware to the nearest of
the `n+2` rays (error `≤ θ/(2(n+2))`, via the `[0, θ)` representative and `round`). -/
theorem cone_net (n : ℕ) (p : Cone θ) :
    ∃ x : PolarGrid θ n,
      dist p (gridToCone θ n x) ≤ 1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2)) := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rcases p with _ | ⟨r, φ⟩
  · refine ⟨none, ?_⟩
    rw [gridToCone_none, dist_self]
    have hA : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hB : (0 : ℝ) ≤ θ / (2 * ((n : ℝ) + 2)) := div_nonneg hθ0.le (by positivity)
    linarith
  · -- radial rounding: the exact tripod ceiling
    have ht0 : (0 : ℝ) < r.1 := r.2.1
    have ht1 : r.1 ≤ 1 := r.2.2
    have hkpos : 0 < ⌈r.1 * ((n : ℝ) + 1)⌉₊ := Nat.ceil_pos.mpr (mul_pos ht0 hc)
    have hkle : ⌈r.1 * ((n : ℝ) + 1)⌉₊ ≤ n + 1 := by
      refine Nat.ceil_le.mpr ?_
      have h := mul_le_mul_of_nonneg_right ht1 hc.le
      rw [one_mul] at h
      push_cast
      linarith
    -- angular rounding: the [0, θ) representative
    obtain ⟨a, haIco, hφ⟩ :
        ∃ a : ℝ, a ∈ Set.Ico (0 : ℝ) (0 + θ) ∧ ((a : ℝ) : AddCircle θ) = φ :=
      ⟨(AddCircle.equivIco θ 0 φ : ℝ), (AddCircle.equivIco θ 0 φ).2,
        AddCircle.coe_equivIco⟩
    have ha0 : (0 : ℝ) ≤ a := haIco.1
    -- the wrap-aware round, as a natural (the mod cast absorbs the possible full turn)
    have hjz0 : 0 ≤ round (((n : ℝ) + 2) * a / θ) := by
      rw [round_eq]
      refine Int.le_floor.mpr ?_
      have h0 : (0 : ℝ) ≤ ((n : ℝ) + 2) * a / θ :=
        div_nonneg (mul_nonneg hn2.le ha0) hθ0.le
      push_cast
      linarith
    obtain ⟨jn, hjn⟩ :
        ∃ jn : ℕ, (jn : ℝ) = ((round (((n : ℝ) + 2) * a / θ) : ℤ) : ℝ) :=
      ⟨(round (((n : ℝ) + 2) * a / θ)).toNat, by exact_mod_cast Int.toNat_of_nonneg hjz0⟩
    have hround : |((n : ℝ) + 2) * a / θ - (jn : ℝ)| ≤ 1 / 2 := by
      rw [hjn]
      exact abs_sub_round _
    -- the angular error
    have herr : |a - (jn : ℝ) * θ / ((n : ℝ) + 2)| ≤ θ / (2 * ((n : ℝ) + 2)) := by
      have hkey : a - (jn : ℝ) * θ / ((n : ℝ) + 2)
          = (((n : ℝ) + 2) * a / θ - (jn : ℝ)) * (θ / ((n : ℝ) + 2)) := by
        field_simp
      rw [hkey, abs_mul, abs_of_pos (div_pos hθ0 hn2)]
      calc |((n : ℝ) + 2) * a / θ - (jn : ℝ)| * (θ / ((n : ℝ) + 2))
          ≤ 1 / 2 * (θ / ((n : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hround (div_pos hθ0 hn2).le
        _ = θ / (2 * ((n : ℝ) + 2)) := by rw [div_mul_div_comm, one_mul]
    have h2step : θ / (2 * ((n : ℝ) + 2)) ≤ θ / 2 := by
      rw [div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [mul_nonneg hθ0.le (Nat.cast_nonneg (α := ℝ) n)]
    have hnorm : ‖φ - gridAngle θ n ((jn : ℕ) : ZMod (n + 2))‖
        ≤ θ / (2 * ((n : ℝ) + 2)) := by
      rw [← hφ, gridAngle_natCast θ n jn,
        angNorm_sub_coe θ a ((jn : ℝ) * θ / ((n : ℝ) + 2)) (herr.trans h2step)]
      exact herr
    refine ⟨some (⟨⟨⌈r.1 * ((n : ℝ) + 1)⌉₊, by omega⟩,
      Fin.ne_of_val_ne (by simpa using hkpos.ne')⟩, ((jn : ℕ) : ZMod (n + 2))), ?_⟩
    refine le_trans (dist_some_grid_le θ n r φ _ _) (add_le_add ?_ hnorm)
    -- the radial estimate, verbatim from the tripod net
    show |r.1 - (⌈r.1 * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1)
    have h1 : r.1 * ((n : ℝ) + 1) ≤ (⌈r.1 * ((n : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈r.1 * ((n : ℝ) + 1)⌉₊ : ℝ) < r.1 * ((n : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg ht0.le hc.le)
    rw [abs_sub_le_iff]
    constructor
    · have hle : r.1 ≤ (⌈r.1 * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) := by
        rw [le_div_iff₀ hc]
        exact h1
      have hpos : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · have hle : (⌈r.1 * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1)
          ≤ 1 / ((n : ℝ) + 1) + r.1 := by
        rw [div_le_iff₀ hc, add_mul, one_div_mul_cancel hc.ne']
        linarith
      linarith

/-! ## Part 4 — the quantitative Gromov–Hausdorff bound -/

/-- **THE B2b BOUND.**  The Gromov–Hausdorff distance between the finite polar grid (with
its pullback metric) and the cone is at most `1/(n+1) + θ/(2(n+2))`: the grid embedding is
an EXACT isometry (`ε₂ = 0`) whose image is a `(1/(n+1) + θ/(2(n+2)))`-net. -/
theorem ghDist_polarGrid_le (n : ℕ) :
    GromovHausdorff.ghDist (PolarGrid θ n) (Cone θ)
      ≤ 1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2)) := by
  have key : GromovHausdorff.ghDist (PolarGrid θ n) (Cone θ)
      ≤ 0 + 0 / 2 + (1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2))) := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
        (s := (Set.univ : Set (PolarGrid θ n))) (fun z => gridToCone θ n z.1) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := cone_net θ n q
      exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (gridToCone θ n x) (gridToCone θ n y)| ≤ 0
      rw [polarGrid_dist_def, sub_self, abs_zero]
  linarith

/-! ## Part 5 — the B2b capstone -/

/-- **THE B2b CAPSTONE (Gromov–Hausdorff convergence to the CONE).**  The finite polar-grid
clouds — apex plus `(n+1)·(n+2)` points, carrying the pullback metric — converge in
Gromov–Hausdorff space to the cone of total angle `θ`, the compact metric space whose apex
carries CONCENTRATED POSITIVE CURVATURE (deficit angle `2π − θ`), provably not isometrically
embeddable in any real inner-product space for `θ < 2π`
(`ConeMetric.cone_no_isometric_embedding_into_inner`).  The program's first
positive-curvature GH limit — but note the honesty firewall: the clouds are exact isometric
SAMPLES (pullback metric), not intrinsic graph-geodesic spaces; the intrinsic hop-metric
version near the bending apex is the cited frontier (see the header). -/
theorem polarGrid_toGHSpace_tendsto_cone :
    Tendsto (fun n : ℕ => GromovHausdorff.toGHSpace (PolarGrid θ n)) atTop
      (𝓝 (GromovHausdorff.toGHSpace (Cone θ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ n : ℕ,
      dist (GromovHausdorff.toGHSpace (PolarGrid θ n))
          (GromovHausdorff.toGHSpace (Cone θ))
        ≤ 1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2)) :=
    fun n => ghDist_polarGrid_le θ n
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have h2 : Tendsto (fun n : ℕ => θ / (2 * ((n : ℝ) + 2))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 2 : ℕ)) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
    have h' := h.const_mul (θ / 2)
    rw [mul_zero] at h'
    refine h'.congr fun n => ?_
    push_cast
    rw [div_mul_div_comm, mul_one]
  have hub : Tendsto
      (fun n : ℕ => 1 / ((n : ℝ) + 1) + θ / (2 * ((n : ℝ) + 2))) atTop (𝓝 0) := by
    simpa using h1.add h2
  exact squeeze_zero (fun n => dist_nonneg) hb hub

end Metric

end QIQTH.ConeGH
