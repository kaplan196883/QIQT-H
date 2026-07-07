/-
  RNCGauge — the generic "diagonal-vanishing ⟹ symmetrized gauge" lemma.

  Route-(c) of the RNC-gauge discharge (THE_EXP_JETS_PLAN.md).  This is the coordinate wrapper that
  turns the abstract Polarization Lemma 5 (`QIQTH.Polarization.trilinear_diag_zero_fullSymm`) into a
  concrete statement about a first-jet-of-Christoffel tensor `dΓ l i j k`.  We package the per-`i`
  cubic form `(l,j,k) ↦ dΓ l i j k` as a genuine trilinear `ContinuousLinearMap` on `Fin n → ℝ`, feed
  its diagonal-vanishing hypothesis (`dGammaDiag = 0`, i.e. the radial identity `DΓ̃₀(v)(v,v)=0`) to
  Lemma 5, and read off the six-permutation gauge sum `GaugeJet` on standard basis vectors.

  Pure multilinear algebra over `ℝ` + the already-proved polarization identity; no geometry, no
  `exp`-map dependency.  HONEST: an algebraic wrapper — it presumes the radial diagonal identity as an
  INPUT (`hdiag`); it does NOT by itself produce that identity (Lemmas 1–4 of the plan), NOT the
  pullback metric, NOT numerical-G.
-/
import Mathlib
import QIQTH.Polarization

namespace QIQTH.RNCGauge

open scoped BigOperators

variable {n : ℕ}

/-- The `a`-th standard basis point of `Fin n → ℝ`. -/
def basisPt (a : Fin n) : Fin n → ℝ := Pi.single a 1

/-- The radial (diagonal) contraction of the Christoffel first-jet at a point `v`, index `i`:
    `∑_{l,j,k} dΓ^i_{ljk} v^l v^j v^k`.  This is the coordinate form of `DΓ̃₀(v)(v,v)` (up to the
    fixed contravariant index `i`); the RNC radial identity asserts it vanishes for all `v`. -/
def dGammaDiag (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ l, ∑ j, ∑ k, dΓ l i j k * v l * v j * v k

/-- The symmetrized normal-coordinate gauge condition on the Christoffel first-jet, index by index:
    the six-fold permutation sum of the lower indices `(l,j,k)` vanishes.  With lower-index Christoffel
    symmetry this is exactly `∂_(l Γ̃^i_{jk)}(0) = 0`. -/
def GaugeJet (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ i l j k,
    dΓ l i j k + dΓ l i k j + dΓ j i l k + dΓ j i k l + dΓ k i l j + dΓ k i j l = 0

/-- Bridging instance: the double continuous-dual `(Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ` carries a
    `ContinuousAdd` for its native `ContinuousLinearMap.add`.  Mathlib's default class search loops on
    this iterated-CLM goal (it resolves `IsTopologicalAddGroup` but not the bare `ContinuousAdd`), which
    in turn blocks synthesising `AddCommMonoid` on the *triple* dual — the type of `gaugeTri`, whose
    definition sums coordinate `smulRight`s.  Reading the `ContinuousAdd` straight off the already-found
    `ContinuousLinearMap.topologicalAddGroup` supplies exactly the missing edge. -/
noncomputable instance instContinuousAddDualDual :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalAddGroup.toContinuousAdd

/-- The per-`i` cubic form `(u,v,w) ↦ ∑_{l,j,k} dΓ^i_{ljk} u^l v^j w^k` packaged as a genuine trilinear
    continuous map on `Fin n → ℝ`, built out of coordinate projections and `smulRight`. -/
noncomputable def gaugeTri (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (i : Fin n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ l, (ContinuousLinearMap.proj l).smulRight
    (∑ j, (ContinuousLinearMap.proj j).smulRight
      (∑ k, dΓ l i j k • ContinuousLinearMap.proj k))

/-- Evaluation of the packaged trilinear form: it computes exactly the triple contraction. -/
@[simp] theorem gaugeTri_apply (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (i : Fin n)
    (u v w : Fin n → ℝ) :
    gaugeTri dΓ i u v w = ∑ l, ∑ j, ∑ k, dΓ l i j k * u l * v j * w k := by
  simp only [gaugeTri, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by ring

/-- On the diagonal the packaged form is exactly `dGammaDiag`. -/
theorem gaugeTri_diag (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    gaugeTri dΓ i v v v = dGammaDiag dΓ v i := by
  rw [gaugeTri_apply, dGammaDiag]

/-- On standard basis vectors the packaged form reads off a single coefficient. -/
theorem gaugeTri_basis (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (i a b c : Fin n) :
    gaugeTri dΓ i (basisPt a) (basisPt b) (basisPt c) = dΓ a i b c := by
  rw [gaugeTri_apply]
  simp only [basisPt, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **THE CAPSTONE.**  If the radial diagonal `dGammaDiag dΓ v i` vanishes for every `v` and `i`
    (the RNC radial-geodesic identity, an INPUT here), then the Christoffel first-jet satisfies the
    symmetrized normal-coordinate gauge `GaugeJet dΓ`.  Proof: package the per-`i` cubic form as the
    trilinear map `gaugeTri`, whose diagonal vanishing is `hdiag`; apply Polarization Lemma 5 on the
    standard basis triple `(l,j,k)`; read off the six coefficients via `gaugeTri_basis`. -/
theorem gaugeJet_of_diag (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hdiag : ∀ v i, dGammaDiag dΓ v i = 0) : GaugeJet dΓ := by
  intro i l j k
  have hdz : ∀ x, gaugeTri dΓ i x x x = 0 := fun x => by rw [gaugeTri_diag]; exact hdiag x i
  have h := QIQTH.Polarization.trilinear_diag_zero_fullSymm (gaugeTri dΓ i) hdz
    (basisPt l) (basisPt j) (basisPt k)
  simpa only [gaugeTri_basis] using h

/-! ### The abstract algebraic core of the RNC-Christoffel gauge.

For an ABSTRACT Christoffel array `Γ` (`Γ i j k = Γ^i_{jk}`, slot 1 the up-index) and an abstract
first-derivative array `dΓ1` (`dΓ1 l i j k = ∂_l Γ^i_{jk}`) we assemble the formal exp-3-jet cubic
coefficient of the RNC linearization and prove that its symmetrized version satisfies the six-fold
`GaugeJet` identically.  This is PURE multilinear algebra: no geometry, no `exp`-map, no metric.

The crux is `sum3_sym_contract`: the diagonal contraction `∑_{l,j,k} f_{ljk} v^l v^j v^k` is invariant
under permuting the three lower arguments of `f`, so replacing `f` by its six-permutation average leaves
the diagonal contraction unchanged.  This is what makes the symmetrized coefficient NON-vacuous: the raw
coefficient's antisymmetric part would be killed by the diagonal contraction, but the symmetrized cubic
coefficient is a genuine (generally nonzero) array whose diagonal happens to reproduce the raw one. -/

variable (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ1 : Fin n → Fin n → Fin n → Fin n → ℝ)

/-- Christoffel-square block A: `∑_a Γ^i_{ak} Γ^a_{lj}`. -/
def christSqA (i l j k : Fin n) : ℝ := ∑ a, Γ i a k * Γ a l j

/-- Christoffel-square block B: `∑_a Γ^i_{ja} Γ^a_{lk}`. -/
def christSqB (i l j k : Fin n) : ℝ := ∑ a, Γ i j a * Γ a l k

/-- Raw contraction-representative of the exp 3-jet cubic coefficient (up-index `i`, lower `l,j,k`). -/
def a3rawArr (i l j k : Fin n) : ℝ := - dΓ1 l i j k + christSqA Γ i l j k + christSqB Γ i l j k

/-- The SYMMETRIZED cubic coefficient (average over the six permutations of the lower triple `l,j,k`). -/
noncomputable def a3symArr (i l j k : Fin n) : ℝ :=
  (1/6 : ℝ) * (a3rawArr Γ dΓ1 i l j k + a3rawArr Γ dΓ1 i l k j + a3rawArr Γ dΓ1 i j l k
    + a3rawArr Γ dΓ1 i j k l + a3rawArr Γ dΓ1 i k l j + a3rawArr Γ dΓ1 i k j l)

/-- The formal RNC-Christoffel linear jet (`l i j k` order, to feed `dGammaDiag`/`GaugeJet`). -/
noncomputable def rncDΓ (l i j k : Fin n) : ℝ :=
  a3symArr Γ dΓ1 i l j k + dΓ1 l i j k - christSqA Γ i l j k - christSqB Γ i l j k

/-- **The crux permutation invariance.**  For any `f : (Fin n)³ → ℝ` and weight `v`, the diagonal
    contraction `∑_{l,j,k} f_{ljk} v^l v^j v^k` is unchanged when `f` is replaced by its six-fold
    average over the permutations of `(l,j,k)`.  Proof: each of the six permutation contractions
    equals the base contraction (adjacent transpositions via `Finset.sum_comm`, the two 3-cycles and
    the outer transposition by composing them); then the `(1/6)·Σ` collapses. -/
theorem sum3_sym_contract (f : Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, (1/6 : ℝ) *
        (f l j k + f l k j + f j l k + f j k l + f k l j + f k j l) * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, f l j k * v l * v j * v k := by
  -- swap of the last two arguments (adjacent inner transposition)
  have hA : ∀ g : Fin n → Fin n → Fin n → ℝ,
      (∑ l, ∑ j, ∑ k, g l k j * v l * v j * v k) = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k := by
    intro g
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  -- swap of the first two arguments (adjacent outer transposition)
  have hB : ∀ g : Fin n → Fin n → Fin n → ℝ,
      (∑ l, ∑ j, ∑ k, g j l k * v l * v j * v k) = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k := by
    intro g
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  have e2 := hA f
  have e3 := hB f
  have e4 := (hB (fun l j k => f l k j)).trans (hA f)
  have e5 := (hA (fun l j k => f j l k)).trans (hB f)
  have e6 := (hB (fun l j k => f k l j)).trans e5
  have split : ∀ l j k : Fin n,
      (1/6 : ℝ) * (f l j k + f l k j + f j l k + f j k l + f k l j + f k j l) * v l * v j * v k
        = (1/6:ℝ) * (f l j k * v l * v j * v k) + (1/6:ℝ) * (f l k j * v l * v j * v k)
          + (1/6:ℝ) * (f j l k * v l * v j * v k) + (1/6:ℝ) * (f j k l * v l * v j * v k)
          + (1/6:ℝ) * (f k l j * v l * v j * v k) + (1/6:ℝ) * (f k j l * v l * v j * v k) := by
    intro l j k; ring
  simp only [split, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e2, e3, e4, e5, e6]
  ring

/-- **The tautology.**  The diagonal contraction of the symmetrized coefficient equals that of the raw
    coefficient — exactly `sum3_sym_contract` for `f := a3rawArr Γ dΓ1 i`. -/
theorem dGammaDiag_a3sym_eq_raw (v : Fin n → ℝ) (i : Fin n) :
    (∑ l, ∑ j, ∑ k, a3symArr Γ dΓ1 i l j k * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, a3rawArr Γ dΓ1 i l j k * v l * v j * v k := by
  unfold a3symArr
  exact sum3_sym_contract (fun l j k => a3rawArr Γ dΓ1 i l j k) v

/-- **The RNC linear jet has vanishing radial diagonal.**  For the formal RNC-Christoffel linearization
    `rncDΓ`, the radial diagonal `dGammaDiag (rncDΓ Γ dΓ1) v i` vanishes for every `v` and `i`:
    the symmetrized cubic term's diagonal reproduces the raw term (`dGammaDiag_a3sym_eq_raw`), and the
    raw term `−∂Γ + Γ² + Γ²` exactly cancels the `+∂Γ − Γ² − Γ²` remainder. -/
theorem expMap_rncDΓ_diag_zero (v : Fin n → ℝ) (i : Fin n) :
    dGammaDiag (rncDΓ Γ dΓ1) v i = 0 := by
  have hstep : ∀ l j k : Fin n, rncDΓ Γ dΓ1 l i j k * v l * v j * v k
      = a3symArr Γ dΓ1 i l j k * v l * v j * v k + dΓ1 l i j k * v l * v j * v k
        - christSqA Γ i l j k * v l * v j * v k - christSqB Γ i l j k * v l * v j * v k := by
    intro l j k; simp only [rncDΓ]; ring
  have hraw : ∀ l j k : Fin n, a3rawArr Γ dΓ1 i l j k * v l * v j * v k
      = christSqA Γ i l j k * v l * v j * v k + christSqB Γ i l j k * v l * v j * v k
        - dΓ1 l i j k * v l * v j * v k := by
    intro l j k; simp only [a3rawArr]; ring
  unfold dGammaDiag
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [dGammaDiag_a3sym_eq_raw Γ dΓ1 v i]
  simp only [hraw, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **THE CAPSTONE (abstract algebraic core).**  The formal RNC-Christoffel linear jet `rncDΓ Γ dΓ1`
    satisfies the symmetrized normal-coordinate gauge `GaugeJet` identically, for ANY abstract
    Christoffel array `Γ` and first-derivative array `dΓ1`.

    HONEST scope: this is the ABSTRACT algebraic core.  For the formal RNC-Christoffel linearization
    `rncDΓ` the symmetrized gauge holds identically (via the diagonal-contraction argument, `route (c)`).
    It does NOT yet GROUND `rncDΓ` in the exp map's actual 3-jet `a₃`: the connection
    `∑ a3rawArr v³ = a₃(v)_i` from `expMap_value_three_jet` and the literal-pullback bridge are the next
    steps; it is NOT the pullback metric, NOT numerical-`G`. -/
theorem rncGaugeJet : GaugeJet (rncDΓ Γ dΓ1) :=
  gaugeJet_of_diag (rncDΓ Γ dΓ1) (fun v i => expMap_rncDΓ_diag_zero Γ dΓ1 v i)

end QIQTH.RNCGauge
