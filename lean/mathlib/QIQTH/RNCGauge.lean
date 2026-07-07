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

end QIQTH.RNCGauge
