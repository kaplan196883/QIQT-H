/-
  F6 (Increment 3 core, GPT-5.5-pro plan) — MICROCAUSALITY: the locality mechanism of the free field.

  The Haag–Kastler local net needs spacelike-separated field observables to COMMUTE (Einstein causality
  / no-signaling).  For Weyl operators this is the **CCR commutation**:
      `W(u) W(v) = W(v) W(u)`  whenever  `Im⟪u,v⟫ = 0`
  (i.e. when `u,v` are symplectically orthogonal — which is exactly what spacelike separation of the
  smeared test functions gives, via the vanishing of the Pauli–Jordan commutator).  This module proves
  that commutation for the bounded Weyl operators of `WeylOp.lean`.

  Results (axiom-free):
    * `weylPre_comp_expVec` — `W(u) W(v) e(g) = c · e(g+v+u)` (the composite on a coherent vector);
    * **`weyl_microcausality`** — `W(u) ∘ W(v) = W(v) ∘ W(u)` when `Im⟪u,v⟫ = 0`: spacelike-separated
      (symplectically orthogonal) Weyl observables commute — the locality / no-signaling core.

  HONEST SCOPE (per the GPT review): the full local net needs the localization map
  `K : TestFun → OneParticleH` from spacetime test functions, with `Im⟪Kf,Kg⟫ = 0` for spacelike-separated
  supports (the Pauli–Jordan structure) — a separate construction (Fourier / mass-shell transform).  What
  is established here is the *algebraic mechanism* that makes that locality bite: symplectic orthogonality
  ⇒ commuting Weyl operators.  Axiom-free.
-/
import QIQTH.Fock.WeylOp
import Mathlib.Tactic

namespace QIQTH.Fock

open Complex
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `W(u) W(v) e(g) = (weylCoeff v g · weylCoeff u (g+v)) · e(g+v+u)`. -/
theorem weylPre_comp_expVec (u v g : H) :
    weylPre u (weylPre v (FockPre.expVec g))
      = Finsupp.single (g + v + u) (Weyl.weylCoeff v g * Weyl.weylCoeff u (g + v)) := by
  have hv : weylPre v (FockPre.expVec g) = Finsupp.single (g + v) (Weyl.weylCoeff v g) := by
    rw [weylPre_apply, show FockPre.expVec g = Finsupp.single g 1 from rfl,
      Finsupp.sum_single_index (by simp), one_mul]
  rw [hv, weylPre_apply, Finsupp.sum_single_index (by simp)]

/-- The Weyl coefficients commute when `u,v` are symplectically orthogonal (`⟪u,v⟫ = ⟪v,u⟫`). -/
theorem weylCoeff_comm (u v g : H) (hsym : ⟪u, v⟫_ℂ = ⟪v, u⟫_ℂ) :
    Weyl.weylCoeff v g * Weyl.weylCoeff u (g + v)
      = Weyl.weylCoeff u g * Weyl.weylCoeff v (g + u) := by
  unfold Weyl.weylCoeff
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [inner_add_right, inner_add_right, hsym]
  ring

/-- `W(u) W(v) e(g) = W(v) W(u) e(g)` when `Im⟪u,v⟫ = 0` (commutation on coherent vectors). -/
theorem weyl_microcausality_expVec (u v : H) (huv : Complex.im ⟪u, v⟫_ℂ = 0) (g : H) :
    weylPre u (weylPre v (FockPre.expVec g)) = weylPre v (weylPre u (FockPre.expVec g)) := by
  have hsym : ⟪u, v⟫_ℂ = ⟪v, u⟫_ℂ := by
    have h := Complex.conj_eq_iff_im.mpr huv
    rw [inner_conj_symm] at h
    exact h.symm
  rw [weylPre_comp_expVec, weylPre_comp_expVec, add_right_comm g v u, weylCoeff_comm u v g hsym]

/-- **MICROCAUSALITY (locality / no-signaling core).**  If `u,v` are symplectically orthogonal
    (`Im⟪u,v⟫ = 0` — as spacelike-separated smearings are), the Weyl operators COMMUTE:
    `W(u) ∘ W(v) = W(v) ∘ W(u)`.  This is the Einstein-causality mechanism of the free field. -/
theorem weyl_microcausality (u v : H) (huv : Complex.im ⟪u, v⟫_ℂ = 0) :
    weylPre u ∘ₗ weylPre v = weylPre v ∘ₗ weylPre u := by
  refine Finsupp.lhom_ext fun g b => ?_
  show weylPre u (weylPre v (Finsupp.single g b)) = weylPre v (weylPre u (Finsupp.single g b))
  have hb : (Finsupp.single g b : H →₀ ℂ) = b • FockPre.expVec g := by
    show (Finsupp.single g b : H →₀ ℂ) = b • (Finsupp.single g 1 : H →₀ ℂ)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hb]
  simp only [map_smul]
  rw [weyl_microcausality_expVec u v huv g]

end QIQTH.Fock
