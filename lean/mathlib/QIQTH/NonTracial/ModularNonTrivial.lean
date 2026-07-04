/-
  N3 (THE_NON_TRACIALITY_PLAN.md) — MODULAR NON-TRIVIALITY: Δ ≠ 1 and Δ^{it} = towerFlow
  is not the identity flow, on a nonzero pure-component eigenvector when the Gibbs weights
  differ.

  The finite modular eigenbasis (ID2/ID3) gives, on the coerced pure matrix-unit component
  `v = ↑(of C E_{nm})`,

      Δ v = (w_n / w_m) • v      and      U_t v = exp(i·t·(log w_n − log w_m)) • v .

  Once `v ≠ 0` is known (its norm-square is `|c|²·w_m > 0`), these eigenvalue equations DEPART
  from the identity as soon as `w_n ≠ w_m`:
  • `Δ v = v` would force `(w_n/w_m − 1)•v = 0`, hence `w_n = w_m` (v ≠ 0) — a contradiction;
  • at `t = π/(log w_n − log w_m)` the phase is `exp(iπ) = −1`, so `U_t v = −v`; `−v = v`
    forces `2•v = 0`, hence `v = 0` — a contradiction.

  HONEST SCOPE (binding verdict, THE_NON_TRACIALITY_PLAN.md): this is a MODULAR
  NON-TRIVIALITY statement — Δ acts non-identically and the modular flow is not the identity
  flow — and NOTHING MORE. It is NOT a type statement. It does not classify `towerLimitVN`,
  does not claim "not type II₁" as an ALGEBRA statement (each finite stage is a full matrix
  algebra = type I_finite and DOES carry the normalized trace — the Gibbs state ω just is not
  it), and makes no type III / III_λ / III₁ / Connes-invariant / modular-spectrum claim
  (those need crossed-product / flow-of-weights machinery absent from Mathlib and the repo and
  depend on weight-sequence asymptotics the finite eigenbasis cannot see). Axiom-free, std-3.
-/
import Mathlib
import QIQTH.Dynamics
import QIQTH.Tower.CornerEmbed
import QIQTH.TowerGNS.Germ
import QIQTH.TowerGNS.ModularUnitaryEigen

namespace QIQTH.NonTracial

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory QIQTH.TowerGNS
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **★ THE PURE COMPONENT IS NONZERO.** For a nonzero scalar `c`, the coerced pure
    matrix-unit component `↑(of C E_{nm} c)` is a nonzero vector of the GNS completion —
    its inner square is `⟪x, x⟫ = w_m · |c|² > 0`. Route: `inner_coe_of_of` collapses the
    completion pairing to `pairInner`, `pairInner_embed` (at the common stage `C`) +
    `cornerEmbed_refl` to the per-stage `gnsInner C (E_{nm}) (E_{nm}) = tr(ρ · E_{nm}ᴴ E_{nm})`;
    `E_{nm}ᴴ E_{nm} = E_{mm}(|c|²)` (`conjTranspose_single` + `single_mul_single_same`) is
    diagonal, so the trace picks out `w_m · (star c · c) ≠ 0`. -/
theorem towerOf_single_ne_zero (C : Finset M) (n m : Micro L C) {c : ℂ} (hc : c ≠ 0) :
    ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β) ≠ 0 := by
  have hval :
      ⟪((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β),
          ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β)⟫_ℂ
        = ((gibbsWeight L C ω β m : ℝ) : ℂ) * (star c * c) := by
    rw [inner_coe_of_of, pairInner_embed L ω β C C C subset_rfl subset_rfl,
      cornerEmbed_refl, gnsInner, stateOf, gibbsDensity,
      Matrix.conjTranspose_single, Matrix.single_mul_single_same,
      QIQTH.Tower.trace_diagonal_mul, Finset.sum_eq_single m]
    · rw [Matrix.single_apply_same]
    · intro i _ hi
      rw [Matrix.single_apply_of_ne m m (star c * c) i i (fun hcc => hi hcc.1.symm), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ m) hmem
  have hne :
      ⟪((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β),
          ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β)⟫_ℂ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (gibbsWeight_pos L C ω β m).ne')
      (mul_ne_zero (star_ne_zero.mpr hc) hc)
  exact inner_self_ne_zero.mp hne

/-- **★ THE MODULAR OPERATOR ACTS NON-IDENTICALLY (Δ ≠ 1).** On the nonzero pure component
    `v = ↑(of C E_{nm})`, whenever the Gibbs weights differ (`w_n ≠ w_m`), the modular
    operator does not fix `v` — `Δ⟨v, _⟩ = (w_n/w_m)•v ≠ v`. Route: `towerModularOp_of_single`
    then `(w_n/w_m − 1)•v = 0`; `smul_eq_zero` + `v ≠ 0` forces `w_n/w_m = 1`, i.e.
    `w_n = w_m`, contradicting `h`.

    HONEST: this is modular non-triviality, NOT a type classification (see the file header). -/
theorem towerModularOp_ne_id (C : Finset M) (n m : Micro L C)
    (h : gibbsWeight L C ω β n ≠ gibbsWeight L C ω β m) :
    towerModularOp L ω β
        ⟨((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerModularDom L ω β C (Matrix.single n m 1)⟩
      ≠ ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β) := by
  intro hEq
  have hvne :
      ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β) ≠ 0 :=
    towerOf_single_ne_zero L ω β C n m (c := 1) one_ne_zero
  have hEV := towerModularOp_of_single L ω β C n m 1
  rw [hEq] at hEV
  -- hEV : v = (w_n / w_m) • v
  have hcoef :
      (((gibbsWeight L C ω β n / gibbsWeight L C ω β m : ℝ) : ℂ) - 1)
        • ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β) = 0 := by
    rw [sub_smul, one_smul, ← hEV, sub_self]
  rcases smul_eq_zero.mp hcoef with hscal | hzero
  · have hone : ((gibbsWeight L C ω β n / gibbsWeight L C ω β m : ℝ) : ℂ) = 1 :=
      sub_eq_zero.mp hscal
    have hreal : gibbsWeight L C ω β n / gibbsWeight L C ω β m = 1 := by exact_mod_cast hone
    exact h ((div_eq_one_iff_eq (gibbsWeight_pos L C ω β m).ne').mp hreal)
  · exact hvne hzero

/-- **★ THE MODULAR FLOW IS NOT THE IDENTITY FLOW (Δ^{it} ≠ id).** On the nonzero pure
    component `v = ↑(of C E_{nm})`, whenever `w_n ≠ w_m`, there is a time `t` at which the
    modular unitary moves `v` — take `t = π/κ` with `κ = log w_n − log w_m ≠ 0`: the phase is
    `exp(i·t·κ) = exp(iπ) = −1`, so `U_t v = −v`, and `−v = v` would force `2•v = 0`, i.e.
    `v = 0`, contradicting `towerOf_single_ne_zero`.

    HONEST: this is modular non-triviality of the flow, NOT a type classification. -/
theorem towerModUnitary_ne_id (C : Finset M) (n m : Micro L C)
    (h : gibbsWeight L C ω β n ≠ gibbsWeight L C ω β m) :
    ∃ t : ℝ, towerModUnitary L ω β t
        ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β)
      ≠ ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β) := by
  set κ : ℝ := Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) with hκ
  have hκne : κ ≠ 0 := by
    rw [hκ, sub_ne_zero]
    intro hlog
    apply h
    have hexp := congrArg Real.exp hlog
    rwa [Real.exp_log (gibbsWeight_pos L C ω β n),
      Real.exp_log (gibbsWeight_pos L C ω β m)] at hexp
  refine ⟨Real.pi / κ, ?_⟩
  intro hEq
  have hvne :
      ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β) ≠ 0 :=
    towerOf_single_ne_zero L ω β C n m (c := 1) one_ne_zero
  have hU := towerModUnitary_of_single L ω β (Real.pi / κ) C n m 1
  rw [← hκ] at hU
  -- hU : U_t v = exp(I · ↑(π/κ) · ↑κ) • v
  have hκℂ : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκne
  have hexp : Complex.I * (↑(Real.pi / κ) : ℂ) * (κ : ℂ) = ↑Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [hexp, Complex.exp_pi_mul_I, hEq] at hU
  -- hU : v = (-1) • v
  have h2 : (2 : ℂ)
      • ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β) = 0 := by
    rw [show (2 : ℂ) = 1 - (-1) by ring, sub_smul, one_smul, ← hU, sub_self]
  rcases smul_eq_zero.mp h2 with h2' | h2'
  · exact two_ne_zero h2'
  · exact hvne h2'

end QIQTH.NonTracial
