/-
  THE MODULAR CONJUGATION J2 (THE_MODULAR_CONJUGATION_PLAN.md) — the cross-stage law:
  `jStage` commutes with the stage embedding AND with the finite modular flow.

  Deliverables:
  • `cornerEmbed_jStage` ★ — THE CROSS-STAGE LAW `ι(J_C a) = J_{C′}(ι a)`: THE ENGINE E1
    (`cornerEmbed_mul_sqrtGibbs`, RightMul.lean) at `b := jStage a` gives
    `ι(J a)·S_{C′} = S_{C′}·ι(rightConj (J a)) = S_{C′}·ι(aᴴ) = S_{C′}·(ι a)ᴴ`
    (`rightConj_jStage` + `cornerEmbed_star`); multiply on the right by `S_{C′}⁻¹` and the
    right side IS `jStage C′ (ι a)`. This is the well-definedness input for the global
    anti-unitary (J3): the stage conjugations glue along the tower.
  • `cornerFlow_jStage` — `J_C ∘ σ_t^C = σ_t^C ∘ J_C` at every stage: both are diagonal
    conjugations (`S`-sandwich-with-ᴴ vs `ρ^{it}`-sandwich), the diagonals commute, and
    `(ρ^{it})ᴴ = ρ^{−it}` flips the flow twice — once through the ᴴ, once through the
    reversed sandwich — landing back on `+t` (the JΔ^{it} = Δ^{it}J signature, stage level).

  HONEST SCOPE: finite-stage matrix identities only. NO global J (J3–J4), no polar
  decomposition (J5), no claim about the completed flow (J6). Everything is diagonal
  bookkeeping over the RightMul.lean √ρ toolkit and the JStage.lean conjugation. Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.JStage
import QIQTH.TowerGNS.FlowPre

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### ★ The cross-stage law — THE ENGINE at `b := jStage a` -/

/-- **★ THE CROSS-STAGE LAW**: the corner embedding intertwines the stage conjugations —
    `ι(J_C a) = J_{C′}(ι a)`. THE ENGINE E1 (`cornerEmbed_mul_sqrtGibbs`) at `b := jStage a`
    gives `ι(J a)·S_{C′} = S_{C′}·ι(rightConj (J a))`; `rightConj_jStage` collapses the
    conjugated element to `aᴴ`, `cornerEmbed_star` pulls the ᴴ out of the embedding, and
    cancelling `S_{C′}` on the right leaves exactly the `C′`-stage conjugation of `ι a`.
    This is the well-definedness input of the global anti-unitary (J3). -/
theorem cornerEmbed_jStage {C C' : Finset M} (h : C ⊆ C') (a : DiamondAlg L C) :
    cornerEmbed L C C' h (jStage L ω β C a)
      = jStage L ω β C' (cornerEmbed L C C' h a) := by
  -- THE ENGINE at b := jStage a: ι(J a)·S = S·ι(rightConj (J a)) = S·(ι a)ᴴ
  have e1 := cornerEmbed_mul_sqrtGibbs L ω β h (jStage L ω β C a)
  rw [rightConj_jStage, cornerEmbed_star] at e1
  -- multiply on the right by S⁻¹ and massage
  calc cornerEmbed L C C' h (jStage L ω β C a)
      = cornerEmbed L C C' h (jStage L ω β C a)
          * (sqrtGibbs L ω β C' * sqrtInvGibbs L ω β C') := by
        rw [sqrtGibbs_mul_sqrtInvGibbs, mul_one]
    _ = cornerEmbed L C C' h (jStage L ω β C a) * sqrtGibbs L ω β C'
          * sqrtInvGibbs L ω β C' := by
        rw [Matrix.mul_assoc]
    _ = sqrtGibbs L ω β C' * (cornerEmbed L C C' h a)ᴴ * sqrtInvGibbs L ω β C' := by
        rw [e1]
    _ = jStage L ω β C' (cornerEmbed L C C' h a) := by
        rw [jStage]

/-! ### The diagonal bookkeeping for the flow exchange -/

/-- `(ρ^{it})ᴴ = ρ^{−it}` at the Gibbs weights — the conjugate transpose of the diagonal
    flow unitary flips the time (the entries `w^{it}` are unimodular for `w > 0`:
    `conj(e^{it·log w}) = e^{−it·log w}`). -/
theorem diagPow_gibbs_conjTranspose (C : Finset M) (t : ℝ) :
    (diagPow (fun n => gibbsWeight L C ω β n) t)ᴴ
      = diagPow (fun n => gibbsWeight L C ω β n) (-t) := by
  rw [diagPow, diagPow, Matrix.diagonal_conjTranspose]
  congr 1
  funext m
  simp only [Pi.star_apply]
  have hpos := gibbsWeight_pos L C ω β m
  have hw : ((gibbsWeight L C ω β m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [Complex.cpow_def_of_ne_zero hw, Complex.cpow_def_of_ne_zero hw,
    ← Complex.ofReal_log hpos.le, ← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `S · ρ^{it} = ρ^{it} · S` — the square-rooted Gibbs density commutes with the diagonal
    flow unitary (both diagonal). -/
theorem sqrtGibbs_diagPow_comm (C : Finset M) (t : ℝ) :
    sqrtGibbs L ω β C * diagPow (fun n => gibbsWeight L C ω β n) t
      = diagPow (fun n => gibbsWeight L C ω β n) t * sqrtGibbs L ω β C := by
  rw [sqrtGibbs, diagPow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  exact mul_comm _ _

/-- `S⁻¹ · ρ^{it} = ρ^{it} · S⁻¹` — the inverse square root commutes with the diagonal
    flow unitary (both diagonal). -/
theorem sqrtInvGibbs_diagPow_comm (C : Finset M) (t : ℝ) :
    sqrtInvGibbs L ω β C * diagPow (fun n => gibbsWeight L C ω β n) t
      = diagPow (fun n => gibbsWeight L C ω β n) t * sqrtInvGibbs L ω β C := by
  rw [sqrtInvGibbs, diagPow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  exact mul_comm _ _

/-! ### The flow exchange — J commutes with the finite modular flow -/

/-- **The flow exchange**: the stage conjugation commutes with the finite modular flow at
    the SAME stage — `J_C(σ_t^C a) = σ_t^C(J_C a)`. The ᴴ inside `jStage` reverses the
    `ρ^{it}`-sandwich and conjugates its entries (`(ρ^{it})ᴴ = ρ^{−it}` — the flow flips
    TWICE, landing back on `+t`), and the diagonal conjugators commute through each other.
    This is the stage-level shadow of `JΔ^{it} = Δ^{it}J` (J6 completes it). -/
theorem cornerFlow_jStage (C : Finset M) (t : ℝ) (a : DiamondAlg L C) :
    jStage L ω β C (cornerFlow L ω β C t a)
      = cornerFlow L ω β C t (jStage L ω β C a) := by
  -- head exchange S·(D_t·z) = D_t·(S·z) and tail exchange D_{−t}·S⁻¹ = S⁻¹·D_{−t}
  have hhead : ∀ z : DiamondAlg L C,
      sqrtGibbs L ω β C * (diagPow (fun n => gibbsWeight L C ω β n) t * z)
        = diagPow (fun n => gibbsWeight L C ω β n) t * (sqrtGibbs L ω β C * z) := by
    intro z
    rw [← Matrix.mul_assoc, sqrtGibbs_diagPow_comm, Matrix.mul_assoc]
  have htail : diagPow (fun n => gibbsWeight L C ω β n) (-t) * sqrtInvGibbs L ω β C
      = sqrtInvGibbs L ω β C * diagPow (fun n => gibbsWeight L C ω β n) (-t) :=
    (sqrtInvGibbs_diagPow_comm L ω β C (-t)).symm
  simp only [jStage, cornerFlow, QIQTH.FiniteModularTheory.sigmaDiag]
  -- LHS: S·(D_t·a·D_{−t})ᴴ·S⁻¹ = S·(D_t·(aᴴ·D_{−t}))·S⁻¹ after the ᴴ flips both D's
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, diagPow_gibbs_conjTranspose,
    diagPow_gibbs_conjTranspose, neg_neg]
  simp only [Matrix.mul_assoc]
  rw [hhead, htail]

end QIQTH.TowerGNS
