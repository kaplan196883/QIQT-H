/-
  N1 (THE_NON_TRACIALITY_PLAN.md) — FINITE NON-TRACIALITY OF THE GIBBS STATE.

  The code's canonical Gibbs state `ω(·) = stateOf ρ_β (·) = tr(ρ_β · ·)` is NOT a trace:
  on the matrix units `a = E_{nm} = single n m 1`, `b = E_{mn} = single m n 1`,

      ω(a·b) = w_n     while     ω(b·a) = w_m,

  so `ω(a·b) ≠ ω(b·a)` at every stage where the Gibbs weights differ (`w_n ≠ w_m`).
  The route is elementary matrix calculus: `single n m 1 * single m n 1 = single n n 1`
  (`Matrix.single_mul_single_same`), and tracing the diagonal density against a diagonal
  matrix unit picks out the single weight (`QIQTH.Tower.trace_diagonal_mul`).

  HONEST SCOPE (binding verdict, THE_NON_TRACIALITY_PLAN.md): this is a STATE
  non-traciality statement — the concrete inequality `ω(ab) ≠ ω(ba)` — and NOTHING MORE.
  It is NOT a type statement: it does NOT claim `towerLimitVN` is "not type II₁" as an
  ALGEBRA statement (ω being non-tracial does not preclude some OTHER faithful normal
  tracial state; each finite stage is a full matrix algebra = type I_finite and DOES carry
  the normalized trace — ω simply is not it). No type III / III_λ / III₁ claim, no Connes
  invariant, no modular-spectrum statement is made. Mathlib has no trace/tracial-state/type
  API at this pin; only the concrete inequalities are proved. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.Dynamics
import QIQTH.Tower.CornerEmbed

namespace QIQTH.NonTracial

open QIQTH.Keystone QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **The Gibbs state on a matrix-unit cycle picks out the single weight.** For the matrix
    units `a = E_{nm} = single n m 1` and `b = E_{mn} = single m n 1`, the product
    `a·b = single n n 1` is diagonal, so `ω(a·b) = tr(ρ_β · single n n 1) = w_n`.

    (One lemma serves both cyclic orders: at `(n,m)` it gives `w_n`; instantiated at
    `(m,n)` it gives `ω(E_{mn}·E_{nm}) = w_m`, the swapped cycle.) -/
theorem gibbs_stateOf_single_cycle (C : Finset M) (n m : Micro L C) :
    stateOf (gibbsDensity L C ω β)
        (Matrix.single n m 1 * Matrix.single m n 1)
      = ((gibbsWeight L C ω β n : ℝ) : ℂ) := by
  rw [Matrix.single_mul_single_same, mul_one, stateOf, gibbsDensity,
    QIQTH.Tower.trace_diagonal_mul, Finset.sum_eq_single n]
  · rw [Matrix.single_apply_same, mul_one]
  · intro i _ hi
    rw [Matrix.single_apply_of_ne n n 1 i i (fun hc => hi hc.1.symm), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ n) hmem

/-- **★ FINITE NON-TRACIALITY**: the Gibbs state `ω = stateOf ρ_β` is not a trace. On the
    matrix units `E_{nm}, E_{mn}`, whenever the Gibbs weights differ (`w_n ≠ w_m`),

        ω(E_{nm}·E_{mn}) = w_n ≠ w_m = ω(E_{mn}·E_{nm}).

    HONEST: this is a state-level inequality, NOT a type classification (see the file
    header / the binding verdict). -/
theorem gibbs_state_not_tracial (C : Finset M) (n m : Micro L C)
    (h : gibbsWeight L C ω β n ≠ gibbsWeight L C ω β m) :
    stateOf (gibbsDensity L C ω β) (Matrix.single n m 1 * Matrix.single m n 1)
      ≠ stateOf (gibbsDensity L C ω β) (Matrix.single m n 1 * Matrix.single n m 1) := by
  rw [gibbs_stateOf_single_cycle L ω β C n m, gibbs_stateOf_single_cycle L ω β C m n]
  exact fun hc => h (Complex.ofReal_injective hc)

end QIQTH.NonTracial
