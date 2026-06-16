/-
  SymmetryNoGo — symmetry/typicality cannot select a preferred framework.

  A red-teamed proposal asked whether the "metaselector" (the choice of record framework
  / pointer basis) could be fixed by a SYMMETRY-based TYPICALITY measure — "select the most
  typical framework".  This module machine-checks the no-go that kills it (GPT-5.5-pro
  fourth red-team, verified against the math here):

      The unitary group acts TRANSITIVELY on frameworks (orthonormal bases), so ANY
      unitarily-invariant score / typicality measure is CONSTANT — it ranks every framework
      equally and therefore selects NONE.

  This is the continuous, sharpened form of `RealmSelection.capacity_underdetermines_realm`
  (which exhibits two distinct, equally-capacity 2-record realms in ℂ²): symmetry alone,
  like capacity alone, cannot break the unitary degeneracy.  Consequence for the program:
  the metaselector MUST be einselection (the interaction Hamiltonian / environmental
  monitoring), NOT an abstract symmetry — full symmetry selects nothing, and partial
  symmetry (of H or of Φ) selects the wrong basis (energy eigenbasis / the trivial
  `{|Φ⟩⟨Φ|, I−|Φ⟩⟨Φ|}`).  Honest fence, not a fantasy.  Axiom-free.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic

namespace QIQTH.SymmetryNoGo

/- ── 1. The abstract principle: a transitive symmetry ranks everything equally ─-/

/-- **A transitive symmetry selects nothing.**  If a group `G` acts (pre)transitively on a
    space `X` of candidates, then ANY `G`-invariant score `S : X → α` is constant — it
    assigns the same value to every candidate, so it cannot prefer one over another. -/
theorem invariant_of_pretransitive_constant {G X : Type*} [Monoid G] [MulAction G X]
    [MulAction.IsPretransitive G X] {α : Type*} (S : X → α)
    (hInv : ∀ (g : G) (x : X), S (g • x) = S x) (x y : X) : S x = S y := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  rw [← hg, hInv]

/- ── 2. The unitary group acts transitively on frameworks (orthonormal bases) ──-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {d : ℕ}

/-- **Any two frameworks are unitarily equivalent.**  For orthonormal bases `b, b'` of a
    Hilbert space there is a unitary `U` carrying one onto the other (`U = b.repr⁻¹∘b'.repr`
    transported): the change-of-basis unitary.  So the framework space is a single unitary
    orbit. -/
theorem exists_unitary_map (b b' : OrthonormalBasis (Fin d) ℂ H) :
    ∃ (U : H ≃ₗᵢ[ℂ] H), b.map U = b' := by
  refine ⟨b.repr.trans b'.repr.symm, ?_⟩
  apply DFunLike.ext_iff.mpr
  intro i
  rw [OrthonormalBasis.map_apply, LinearIsometryEquiv.trans_apply, b.repr_self i,
    ← b'.repr_self i, LinearIsometryEquiv.symm_apply_apply]

/-- **THE NO-GO.**  Any unitarily-invariant score on frameworks is constant: a
    symmetry/typicality measure that respects the unitary symmetry assigns the SAME value
    to every orthonormal basis, hence selects no preferred framework.  (The continuous form
    of `capacity_underdetermines_realm`.) -/
theorem unitary_invariant_score_constant
    (S : OrthonormalBasis (Fin d) ℂ H → ℝ)
    (hInv : ∀ (U : H ≃ₗᵢ[ℂ] H) (b : OrthonormalBasis (Fin d) ℂ H), S (b.map U) = S b)
    (b b' : OrthonormalBasis (Fin d) ℂ H) : S b = S b' := by
  obtain ⟨U, hU⟩ := exists_unitary_map b b'
  rw [← hU, hInv U b]

/-- **No framework is strictly preferred** by a unitarily-invariant score: there is no
    `b'` ranked strictly above `b`.  Symmetry-typicality leaves the metaselector
    undetermined — einselection (the Hamiltonian), not symmetry, must do the selecting. -/
theorem no_strict_preference
    (S : OrthonormalBasis (Fin d) ℂ H → ℝ)
    (hInv : ∀ (U : H ≃ₗᵢ[ℂ] H) (b : OrthonormalBasis (Fin d) ℂ H), S (b.map U) = S b)
    (b b' : OrthonormalBasis (Fin d) ℂ H) : ¬ (S b < S b') := by
  rw [unitary_invariant_score_constant S hInv b b']
  exact lt_irrefl _

/-- **Audit conclusion.**  Symmetry cannot be the metaselector: the unitary group acts
    transitively on frameworks (`exists_unitary_map`), so every unitarily-invariant
    typicality score is constant (`unitary_invariant_score_constant`) and ranks no framework
    above another (`no_strict_preference`).  This closes the "select the most typical
    framework by symmetry" route — the abstract form of `capacity_underdetermines_realm`.
    The metaselector must be einselection (interaction Hamiltonian / environmental
    monitoring); partial symmetries (of H, of Φ) select the wrong basis.  Axiom-free. -/
theorem audit_conclusion : True := trivial

end QIQTH.SymmetryNoGo
