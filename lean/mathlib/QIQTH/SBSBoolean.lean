/-
SBSBoolean.lean — SBS ⇒ Boolean record algebra (objectivity), Born-FREE.

Layer 1 of the Born decomposition (see `paper_strategy/49_Born_Status.md` §5): records give
DEFINITE, context-independent outcomes. Here is the qualitative content, with NO probabilities,
weights, or entropies used — only orthogonality / support (so nothing Born-flavoured is smuggled in,
per the GPT-5.5-pro caveat).

Spectrum-broadcast structure (SBS, Korbicz et al.): a pointer value is redundantly imprinted across
many environment fragments, each fragment perfectly distinguishing the value via mutually orthogonal
record sectors. The objectivity claim: every redundant readout is co-referential — a function of ONE
classical pointer variable K₀.

Modelled as orthogonal idempotent projectors `proj k : M →ₗ M` (one sector per pointer value, sectors
mutually annihilating). The load-bearing lemma is purely algebraic:

  `record_unique` — a NONZERO state cannot lie in two different sectors (orthogonality ⇒ unambiguous
  records), and hence
  `fragments_co_referential` — any two fragment readouts of the state agree.

This is the Boolean-record-algebra / objectivity half. It gives definiteness, NOT the Born weights:
the quantitative `p_k = |c_k|²` needs refinement additivity, which records do NOT supply
(`QIQTH/RefinementBorn.lean`). HONEST SCOPE: finite/algebraic; no `sorry`, no project axioms.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Module.LinearMap.Defs

namespace QIQTH.SBSBoolean

variable {𝕜 M K ι : Type*} [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M]

/-- A fragment's record observable: orthogonal projectors, one sector per pointer value `K`, the
sectors mutually annihilating (`proj k ∘ proj l = 0` for `k ≠ l`). Only orthogonality is used. -/
structure RecordObservable (K : Type*) (𝕜 M : Type*)
    [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M] where
  proj : K → (M →ₗ[𝕜] M)
  orthog : ∀ {k l : K}, k ≠ l → proj k ∘ₗ proj l = 0

/-- **Records are unambiguous.** A nonzero state cannot lie in two different pointer sectors:
if `proj k ψ = ψ` and `proj l ψ = ψ` with `ψ ≠ 0` then `k = l`. (Pure consequence of orthogonality.) -/
theorem record_unique (O : RecordObservable K 𝕜 M) {ψ : M} (hψ : ψ ≠ 0)
    {k l : K} (hk : O.proj k ψ = ψ) (hl : O.proj l ψ = ψ) : k = l := by
  by_contra hkl
  have hz : (O.proj k ∘ₗ O.proj l) ψ = 0 := by rw [O.orthog hkl]; simp
  rw [LinearMap.comp_apply, hl, hk] at hz
  exact hψ hz

/-- An exact SBS configuration: `ι`-many fragments whose record observables all place the nonzero
global `state` in the SAME pointer sector `pointer = K₀` (redundant broadcast of one classical value). -/
structure SBSConfig (K ι 𝕜 M : Type*)
    [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M] where
  frag : ι → RecordObservable K 𝕜 M
  state : M
  ne : state ≠ 0
  pointer : K
  matched : ∀ j, (frag j).proj pointer state = state

/-- **SBS ⇒ the broadcast value.** Whatever value a fragment reads on the state equals the one
broadcast pointer `K₀`. -/
theorem record_eq_pointer (C : SBSConfig K ι 𝕜 M) (j : ι) {k : K}
    (hk : (C.frag j).proj k C.state = C.state) : k = C.pointer :=
  record_unique (C.frag j) C.ne hk (C.matched j)

/-- **Redundant records are co-referential (objectivity).** Any two fragment readouts of the global
state agree — so the records are all functions of the single classical pointer variable `K₀`. This is
the Boolean-record-algebra content: definiteness of the macroscopic outcome, with no Born weights. -/
theorem fragments_co_referential (C : SBSConfig K ι 𝕜 M) (j j' : ι) {k k' : K}
    (hk : (C.frag j).proj k C.state = C.state) (hk' : (C.frag j').proj k' C.state = C.state) :
    k = k' := by
  rw [record_eq_pointer C j hk, record_eq_pointer C j' hk']

/-- Non-vacuity: the SBS structures are inhabitable (no soundness/vacuity hole). -/
example : SBSConfig (Fin 1) (Fin 1) ℝ ℝ where
  frag := fun _ => { proj := fun _ => LinearMap.id, orthog := fun {k l} h => absurd (Subsingleton.elim k l) h }
  state := 1
  ne := one_ne_zero
  pointer := 0
  matched := fun _ => rfl

end QIQTH.SBSBoolean
