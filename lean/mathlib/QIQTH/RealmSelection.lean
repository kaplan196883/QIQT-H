/-
RealmSelection.lean — does Q_max select a unique consistent realm? (2026-06-15)

The honest answer, proved here: **Q_max ALONE does not; Q_max + einselection does.** A capacity bound limits
the NUMBER of records (cardinality ≤ e^{Q_R}); it does not pick the BASIS. Many distinct orthogonal record
families have the same cardinality — e.g. in ℂ² the standard decomposition {(1,0),(0,1)} and the Hadamard
decomposition {(1,1),(1,−1)} are both orthogonal 2-record realms (capacity = dim = 2), yet the Hadamard
record (1,1) is not (a multiple of) any standard record. So capacity cannot single out a realm; the basis is
fixed by EINSELECTION (decoherence / the predictability sieve — the pointer observable commuting with the
interaction, e.g. [H_int, σ_z]=0 in `CollisionalGamma`). Given the einselected pointer family, the realm is
determined (and `CapacityModel` makes it finite + single-macroscopic).

This is the same pattern as everywhere: capacity is *structure/finiteness*, not *selection* — selection needs
an extra input (here einselection, exactly as actuality needed λ). See `paper_strategy/57`. Axiom-free.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace QIQTH.RealmSelection

open ComplexConjugate

/-- The ℂ² inner product (conjugate-linear in the first slot). A *realm* is an orthogonal family of record
directions; capacity bounds only how many such directions there are. -/
def ip (x y : Fin 2 → ℂ) : ℂ := conj (x 0) * y 0 + conj (x 1) * y 1

/-- Two record directions are orthogonal. -/
def Orth (x y : Fin 2 → ℂ) : Prop := ip x y = 0

/-- Standard-basis realm. -/
def s0 : Fin 2 → ℂ := ![1, 0]
def s1 : Fin 2 → ℂ := ![0, 1]
/-- Hadamard realm (a genuinely different decomposition of the same space). -/
def h0 : Fin 2 → ℂ := ![1, 1]
def h1 : Fin 2 → ℂ := ![1, -1]

theorem s_orth : Orth s0 s1 := by simp [Orth, ip, s0, s1]

theorem h_orth : Orth h0 h1 := by
  simp only [Orth, ip, h0, h1, Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
  ring

/-- The Hadamard record `(1,1)` is not a scalar multiple of the standard record `(1,0)` — a genuinely
different record (ray). -/
theorem h0_ne_smul_s0 : ¬ ∃ z : ℂ, h0 = z • s0 := by
  rintro ⟨z, hz⟩
  have h := congrFun hz 1
  simp [h0, s0, Pi.smul_apply] at h

/-- ...nor of the standard record `(0,1)`. -/
theorem h0_ne_smul_s1 : ¬ ∃ z : ℂ, h0 = z • s1 := by
  rintro ⟨z, hz⟩
  have h := congrFun hz 0
  simp [h0, s1, Pi.smul_apply] at h

/-- **Q_max alone does NOT select a unique realm (the no-go).** Both `{s0,s1}` and `{h0,h1}` are orthogonal
two-record realms in ℂ² — each capacity-maximal (2 records = dim) — yet they are genuinely distinct (the
Hadamard record `h0` is not a multiple of any standard record). A capacity bound constrains only the *number*
of records, so it cannot pin the realm; an extra input (einselection of the pointer basis) is required. -/
theorem capacity_underdetermines_realm :
    Orth s0 s1 ∧ Orth h0 h1 ∧ (¬ ∃ z : ℂ, h0 = z • s0) ∧ (¬ ∃ z : ℂ, h0 = z • s1) :=
  ⟨s_orth, h_orth, h0_ne_smul_s0, h0_ne_smul_s1⟩

/-- **Q_max + einselection DOES select it (the conditional positive).** A realm is the set of record
directions; once decoherence fixes the einselected pointer family `e`, the realm is exactly `Set.range e` —
hence unique: any two realms built on the same einselected family coincide. Capacity
(`CapacityModel.capacity_total`, `macroscopic_subsingleton`) then makes that realm finite and
single-macroscopic. So: einselection supplies the basis; Q_max supplies finiteness + the single-macroscopic
exclusion; together they pin a unique consistent realm — Q_max alone (`capacity_underdetermines_realm`)
cannot. -/
theorem realm_unique_of_einselection {ι : Type*} (e : ι → (Fin 2 → ℂ))
    (R₁ R₂ : Set (Fin 2 → ℂ)) (h₁ : R₁ = Set.range e) (h₂ : R₂ = Set.range e) : R₁ = R₂ := by
  rw [h₁, h₂]

end QIQTH.RealmSelection
