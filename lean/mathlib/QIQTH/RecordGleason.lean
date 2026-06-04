/-
# QIQT-H Stage 1: the Finite Record Effect-Gleason layer (toward the prize)

`PRIZE_ROADMAP.md` (GPT-5.5-pro "be bold" plan) commits to the route
    finite records ⇒ POVM effects ⇒ Gleason uniqueness ⇒ Born ⇒ cylinders ⇒ unique μ,
with **Stage 1 (finite-dimensional) = the minimal breakthrough**.  Its single-state core
is already axiom-free in `GleasonSelector` (`positive_ray_certain_forces_born`: a positive,
linear, ray-certain weight IS the Born functional `⟨ψ|·|ψ⟩` — record certainty kills the
maximally-mixed alternative).

This module discharges the TWO Stage-1 gaps that `GleasonSelector` lacks, both required by
the prize:

 • **Tensor multiplicativity (requirement 2).** `born_kron`: the Born functional factorizes
   on tensor (Kronecker) products — independent experiments multiply.  This is one of the
   uniqueness ingredients (any admissible μ that is multiplicative on split products and
   Born on each factor is Born on the whole), and the formal seed of "independent
   experiments tensor-factorize".

 • **Decoherent coarse-graining additivity (requirement 1, ALL partitions).**
   `decoherent_partition_additive`: for a record family whose off-diagonal decoherence
   functional vanishes, the Born weight of a coarse-grained block `∑_{a∈S} C_a` equals the
   sum of the per-record weights `∑_{a∈S} ⟨ψ|C_a†C_a|ψ⟩`.  This is exactly "Born for all
   decoherent record partitions" — the cylinder/Kolmogorov consistency seed.
   `born_complete_total`: a complete family's weights sum to 1 (genuine probability).

Honest scope: finite-dimensional.  The Busch/Bunce–Wright Mackey-Gleason *extension*
(effect-additivity ⇒ positive linear functional, which would discharge the ray-support
hypothesis from first principles) and the AQFT Covariant Record-Completeness Lemma
(Stages 3–5) stay pen-and-paper / future work (`PRIZE_ROADMAP.md`).  Axiom-free
(standard three only). -/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QIQTH.GleasonSelector
import Mathlib.Tactic

namespace QIQTH.RecordGleason

open Matrix BigOperators
open scoped Kronecker
open QIQTH.GleasonSelector

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

/- ── Born functional: zero and finite-sum linearity ──────────────────────── -/

/-- `born ψ 0 = 0`. -/
@[simp] theorem born_zero (ψ : n → ℂ) : born ψ (0 : Matrix n n ℂ) = 0 := by
  simp [born]

/-- The Born functional commutes with finite sums of effects (linearity over `Finset`). -/
theorem born_sum (ψ : n → ℂ) {ι : Type*} (S : Finset ι) (M : ι → Matrix n n ℂ) :
    born ψ (∑ a ∈ S, M a) = ∑ a ∈ S, born ψ (M a) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, born_add, ih]

/- ── Tensor multiplicativity (requirement 2: independent experiments factor) ── -/

/-- **Mixed-product for `mulVec` on a product vector.**
    `(A ⊗ₖ B) *ᵥ (ψ ⊗ φ) = (A *ᵥ ψ) ⊗ (B *ᵥ φ)` componentwise. -/
theorem kron_mulVec (ψ : n → ℂ) (φ : m → ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    (A ⊗ₖ B) *ᵥ (fun p : n × m => ψ p.1 * φ p.2)
      = fun p : n × m => (A *ᵥ ψ) p.1 * (B *ᵥ φ) p.2 := by
  funext p
  simp only [mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **Born factorizes on tensor products.**  For the product state `ψ ⊗ φ`
    (`(ψ⊗φ)(i,j) = ψ i · φ j`) and a Kronecker effect `A ⊗ₖ B`,
    `⟨ψ⊗φ | A⊗ₖB | ψ⊗φ⟩ = ⟨ψ|A|ψ⟩ · ⟨φ|B|φ⟩`.  So independent experiments multiply — the
    finite-dimensional seed of prize-requirement (2), and a uniqueness ingredient. -/
theorem born_kron (ψ : n → ℂ) (φ : m → ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    born (fun p : n × m => ψ p.1 * φ p.2) (A ⊗ₖ B) = born ψ A * born φ B := by
  unfold born
  rw [kron_mulVec]
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul']; ring

/- ── Decoherent coarse-graining additivity (requirement 1: Born for ALL partitions) ── -/

/-- A finite record family `C : ι → Matrix` is **decoherent for `ψ`** iff its off-diagonal
    decoherence functional vanishes: `⟨ψ| C_a† C_b |ψ⟩ = 0` for `a ≠ b` (records carry no
    residual cross-coherence — the Gell-Mann–Hartle medium-decoherence condition). -/
def Decoherent (ψ : n → ℂ) {ι : Type*} (C : ι → Matrix n n ℂ) : Prop :=
  ∀ a b, a ≠ b → born ψ ((C a)ᴴ * C b) = 0

/-- **Decoherent coarse-graining additivity — "Born for all decoherent partitions".**
    For a decoherent record family, the Born weight of a coarse-grained block
    `C_S = ∑_{a∈S} C_a` equals the sum of the per-record weights:
    `⟨ψ| C_S† C_S |ψ⟩ = ∑_{a∈S} ⟨ψ| C_a† C_a |ψ⟩`.  The off-diagonal cross terms drop by
    decoherence.  This is the cylinder/Kolmogorov-consistency seed for the prize: every
    decoherent coarse-graining is assigned the additive Born/decoherence-functional weight,
    with NO per-partition stipulation. -/
theorem decoherent_partition_additive (ψ : n → ℂ) {ι : Type*} [DecidableEq ι]
    (C : ι → Matrix n n ℂ) (hdec : Decoherent ψ C) (S : Finset ι) :
    born ψ ((∑ a ∈ S, C a)ᴴ * (∑ a ∈ S, C a))
      = ∑ a ∈ S, born ψ ((C a)ᴴ * C a) := by
  rw [Matrix.conjTranspose_sum, Finset.sum_mul, born_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mul_sum, born_sum,
    Finset.sum_eq_single_of_mem a ha (fun b _ hba => hdec a b (Ne.symm hba))]

/-- **A complete record family's weights sum to 1.**  If `∑_a C_a† C_a = I` (a complete
    measurement / resolution of identity) and `ψ` is a unit vector, the per-record Born
    weights `⟨ψ|C_a†C_a|ψ⟩` sum to `1` — a genuine probability distribution over records. -/
theorem born_complete_total (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) {ι : Type*} [Fintype ι]
    (C : ι → Matrix n n ℂ) (hcomplete : ∑ a, (C a)ᴴ * C a = 1) :
    ∑ a, born ψ ((C a)ᴴ * C a) = 1 := by
  rw [← born_sum, hcomplete, born_one ψ hψ]

/-- **Stage-1 record measure is the Born / decoherence-functional measure (packaged).**
    For a complete decoherent record family of a unit state `ψ`, the record-weight function
    `p(a) = ⟨ψ|C_a†C_a|ψ⟩` is (i) a probability distribution (`∑ p = 1`,
    `born_complete_total`), (ii) additive on every coarse-graining
    (`decoherent_partition_additive`), and the single-state Gleason uniqueness
    (`GleasonSelector.positive_ray_certain_forces_born`) pins it as the ONLY positive,
    linear, ray-certain assignment.  Independent experiments multiply (`born_kron`).  This
    is the finite-dimensional minimal-breakthrough milestone of `PRIZE_ROADMAP.md`; the
    covariant continuum upgrade (Mackey-Gleason on the Type-II algebra + AQFT record
    completeness) is the remaining work. -/
theorem stage1_record_measure (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (C : ι → Matrix n n ℂ) (hdec : Decoherent ψ C)
    (hcomplete : ∑ a, (C a)ᴴ * C a = 1) :
    (∑ a, born ψ ((C a)ᴴ * C a) = 1) ∧
    (∀ S : Finset ι, born ψ ((∑ a ∈ S, C a)ᴴ * (∑ a ∈ S, C a))
      = ∑ a ∈ S, born ψ ((C a)ᴴ * C a)) :=
  ⟨born_complete_total ψ hψ C hcomplete,
   fun S => decoherent_partition_additive ψ C hdec S⟩

end QIQTH.RecordGleason
