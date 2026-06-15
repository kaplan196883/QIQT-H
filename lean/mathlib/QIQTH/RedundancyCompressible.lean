/-
RedundancyCompressible.lean — redundant records are compressible: the category-error core (2026-06-15)

Machine-checks the LOGICAL core of the 2026-06-15 correction (two GPT-5.5-pro consults): charging a
holographic capacity bound for the UNCOMPRESSED count of redundant Quantum-Darwinism imprints is a category
error, because `R` identical copies of a classical record carry the information of ONE copy, not `R` of them.

The continuum `A^{3/4}` thermodynamic ceiling (radiation `S~T³,E~T⁴` + Schwarzschild) is NOT formalized here
— it needs Stefan–Boltzmann/Schwarzschild, absent from Mathlib, and stays a cited estimate (the foundations
paper §7.6 Lemma derives it in text). What IS formalized is the part that does the refuting:

- `card_redundantCodewords` — the number of DISTINGUISHABLE `R`-fold redundant records equals the number of
  distinct values `|X|`, independent of the redundancy `R` (NOT `|X|^R`).
- `logb_card_redundant_eq` — hence the information content (log-cardinality / max entropy) of a redundant
  record is `log|X|`, the SAME as a single copy, for every `R`.
- `naive_overcounts` — the naive "`R` copies cost `R·log|X|` bits" strictly exceeds the true `log|X|` (for
  `R ≥ 2`, `|X| ≥ 2`): treating each redundant carrier as independent overcounts the same information `R`-fold.
- `code_subspace_dim` — Hilbert reading: orthonormal redundant-copy states (indexed by the distinct values)
  span a subspace of dimension `|X|`, NOT exponential in `R` — the "code dimension is `#values`, not `2^R`"
  point. (The `R`-fold tensor copies of orthonormal states are orthonormal and in bijection with `X`; that
  structure is captured here by an orthonormal family indexed by `X`.)

So redundancy does not add information: it cannot lift a record's cost against a bound that counts independent
degrees of freedom (joint entropy / code dimension). This is the exact statement the foundations paper's
§7.6 Remark asserts; it is now a theorem. Axiom-free.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

namespace QIQTH.RedundancyCompressible

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `R`-fold redundant broadcast of a value `x`: the same value copied to all `R` carriers. -/
def rep (R : ℕ) (x : X) : Fin R → X := fun _ => x

/-- Distinct values give distinct redundant records (for `R ≥ 1`). -/
theorem rep_injective {R : ℕ} (hR : 0 < R) : Function.Injective (rep (X := X) R) := by
  intro x y h
  have := congrFun h ⟨0, hR⟩
  simpa [rep] using this

/-- The set of redundant codewords: the constant `R`-tuples (one per value broadcast `R` times). -/
noncomputable def redundantCodewords (R : ℕ) : Finset (Fin R → X) :=
  Finset.univ.image (rep R)

/-- **Redundancy is compressible.** The number of DISTINGUISHABLE `R`-fold redundant records equals the
number of distinct values `|X|` — independent of the redundancy `R`, NOT `|X|^R`. -/
theorem card_redundantCodewords {R : ℕ} (hR : 0 < R) :
    (redundantCodewords (X := X) R).card = Fintype.card X := by
  rw [redundantCodewords, Finset.card_image_of_injective _ (rep_injective hR), Finset.card_univ]

/-- The full space of INDEPENDENT `R`-tuples has `|X|^R` elements (exponential in `R`) — the count the
naive "every imprint a separate d.o.f." reading would use. -/
theorem card_allTuples (R : ℕ) :
    Fintype.card (Fin R → X) = (Fintype.card X) ^ R := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **The information content of a redundant record is `R`-independent** — equal to a single copy's. The
log-cardinality (bits / max entropy) of the distinguishable redundant records is `log|X|` for every `R`. -/
theorem logb_card_redundant_eq {R : ℕ} (hR : 0 < R) :
    Real.logb 2 ((redundantCodewords (X := X) R).card : ℝ) = Real.logb 2 (Fintype.card X : ℝ) := by
  rw [card_redundantCodewords hR]

/-- **The naive "`R` copies cost `R·log|X|`" overcounts.** For `R ≥ 2` distinct redundant carriers of a
nontrivial record (`|X| ≥ 2`), the true information `log|X|` is strictly less than the naive
uncompressed `R·log|X|`: charging the bound for each redundant imprint counts the same information `R`-fold. -/
theorem naive_overcounts {R : ℕ} (hR : 2 ≤ R) (hX : 2 ≤ Fintype.card X) :
    Real.logb 2 ((redundantCodewords (X := X) R).card : ℝ)
      < (R : ℝ) * Real.logb 2 (Fintype.card X : ℝ) := by
  rw [logb_card_redundant_eq (by omega)]
  have hx1 : (1 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast (by omega : 1 < Fintype.card X)
  have hpos : 0 < Real.logb 2 (Fintype.card X : ℝ) := Real.logb_pos (by norm_num) hx1
  have h2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2 : (0 : ℝ) ≤ (R : ℝ) - 2 := by linarith
  nlinarith [hpos, mul_nonneg hR2 (le_of_lt hpos)]

/-- **Hilbert reading: the redundant code subspace has dimension `|X|`, not exponential in `R`.** The
`R`-fold tensor copies of orthonormal record states are themselves orthonormal and in bijection with the
distinct values `X`; modelled here as an orthonormal family `e : X → H`, they span a subspace of dimension
exactly `|X|` (the number of values), NOT `(dim H)^R`. So a redundant code occupies `log|X|` qubits' worth of
dimension regardless of `R`. -/
theorem code_subspace_dim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {e : X → H} (he : Orthonormal ℂ e) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range e)) = Fintype.card X :=
  finrank_span_eq_card he.linearIndependent

end QIQTH.RedundancyCompressible
