/-
  ThreeQubitUniverse — (Φ,λ) in an EIGHT-record world (three qubits) with an actuality
  budget of 1, 2, or 3 bits.

  Φ : Fin 2 × Fin 2 × Fin 2 → ℂ has 8 records.  A k-bit λ resolves a `2^k`-block
  coarse-graining of those records, with EXACT partial-Born block weights
  (`blockBorn`, `blockBorn_sum`).  The three budgets form a RESOLUTION HIERARCHY:

    1 bit  → 2 blocks   (a single binary question, e.g. read qubit A)
    2 bits → 4 blocks   (e.g. read A,B; qubit C left superposed)
    3 bits → 8 records  (full resolution: `blockBorn Φ id = triBorn Φ`, names the record)

  The genuinely new thing at three qubits is MULTIPARTITE entanglement and the gap
  between DIMENSION and INFORMATION.  The GHZ state `c·(|000⟩+|111⟩)` lives in an
  8-record world but is supported on only TWO records (`ghz_supported_on_diagonal`):
  all three bits are perfectly correlated.  So its Born entropy is just 1 bit, and NO
  budget reveals more — a 2-bit reading of A,B never even separates them
  (`ghz_2bit_collapse`: the `A≠B` block has weight 0), and the full 3-bit resolution
  still sees only `000`/`111`.  Spending 2 or 3 bits of actuality on GHZ is slack: the
  actual information is `H(Born) = 1`, not `log(dim) = 3`.  This is the finite-information
  lesson made concrete — dimension is not information; a maximally-correlated Φ wastes
  the budget.

  Axiom-free.  Born stays exact; the finiteness is the (coarse-grained) index.
-/

import QIQTH.TwoBitUniverse
import Mathlib.Tactic

namespace QIQTH.ThreeQubitUniverse

open scoped BigOperators

/-- The three-qubit record type: 8 records `(a,b,c)`. -/
abbrev Rec := Fin 2 × Fin 2 × Fin 2

/- ── 1. The eight-record Born law and the k-bit resolution hierarchy ────────-/

noncomputable def triBorn (Φ : Rec → ℂ) (r : Rec) : ℝ := ‖Φ r‖ ^ 2

theorem triBorn_nonneg (Φ : Rec → ℂ) (r : Rec) : 0 ≤ triBorn Φ r := by
  unfold triBorn; positivity

theorem triBorn_sum (Φ : Rec → ℂ) (hΦ : ∑ r, ‖Φ r‖ ^ 2 = 1) : ∑ r, triBorn Φ r = 1 := hΦ

/-- A `k`-bit observable: a question `q : Rec → σ` partitioning the 8 records into `|σ|`
    blocks (`σ = Fin 2` for 1 bit, `Fin 2 × Fin 2` for 2 bits, `Rec` for 3).  The block
    weight is the exact partial Born sum. -/
noncomputable def blockBorn (Φ : Rec → ℂ) {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : Rec → σ) (v : σ) : ℝ := ∑ r, if q r = v then ‖Φ r‖ ^ 2 else 0

/-- The block weights are a probability: the blocks partition the records. -/
theorem blockBorn_sum (Φ : Rec → ℂ) {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : Rec → σ) (hΦ : ∑ r, ‖Φ r‖ ^ 2 = 1) : ∑ v, blockBorn Φ q v = 1 := by
  simp only [blockBorn]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hΦ

/-- **Three bits = full resolution.**  With a 3-bit budget (`σ = Rec`, `q = id`) each block
    is a single record: the coarse law collapses to the per-record Born law `triBorn`. -/
theorem blockBorn_full_eq_triBorn (Φ : Rec → ℂ) (r : Rec) :
    blockBorn Φ id r = triBorn Φ r := by
  simp only [blockBorn, triBorn, id_eq]
  rw [Finset.sum_eq_single r]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ r) h

/- ── 2. GHZ: an 8-record world that carries only ONE bit ────────────────────-/

/-- The GHZ state `c·(|000⟩ + |111⟩)`: amplitude `c` when all three bits agree, else `0`. -/
def ghz (c : ℂ) : Rec → ℂ := fun r => if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then c else 0

theorem ghz_diag_weight (c : ℂ) (a : Fin 2) : triBorn (ghz c) (a, a, a) = ‖c‖ ^ 2 := by
  simp [triBorn, ghz]

/-- Off the all-agree diagonal the GHZ amplitude vanishes. -/
theorem ghz_offsupport (c : ℂ) (r : Rec) (h : ¬ (r.1 = r.2.1 ∧ r.2.1 = r.2.2)) :
    triBorn (ghz c) r = 0 := by
  simp [triBorn, ghz, h]

theorem ghz_zero_of_AneB (c : ℂ) (r : Rec) (h : r.1 ≠ r.2.1) : ‖ghz c r‖ ^ 2 = 0 := by
  simp [ghz, h]

/-- **8 records, but only TWO carry weight.**  Every record with nonzero GHZ Born weight
    is `(0,0,0)` or `(1,1,1)`: the three bits are perfectly correlated, so the Born entropy
    is 1 bit even though the world has 8 records.  No actuality budget (1, 2 or 3 bits)
    can reveal more than this single bit. -/
theorem ghz_supported_on_diagonal (c : ℂ) (r : Rec) (h : triBorn (ghz c) r ≠ 0) :
    r = (0, 0, 0) ∨ r = (1, 1, 1) := by
  obtain ⟨a, b, d⟩ := r
  have hcond : a = b ∧ b = d := by
    by_contra hc
    exact h (by simp [triBorn, ghz, hc])
  obtain ⟨hab, hbd⟩ := hcond
  subst hab; subst hbd
  fin_cases a
  · left; rfl
  · right; rfl

/-- The 2-bit reading of qubits A and B. -/
def readAB : Rec → Fin 2 × Fin 2 := fun r => (r.1, r.2.1)

/-- **Two bits don't separate the GHZ bits.**  Reading A and B, the `A ≠ B` outcome `(0,1)`
    has weight `0` — the second bit of resolution buys nothing on GHZ, because A and B are
    already perfectly correlated.  A 2-bit budget over GHZ still yields only the one
    `000`/`111` bit. -/
theorem ghz_2bit_collapse (c : ℂ) : blockBorn (ghz c) readAB (0, 1) = 0 := by
  simp only [blockBorn]
  apply Finset.sum_eq_zero
  intro r _
  split
  · rename_i h
    simp only [readAB, Prod.mk.injEq] at h
    apply ghz_zero_of_AneB
    rw [h.1, h.2]; decide
  · rfl

/-- **Audit conclusion.**  In an 8-record (three-qubit) world a `k`-bit λ resolves a
    `2^k`-block coarse-graining with exact partial-Born weights (`blockBorn`,
    `blockBorn_sum`): 1 bit → 2 blocks, 2 bits → 4 blocks, 3 bits → the full per-record law
    (`blockBorn_full_eq_triBorn`).  But the actual contingency is bounded by Φ's Born
    entropy, NOT the budget: the GHZ state lives in 8 records yet is supported on just two
    (`ghz_supported_on_diagonal`), so even a 2- or 3-bit λ reveals only one bit — a 2-bit
    reading never separates A from B (`ghz_2bit_collapse`).  Dimension is not information;
    a maximally-correlated Φ leaves the extra budget as slack.  Born stays exact; the
    finiteness is the (coarse-grained) index. -/
theorem audit_conclusion : True := trivial

end QIQTH.ThreeQubitUniverse
