/-
  Step 1 — Schur classification of unitary-equivariant linear maps.

  GPT-5.5-pro's proof recipe (2-5 weeks of dedicated Lean work):
    1a. Extend D to a complex-linear T on all complex matrices.
    1b. Diagonal unitaries ⇒ T preserves matrix-unit basis:
        T(E_{ij}) is a scalar multiple of E_{ij} for all i, j.
    1c. Permutation unitaries ⇒ unified scalar c_off on off-diagonal
        E_{ij} and c_diag on diagonal E_{ii}.
    1d. Hadamard rotation ⇒ c_diag = α + β/d and c_off = α
        for some α, β ∈ ℂ.
    1e. Hermitian restriction ⇒ α, β ∈ ℝ.

  **A1/A2 strengthening pass (GPT-5.5-pro sixth audit, 2026-05):**

  Sub-axiom 1c (permutation coefficient unification) has been UPGRADED
  to a **proved theorem** under the explicit hypothesis that the
  coefficient family is permutation-symmetric — the hypothesis that
  Step 1b + permutation equivariance of T actually delivers.  The
  original axiomatized form (without the symmetry hypothesis) was
  literally false; the corrected theorem `step1c_collapse_of_perm_symmetric`
  is concretely proved here using `Equiv.swap`-based transitivity on
  ordered pairs.

  The concrete matrix-conjugation lemma `permutation_conj_matrixUnit`
  is also proved here — this is the foundational identity
  `P_σ · E_ij · P_σ* = E_{σ(i), σ(j)}` that drives step 1c's
  coefficient transport.

  Sub-lemmas 1a, 1b, 1d, 1e remain axioms at the interface layer.
  Discharging 1b concretely requires complex-exponential infrastructure
  for diagonal unitaries `D(θ)_{kk} = e^{iθ_k}` plus a multi-θ
  separating-character argument; this is left to a future Mathlib-
  integration round.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases
import QIQTH.GoldsteinStruyveFinDim

namespace QIQTH
namespace GoldsteinStruyveStep1

open Matrix

/-- Matrix unit E_{ij}: the matrix with 1 at position (i, j) and 0
    elsewhere.  This is `Matrix.stdBasisMatrix i j 1` from Mathlib. -/
noncomputable def matrixUnit (d : ℕ) (i j : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun k l => if k = i ∧ l = j then (1 : ℂ) else 0

/-- E_{ij} at component (k, l) — explicit form. -/
lemma matrixUnit_apply (d : ℕ) (i j k l : Fin d) :
    matrixUnit d i j k l = if k = i ∧ l = j then 1 else 0 := rfl

/-- E_{ij} at component (i, j) is 1. -/
lemma matrixUnit_at_ij (d : ℕ) (i j : Fin d) :
    matrixUnit d i j i j = 1 := by simp [matrixUnit]

/-- E_{ij} at any other component is 0. -/
lemma matrixUnit_at_other (d : ℕ) (i j k l : Fin d)
    (h : ¬ (k = i ∧ l = j)) :
    matrixUnit d i j k l = 0 := by simp [matrixUnit, h]

/- ── PROVED: permutation-matrix conjugation foundation lemmas ──────── -/

/-- Permutation matrix associated with a permutation `σ : Equiv.Perm (Fin d)`.
    `P_σ_{kl} = 1` if `k = σ l`, else 0.  This is the standard
    representation: `P_σ · e_l = e_{σ l}` (column-action). -/
noncomputable def permMatrix (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun k l => if k = σ l then (1 : ℂ) else 0

/-- `(P_σ · M)_{kl} = M_{σ⁻¹ k, l}`. -/
lemma permMatrix_mul_apply (d : ℕ) (σ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) ℂ) (k l : Fin d) :
    (permMatrix d σ * M) k l = M (σ.symm k) l := by
  show ∑ m, permMatrix d σ k m * M m l = _
  rw [Finset.sum_eq_single (σ.symm k)]
  · simp [permMatrix]
  · intro m _ hne
    have h_ne : k ≠ σ m := by
      intro h
      apply hne
      rw [h]; exact (σ.symm_apply_apply m).symm
    simp [permMatrix, h_ne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `(M · P_σ)_{kl} = M_{k, σ l}`. -/
lemma mul_permMatrix_apply (d : ℕ) (σ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) ℂ) (k l : Fin d) :
    (M * permMatrix d σ) k l = M k (σ l) := by
  show ∑ m, M k m * permMatrix d σ m l = _
  rw [Finset.sum_eq_single (σ l)]
  · simp [permMatrix]
  · intro m _ hne
    simp [permMatrix, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Conjugate-transpose of a permutation matrix is the inverse-permutation
    matrix. -/
lemma permMatrix_star (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    star (permMatrix d σ) = permMatrix d σ.symm := by
  funext k l
  show star (permMatrix d σ l k) = _
  unfold permMatrix
  by_cases h : l = σ k
  · rw [if_pos h]
    have : k = σ.symm l := by rw [h]; exact (σ.symm_apply_apply k).symm
    rw [if_pos this]
    simp
  · rw [if_neg h]
    have : k ≠ σ.symm l := by
      intro heq
      apply h
      rw [heq]; exact (σ.apply_symm_apply l).symm
    rw [if_neg this]
    simp

/-- **PROVED.**  A permutation matrix is unitary: `P_σ · P_σ* = 1`.
    (`P_σ* = P_{σ⁻¹}` and `P_σ · P_{σ⁻¹} = 1`.)  This is the hypothesis
    needed to feed `P_σ` into `IsUnitaryEquivariant`. -/
lemma permMatrix_unitary (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    permMatrix d σ * star (permMatrix d σ) = 1 := by
  rw [permMatrix_star]
  funext k l
  rw [mul_permMatrix_apply]
  unfold permMatrix
  rw [Equiv.apply_symm_apply]
  by_cases h : k = l
  · subst h; rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg h, Matrix.one_apply_ne h]

/-- **PROVED.**  Conjugation of `E_ij` by a permutation matrix permutes
    the indices: `P_σ · E_ij · P_σ* = E_{σ(i), σ(j)}`.

    *Reason:* Direct matrix-entry computation using
    `permMatrix_mul_apply` and `mul_permMatrix_apply`, then matching
    the `if`-conditions via `σ.symm_apply_apply` / `σ.apply_symm_apply`. -/
theorem permutation_conj_matrixUnit (d : ℕ) (σ : Equiv.Perm (Fin d))
    (i j : Fin d) :
    permMatrix d σ * matrixUnit d i j * star (permMatrix d σ)
      = matrixUnit d (σ i) (σ j) := by
  funext k l
  rw [permMatrix_star]
  -- (P_σ · E_ij)_{k, m} = E_ij_{σ⁻¹ k, m}.
  -- ((P_σ · E_ij) · P_{σ⁻¹})_{kl} = (P_σ · E_ij)_{k, σ⁻¹ l} = E_ij_{σ⁻¹ k, σ⁻¹ l}.
  rw [mul_permMatrix_apply, permMatrix_mul_apply]
  -- Goal: matrixUnit d i j (σ.symm k) (σ.symm l) = matrixUnit d (σ i) (σ j) k l.
  unfold matrixUnit
  have h_iff : (σ.symm k = i ∧ σ.symm l = j) ↔ (k = σ i ∧ l = σ j) := by
    constructor
    · rintro ⟨hk, hl⟩
      refine ⟨?_, ?_⟩
      · rw [← hk]; exact (σ.apply_symm_apply k).symm
      · rw [← hl]; exact (σ.apply_symm_apply l).symm
    · rintro ⟨hk, hl⟩
      refine ⟨?_, ?_⟩
      · rw [hk]; exact σ.symm_apply_apply i
      · rw [hl]; exact σ.symm_apply_apply j
  by_cases h : k = σ i ∧ l = σ j
  · rw [if_pos h, if_pos (h_iff.mpr h)]
  · rw [if_neg h, if_neg (fun heq => h (h_iff.mp heq))]

/- ── PROVED: step 1c with explicit permutation-symmetry hypothesis ── -/

/-- A coefficient family `c : Fin d → Fin d → ℂ` is
    **permutation-symmetric** iff `c (σ i) (σ j) = c i j` for every
    permutation `σ`.

    This is the property that step1b + permutation equivariance of T
    actually delivers: under permutation conjugation, the off-diagonal
    coefficient `c_{ij}` transports to `c_{σi, σj}`, and equivariance
    forces equality. -/
def IsPermutationSymmetric {d : ℕ} (c : Fin d → Fin d → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) (i j : Fin d), c (σ i) (σ j) = c i j

/-- A permutation-symmetric `c` is constant on the diagonal. -/
lemma diag_const_of_perm_symmetric
    {d : ℕ} (c : Fin d → Fin d → ℂ) (hc : IsPermutationSymmetric c)
    (i j : Fin d) : c i i = c j j := by
  -- Use the transposition (i j); under this, c (swap i j i) (swap i j i) = c i i.
  -- (swap i j) i = j.  So c j j = c i i.
  have h := hc (Equiv.swap i j) i i
  rw [Equiv.swap_apply_left] at h
  exact h.symm

/-- A permutation-symmetric `c` is constant on off-diagonal pairs
    (assuming `d ≥ 2`, so off-diagonal pairs exist). -/
lemma offdiag_const_of_perm_symmetric
    {d : ℕ} (c : Fin d → Fin d → ℂ) (hc : IsPermutationSymmetric c)
    (i j k l : Fin d) (hij : i ≠ j) (hkl : k ≠ l) :
    c i j = c k l := by
  -- Plan: explicitly construct a permutation σ with σ i = k and σ j = l.
  -- Compose two transpositions: first move i to k, then move j to l
  -- carefully so the second transposition doesn't move k.
  --
  -- Case analysis on whether the four indices collide.
  -- σ₁ := swap i k:    σ₁ i = k.
  -- After applying σ₁, j has been mapped to swap i k j.  Call this j₁.
  --   If j ∉ {i, k}: j₁ = j.   Then σ₂ := swap j l:  σ₂ j = l, σ₂ k = k iff k ∉ {j, l}.
  --     Need k ≠ j (true, since hkl) and k ≠ l (true, hkl).  ✓
  --   If j = k (impossible since hij says j ≠ i — wait, j = k is allowed).
  --     j = k: j₁ = swap i k k = i.   Then σ₂ := swap i l: σ₂ j₁ = σ₂ i = l.  σ₂ k = ?
  --       σ₂ k = swap i l k.  If k = i: σ₂ k = l, but k ≠ i (we are in case j = k and j ≠ i).
  --       If k = l: σ₂ k = i.  But we need σ₂ (σ₁ i) = σ₂ k = k, so need σ₂ k = k.
  --       So this case requires k ≠ l (which holds) AND k ≠ i (which holds in subcase).
  --       Hmm but we need σ₂ (σ₁ i) = σ₂ k = k AND k ≠ i means σ₂ k = k iff k ∉ {i, l}.
  --   If j = i: contradicts hij.
  --
  -- This case analysis is somewhat involved.  Use a cleaner approach:
  -- construct σ as composition of swaps, and verify via Finite case
  -- analysis through equiv arithmetic.
  --
  -- Cleaner: define σ piecewise as a Finite-valued bijection.  Use
  -- σ = swap k (swap i k j ↦ l) ∘ swap i k  (informally).
  -- Easier: directly write σ as the function and check σ ∘ σ = id type style.
  --
  -- Even simpler: split into two transposition transports.
  --   Step A: c i j = c k (τ j), where τ = swap i k (so τ i = k).
  --   Step B: c k m = c k l, for m = τ j, provided we can find a permutation
  --     fixing k and mapping m to l.
  -- For Step B: if m = l, done.  Else: swap m l fixes k iff k ∉ {m, l}.
  -- Need k ≠ m and k ≠ l.  k ≠ l is hkl.  k ≠ m = τ j = swap i k j:
  --   if j = i: m = k.  But hij says j ≠ i.
  --   if j = k: m = i ≠ k (k ≠ i since hij would say j ≠ i means i, j distinct;
  --     but we're in subcase j = k, then i ≠ k.  So m = i ≠ k.) ✓
  --   if j ∉ {i, k}: m = j.  Is k = j possible? Yes if j = k, but we just
  --     handled that. So m = j ≠ k. ✓
  -- So we always have k ≠ m, hence swap m l fixes k.
  --
  -- Combine:  c i j = c (swap i k i) (swap i k j) = c k m;
  --           c k m = c (swap m l k) (swap m l m) = c k l (since k ∉ {m, l}).
  set τ : Equiv.Perm (Fin d) := Equiv.swap i k with hτ
  set m : Fin d := τ j with hm
  -- Step A: c i j = c k m.
  have hA : c i j = c k m := by
    have := hc τ i j
    rw [hτ] at this
    rw [Equiv.swap_apply_left] at this
    -- this : c k (τ j) = c i j;  here τ j = m by definition.
    exact this.symm
  -- Step B: c k m = c k l.
  -- Need to show k ≠ m and k ≠ l, then use swap m l (which fixes k).
  have hk_ne_m : k ≠ m := by
    -- m = swap i k j.  Cases on j.
    by_cases hj_eq_i : j = i
    · -- contradicts hij (i ≠ j).
      exact absurd hj_eq_i.symm hij
    · by_cases hj_eq_k : j = k
      · -- m = swap i k k = i.  Need k ≠ i.
        have hk_ne_i : k ≠ i := by
          -- hij : i ≠ j;  if j = k and k = i, then j = i, contradiction.
          intro hki
          apply hij
          rw [hj_eq_k, ← hki]
        rw [hm, hj_eq_k, hτ, Equiv.swap_apply_right]
        exact hk_ne_i
      · -- m = j (j ∉ {i, k}).  Need k ≠ j.
        have : τ j = j := Equiv.swap_apply_of_ne_of_ne hj_eq_i hj_eq_k
        rw [hm, this]
        exact fun h => hj_eq_k h.symm
  -- Now build the second swap and apply.
  by_cases hml : m = l
  · -- m = l: c k m = c k l trivially.
    rw [hA, hml]
  · -- m ≠ l: use swap m l.  k ∉ {m, l} (we just verified k ≠ m, k ≠ l),
    -- so swap m l fixes k.
    set ρ : Equiv.Perm (Fin d) := Equiv.swap m l with hρ
    -- ρ k = k (since k ∉ {m, l}).
    have hρ_fix_k : ρ k = k := Equiv.swap_apply_of_ne_of_ne hk_ne_m hkl
    -- ρ m = l.
    have hρ_m : ρ m = l := by rw [hρ]; exact Equiv.swap_apply_left m l
    have h_apply := hc ρ k m
    -- h_apply : c (ρ k) (ρ m) = c k m.
    rw [hρ_fix_k, hρ_m] at h_apply
    -- h_apply : c k l = c k m.
    rw [hA, ← h_apply]

/-- **PROVED — Step 1c via explicit permutation-symmetry.**

    Under the hypothesis that the coefficient family `c : Fin d → Fin d
    → ℂ` is permutation-symmetric (the hypothesis that step1b +
    permutation equivariance of T delivers, in the actual Step 1
    argument), the coefficient family collapses to exactly two scalars:
    `c_off` for all off-diagonal entries and `c_diag` for all diagonal
    entries.

    This upgrades the original `step1c_coefficient_unification` axiom
    from a literally-false bare-c claim to a true theorem under the
    correct hypothesis. -/
theorem step1c_collapse_of_perm_symmetric
    {d : ℕ} (hd : 1 < d) (c : Fin d → Fin d → ℂ)
    (hc : IsPermutationSymmetric c) :
    ∃ c_off c_diag : ℂ,
      (∀ i j : Fin d, i ≠ j → c i j = c_off) ∧
      (∀ i : Fin d, c i i = c_diag) := by
  -- Witnesses: c_off := c 0 1 (using d ≥ 2),  c_diag := c 0 0.
  refine ⟨c ⟨0, by omega⟩ ⟨1, by omega⟩, c ⟨0, by omega⟩ ⟨0, by omega⟩, ?_, ?_⟩
  · intro i j hij
    have h_off : (⟨0, by omega⟩ : Fin d) ≠ (⟨1, by omega⟩ : Fin d) := by
      intro h
      have := Fin.val_eq_of_eq h
      simp at this
    exact offdiag_const_of_perm_symmetric c hc i j ⟨0, by omega⟩ ⟨1, by omega⟩ hij h_off
  · intro i
    exact diag_const_of_perm_symmetric c hc i ⟨0, by omega⟩

/- ── PROVED: diagonal-unitary conjugation foundation lemmas ───────── -/

/-- Diagonal unitary parameterised directly by a coefficient vector
    `z : Fin d → ℂ` (self-contained; avoids `Complex.exp` / `Circle`
    analytic infrastructure).  `diagonalU z _{kk} = z k`,
    `diagonalU z _{kl} = 0` for `k ≠ l`.  For a *unitary* diagonal one
    takes each `z k` of unit modulus (`z k · star (z k) = 1`); but the
    conjugation identity below holds for *any* diagonal `z`. -/
noncomputable def diagonalU (d : ℕ) (z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun k l => if k = l then z k else 0

/-- `(diagonalU z · M)_{kl} = z k · M_{kl}` (scales row `k`). -/
lemma diagonalU_mul_apply (d : ℕ) (z : Fin d → ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) (k l : Fin d) :
    (diagonalU d z * M) k l = z k * M k l := by
  show ∑ m, diagonalU d z k m * M m l = _
  rw [Finset.sum_eq_single k]
  · simp [diagonalU]
  · intro m _ hne
    have hkm : k ≠ m := fun h => hne h.symm
    simp [diagonalU, hkm]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `(M · diagonalU z)_{kl} = M_{kl} · z l` (scales column `l`). -/
lemma mul_diagonalU_apply (d : ℕ) (z : Fin d → ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) (k l : Fin d) :
    (M * diagonalU d z) k l = M k l * z l := by
  show ∑ m, M k m * diagonalU d z m l = _
  rw [Finset.sum_eq_single l]
  · simp [diagonalU]
  · intro m _ hne
    simp [diagonalU, hne]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- Conjugate-transpose of a diagonal matrix is the conjugated diagonal. -/
lemma diagonalU_star (d : ℕ) (z : Fin d → ℂ) :
    star (diagonalU d z) = diagonalU d (fun i => star (z i)) := by
  funext k l
  show star (diagonalU d z l k) = _
  unfold diagonalU
  by_cases h : k = l
  · subst h; simp
  · rw [if_neg (fun heq => h heq.symm), if_neg h]
    simp

/-- **PROVED — diagonal-unitary conjugation of a matrix unit.**

    `diagonalU z · E_ij · (diagonalU z)* = (z i · conj (z j)) • E_ij`.

    This is the diagonal-character analog of `permutation_conj_matrixUnit`
    and the concrete content GPT-5.5-pro's recipe asks for in step 1b
    (phrased via unit-modulus coefficients rather than `e^{iθ}`).  The
    identity itself holds for *any* diagonal `z`; unitarity (`z k` of
    unit modulus) is only needed downstream when one wants the
    conjugation to be a genuine symmetry of the state space. -/
theorem diagonalU_conj_matrixUnit (d : ℕ) (z : Fin d → ℂ) (i j : Fin d) :
    diagonalU d z * matrixUnit d i j * star (diagonalU d z)
      = (z i * star (z j)) • matrixUnit d i j := by
  funext k l
  rw [diagonalU_star]
  rw [mul_diagonalU_apply, diagonalU_mul_apply]
  -- LHS at (k,l): z k * (E_ij)_{kl} * star (z l).
  -- RHS at (k,l): (z i * star (z j)) * (E_ij)_{kl}.
  show z k * matrixUnit d i j k l * star (z l)
       = (z i * star (z j)) * matrixUnit d i j k l
  unfold matrixUnit
  by_cases h : k = i ∧ l = j
  · obtain ⟨hk, hl⟩ := h
    subst hk; subst hl
    rw [if_pos ⟨rfl, rfl⟩]
    ring
  · rw [if_neg h, mul_zero, mul_zero, zero_mul]

/-- **PROVED.**  A diagonal matrix with unit-modulus entries
    (`z k · conj (z k) = 1` for all `k`) is unitary:
    `diagonalU z · (diagonalU z)* = 1`.  This is the hypothesis needed
    to feed `diagonalU z` into `IsUnitaryEquivariant`. -/
lemma diagonalU_unitary (d : ℕ) (z : Fin d → ℂ)
    (hz : ∀ k, z k * star (z k) = 1) :
    diagonalU d z * star (diagonalU d z) = 1 := by
  rw [diagonalU_star]
  funext k l
  rw [diagonalU_mul_apply]
  unfold diagonalU
  by_cases h : k = l
  · subst h; rw [if_pos rfl, hz, Matrix.one_apply_eq]
  · rw [if_neg h, mul_zero, Matrix.one_apply_ne h]

/- ── PROVED: the off-diagonal support step (step 1b core) ──────────── -/

/-- The single-marker diagonal `z_p = I` at `p`, `1` elsewhere, is
    unit modulus at every index. -/
lemma marker_unit (d : ℕ) (p m : Fin d) :
    (if m = p then Complex.I else 1) * star (if m = p then Complex.I else 1) = 1 := by
  by_cases hm : m = p
  · rw [if_pos hm, show star Complex.I = -Complex.I from by simp, mul_neg,
      Complex.I_mul_I, neg_neg]
  · rw [if_neg hm, star_one, one_mul]

/-- **PROVED — phase separation (diagonal version).**  For `k ≠ l` there is
    a unit-modulus diagonal with `z k · conj (z l) ≠ 1` (marker at `k`). -/
lemma phase_separation_diag {d : ℕ} {k l : Fin d} (hkl : k ≠ l) :
    ∃ z : Fin d → ℂ, (∀ m, z m * star (z m) = 1) ∧ z k * star (z l) ≠ 1 := by
  refine ⟨fun m => if m = k then Complex.I else 1, marker_unit d k, ?_⟩
  simp [Ne.symm hkl, Complex.ext_iff] <;> norm_num

/-- **PROVED — phase separation.**

    For `i ≠ j` and any off-target index pair `(k,l) ≠ (i,j)`, there is a
    unit-modulus diagonal `z` whose character separates the two pairs:
    `z i · conj (z j) ≠ z k · conj (z l)`.

    Construction: a single-marker diagonal `z_p = I` at one index `p`,
    `1` elsewhere (both unit modulus).  Choosing `p = i` works whenever
    `k ≠ i`; the remaining case `k = i` (forcing `l ≠ j`) is separated by
    `p = j`.  This is the analytic heart of the "diagonal characters
    pin the support of `D(E_ij)`" argument, done with `{1, I}` phases so
    it stays `Complex.exp`-free. -/
lemma phase_separation {d : ℕ} {i j k l : Fin d} (hij : i ≠ j)
    (hkl : (k, l) ≠ (i, j)) :
    ∃ z : Fin d → ℂ, (∀ m, z m * star (z m) = 1) ∧
      z i * star (z j) ≠ z k * star (z l) := by
  have hstarI : star Complex.I = -Complex.I := by simp
  have hI_unit : Complex.I * star Complex.I = 1 := by
    rw [hstarI, mul_neg, Complex.I_mul_I, neg_neg]
  have hmarker : ∀ (p : Fin d) (m : Fin d),
      (if m = p then Complex.I else 1) * star (if m = p then Complex.I else 1) = 1 := by
    intro p m
    by_cases hm : m = p
    · rw [if_pos hm]; exact hI_unit
    · rw [if_neg hm, star_one, one_mul]
  by_cases hki : k = i
  · -- k = i, hence l ≠ j; separate with the marker at j
    have hlj : l ≠ j := fun h => hkl (by rw [hki, h])
    refine ⟨fun m => if m = j then Complex.I else 1, hmarker j, ?_⟩
    simp [hki, hij, hlj, hstarI, Complex.ext_iff] <;> norm_num
  · -- k ≠ i; separate with the marker at i
    refine ⟨fun m => if m = i then Complex.I else 1, hmarker i, ?_⟩
    by_cases hli : l = i
    · simp [hki, hij.symm, hli, hstarI, Complex.ext_iff] <;> norm_num
    · simp [hki, hij.symm, hli, Complex.ext_iff] <;> norm_num

/-- **PROVED — off-diagonal support of a unitary-equivariant map.**

    For a ℂ-linear, unitary-equivariant `D` and `i ≠ j`, the image
    `D(E_ij)` of an off-diagonal matrix unit vanishes off the `(i,j)`
    entry: `D(E_ij) k l = 0` whenever `(k,l) ≠ (i,j)`.  Equivalently,
    `D(E_ij)` is a scalar multiple of `E_ij`.

    *Proof:* conjugating `E_ij` by a unit-modulus diagonal `U = diagonalU z`
    multiplies it by the character `z_i · conj z_j`
    (`diagonalU_conj_matrixUnit`); equivariance + linearity then force, at
    each entry `(k,l)`, `(z_i conj z_j − z_k conj z_l) · D(E_ij) k l = 0`.
    `phase_separation` supplies a `z` with nonzero bracket, so the entry
    is `0`.  This is the genuine content of Goldstein-Struyve step 1b. -/
theorem offdiag_support_of_unitary_equivariant
    {d : ℕ} (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_lin : GoldsteinStruyveFinDim.IsLinear D)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D)
    {i j k l : Fin d} (hij : i ≠ j) (hkl : (k, l) ≠ (i, j)) :
    D (matrixUnit d i j) k l = 0 := by
  have hsmul : ∀ (c : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ), D (c • ρ) = c • D ρ := by
    intro c ρ; have := h_lin c 0 ρ ρ; simpa using this
  obtain ⟨z, hzunit, hsep⟩ := phase_separation hij hkl
  have hU : diagonalU d z * star (diagonalU d z) = 1 := diagonalU_unitary d z hzunit
  have heq := h_uniteq (diagonalU d z) hU (matrixUnit d i j)
  rw [diagonalU_conj_matrixUnit, hsmul] at heq
  have hRHS : (diagonalU d z * D (matrixUnit d i j) * star (diagonalU d z)) k l
      = z k * D (matrixUnit d i j) k l * star (z l) := by
    rw [diagonalU_star, mul_diagonalU_apply, diagonalU_mul_apply]
  have hkey := congrFun (congrFun heq k) l
  rw [Matrix.smul_apply, smul_eq_mul, hRHS] at hkey
  set X := D (matrixUnit d i j) k l with hX
  have hzero : (z i * star (z j) - z k * star (z l)) * X = 0 := by
    have hcomm : z i * star (z j) * X = z k * star (z l) * X := by rw [hkey]; ring
    rw [sub_mul, hcomm, sub_self]
  rcases mul_eq_zero.mp hzero with hb | hx
  · exact absurd (sub_eq_zero.mp hb) hsep
  · exact hx

/-- **PROVED.**  Consequence of the support step: an off-diagonal matrix
    unit maps to a scalar multiple of itself,
    `D(E_ij) = (D(E_ij) i j) • E_ij` (for `i ≠ j`). -/
theorem offdiag_eq_smul
    {d : ℕ} (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_lin : GoldsteinStruyveFinDim.IsLinear D)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D)
    {i j : Fin d} (hij : i ≠ j) :
    D (matrixUnit d i j) = (D (matrixUnit d i j) i j) • matrixUnit d i j := by
  funext k l
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hkl : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := hkl
    rw [matrixUnit_at_ij, mul_one]
  · have hne : (k, l) ≠ (i, j) := fun h => hkl (by rwa [Prod.mk.injEq] at h)
    rw [offdiag_support_of_unitary_equivariant D h_lin h_uniteq hij hne,
      matrixUnit_at_other d i j k l hkl, mul_zero]

/-- **PROVED — diagonal support of a unitary-equivariant map.**

    The diagonal analog of the support step: a diagonal matrix unit `E_ii`
    maps to a *diagonal* matrix, `D(E_ii) k l = 0` for `k ≠ l`.  Since the
    character `z_i · conj z_i = 1`, `E_ii` is fixed by every unit-modulus
    diagonal conjugation, so `D(E_ii)` commutes with all of them; reading
    entry `(k,l)` with `k ≠ l` and a separating `z` forces it to vanish. -/
theorem diag_support_of_unitary_equivariant
    {d : ℕ} (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D)
    {i k l : Fin d} (hkl : k ≠ l) :
    D (matrixUnit d i i) k l = 0 := by
  obtain ⟨z, hzunit, hsep⟩ := phase_separation_diag hkl
  have hU : diagonalU d z * star (diagonalU d z) = 1 := diagonalU_unitary d z hzunit
  have heq := h_uniteq (diagonalU d z) hU (matrixUnit d i i)
  rw [diagonalU_conj_matrixUnit, hzunit i, one_smul] at heq
  have hRHS : (diagonalU d z * D (matrixUnit d i i) * star (diagonalU d z)) k l
      = z k * D (matrixUnit d i i) k l * star (z l) := by
    rw [diagonalU_star, mul_diagonalU_apply, diagonalU_mul_apply]
  have hkey := congrFun (congrFun heq k) l
  rw [hRHS] at hkey
  set X := D (matrixUnit d i i) k l with hX
  have hzero : (1 - z k * star (z l)) * X = 0 := by
    have hc : z k * star (z l) * X = X := by
      conv_rhs => rw [hkey]
      ring
    rw [sub_mul, one_mul, hc, sub_self]
  rcases mul_eq_zero.mp hzero with hb | hx
  · exact absurd (sub_eq_zero.mp hb).symm hsep
  · exact hx

/-- **PROVED.**  The coefficient family `c i j := D(E_ij) i j` of a
    unitary-equivariant `D` is permutation-symmetric:
    `c (σ i) (σ j) = c i j`.

    *Proof:* conjugation by `P_σ` sends `E_ij` to `E_{σi,σj}`
    (`permutation_conj_matrixUnit`) and reads `(P_σ M P_σ*)_{σi,σj} = M_{ij}`
    off the permutation-matrix apply lemmas; equivariance equates the two. -/
theorem coeff_perm_symmetric
    {d : ℕ} (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D) :
    IsPermutationSymmetric (fun i j => D (matrixUnit d i j) i j) := by
  intro σ i j
  have hP : permMatrix d σ * star (permMatrix d σ) = 1 := permMatrix_unitary d σ
  have heq := h_uniteq (permMatrix d σ) hP (matrixUnit d i j)
  rw [permutation_conj_matrixUnit] at heq
  have hpt := congrFun (congrFun heq (σ i)) (σ j)
  rw [permMatrix_star, mul_permMatrix_apply, permMatrix_mul_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hpt
  exact hpt

/-- **PROVED.**  For a unitary-equivariant `D` (with `d ≥ 2`), the
    coefficient `D(E_ij) i j` takes a single value `c_off` across all
    off-diagonal `(i,j)`, and a single value `c_diag` across all diagonal
    `(i,i)`.  Combines `coeff_perm_symmetric` with the permutation-symmetry
    collapse `step1c_collapse_of_perm_symmetric`. -/
theorem coeff_collapse
    {d : ℕ} (hd : 1 < d) (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D) :
    ∃ c_off c_diag : ℂ,
      (∀ i j, i ≠ j → D (matrixUnit d i j) i j = c_off) ∧
      (∀ i, D (matrixUnit d i i) i i = c_diag) :=
  step1c_collapse_of_perm_symmetric hd _ (coeff_perm_symmetric D h_uniteq)

/-- **PROVED.**  The *diagonal* coefficient family `e i k := D(E_ii) k k`
    (the `(k,k)` entry of the image of the diagonal unit `E_ii`) is
    permutation-symmetric. -/
theorem diag_coeff_perm_symmetric
    {d : ℕ} (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D) :
    IsPermutationSymmetric (fun i k => D (matrixUnit d i i) k k) := by
  intro σ i k
  have hP : permMatrix d σ * star (permMatrix d σ) = 1 := permMatrix_unitary d σ
  have heq := h_uniteq (permMatrix d σ) hP (matrixUnit d i i)
  rw [permutation_conj_matrixUnit] at heq
  have hpt := congrFun (congrFun heq (σ k)) (σ k)
  rw [permMatrix_star, mul_permMatrix_apply, permMatrix_mul_apply,
    Equiv.symm_apply_apply] at hpt
  exact hpt

/-- **PROVED.**  `D(E_ii)` is diagonal (`diag_support`) with a single
    on-diagonal value `c_diag` at `(i,i)` and a single value `c_rest` at
    every other diagonal slot `(k,k)`, `k ≠ i`.  Hence
    `D(E_ii) = c_rest · I + (c_diag − c_rest) · E_ii`. -/
theorem diag_coeff_collapse
    {d : ℕ} (hd : 1 < d) (D : GoldsteinStruyveFinDim.DensityFunctional d)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D) :
    ∃ c_rest c_diag : ℂ,
      (∀ i k, i ≠ k → D (matrixUnit d i i) k k = c_rest) ∧
      (∀ i, D (matrixUnit d i i) i i = c_diag) :=
  step1c_collapse_of_perm_symmetric hd _ (diag_coeff_perm_symmetric D h_uniteq)

/- ── Honest residual interface ────────────────────────────────────── -/

/-  The earlier version of this module carried five placeholder
    "sub-lemma" axioms (1a–1e).  Three of them (1b, 1c, 1e) were
    *literally false as stated* — e.g. 1b's bare claim "for any `T`,
    `T(E_ij)` is a scalar multiple of `E_ij`" is refuted by the
    transpose map `M ↦ Mᵀ`, and 1e's "every complex number is real"
    is plainly false.  All five were unused: `step1_via_sub_lemmas`
    delegates directly to `GoldsteinStruyveFinDim.step1_schur_classification`.
    They have therefore been DELETED.

    What survives is genuinely proved:
      • `permutation_conj_matrixUnit` : P_σ · E_ij · P_σ* = E_{σi,σj}.
      • `diagonalU_conj_matrixUnit`   : D(z) · E_ij · D(z)* =
                                        (z_i · conj z_j) • E_ij.
      • `step1c_collapse_of_perm_symmetric` : permutation-symmetric
        coefficient families collapse to two scalars.

    The single remaining Step-1 interface axiom in the project is the
    top-level `GoldsteinStruyveFinDim.step1_schur_classification`
    (the full Schur classification of unitary-equivariant maps); the
    two conjugation lemmas above are the concrete building blocks of
    its eventual discharge.  -/

/-- **Step 1 (delegation).**

    A linear, unitary-equivariant density functional on `d × d` matrices
    (d ≥ 2) has the Schur form `D = α · canonical + β · uniform` for
    some `α, β ∈ ℝ`.

    Delegates to the single top-level interface axiom
    `GoldsteinStruyveFinDim.step1_schur_classification`.  The concrete
    foundation lemmas proved in this module (`permutation_conj_matrixUnit`,
    `diagonalU_conj_matrixUnit`, `step1c_collapse_of_perm_symmetric`)
    are the building blocks of that axiom's eventual full discharge. -/
theorem step1_via_sub_lemmas
    (d : ℕ) (hd : 1 < d)
    (D : @GoldsteinStruyveFinDim.DensityFunctional d)
    (h_lin : GoldsteinStruyveFinDim.IsLinear D)
    (h_uniteq : GoldsteinStruyveFinDim.IsUnitaryEquivariant D) :
    ∃ α β : ℝ, D = @GoldsteinStruyveFinDim.schurForm d α β := by
  exact GoldsteinStruyveFinDim.step1_schur_classification d hd D h_lin h_uniteq

end GoldsteinStruyveStep1
end QIQTH
