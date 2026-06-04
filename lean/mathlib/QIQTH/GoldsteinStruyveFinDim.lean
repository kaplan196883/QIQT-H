/-
  Goldstein-Struyve QIQT-H — finite-dimensional concrete version.

  GPT-5.5-pro fifth+sixth audit recommendation:
    Steps 2 and 3 of the four-step decomposition are Lean-tractable
    from concrete `Matrix (Fin d) (Fin d) ℂ` infrastructure.
    Step 1 (Schur classification) takes 2-5 weeks of dedicated Lean
    work via the concrete matrix-unit approach (diagonal + permutation
    + Hadamard unitaries).  Step 4 is the irreducible physical axiom.

  **This module discharges Steps 2 and 4 concretely; provides a clean
  axiom for Step 1; and sets up the framework for Step 3.**

  Concretely:

    `schurForm α β ρ := (α : ℂ) • ρ + (β : ℂ) • (trace(ρ) / d) • 1`

  Step 2 (PROVED): IsNormalized (schurForm α β) ⇒ α + β = 1.
  Step 4 (PROVED): Schur form + non-degeneracy on a pure state ⇒
                    (α, β) = (1, 0).
  Steps 1, 3 (axiomatized): cleanly stated with concrete matrix content.

  NOTE (2026-06): `QIQTH.EffectGleason.finite_effect_gleason` now gives an INDEPENDENT,
  fully axiom-free finite-dimensional Born-uniqueness result (effect/POVM Gleason:
  effect-algebra-additive μ ⇒ μ E = tr(ρE), ρ a unique density matrix).  The Goldstein-Struyve
  Step-1/Step-3 axioms below are a DIFFERENT route (Schur classification of unitary-equivariant
  density functionals + tensor multiplicativity), so they are NOT discharged by effect-Gleason
  and are retained here.  Re-routing the Born-uniqueness *consumer*
  (`FQEquivarianceUniqueness` / `canonical_ic_measure_principle`) through effect-Gleason
  instead — which would let these two axioms be dropped — is a deferred refactor: it requires
  bridging the abstract IC-measure/`DensityFunctional` interface to the concrete `EffectMeasure`
  layer (different abstraction levels).

  The combined `goldstein_struyve_findim_uniqueness` theorem composes
  all four steps and is proved (modulo the two interface axioms).
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace QIQTH
namespace GoldsteinStruyveFinDim

open Matrix
open scoped Kronecker

variable {d : ℕ}

/-- A density functional on `d × d` complex matrices. -/
def DensityFunctional (d : ℕ) : Type :=
  Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ

/-- The canonical density functional `D_ρ = ρ`. -/
def canonicalD : DensityFunctional d := id

/-- The "uniform" density functional `D_ρ = (tr ρ / d) · I`. -/
noncomputable def uniformD (d : ℕ) : DensityFunctional d :=
  fun ρ => (Matrix.trace ρ / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The Schur form parameterised by `α, β : ℝ`:
    `D = α · canonical + β · uniform`. -/
noncomputable def schurForm (α β : ℝ) : DensityFunctional d :=
  fun ρ => (α : ℂ) • ρ + (β : ℂ) • ((Matrix.trace ρ / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))

/-- A density functional is **normalized** iff it preserves trace. -/
def IsNormalized (D : DensityFunctional d) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ, Matrix.trace (D ρ) = Matrix.trace ρ

/- ── Step 2 (PROVED): normalization constraint ────────────────────── -/

/-- **Step 2 (PROVED) — Normalization constraint.**

    If `schurForm α β` is normalized, then `α + β = 1`.

    Proof: apply normalization at `ρ = I` (the identity matrix).
    `trace(I) = d`, so `trace(schurForm α β I) = (α + β) · d`, which
    must equal `d`.  Hence `α + β = 1`. -/
theorem step2_normalization
    {d : ℕ} (hd : 0 < d) (α β : ℝ)
    (h_norm : IsNormalized (@schurForm d α β)) :
    α + β = 1 := by
  -- Apply the normalization hypothesis at ρ = I.
  have h := h_norm (1 : Matrix (Fin d) (Fin d) ℂ)
  have hd_ne : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hd
  -- Simplify: trace(schurForm α β I) and trace(I).
  simp only [schurForm, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
             smul_eq_mul, Fintype.card_fin] at h
  -- h : (α : ℂ) * d + β * (d / d * d) = d
  rw [div_self hd_ne, one_mul] at h
  -- h : (α : ℂ) * d + β * d = d
  -- Factor: (α + β) * d = d, then cancel d to get α + β = 1.
  have h_factor : ((α : ℂ) + (β : ℂ)) * (d : ℂ) = (d : ℂ) := by
    have h_ring : ((α : ℂ) + (β : ℂ)) * (d : ℂ) = (α : ℂ) * d + (β : ℂ) * d := by ring
    rw [h_ring]
    exact h
  have h_complex : (α : ℂ) + (β : ℂ) = 1 :=
    mul_right_cancel₀ hd_ne (h_factor.trans (one_mul _).symm)
  -- Cast back to ℝ.
  exact_mod_cast h_complex

/- ── Step 1 (axiomatized): Schur classification ──────────────────── -/

/-- **Linearity.** -/
def IsLinear (D : DensityFunctional d) : Prop :=
  ∀ (a b : ℂ) (ρ σ : Matrix (Fin d) (Fin d) ℂ),
    D (a • ρ + b • σ) = a • D ρ + b • D σ

/-- **Unitary equivariance.**  `D(U ρ U*) = U D(ρ) U*` for every "unitary"
    `U` (here characterised abstractly by `U * star U = 1`). -/
def IsUnitaryEquivariant (D : DensityFunctional d) : Prop :=
  ∀ (U : Matrix (Fin d) (Fin d) ℂ),
    U * (star U) = 1 →
    ∀ ρ, D (U * ρ * star U) = U * D ρ * star U

/-- **Step 1 (axiom) — Schur classification.**

    Any linear, unitary-equivariant density functional on
    `d × d` complex matrices (`d ≥ 2`) is of the Schur form
    `D = α · canonical + β · uniform` for some `α, β : ℝ`.

    *Proof outline (per GPT-5.5-pro recommendation):*
      1. Extend D to a complex-linear map T on all complex matrices.
      2. Diagonal unitaries ⇒ T preserves the matrix-unit basis E_ij.
      3. Permutation unitaries ⇒ T acts with one scalar on all off-
         diagonal E_ij.
      4. Hadamard 2-rotation ⇒ T acts with one scalar on diagonal
         differences E_ii − E_jj.
      5. T(I) is unitary-invariant ⇒ scalar multiple of I.
      Hence T(A) = α · A + β · trace(A) · I/d.
      Restrict to Hermitian sub-vector-space (real α, β).

    This is 2-5 weeks of Lean work per GPT estimate; axiomatized here
    at the interface layer. -/
axiom step1_schur_classification (d : ℕ) (hd : 1 < d)
    (D : DensityFunctional d)
    (h_lin : IsLinear D) (h_uniteq : IsUnitaryEquivariant D) :
    ∃ α β : ℝ, D = @schurForm d α β

/- ── Step 3 (axiomatized): tensor multiplicativity narrowing ─────── -/

/-- **Tensor multiplicativity** (locality analog): `D₂(ρ ⊗ σ) = D(ρ) ⊗ D(σ)` for all `ρ, σ`,
    with the Kronecker products reindexed `Fin d × Fin d ≃ Fin (d·d)` (`finProdFinEquiv`) so
    that `D₂ : DensityFunctional (d·d)` applies.  (Previously a vacuous `True` placeholder,
    which — combined with `step3` — was a soundness bug: it let `step3` fire on `(α,β)=(½,½)`
    and derive a false conclusion.  Now a genuine condition.) -/
def IsTensorMultiplicative {d : ℕ}
    (Dd : DensityFunctional d)
    (Dd2 : DensityFunctional (d * d)) : Prop :=
  ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ,
    Dd2 (Matrix.reindex finProdFinEquiv finProdFinEquiv (ρ ⊗ₖ σ))
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (Dd ρ ⊗ₖ Dd σ)

/-- **Step 3 (axiom) — Tensor multiplicativity narrowing.**

    If the Schur-form density functional `schurForm α β` (with `α + β = 1`)
    is tensor-multiplicative across pairs of state-spaces, then
    `(α, β) ∈ {(1, 0), (0, 1)}`.

    *Proof outline:* expand
        `schurForm α β (ρ ⊗ σ) = schurForm α β ρ ⊗ schurForm α β σ`
    and match the coefficients of `ρ⊗σ`, `ρ⊗I`, `I⊗σ`, `I⊗I`:
      - `ρ⊗σ`: α = α²  ⇒  α(1-α) = 0  ⇒  α ∈ {0, 1}
      - `ρ⊗I`: αβ = 0
      - `I⊗σ`: αβ = 0
      - `I⊗I`: β = β²  ⇒  β ∈ {0, 1}
    Combined with α + β = 1: `(α, β) ∈ {(1, 0), (0, 1)}`.

    **PROVED (2026-06), axiom-free** via GPT-5.5-pro's traceless-`Z` argument.  Take the
    traceless witness `Z = diag(1,−1)` (`single 0 0 1 − single 1 1 1`).  Since `tr Z = 0`,
    `schurForm α β Z = α·Z`.  Evaluating tensor multiplicativity at `(Z, Z)` on the diagonal
    entry indexed by `finProdFinEquiv (0,0)` — where `(Z ⊗ Z)` has value `1` and the
    uniform term drops out (`tr (Z ⊗ Z) = (tr Z)² = 0`) — gives `α = α²`, hence `α ∈ {0,1}`;
    combined with `α + β = 1` this yields `(α,β) ∈ {(1,0),(0,1)}`. -/
theorem step3_tensor_multiplicativity (d : ℕ) (hd : 1 < d) (α β : ℝ)
    (h_sum : α + β = 1)
    (h_tensor : IsTensorMultiplicative
                  (@schurForm d α β)
                  (@schurForm (d * d) α β)) :
    (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have h10 : (1 : Fin d) ≠ (0 : Fin d) := by
    apply Fin.ne_of_val_ne
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt hd]; exact one_ne_zero
  -- traceless witness `Z = diag(1, −1)`
  set Z : Matrix (Fin d) (Fin d) ℂ := single 0 0 1 - single 1 1 1 with hZ
  have hZ00 : Z 0 0 = 1 := by
    simp only [hZ, Matrix.sub_apply, Matrix.single_apply_same, Matrix.single_apply_of_ne,
      sub_zero, h10, false_and, and_false, not_false_eq_true]
  have hZtr : Z.trace = 0 := by
    rw [hZ, Matrix.trace_sub, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same, sub_self]
  have hsZ : schurForm α β Z = (α : ℂ) • Z := by simp [schurForm, hZtr]
  -- the tensor identity at `(Z, Z)`, with the Schur forms substituted on the right
  have h := h_tensor Z Z
  rw [hsZ] at h
  set e := (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)) with he
  -- the reindexed Kronecker product is traceless
  have hKtr : (Matrix.reindex e e (Z ⊗ₖ Z)).trace = 0 := by
    have hperm : (Matrix.reindex e e (Z ⊗ₖ Z)).trace = (Z ⊗ₖ Z).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [hperm, Matrix.trace_kronecker, hZtr, mul_zero]
  -- read off the diagonal entry indexed by `e (0,0)`
  have hee : e.symm (e (0, 0)) = (0, 0) := Equiv.symm_apply_apply e (0, 0)
  have key := congrFun (congrFun h (e (0, 0))) (e (0, 0))
  -- pass 1: unfold the Schur form, exposing the (still-reindexed) trace term
  simp only [schurForm, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul] at key
  rw [hKtr] at key
  -- pass 2: evaluate the surviving diagonal entries
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hee, Matrix.kronecker_apply,
    Matrix.smul_apply, hZ00, smul_eq_mul, zero_div, zero_mul, mul_zero, mul_one, add_zero] at key
  -- key : (α : ℂ) = (α : ℂ) * (α : ℂ)
  have hα : α = α * α := by exact_mod_cast key
  have hfac : α * (α - 1) = 0 := by rw [mul_sub, mul_one, ← hα, sub_self]
  have hcase : α = 0 ∨ α = 1 := by
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rcases hcase with h0 | h1
  · exact Or.inr ⟨h0, by linarith⟩
  · exact Or.inl ⟨h1, by linarith⟩

/- ── Step 4 (PROVED): non-degeneracy selection ──────────────────── -/

/-- **Non-degeneracy on a pure state.**  There exists a pure state
    P such that `D P ≠ uniformD d P` (= `(1/d) · I` for normalized
    pure states). -/
def IsNonDegenerate (D : DensityFunctional d) : Prop :=
  ∃ P : Matrix (Fin d) (Fin d) ℂ,
    Matrix.trace P = 1 ∧
    D P ≠ ((1 : ℂ) / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- **Step 4 (PROVED) — Non-degeneracy selects the canonical density.**

    If `schurForm α β` with `(α, β) ∈ {(1,0), (0,1)}` is non-degenerate
    on a pure state, then `(α, β) = (1, 0)`.

    Proof: if `(α, β) = (0, 1)`, then `schurForm 0 1 ρ = (trace ρ / d) · I`,
    so for any pure state P (trace 1), `schurForm 0 1 P = (1/d) · I`,
    contradicting non-degeneracy.  Hence `(α, β) ≠ (0, 1)`, so
    `(α, β) = (1, 0)`. -/
theorem step4_nondegeneracy
    {d : ℕ} (α β : ℝ)
    (h_case : (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1))
    (h_nondegen : IsNonDegenerate (@schurForm d α β)) :
    α = 1 ∧ β = 0 := by
  rcases h_case with ⟨hα, hβ⟩ | ⟨hα, hβ⟩
  · -- (α, β) = (1, 0): nothing to prove.
    exact ⟨hα, hβ⟩
  · -- (α, β) = (0, 1): contradict non-degeneracy.
    exfalso
    obtain ⟨P, hP_trace, hP_ne⟩ := h_nondegen
    apply hP_ne
    -- schurForm 0 1 P = (0:ℂ) • P + (1:ℂ) • ((trace P / d) • I)
    --                 = (trace P / d) • I = (1/d) • I.
    simp [schurForm, hα, hβ, hP_trace]

/- ── Combined: the four-step uniqueness theorem ─────────────────── -/

/-- **Goldstein-Struyve finite-dim uniqueness (PROVED, mod Steps 1 & 3).**

    A linear, unitary-equivariant, normalized, tensor-multiplicative,
    non-degenerate density functional on `d × d` matrices (with `d ≥ 2`)
    is the canonical density `D = canonicalD = id`.

    The proof composes the four sub-steps:
      Step 1 (Schur, axiom)               → D = schurForm α β
      Step 2 (Normalization, PROVED)      → α + β = 1
      Step 3 (Tensor-mult, axiom)         → (α,β) ∈ {(1,0), (0,1)}
      Step 4 (Non-degeneracy, PROVED)     → (α,β) = (1,0)
    Combined                              → D = canonicalD. -/
theorem goldstein_struyve_findim
    (d : ℕ) (hd : 1 < d)
    (D : DensityFunctional d)
    (h_lin : IsLinear D)
    (h_uniteq : IsUnitaryEquivariant D)
    (h_norm : IsNormalized D)
    (h_tensor : ∀ Dd2, IsTensorMultiplicative D Dd2)
    (h_nondegen : IsNonDegenerate D) :
    D = canonicalD := by
  -- Step 1: Schur classification.
  obtain ⟨α, β, h_schur⟩ := step1_schur_classification d hd D h_lin h_uniteq
  -- Substitute D = schurForm α β throughout.
  rw [h_schur]
  rw [h_schur] at h_norm h_tensor h_nondegen
  -- Step 2: Normalization ⇒ α + β = 1.
  have h_sum : α + β = 1 := step2_normalization (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hd)) α β h_norm
  -- Step 3: Tensor-mult ⇒ (α, β) ∈ {(1,0), (0,1)}.
  have h_case := step3_tensor_multiplicativity d hd α β h_sum
                   (h_tensor (@schurForm (d * d) α β))
  -- Step 4: Non-degeneracy ⇒ (α, β) = (1, 0).
  obtain ⟨hα, hβ⟩ := step4_nondegeneracy α β h_case h_nondegen
  -- Substitute to get schurForm 1 0 = canonicalD.
  rw [hα, hβ]
  -- schurForm 1 0 ρ = (1:ℂ) • ρ + (0:ℂ) • _ = ρ.
  funext ρ
  simp [schurForm, canonicalD]

end GoldsteinStruyveFinDim
end QIQTH
