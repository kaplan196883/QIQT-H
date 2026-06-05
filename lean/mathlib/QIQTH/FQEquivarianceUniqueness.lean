/-
  Sub-theorem C — Goldstein-Struyve uniqueness for QIQT-H.

  GPT-5.5-pro fifth audit identified this as the third sub-theorem
  needed for the Canonical IC Measure Principle (Open Problem 1).

  **Statement (informal):**
    Among trace-density typicality structures `μ_ρ(B) = τ_R(D_ρ · P_B)`,
    locality + naturality + FQ-equivariance uniquely force the density
    functional to be the canonical state-density `D_ρ = ρ`.

  **Precedent:** Goldstein-Struyve (J. Stat. Phys. 128, 1197, 2007)
  prove the analogous result in Bohmian mechanics for the
  configuration-space density `p^ψ(q)`.

  **CONSOLIDATION PASS (2026-05):**

  This module previously duplicated Steps 1-4 + `combine_canonical` as
  five independent abstract axioms — separate from the concrete versions
  of those same steps in `GoldsteinStruyveFinDim`.  The duplication
  added 5 redundant axioms and 7 opaque type/value declarations to the
  axiom audit without adding mathematical content.

  Consolidated structure:

    • The abstract types (`QState`, `Density`, `DensityFunctional`,
      `canonicalDensity`, `uniformDensity`, `combine`) are REPLACED with
      dimension-parameterised `abbrev`s pointing to the concrete
      `Matrix (Fin d) (Fin d) ℂ` infrastructure in
      `GoldsteinStruyveFinDim`.

    • The abstract property predicates (`IsLinear`, `IsUnitaryEquivariant`,
      `IsNormalized`, `IsTensorMultiplicative`, `IsNonDegenerate`,
      `IsFQEquivariant`) are REPLACED with `def`s pointing to the
      concrete property predicates from `GoldsteinStruyveFinDim`.

    • The five sub-step axioms (`step1_schur_classification`,
      `step2_normalization_constraint`,
      `step3_tensor_multiplicativity_narrowing`,
      `step4_nondegeneracy_selection`, `combine_canonical`) are
      ELIMINATED — they were duplicates of the concrete versions
      proved or axiomatized in `GoldsteinStruyveFinDim`.

    • The combined theorem `canonical_ic_measure_principle` is now
      a thin wrapper delegating to the concrete proved theorem
      `GoldsteinStruyveFinDim.goldstein_struyve_findim`.

  *Net axiom savings:* 12 axiom-objects removed from
  `FQEquivarianceUniqueness`'s namespace.  Sub-theorem C now depends
  only on the two genuinely-open Goldstein-Struyve axioms (Step 1
  Schur classification and Step 3 tensor multiplicativity) from the
  concrete module — both of which are decomposed further into named
  sub-lemmas in `GoldsteinStruyveStep1` / `GoldsteinStruyveStep3` /
  `GoldsteinStruyveKronecker`.
-/

import QIQTH.GoldsteinStruyveFinDim
import QIQTH.GoldsteinStruyveStep1

namespace QIQTH
namespace FQEquivarianceUniqueness

/- ── Abstract interface — now concrete via abbreviations ────────── -/

/-- A QIQT-H density functional on dimension-`d` matrices.  Concretely
    realised as `Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ`. -/
abbrev DensityFunctional (d : ℕ) : Type :=
  GoldsteinStruyveFinDim.DensityFunctional d

/-- The canonical density functional `D_ρ = ρ`. -/
abbrev canonicalDensity (d : ℕ) : DensityFunctional d :=
  @GoldsteinStruyveFinDim.canonicalD d

/-- The "uniform" density functional `D_ρ = tr(ρ) · I/d`. -/
noncomputable abbrev uniformDensity (d : ℕ) : DensityFunctional d :=
  GoldsteinStruyveFinDim.uniformD d

/- ── Properties of density functionals (concrete) ────────────────── -/

/-- **Linearity.** -/
def IsLinear {d : ℕ} (D : DensityFunctional d) : Prop :=
  GoldsteinStruyveFinDim.IsLinear D

/-- **Unitary equivariance.** -/
def IsUnitaryEquivariant {d : ℕ} (D : DensityFunctional d) : Prop :=
  GoldsteinStruyveFinDim.IsUnitaryEquivariant D

/-- **Hermiticity preservation** (reality condition; required for soundness
    of Step 1 — see `GoldsteinStruyveFinDim.step1_schur_classification`). -/
def IsHermitianPreserving {d : ℕ} (D : DensityFunctional d) : Prop :=
  GoldsteinStruyveFinDim.IsHermitianPreserving D

/-- **Trace normalization.** -/
def IsNormalized {d : ℕ} (D : DensityFunctional d) : Prop :=
  GoldsteinStruyveFinDim.IsNormalized D

/-- **Tensor multiplicativity (locality analog).**  Genuine factorization of a
    *specific* composite functional `Dd2` through `D`: `Dd2(ρ⊗σ) = D(ρ)⊗D(σ)`.
    (Previously `∀ Dd2, …`, which was UNSATISFIABLE — making the flagship theorem
    vacuous; fixed 2026-06.) -/
def IsTensorMultiplicative {d : ℕ} (D : DensityFunctional d)
    (Dd2 : DensityFunctional (d * d)) : Prop :=
  GoldsteinStruyveFinDim.IsTensorMultiplicative D Dd2

/-- **Non-degeneracy on pure states.** -/
def IsNonDegenerate {d : ℕ} (D : DensityFunctional d) : Prop :=
  GoldsteinStruyveFinDim.IsNonDegenerate D

/-- **FQ-equivariance.**  `D` is preserved under (FQ)-restricted
    Hamiltonian flow.  Abstract placeholder (analogous to the
    QIQT-H-side dynamical commitment, complementary to the
    measure-theoretic content). -/
def IsFQEquivariant {d : ℕ} (_D : DensityFunctional d) : Prop :=
  True

/- ── Combined: the QIQT-H Goldstein-Struyve uniqueness theorem ─── -/

/-- **Sub-theorem C — Goldstein-Struyve QIQT-H uniqueness (PROVED via
    delegation to the concrete `GoldsteinStruyveFinDim` proof).**

    A density functional satisfying linearity + unitary-equivariance +
    normalization + tensor-multiplicativity + non-degeneracy is the
    canonical density.

    *Where the content lives (all four steps now PROVED, axiom-free):*
      Step 1 (Schur classification) — PROVED in `GoldsteinStruyveStep1.schur_classification_real`
      Step 2 (Normalization)        — PROVED in `GoldsteinStruyveFinDim`
      Step 3 (Tensor multiplicativity) — PROVED in `GoldsteinStruyveFinDim.step3_tensor_narrowing`
      Step 4 (Non-degeneracy)       — PROVED in `GoldsteinStruyveFinDim`

    The tensor hypothesis is the GENUINE factorization `Dd2(ρ⊗σ) = D(ρ)⊗D(σ)` for a concrete
    composite functional `Dd2` (also classified by Step 1).  The earlier `∀ Dd2, …` form was
    unsatisfiable, rendering this theorem vacuous; that is fixed. -/
theorem goldstein_struyve_qiqth_proved
    {d : ℕ} (hd : 1 < d)
    (D : DensityFunctional d) (Dd2 : DensityFunctional (d * d))
    (h_linear : IsLinear D) (h_uniteq : IsUnitaryEquivariant D)
    (h_herm : IsHermitianPreserving D)
    (h_linear2 : IsLinear Dd2) (h_uniteq2 : IsUnitaryEquivariant Dd2)
    (h_herm2 : IsHermitianPreserving Dd2)
    (h_norm : IsNormalized D)
    (h_tensor : IsTensorMultiplicative D Dd2)
    (h_nondegen : IsNonDegenerate D) :
    D = canonicalDensity d :=
  GoldsteinStruyveFinDim.goldstein_struyve_findim d hd D Dd2
    (GoldsteinStruyveStep1.schur_classification_real hd D h_linear h_uniteq h_herm)
    (GoldsteinStruyveStep1.schur_classification_real
      (by nlinarith [hd] : 1 < d * d) Dd2 h_linear2 h_uniteq2 h_herm2)
    h_norm h_tensor h_nondegen

/-- **The QIQT-H Canonical IC Measure Principle (final form).**

    Combined with sub-theorem A (Mackey-Gleason ⇒ trace-density form,
    `TypicalityMackeyGleason.qiqth_typicality_mackey_gleason`) and the
    two acknowledged interface axioms in `GoldsteinStruyveFinDim`
    (Step 1 Schur classification and Step 3 tensor multiplicativity):
    the canonical IC measure on QIQT-H's IC space is uniquely the
    trace-density measure `μ_ρ(B) = τ_R(ρ · P_B)`.

    *Dependency (2026-06):* this theorem is now **axiom-free** (only the standard
    `propext`/`Classical.choice`/`Quot.sound`).  Steps 1 and 3 — formerly interface axioms —
    are fully proved; the previous duplicate sub-axioms (5 axioms + 7 opaque types) were
    eliminated earlier.  The hypotheses are jointly satisfiable (the identity is a witness),
    so the statement is non-vacuous; see the regression suite `GoldsteinStruyveModels`. -/
theorem canonical_ic_measure_principle
    {d : ℕ} (hd : 1 < d)
    (D : DensityFunctional d) (Dd2 : DensityFunctional (d * d))
    (h_linear : IsLinear D) (h_uniteq : IsUnitaryEquivariant D)
    (h_herm : IsHermitianPreserving D)
    (h_linear2 : IsLinear Dd2) (h_uniteq2 : IsUnitaryEquivariant Dd2)
    (h_herm2 : IsHermitianPreserving Dd2)
    (h_norm : IsNormalized D)
    (h_tensor : IsTensorMultiplicative D Dd2)
    (h_nondegen : IsNonDegenerate D) :
    D = canonicalDensity d :=
  goldstein_struyve_qiqth_proved hd D Dd2 h_linear h_uniteq h_herm
    h_linear2 h_uniteq2 h_herm2 h_norm h_tensor h_nondegen

/-- **Uniqueness corollary.**  Two density functionals each satisfying
    the five properties must agree (both equal the canonical density). -/
theorem qiqth_typicality_uniqueness
    {d : ℕ} (hd : 1 < d)
    (D₁ D₂ : DensityFunctional d) (Dd2₁ Dd2₂ : DensityFunctional (d * d))
    (h₁_linear : IsLinear D₁) (h₂_linear : IsLinear D₂)
    (h₁_uniteq : IsUnitaryEquivariant D₁) (h₂_uniteq : IsUnitaryEquivariant D₂)
    (h₁_herm : IsHermitianPreserving D₁) (h₂_herm : IsHermitianPreserving D₂)
    (h₁_linear2 : IsLinear Dd2₁) (h₂_linear2 : IsLinear Dd2₂)
    (h₁_uniteq2 : IsUnitaryEquivariant Dd2₁) (h₂_uniteq2 : IsUnitaryEquivariant Dd2₂)
    (h₁_herm2 : IsHermitianPreserving Dd2₁) (h₂_herm2 : IsHermitianPreserving Dd2₂)
    (h₁_norm : IsNormalized D₁) (h₂_norm : IsNormalized D₂)
    (h₁_tensor : IsTensorMultiplicative D₁ Dd2₁) (h₂_tensor : IsTensorMultiplicative D₂ Dd2₂)
    (h₁_nondegen : IsNonDegenerate D₁) (h₂_nondegen : IsNonDegenerate D₂) :
    D₁ = D₂ := by
  rw [goldstein_struyve_qiqth_proved hd D₁ Dd2₁ h₁_linear h₁_uniteq h₁_herm
        h₁_linear2 h₁_uniteq2 h₁_herm2 h₁_norm h₁_tensor h₁_nondegen]
  rw [goldstein_struyve_qiqth_proved hd D₂ Dd2₂ h₂_linear h₂_uniteq h₂_herm
        h₂_linear2 h₂_uniteq2 h₂_herm2 h₂_norm h₂_tensor h₂_nondegen]

end FQEquivarianceUniqueness
end QIQTH
