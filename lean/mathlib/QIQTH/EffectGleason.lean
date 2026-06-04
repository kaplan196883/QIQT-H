/-
# QIQT-H: finite-dimensional Effect (POVM) Gleason — Stage 1 / step G1

Target (`GLEASON_SCOPE.md`): the Busch / Caves–Fuchs–Manne–Renes finite-dimensional
effect-Gleason theorem — a normalized, nonnegative, (coexistent-)additive functional on
effects `0 ≤ E ≤ 1` is `μ E = tr(ρ E)` for a unique density matrix `ρ`.  This discharges
the finite-dim case of `TypicalityMackeyGleason.mackey_gleason_to_trace_density`, makes the
`GoldsteinStruyveFinDim` Born-uniqueness axioms retirable, and completes the Stage-1
"minimal breakthrough" of `PRIZE_ROADMAP.md` by discharging the `hsupp` hypothesis of
`GleasonSelector.born_is_forced` from first principles.

This installment lands **step G1's foundation**: the effect predicate, effect closure
(`0`, `1`, scaling, subtraction), `μ 0 = 0`, **monotonicity**, and the
scaling-additivity that drives the homogeneity argument.  The remaining G1 core (additive +
bounded ⇒ ℝ-homogeneous, via the Cauchy-on-`[0,1]` squeeze) and steps G2–G4 follow.

Axiom-free (standard three only). -/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace QIQTH.EffectGleason

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-- An **effect** is a positive-semidefinite matrix `E` with `1 - E` also PSD, i.e.
    `0 ≤ E ≤ 1` in the Löwner order — the yes-part of a POVM. -/
def IsEffect (E : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

theorem isEffect_zero : IsEffect (0 : Matrix (Fin d) (Fin d) ℂ) :=
  ⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one⟩

theorem isEffect_one : IsEffect (1 : Matrix (Fin d) (Fin d) ℂ) :=
  ⟨Matrix.PosSemidef.one, by simpa using Matrix.PosSemidef.zero⟩

/-- Effects are closed under scaling by `t ∈ [0,1]`:  `1 - t•E = (1-t)•1 + t•(1-E)` is a
    sum of PSD matrices. -/
theorem isEffect_smul {E : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : IsEffect (t • E) := by
  refine ⟨hE.1.smul h0, ?_⟩
  have hsplit : (1 : Matrix (Fin d) (Fin d) ℂ) - t • E
      = (1 - t) • (1 : Matrix (Fin d) (Fin d) ℂ) + t • (1 - E) := by
    rw [smul_sub]; module
  rw [hsplit]
  exact (Matrix.PosSemidef.one.smul (by linarith : (0:ℝ) ≤ 1 - t)).add (hE.2.smul h0)

/-- If `E ≤ F` (i.e. `F - E` is PSD) with both effects, then `F - E` is an effect:
    `1 - (F - E) = (1 - F) + E` is PSD. -/
theorem isEffect_sub {E F : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) (hF : IsEffect F)
    (hle : (F - E).PosSemidef) : IsEffect (F - E) := by
  refine ⟨hle, ?_⟩
  have : (1 : Matrix (Fin d) (Fin d) ℂ) - (F - E) = (1 - F) + E := by abel
  rw [this]
  exact hF.2.add hE.1

/-- A **finite effect measure** (generalized probability measure on effects): normalized,
    nonnegative, and additive on coexistent effects.  This is the hypothesis of
    effect-Gleason; the theorem (future installments) is that `μ E = tr(ρ E)`. -/
structure EffectMeasure (d : ℕ) where
  μ : Matrix (Fin d) (Fin d) ℂ → ℝ
  normalized : μ 1 = 1
  nonneg : ∀ E, IsEffect E → 0 ≤ μ E
  additive : ∀ E F, IsEffect E → IsEffect F → IsEffect (E + F) → μ (E + F) = μ E + μ F

namespace EffectMeasure

variable (m : EffectMeasure d)

/-- `μ 0 = 0` — from `μ 1 = μ(1 + 0) = μ 1 + μ 0`. -/
theorem map_zero : m.μ 0 = 0 := by
  have h := m.additive 1 0 isEffect_one isEffect_zero (by rw [add_zero]; exact isEffect_one)
  rw [add_zero] at h
  have := m.normalized
  linarith

/-- **Monotonicity.**  If `E ≤ F` (`F - E` PSD) with both effects, then `μ E ≤ μ F`.
    From `μ F = μ E + μ(F - E)` and `μ(F - E) ≥ 0`. -/
theorem mono {E F : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) (hF : IsEffect F)
    (hle : (F - E).PosSemidef) : m.μ E ≤ m.μ F := by
  have hsub : IsEffect (F - E) := isEffect_sub hE hF hle
  have hEF : E + (F - E) = F := by abel
  have hadd := m.additive E (F - E) hE hsub (by rw [hEF]; exact hF)
  rw [hEF] at hadd
  have := m.nonneg (F - E) hsub
  linarith

/-- **Scaling additivity.**  For `s, s' ≥ 0` with `s•E`, `s'•E`, `(s+s')•E` all effects,
    `μ((s+s')•E) = μ(s•E) + μ(s'•E)`.  The seed of the homogeneity argument: the map
    `s ↦ μ(s•E)` is additive on `[0,1]` (next: Cauchy ⇒ `μ(s•E) = s·μ E`). -/
theorem map_smul_add {E : Matrix (Fin d) (Fin d) ℂ} {s s' : ℝ}
    (hsE : IsEffect (s • E)) (hs'E : IsEffect (s' • E)) (hsum : IsEffect ((s + s') • E)) :
    m.μ ((s + s') • E) = m.μ (s • E) + m.μ (s' • E) := by
  have hsplit : (s + s') • E = s • E + s' • E := by module
  rw [hsplit] at hsum ⊢
  exact m.additive (s • E) (s' • E) hsE hs'E hsum

end EffectMeasure

end QIQTH.EffectGleason
