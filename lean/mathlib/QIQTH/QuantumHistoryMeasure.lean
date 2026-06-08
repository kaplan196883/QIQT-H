/-
  XL-step Phase A, A0 + i.i.d. quantum instance: connect the matrix Born world (`bornW`) to the
  continuum history measure.  The single-measurement Born law is a genuine probability mass function
  `bornPMF`; for independently prepared trials this gives, via Mathlib `infinitePi`, a genuine
  σ-additive probability measure on the space of histories `ℕ → α` whose finite marginals are the
  i.i.d. Born product measures (`quantumHistoryMeasure`, `..._isProjectiveLimit`, `..._marginal`).

  HONEST SCOPE (per GPT-5.5-pro review): this is the PRODUCT / i.i.d. (independent-trial) case —
  the concrete quantum endpoint of the reachable part of XL Phase A, NOT the prize.  The correlated /
  entangled case (a single consistent family of COMPATIBLE measurements with non-product joint Born
  weights) is the finite-fiber Kolmogorov extension A2b — whose existence reduces to σ-subadditivity of
  `projectiveFamilyContent` (then `AddContent.measure`), the remaining XL Mathlib crux.

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import QIQTH.CoarseGrainNaturality
import QIQTH.FiniteMarginals
import QIQTH.BornTypicalityQuantum
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace QIQTH.QuantumHistoryMeasure

open MeasureTheory
open QIQTH.CoarseGrainNaturality
open scoped ComplexOrder

variable {d : ℕ} {α : Type*} [Fintype α]

/-- **The single-measurement Born law as a probability mass function.**  For a density matrix `ρ`
    (PSD, `tr ρ = 1`) and a POVM `{E a}` (PSD, `∑ E = 1`), the Born weights `a ↦ Re tr(ρ E_a)` form a
    PMF on the outcome space `α` — nonnegative (PSD) and summing to one (`tr ρ = 1`). -/
noncomputable def bornPMF (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1) :
    PMF α := by
  refine PMF.ofFintype (fun a => ENNReal.ofReal (bornW ρ (E a))) ?_
  have hnn : ∀ a, 0 ≤ bornW ρ (E a) := fun a => by
    have h := QIQTH.BornTypicalityQuantum.trace_mul_nonneg hρ (hE a)
    simpa [bornW] using (Complex.le_def.mp h).1
  have hs : ∑ a, bornW ρ (E a) = 1 := by
    unfold bornW
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hsum, Matrix.mul_one, htr,
      Complex.one_re]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnn a), hs, ENNReal.ofReal_one]

/-- `bornPMF` assigns each outcome its Born weight. -/
@[simp] theorem bornPMF_apply (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1) (a : α) :
    bornPMF ρ hρ htr E hE hsum a = ENNReal.ofReal (bornW ρ (E a)) := rfl

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **The i.i.d. quantum history measure.**  For independently prepared trials each measured by the
    POVM `{E a}` on the state `ρ`, the σ-additive probability measure on the history space `ℕ → α`
    whose marginal at every finite set of trials is the Born product measure.  Built from `bornPMF`
    via Mathlib's Kolmogorov extension `infinitePi`. -/
noncomputable def quantumHistoryMeasure (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => (bornPMF ρ hρ htr E hE hsum).toMeasure)

/-- The i.i.d. quantum history measure is a probability measure. -/
theorem quantumHistoryMeasure_isProbabilityMeasure (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) :
    IsProbabilityMeasure (quantumHistoryMeasure ρ hρ htr E hE hsum) := by
  unfold quantumHistoryMeasure; infer_instance

/-- **The history measure restricts to the i.i.d. Born product marginal at every finite set of
    trials** — "Born for every finite (decoherent, independent-trial) record partition," at the
    continuum.  Immediate from `infinitePi_map_restrict`. -/
theorem quantumHistoryMeasure_marginal (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (E : α → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) (J : Finset ℕ) :
    (quantumHistoryMeasure ρ hρ htr E hE hsum).map J.restrict
      = Measure.pi (fun _ : J => (bornPMF ρ hρ htr E hE hsum).toMeasure) :=
  Measure.infinitePi_map_restrict _

end QIQTH.QuantumHistoryMeasure
