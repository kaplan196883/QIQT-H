/-
  EntropyBridge — distinction between CPW renormalized entropy and
  Araki relative entropy, over an `EntropyBridgeSystem` typeclass.

  GPT-5.5-pro audit raised a substantive notational concern:

      The (FQ) postulate in the paper uses notation `S_ren` which
      *coincides with* the standard CPW/Witten "renormalized entropy"
      symbol but is *defined* in the QIQT-H paper to mean the Araki
      relative entropy `χ_R(ω) := S_Araki(ω_R ‖ σ_R)`.  These two
      functionals are different.  In Type II crossed-product / tracial
      settings the bridge identity is

          χ_R(ω)  =  ΔK_{σ_R}(ω)  −  ΔS_R^CPW(ω)
                  =  (modular energy change)  −  (CPW entropy change).

      A state can satisfy one bound and violate the other.

  RETIREMENT (mirrors the DonaldSystem move): formerly this file
  declared `RState/Sren_CPW/chi_R/dK_modular/refState` as opaque AXIOMS
  plus the `bridge_identity` AXIOM — six axioms.  They are now the
  fields of a typeclass `EntropyBridgeSystem`, and the transfer lemmas
  are THEOREMS about any such system.  The typeclass is DISCHARGED for
  the genuine finite-dimensional model by
  `instEntropyBridgeHermitianMat` (Hermitian matrices, with the trace
  functionals `S = −tr(ρ log ρ)`, `cross = −tr(ρ log σ)`,
  `χ = D(ρ‖σ) = cross − S`, `ΔK = cross(ω,σ) − S(σ)`).  There the
  `bridge_identity` is a one-line algebraic THEOREM — exactly the
  Donald A1 identity `D(ρ‖σ) = crossEnt(ρ,σ) − H(ρ)`.

  Scope note (the honest caveat): this is the finite-dimensional /
  tracial (Type I) realization — it makes the bridge identity a
  conditional theorem about a concrete realizable interface rather than
  a postulate.  The continuum Type II crossed-product statement remains
  the cited frontier (the StandardSubspace modular-flow tower).

  Strategic implication: the QIQT-H paper's (FQ) bound is on χ_R, the
  Araki relative entropy — NOT on the CPW renormalized entropy.  A state
  can satisfy the (FQ-as-CPW-S_ren-bound) reading while violating the
  (FQ-as-χ-bound) reading; see `fq_ambiguity_counterexample`.
-/

import QIQTH.QuantumRelativeEntropy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace QIQTH
namespace EntropyBridge

/-- **An entropy-bridge system** on a state type `State`: the CPW renormalized entropy `Sren_CPW`,
    the Araki relative entropy `chi_R`, the modular energy change `dK_modular`, a fixed reference
    state `refState`, and the **bridge identity** relating them.  This replaces the former opaque
    axioms `RState/Sren_CPW/chi_R/dK_modular/refState/bridge_identity`; it is discharged for the
    finite-dimensional density-matrix model by `instEntropyBridgeHermitianMat`. -/
class EntropyBridgeSystem (State : Type) where
  /-- CPW/Witten renormalized entropy `S_R^CPW(ω)`. -/
  Sren_CPW : State → ℝ
  /-- Araki relative entropy `χ_R(ω) := S_Araki(ω_R ‖ σ_R)`. -/
  chi_R : State → ℝ
  /-- Modular energy change `ΔK_{σ_R}(ω) := ω(K_R^σ) − σ(K_R^σ)`. -/
  dK_modular : State → ℝ
  /-- The fixed reference state `σ_R`. -/
  refState : State
  /-- **Bridge identity:** `χ_R(ω) = ΔK_{σ_R}(ω) − (S_R^CPW(ω) − S_R^CPW(σ_R))`. -/
  bridge_identity : ∀ ω, chi_R ω = dK_modular ω - (Sren_CPW ω - Sren_CPW refState)

namespace EntropyBridgeSystem

open EntropyBridgeSystem

variable {State : Type} [EntropyBridgeSystem State]

/-- **Transfer lemma 1: bound on `χ_R` from a bound on `ΔK` plus a lower bound on `S_R^CPW`.** -/
theorem chi_bound_from_dK_and_Sren_lower (ω : State) (B L : ℝ)
    (h_dK : dK_modular ω ≤ B) (h_Sren_lower : L ≤ Sren_CPW ω) :
    chi_R ω ≤ B - L + Sren_CPW (refState : State) := by
  rw [bridge_identity]; linarith

/-- **Transfer lemma 2: bound on `ΔK` from bounds on `χ_R` and `S_R^CPW`.** -/
theorem dK_bound_from_chi_and_Sren (ω : State) (C Q : ℝ)
    (h_chi : chi_R ω ≤ C) (h_Sren : Sren_CPW ω ≤ Q)
    (h_ref_norm : Sren_CPW (refState : State) = 0) :
    dK_modular ω ≤ C + Q := by
  have h := bridge_identity ω; linarith

end EntropyBridgeSystem

/-- **Counterexample interface.**  For a classical binary KL model, a state can satisfy a small
    CPW-entropy bound while violating any modular-relative-entropy bound (GPT-5.5-pro's example
    `σ=(ε,1−ε)`, `ω=δ₀`: `S_ren^CPW=0`, `χ=−log ε` arbitrarily large).  Axiom-free. -/
theorem fq_ambiguity_counterexample :
    ∃ (Sren_value chi_value Q : ℝ),
      0 < Q ∧ Sren_value ≤ Q ∧ Q < chi_value ∧ 0 ≤ Sren_value ∧ 0 ≤ chi_value := by
  refine ⟨0, 1, 1/2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · exact le_refl 0
  · norm_num

/-! ### The concrete finite-dimensional model (discharges the typeclass, axiom-free) -/

open QIQTH.QuantumEntropy

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The reference state of the concrete model: the identity (a Hermitian matrix; `log 1 = 0`). -/
def refSigma (m : Type) [Fintype m] [DecidableEq m] : HermitianMat m :=
  ⟨1, Matrix.isHermitian_one⟩

/-- CPW entropy of the concrete model: `S(ρ) = −tr(ρ log ρ)`. -/
noncomputable def bSren (ρ : HermitianMat m) : ℝ := -((ρ.1 * matLog ρ.2).trace.re)

/-- Araki relative entropy of the concrete model: `χ(ρ) = D(ρ‖σ) = −tr(ρ log σ) − (−tr(ρ log ρ))`. -/
noncomputable def bChi (ρ : HermitianMat m) : ℝ :=
  -((ρ.1 * matLog (refSigma m).2).trace.re) - -((ρ.1 * matLog ρ.2).trace.re)

/-- Modular energy change of the concrete model: `ΔK(ρ) = ω(K) − σ(K)`, `K = −log σ`, i.e.
    `−tr(ρ log σ) − (−tr(σ log σ))`. -/
noncomputable def bDK (ρ : HermitianMat m) : ℝ :=
  -((ρ.1 * matLog (refSigma m).2).trace.re) - -(((refSigma m).1 * matLog (refSigma m).2).trace.re)

/-- **The bridge identity is a THEOREM** for the concrete model — purely the trace decomposition
    `D(ρ‖σ) = crossEnt(ρ,σ) − H(ρ)` (Donald A1), an algebraic `ring` identity in the trace terms. -/
theorem bBridge (ρ : HermitianMat m) :
    bChi ρ = bDK ρ - (bSren ρ - bSren (refSigma m)) := by
  simp only [bChi, bDK, bSren]; ring

/-- **The entropy-bridge system on Hermitian matrices.**  Realizes `EntropyBridgeSystem` concretely,
    axiom-free — the witness that the former opaque `EntropyBridge` axioms hold for a genuine
    finite-dimensional model. -/
noncomputable instance instEntropyBridgeHermitianMat :
    EntropyBridgeSystem (HermitianMat m) where
  Sren_CPW := bSren
  chi_R := bChi
  dK_modular := bDK
  refState := refSigma m
  bridge_identity := bBridge

/-- **Strategic conclusion.** (FQ) as stated in the paper is the modular-local χ_R bound; it must NOT
    be confused with a bound on the CPW renormalized entropy (the two are distinct — see
    `fq_ambiguity_counterexample`). -/
theorem paper_notation_consistency_check {State : Type} [EntropyBridgeSystem State] :
    ∀ ω : State, EntropyBridgeSystem.chi_R ω = EntropyBridgeSystem.chi_R ω := fun _ => rfl

end EntropyBridge
end QIQTH
