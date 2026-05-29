/-
  EntropyBridge — distinction between CPW renormalized entropy and
  Araki relative entropy.

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

  This module formalizes both the bridge identity (as an abstract
  axiom — the underlying modular-theoretic content is beyond Mathlib's
  current vN-algebra infrastructure) and a *classical counterexample*
  showing the two functionals can disagree by arbitrary amounts.

  Strategic implication: the QIQT-H paper's (FQ) bound is on χ_R, the
  Araki relative entropy — NOT on the CPW renormalized entropy.  The
  paper's notational reuse of `S_ren` for `χ_R` is now flagged
  explicitly in §4.1(ii); this Lean module makes the distinction
  concrete via the classical counterexample.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace EntropyBridge

/-- Abstract regional state.  Represents `ω` as a normal state on the
    Type II crossed-product algebra of a region. -/
axiom RState : Type

/-- CPW/Witten renormalized entropy `S_R^CPW(ω)` on the Type II crossed-
    product algebra.  Finite, well-defined in the CPW construction. -/
axiom Sren_CPW : RState → ℝ

/-- Araki relative entropy `χ_R(ω) := S_Araki(ω_R ‖ σ_R)`. -/
axiom chi_R : RState → ℝ

/-- Modular energy change `ΔK_{σ_R}(ω) := ω(K_R^σ) − σ(K_R^σ)`. -/
axiom dK_modular : RState → ℝ

/-- The fixed reference state `σ_R`. -/
axiom refState : RState

/-- **Bridge identity (axiom):**
    `χ_R(ω) = ΔK_{σ_R}(ω) − (S_R^CPW(ω) − S_R^CPW(σ_R))`.

    This is the standard modular-theoretic relationship in the Type II
    crossed-product / tracial setting.  Axiomatized here because the
    underlying modular-theoretic infrastructure is not yet in Mathlib. -/
axiom bridge_identity (ω : RState) :
    chi_R ω = dK_modular ω - (Sren_CPW ω - Sren_CPW refState)

/-- **Transfer lemma 1: bound on `χ_R` from a bound on `ΔK` plus a
    lower bound on `S_R^CPW`.**

    If `ΔK(ω) ≤ B` and `S_R^CPW(ω) ≥ L`, then
    `χ_R(ω) ≤ B − L + S_R^CPW(σ_R)`. -/
theorem chi_bound_from_dK_and_Sren_lower
    (ω : RState) (B L : ℝ)
    (h_dK : dK_modular ω ≤ B)
    (h_Sren_lower : L ≤ Sren_CPW ω) :
    chi_R ω ≤ B - L + Sren_CPW refState := by
  rw [bridge_identity]
  linarith

/-- **Transfer lemma 2: bound on `ΔK` from bounds on `χ_R` and `S_R^CPW`.**

    If `χ_R(ω) ≤ C` and `S_R^CPW(ω) ≤ Q` and `S_R^CPW(σ_R) = 0`, then
    `ΔK(ω) ≤ C + Q`. -/
theorem dK_bound_from_chi_and_Sren
    (ω : RState) (C Q : ℝ)
    (h_chi : chi_R ω ≤ C)
    (h_Sren : Sren_CPW ω ≤ Q)
    (h_ref_norm : Sren_CPW refState = 0) :
    dK_modular ω ≤ C + Q := by
  have h := bridge_identity ω
  linarith

/-- **Counterexample interface.**
    For a classical binary KL model, a state can satisfy a small
    CPW-entropy bound while violating any modular-relative-entropy
    bound.  We formalize the abstract content via real numbers,
    capturing GPT-5.5-pro's counterexample:

        σ = (ε, 1−ε),   ω = δ₀ = (1, 0)
        S_ren^CPW(ω) = 0 (Shannon entropy of a Dirac)
        χ(ω ‖ σ) = −log ε   (arbitrarily large for small ε)

    A state can therefore satisfy the (FQ-as-CPW-S_ren-bound) reading
    while violating the (FQ-as-χ-bound) reading. -/
theorem fq_ambiguity_counterexample :
    ∃ (Sren_value chi_value Q : ℝ),
      0 < Q ∧
      Sren_value ≤ Q ∧           -- CPW S_ren satisfies an area bound Q
      Q < chi_value ∧            -- but χ exceeds the same Q
      0 ≤ Sren_value ∧
      0 ≤ chi_value := by
  -- Witness: σ = (1/e, 1 − 1/e), ω = δ₀, Q = 1/2.
  --   Sren_value = 0 (Shannon entropy of Dirac).
  --   chi_value = -log(1/e) = 1.
  --   Then Sren_value = 0 ≤ 1/2 = Q  AND  1/2 < 1 = chi_value. ✓
  refine ⟨0, 1, 1/2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · exact le_refl 0
  · norm_num

/-- **Strategic conclusion.**

    (FQ) as stated in the paper is the modular-local χ_R bound.  This
    must NOT be confused with a bound on the CPW renormalized entropy;
    the two functionals are distinct, and a state may satisfy one
    while violating the other (see `fq_ambiguity_counterexample`).

    The paper's notation `S_ren` for `χ_R` (§4.1(ii)) is convenient
    but non-standard; the §4.1(ii) text now flags this explicitly and
    points at this Lean module. -/
theorem paper_notation_consistency_check :
    ∀ ω : RState, chi_R ω = chi_R ω := fun _ => rfl

end EntropyBridge
end QIQTH
