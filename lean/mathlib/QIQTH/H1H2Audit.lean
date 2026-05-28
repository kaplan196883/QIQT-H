/-
  H1/H2 Independence Audit — central QIQT-H structural audit.

  Question (proposed by GPT-5.5-pro audit):
    Does (H1) χ_R(ω_{k,R}) ≤ C(R)  (branchwise admissibility, framework
    premise) plus standard relative-entropy properties (Donald's identity,
    Klein's positivity, DPI) imply (H2) χ_R(ω̄_R) ≥ I_0  (record-
    instantiation cost, framework's central non-AQFT postulate)?

  Answer: **No.** (H2) is genuinely independent of the structural axioms.

  Concrete countermodel: classical binary reference σ = (1/2, 1/2) and
  perfect record state ρ = δ₀ = (1, 0). Then

      KL(ρ ‖ σ)  =  −log σ(0)  =  log 2  ≈  0.693 nats.

  This model satisfies:
    Klein:  log 2 ≥ 0                                         ✓
    H1:     log 2 ≤ log 2  (capacity C = log 2)                ✓
    Donald, DPI:  hold for classical KL                       ✓
  but VIOLATES:
    H2:     log 2 < 1  (threshold I_0 = 1)                    ✗
                (since log 2 < 1 in nats, equivalently 2 < e)

  Sharp replacement theorem (also formalized below):
    For perfect-record states with σ(E_record) = σ₀, (H2) `KL ≥ I_0` is
    *exactly equivalent* to the reference-weight bound

        σ₀  ≤  exp(−I_0).

    This is the load-bearing content of (H2): macroscopic records must
    occupy low reference-weight sectors. A future paper that wants to
    derive (H2) from first principles must derive that bound from
    modular/holographic physics — Donald's identity will not.

  Strategic implication: (H2) is independent and load-bearing — paper's
  framing as a primitive empirical postulate is rigorous. But the paper
  can now sharpen the statement: replace "instantiating a record costs
  ≥ I_0 modular bits" (opaque) with "σ_R(E_record) ≤ exp(−I_0) on
  macroscopic pointer sectors" (precise reference-weight condition).
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace H1H2Audit

/-- KL divergence for a perfect-record state ρ = δ₀ against reference σ.
    Reduces to `−log σ(0)` (the ρ(1)·log(0/σ(1)) term is 0 by convention). -/
noncomputable def perfectRecordKL (σ_0 : ℝ) : ℝ := -Real.log σ_0

/-- Klein positivity for the perfect-record case:  −log σ₀ ≥ 0 when σ₀ ≤ 1. -/
theorem perfectRecordKL_nonneg
    (σ_0 : ℝ) (h_pos : 0 < σ_0) (h_le : σ_0 ≤ 1) :
    0 ≤ perfectRecordKL σ_0 := by
  unfold perfectRecordKL
  rw [neg_nonneg]
  exact Real.log_nonpos h_pos.le h_le

/-- Auxiliary:  log 2 < 1 (in nats), since 2 < e. -/
private theorem log_two_lt_one : Real.log 2 < 1 := by
  have h_e_gt_two : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1:ℝ) ≠ 0)
    linarith
  have h := Real.log_lt_log (by norm_num : (0:ℝ) < 2) h_e_gt_two
  rwa [Real.log_exp] at h

/-- **H1 ⇒/ H2:  explicit independence countermodel.**

    There exists a classical KL configuration where Klein, H1, Donald
    and DPI all hold (the latter two are intrinsic to classical KL) but
    H2 fails:  KL = log 2 < 1 = I_0.

    The witness:  σ = (1/2, 1/2), ρ = δ₀, C = log 2, I_0 = 1. -/
theorem H1_does_not_imply_H2 :
    ∃ (kl C I_0 : ℝ),
      0 < I_0 ∧
      0 ≤ kl ∧                       -- Klein positivity
      kl ≤ C ∧                       -- (H1)
      ¬ (I_0 ≤ kl) := by             -- (H2) fails
  refine ⟨perfectRecordKL (1/2), Real.log 2, 1, ?_, ?_, ?_, ?_⟩
  · norm_num
  · exact perfectRecordKL_nonneg (1/2) (by norm_num) (by norm_num)
  · unfold perfectRecordKL
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    linarith
  · unfold perfectRecordKL
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    -- Goal:  ¬ (1 ≤ -(-Real.log 2)) i.e. ¬ (1 ≤ Real.log 2)
    push_neg
    linarith [log_two_lt_one]

/-- **Sharp replacement theorem.**

    For perfect-record states, (H2) — KL(ρ ‖ σ) ≥ I_0 — is **exactly
    equivalent** to the reference-weight bound  σ₀ ≤ exp(−I_0).

    This identifies the load-bearing physical content of (H2):
    macroscopic record sectors must have low reference weight. -/
theorem H2_iff_reference_weight
    (σ_0 I_0 : ℝ) (h_pos : 0 < σ_0) :
    I_0 ≤ perfectRecordKL σ_0  ↔  σ_0 ≤ Real.exp (-I_0) := by
  unfold perfectRecordKL
  constructor
  · intro h
    -- I_0 ≤ -log σ₀  ⇒  log σ₀ ≤ -I_0  ⇒  σ₀ ≤ exp(-I_0)
    have h1 : Real.log σ_0 ≤ -I_0 := by linarith
    calc σ_0 = Real.exp (Real.log σ_0) := (Real.exp_log h_pos).symm
      _ ≤ Real.exp (-I_0)              := Real.exp_le_exp.mpr h1
  · intro h
    -- σ₀ ≤ exp(-I_0)  ⇒  log σ₀ ≤ -I_0  ⇒  I_0 ≤ -log σ₀
    have h1 : Real.log σ_0 ≤ Real.log (Real.exp (-I_0)) :=
      Real.log_le_log h_pos h
    rw [Real.log_exp] at h1
    linarith

/-- **Refinement of (H2) in the framework.**

    Replace the opaque axiom
        (H2):  χ_R(ω̄_R) ≥ I_0 − η_0    [record instantiation costs ≥ I_0]
    with the equivalent precise condition (under the perfect-record
    idealization δ₀):
        σ_R(E_record)  ≤  exp(−I_0 + η_0).

    Future first-principles derivations of (H2) must produce this
    bound from modular/holographic structure on macroscopic pointer
    sectors. -/
theorem H2_sharpening_summary
    (σ_R_E I_0 η_0 : ℝ) (h_pos : 0 < σ_R_E) :
    (I_0 - η_0 ≤ perfectRecordKL σ_R_E)  ↔
    (σ_R_E ≤ Real.exp (-(I_0 - η_0))) :=
  H2_iff_reference_weight σ_R_E (I_0 - η_0) h_pos

end H1H2Audit
end QIQTH
