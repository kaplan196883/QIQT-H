/-
  Worked instance:  applying QIQT-H Theorem 6 to the double-slit
  screen region (paper:  QIQT_Math.md  §9A).

  We construct a concrete `BranchData` for the screen region `R_S`
  at *exact saturation* of the holographic bound (I_0 = C(R_S),
  η_0 = η_def = 0), corresponding to the post-detection state on
  the screen where one spot has occurred.  Theorem 6 then collapses
  to a determinacy statement:  the effective number of spots is 1.

  This is a *worked example*, not a new theorem — it exercises
  `Theorem6.BranchData` + `effective_definiteness` on a physically
  meaningful instance.
-/

import QIQTH.Theorem6
import Mathlib.Tactic.Linarith

namespace QIQTH
namespace DoubleSlit

open Theorem6

/-- The single-spot branch decomposition for the double-slit screen
    region `R_S` at *exact saturation*:

      · `S      = I_0`    one branch, weight 1, modular cost `I_0`
      · `D_bar  = I_0`    the mixed state is the single-spot state
      · `I      = 0`      Holographic information vanishes
                          (one branch ⇒ no branch-discrimination cost)
      · `C      = I_0`    exact saturation of the holographic bound

    The Donald identity `S = D_bar + I` reduces to `I_0 = I_0 + 0`.

    `I_0` is left as a parameter because the paper calibrates it
    empirically against the Schrödinger-cat scale; the concrete
    numerical value for a macroscopic screen is `~10^68` nats. -/
def singleSpot (I_0 : ℝ) (hI_0_nonneg : 0 ≤ I_0) : BranchData where
  S       := I_0
  D_bar   := I_0
  I       := 0
  C       := I_0
  donald          := by linarith
  sum_le_capacity := le_refl _
  D_bar_nonneg    := hI_0_nonneg

/-- For the single-spot saturation decomposition, the Holographic
    mutual information vanishes. -/
theorem singleSpot_holevo_zero (I_0 : ℝ) (h : 0 ≤ I_0) :
    (singleSpot I_0 h).I = 0 := rfl

/-- The holographic-capacity bound for `singleSpot` is `0 ≤ I_0`,
    i.e. trivially saturated by the vanishing Holographic info. -/
theorem singleSpot_holevo_le_capacity (I_0 : ℝ) (h : 0 ≤ I_0) :
    (singleSpot I_0 h).I ≤ (singleSpot I_0 h).C :=
  BranchData.holevo_le_capacity _

/-- **Single-spot certainty.**

    Apply `effective_definiteness` to the single-spot saturation
    decomposition with `η_0 = η_def = 0` and Fano-baseline `I_0`
    equal to the BranchData's `I_0`.  The result `H_ε ≤ 0` says
    the effective number of spots is `exp(0) = 1` — Theorem 6
    yields *deterministic* single-spot outcome at exact saturation,
    as claimed in QIQT_Math §9A.4. -/
theorem singleSpot_certainty
    (I_0 : ℝ) (hI_0_nonneg : 0 ≤ I_0)
    (H_eps I_acc : ℝ)
    (acc_le  : I_acc ≤ (singleSpot I_0 hI_0_nonneg).I)
    (fano_le : H_eps ≤ I_acc + 0) :
    H_eps ≤ 0 := by
  have h := effective_definiteness
              (singleSpot I_0 hI_0_nonneg) H_eps I_acc I_0 0 0
              acc_le fano_le
              (by show (0 : ℝ) ≤ I_0 - I_0 + 0; linarith)
  -- h : H_eps ≤ (singleSpot _ _).C - I_0 + 0 + 0
  -- (singleSpot _ _).C is by definition I_0, so the bound = 0.
  have hC : (singleSpot I_0 hI_0_nonneg).C = I_0 := rfl
  linarith [h, hC]

/-
  Remark on the multi-branch / interference regime.
  -------------------------------------------------
  Before detection, the screen state is the formally interfering
  superposition  Σ_k c_k |x_k⟩|S_k⟩|E_k⟩.  The corresponding
  BranchData has Holographic info `I > 0` and Donald-bound
  `I ≤ C(R_S)` (via `BranchData.holevo_le_capacity`).  Calibrating
  `I_0` against the macroscopic record cost then yields the
  effective bound `H_ε ≤ C - I_0 + η_0 + η_def`, which is the
  general statement of Theorem 6.  The `singleSpot` instance above
  is the *exact-saturation limit* of that general bound — the
  regime where the effective multiplicity drops to 1.
-/

end DoubleSlit
end QIQTH
