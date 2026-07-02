/-
  E5 (MICROTHEORY_EARNS_GRAVITY_PLAN.md) — the Deser rung: the graviton sources ITSELF consistently (2nd order).

  Deser's bootstrap (1970): a massless spin-2 field coupled to its own stress tensor iterates to full GR. This
  module lands the FIRST rung in the plane-wave symbol calculus: the graviton's own (Isaacson-form, TT-gauge)
  stress symbol for a mode `(k, e)` is
      T^{μν}_GW = k^μ k^ν · ⟨e,e⟩_η        (radiation form: null-aligned, amplitude = e^{αβ}e_{αβ}),
  and the three consistency facts that make second-order self-sourcing WORK:
  • `gravStress_symm` — symmetric (a legitimate B1 source);
  • `gravStress_conserved` — ON-SHELL (null `k`, i.e. the graviton's own masslessness) the self-stress is
    conserved, `k_μ T^{μν}_GW = 0` — exactly the condition B1 proved equivalent to gauge invariance;
  • `deser_selfcoupling_consistent` — therefore the coupling `∫ h·T_GW` of the graviton TO ITS OWN STRESS is
    invariant under every linearized diffeomorphism: the second-order self-interaction is gauge-consistent.
  Plus `gravStress_traceless` (the on-shell radiation stress is η-traceless). The bootstrap's first order: the
  massless spin-2 field CAN eat its own stress-energy — B2's universality already forces that it MUST.

  ⚠ Honest labels: the FIRST order of the bootstrap only (second order in `h`); the full iteration to nonlinear
  GR (and its quantum non-renormalizability) is not built; plane-wave symbol level; free, flat. NOT QG.
-/
import Mathlib
import QIQTH.MatterCoupling

namespace QIQTH.EarnGravity

open QIQTH.GravDyn QIQTH.LinEinstein QIQTH.MatterCoupling

/-- The η-contracted amplitude `⟨e,e⟩_η = e^{αβ}e_{αβ}` of a polarization symbol. -/
def gravAmp (e : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ α, ∑ β, raiseSign α * raiseSign β * e α β * e α β

/-- **The graviton's own stress symbol** (Isaacson/radiation form, up indices):
    `T^{μν}_GW = k^μ k^ν · ⟨e,e⟩_η`. -/
noncomputable def gravStress (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => raiseIdx k μ * raiseIdx k ν * gravAmp e

/-- The self-stress is symmetric — a legitimate B1 source. -/
theorem gravStress_symm (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) :
    (gravStress k e).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  rw [Matrix.transpose_apply]
  simp only [gravStress, Matrix.of_apply]
  ring

/-- **On-shell conservation**: for a null mode (`k² = 0` — the graviton's own masslessness), the self-stress is
    conserved, `k_μ T^{μν}_GW = 0`. Masslessness ⟹ conservation of the graviton's own energy flux. -/
theorem gravStress_conserved (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hnull : minkQuad k = 0) (ν : Fin 4) : divT k (gravStress k e) ν = 0 := by
  have h0 : raiseIdx k 0 = -(k 0) := rfl
  have h1 : raiseIdx k 1 = k 1 := rfl
  have h2 : raiseIdx k 2 = k 2 := rfl
  have h3 : raiseIdx k 3 = k 3 := rfl
  simp only [divT, gravStress, Matrix.of_apply, Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [minkQuad] at hnull
  linear_combination (raiseIdx k ν * gravAmp e) * hnull

/-- **E5 CAPSTONE — the Deser rung: the graviton's self-coupling is gauge-consistent.** Because the on-shell
    self-stress is conserved, B1's iff makes the coupling of the graviton to ITS OWN stress invariant under every
    linearized diffeomorphism: `couple (e' + k⊙ξ) T_GW = couple e' T_GW`. The massless spin-2 field can
    consistently eat its own stress-energy — the first order of Deser's bootstrap to nonlinear GR (which B2's
    equivalence principle already forces it to attempt). -/
theorem deser_selfcoupling_consistent (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hnull : minkQuad k = 0) (e' : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 4 → ℝ) :
    couple (e' + gaugeShiftK k ξ) (gravStress k e) = couple e' (gravStress k e) :=
  gauge_invariant_of_conserved k (gravStress k e) (gravStress_symm k e)
    (gravStress_conserved k e hnull) e' ξ

/-- The on-shell self-stress is η-traceless — pure radiation. -/
theorem gravStress_traceless (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ)
    (hnull : minkQuad k = 0) :
    ∑ μ, ∑ ν, minkMetric μ ν * gravStress k e μ ν = 0 := by
  have h0 : raiseIdx k 0 = -(k 0) := rfl
  have h1 : raiseIdx k 1 = k 1 := rfl
  have h2 : raiseIdx k 2 = k 2 := rfl
  have h3 : raiseIdx k 3 = k 3 := rfl
  simp [gravStress, Matrix.of_apply, minkMetric, Matrix.diagonal_apply,
    Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [minkQuad] at hnull
  linear_combination (gravAmp e) * hnull

end QIQTH.EarnGravity
