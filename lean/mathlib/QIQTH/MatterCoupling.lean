/-
  BRIDGE B1 — matter coupling ⟺ stress-energy conservation (the first half of Weinberg).

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified; flat background, plane-wave symbols as in
    `LinearizedEinstein.lean`). The linearized matter coupling is `∫ h_{μν} T^{μν}`; on the plane-wave sector it is
    the pairing `couple e T = ∑ e_{μν} T^{μν}` between the perturbation symbol `e` (down indices) and the
    stress-energy symbol `T` (up indices). A linearized diffeomorphism shifts `e ↦ e + k⊙ξ`; momentum-space
    stress-energy conservation is `k_μ T^{μν} = 0` (the symbol of `∂_μ T^{μν} = 0`).

  Results (all axiom-free, std 3):
  • `couple_gauge` — the gauge variation of the coupling is exactly `2 ∑ ξ_ν (k_μT^{μν})`.
  • `couple_gauge_invariant_iff_conserved` — **THE IFF**: the coupling is gauge invariant (for every `e` and every
    gauge parameter `ξ`) ⟺ the stress-energy is conserved (`k_μT^{μν} = 0`). Gauge invariance of the graviton-matter
    coupling and conservation of the source are the SAME statement — the first half of Weinberg's argument.
  • `einstein_source_conserved` / `source_conserved_of_einstein_eq` — **the Bianchi payoff**: the (index-raised)
    linearized Einstein tensor is identically conserved (`bianchi_einsteinSymbol` from A1), so any stress tensor
    sourced by `δG^{μν} = κ T^{μν}` is AUTOMATICALLY conserved. GR's consistency: the geometry side forces exactly
    the conservation law the coupling side demands.

  ⚠ Honest labels: linearized ≠ full; free ≠ interacting (this is the linear coupling's consistency condition, not
    an interacting theory); flat background; universality of the coupling (all species, one `G`) is B2, not here.
-/
import Mathlib
import QIQTH.LinearizedEinstein

namespace QIQTH.MatterCoupling

open QIQTH.GravDyn QIQTH.LinEinstein

/-- The **linearized matter coupling** (plane-wave pairing) `couple e T = ∑_{μν} e_{μν} T^{μν}` — the momentum-space
    symbol of `∫ h_{μν} T^{μν}` (`e` down-index, `T` up-index). -/
def couple (e T : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := ∑ μ, ∑ ν, e μ ν * T μ ν

/-- **Momentum-space stress-energy divergence** `(divT k T)_ν = k_μ T^{μν}` — the plane-wave symbol of
    `∂_μ T^{μν}`; conservation is `divT k T = 0`. -/
def divT (k : Fin 4 → ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) : ℝ := ∑ μ, k μ * T μ ν

/-- The coupling is additive in the perturbation. -/
theorem couple_add (e f T : Matrix (Fin 4) (Fin 4) ℝ) :
    couple (e + f) T = couple e T + couple f T := by
  simp only [couple, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The divergence is linear in the stress tensor (scalar multiples). -/
theorem divT_smul (k : Fin 4 → ℝ) (κ : ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    divT k (κ • T) ν = κ * divT k T ν := by
  simp only [divT, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => by ring

/-- **The gauge variation of the coupling** — for symmetric `T`, a pure-gauge shift `e = k⊙ξ` couples as
    `2 ∑_ν ξ_ν (k_μ T^{μν})`: the coupling's gauge variation IS (twice) the `ξ`-weighted divergence of the source. -/
theorem couple_gauge (k ξ : Fin 4 → ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ) (hSym : T.IsSymm) :
    couple (gaugeShiftK k ξ) T = 2 * ∑ ν, ξ ν * divT k T ν := by
  have h01 : T 1 0 = T 0 1 := hSym.apply 0 1
  have h02 : T 2 0 = T 0 2 := hSym.apply 0 2
  have h03 : T 3 0 = T 0 3 := hSym.apply 0 3
  have h12 : T 2 1 = T 1 2 := hSym.apply 1 2
  have h13 : T 3 1 = T 1 3 := hSym.apply 1 3
  have h23 : T 3 2 = T 2 3 := hSym.apply 2 3
  simp only [couple, gaugeShiftK, divT, Matrix.of_apply, Fin.sum_univ_four]
  linear_combination (k 0 * ξ 1 - k 1 * ξ 0) * h01 + (k 0 * ξ 2 - k 2 * ξ 0) * h02
    + (k 0 * ξ 3 - k 3 * ξ 0) * h03 + (k 1 * ξ 2 - k 2 * ξ 1) * h12
    + (k 1 * ξ 3 - k 3 * ξ 1) * h13 + (k 2 * ξ 3 - k 3 * ξ 2) * h23

/-- **Conservation ⟹ gauge invariance**: a conserved source makes the coupling invariant under every linearized
    diffeomorphism, `couple (e + k⊙ξ) T = couple e T`. -/
theorem gauge_invariant_of_conserved (k : Fin 4 → ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : T.IsSymm) (hcons : ∀ ν, divT k T ν = 0) (e : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 4 → ℝ) :
    couple (e + gaugeShiftK k ξ) T = couple e T := by
  rw [couple_add, couple_gauge k ξ T hSym]
  simp [hcons]

/-- **Gauge invariance ⟹ conservation**: if the coupling is invariant for every gauge parameter (the separating
    class `ξ = δ_ν`), the source is conserved. -/
theorem conserved_of_gauge_invariant (k : Fin 4 → ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : T.IsSymm) (hinv : ∀ ξ : Fin 4 → ℝ, couple (gaugeShiftK k ξ) T = 0) (ν : Fin 4) :
    divT k T ν = 0 := by
  have h := hinv (fun j => if j = ν then (1 : ℝ) else 0)
  rw [couple_gauge k _ T hSym] at h
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  linarith

/-- **B1 CAPSTONE — the iff**: the graviton-matter coupling is gauge invariant (for every perturbation and every
    linearized diffeomorphism) **iff** the stress-energy source is conserved (`k_μT^{μν} = 0`). The consistency of
    coupling a gauge field `h_{μν}` to matter and the conservation of that matter's stress-energy are the SAME
    condition — the first half of Weinberg. ⚠ Linearized; symbol form; universality (one `G` for all species) is B2. -/
theorem couple_gauge_invariant_iff_conserved (k : Fin 4 → ℝ) (T : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : T.IsSymm) :
    (∀ (e : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 4 → ℝ),
        couple (e + gaugeShiftK k ξ) T = couple e T)
      ↔ (∀ ν, divT k T ν = 0) := by
  constructor
  · intro hinv ν
    refine conserved_of_gauge_invariant k T hSym (fun ξ => ?_) ν
    have h := hinv 0 ξ
    rw [couple_add] at h
    -- `couple 0 T + couple gauge T = couple 0 T` reduces to `couple gauge T = 0`
    linarith
  · intro hcons e ξ
    exact gauge_invariant_of_conserved k T hSym hcons e ξ

/-! ## The Bianchi payoff — the geometry side automatically satisfies the conservation the coupling demands -/

/-- The index-raising signs of `η = diag(−1,1,1,1)`. -/
def raiseSign : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- Double index raising `S^{μν} = η^{μα}η^{νβ}S_{αβ}` (diagonal `η`: sign flips). -/
def raise2 (S : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => raiseSign μ * raiseSign ν * S μ ν

/-- **The linearized Einstein tensor is identically conserved** (up indices): `k_μ (δG)^{μν} = 0` for EVERY `k, e`
    — the up-index form of the linearized Bianchi identity (`bianchi_einsteinSymbol`, A1). -/
theorem einstein_source_conserved (k : Fin 4 → ℝ) (e : Matrix (Fin 4) (Fin 4) ℝ) (ν : Fin 4) :
    divT k (raise2 (einsteinSymbol k e)) ν = 0 := by
  have hdiv : divT k (raise2 (einsteinSymbol k e)) ν
      = raiseSign ν * kContract k (einsteinSymbol k e) ν := by
    simp only [divT, raise2, raiseSign, kContract, raiseIdx, Matrix.of_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hdiv, bianchi_einsteinSymbol, mul_zero]

/-- **A source of the linearized Einstein equation is automatically conserved.** If `δG^{μν} = κ T^{μν}` (the sourced
    linearized Einstein equation, `κ ≠ 0` e.g. `8πG`), then `k_μT^{μν} = 0` — the Bianchi identity FORCES exactly the
    conservation law that gauge invariance of the coupling demands (`couple_gauge_invariant_iff_conserved`). The two
    halves of the linearized consistency triangle meet. ⚠ `κ`/`G` is a carried constant, not derived. -/
theorem source_conserved_of_einstein_eq (k : Fin 4 → ℝ) (e T : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ)
    (hκ : κ ≠ 0) (hEq : raise2 (einsteinSymbol k e) = κ • T) (ν : Fin 4) :
    divT k T ν = 0 := by
  have h := einstein_source_conserved k e ν
  rw [hEq, divT_smul] at h
  exact (mul_eq_zero.mp h).resolve_left hκ

end QIQTH.MatterCoupling
