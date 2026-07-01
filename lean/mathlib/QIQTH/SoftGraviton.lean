/-
  BRIDGE B2a — the soft-graviton Ward identity (the algebraic core of Weinberg 1964–65).

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified; B2 split into B2a Ward + B2b universality per the verification).
    In a scattering amplitude with `n` external particles (momenta `p_i`, incoming/outgoing signs `η_i`, graviton
    couplings `g_i`), the emission of a soft graviton of momentum `q` and polarization `ε` multiplies the amplitude
    by the **soft factor**
        S(ε) = ∑_i η_i g_i (p_i·ε·p_i)/(p_i·q).
    ⚠ The soft factor is TAKEN as the given algebraic object — its derivation from S-matrix pole factorization is
    QFT input (CARRIED), and the full analytic soft theorem is NOT proven here. What IS proven is the algebraic
    heart: a massless spin-2 polarization is defined only up to the longitudinal (gauge) shift
    `ε ↦ ε + q⊙ξ` (the on-shell residual gauge, `gaugeShiftK q ξ` of A1), so a consistent (Lorentz-invariant)
    amplitude must have a gauge-INVARIANT soft factor — and

        S(ε + q⊙ξ) = S(ε)  for every ξ   ⟺   ∑_i η_i g_i p_i^μ = 0   (THE WARD IDENTITY).

    The gauge variation is EXACTLY `2 ξ·(∑_i η_i g_i p_i)` (`softFactor_gauge_shift`) — longitudinal decoupling
    and the weighted-momentum sum rule are the same statement. With momentum conservation `∑_i η_i p_i = 0`,
    a sufficiently rich scattering family then forces all `g_i` EQUAL (universality = the equivalence principle)
    — that step is B2b. Everything here is finite algebra over `Fin n` and `Fin 4`; std-3, axiom-free.
-/
import Mathlib
import QIQTH.LinearizedEinstein
import QIQTH.AreaEmergence

namespace QIQTH.SoftGraviton

open QIQTH.GravDyn QIQTH.LinEinstein QIQTH.AreaMap

/-- The plain four-vector pairing `v·w = ∑_μ v^μ w_μ` (up-down contraction — no metric needed: `p` carries up
    indices, `q`/`ξ`/`ε` down indices throughout). -/
def dot (v w : Fin 4 → ℝ) : ℝ := ∑ μ, v μ * w μ

/-- The **weighted momentum sum** `P^μ = ∑_i η_i g_i p_i^μ` — the object the Ward identity constrains. -/
def weightedMomentum {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  ∑ i, η i * g i * p i μ

/-- **The soft factor** `S(ε) = ∑_i η_i g_i (p_i·ε·p_i)/(p_i·q)` — the universal multiplicative factor for
    soft-graviton emission (TAKEN as given; its S-matrix derivation is carried QFT input). -/
noncomputable def softFactor {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) (q : Fin 4 → ℝ)
    (ε : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, η i * g i * quadForm ε (p i) / dot (p i) q

/-- The longitudinal shift evaluates on a momentum as `p·(q⊙ξ)·p = 2(p·q)(p·ξ)`. -/
theorem quadForm_gaugeShiftK (q ξ p : Fin 4 → ℝ) :
    quadForm (gaugeShiftK q ξ) p = 2 * dot p q * dot p ξ := by
  simp only [quadForm, gaugeShiftK, dot, Matrix.of_apply, Fin.sum_univ_four]
  ring

/-- **The gauge variation of the soft factor is exactly the weighted-momentum pairing:**
    `S(ε + q⊙ξ) = S(ε) + 2 ξ·P` with `P = ∑_i η_i g_i p_i`. The denominators `p_i·q` cancel against the
    longitudinal numerator — the entire gauge dependence collapses to the sum rule object. -/
theorem softFactor_gauge_shift {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) (q : Fin 4 → ℝ)
    (hne : ∀ i, dot (p i) q ≠ 0) (ε : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 4 → ℝ) :
    softFactor η g p q (ε + gaugeShiftK q ξ)
      = softFactor η g p q ε + 2 * ∑ μ, ξ μ * weightedMomentum η g p μ := by
  have hterm : ∀ i, η i * g i * quadForm (ε + gaugeShiftK q ξ) (p i) / dot (p i) q
      = η i * g i * quadForm ε (p i) / dot (p i) q + 2 * (η i * g i) * dot (p i) ξ := by
    intro i
    have h0 : dot (p i) q ≠ 0 := hne i
    rw [quadForm_add, quadForm_gaugeShiftK]
    field_simp
  rw [softFactor, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  congr 1
  -- `∑_i 2 η_i g_i (p_i·ξ) = 2 ∑_μ ξ_μ P^μ` — swap the finite sums
  simp only [dot, weightedMomentum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Ward ⟸ decoupling:** if the soft factor is gauge invariant for every longitudinal shift, the weighted
    momentum sum vanishes: `∑_i η_i g_i p_i^μ = 0`. -/
theorem ward_of_gauge_invariant {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) (q : Fin 4 → ℝ)
    (hne : ∀ i, dot (p i) q ≠ 0) (ε : Matrix (Fin 4) (Fin 4) ℝ)
    (hinv : ∀ ξ : Fin 4 → ℝ, softFactor η g p q (ε + gaugeShiftK q ξ) = softFactor η g p q ε)
    (μ : Fin 4) : weightedMomentum η g p μ = 0 := by
  have h := hinv (fun j => if j = μ then (1 : ℝ) else 0)
  rw [softFactor_gauge_shift η g p q hne] at h
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  linarith

/-- **B2a CAPSTONE — the soft-graviton Ward identity (iff):** the soft factor is invariant under every
    longitudinal (residual-gauge) shift of the polarization **iff** the weighted momentum sum rule
    `∑_i η_i g_i p_i^μ = 0` holds. Longitudinal decoupling of the massless spin-2 mode and the Weinberg sum rule
    are the SAME statement — the algebraic heart of "massless spin-2 ⟹ universal coupling" (universality itself,
    from momentum conservation + a rich scattering family, is B2b). ⚠ Algebraic identity only — the soft factor's
    S-matrix derivation and the full analytic soft theorem are carried QFT inputs, not proven here. -/
theorem soft_gauge_invariant_iff_ward {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ)
    (q : Fin 4 → ℝ) (hne : ∀ i, dot (p i) q ≠ 0) :
    (∀ (ε : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 4 → ℝ),
        softFactor η g p q (ε + gaugeShiftK q ξ) = softFactor η g p q ε)
      ↔ (∀ μ, weightedMomentum η g p μ = 0) := by
  constructor
  · intro hinv μ
    exact ward_of_gauge_invariant η g p q hne 0 (hinv 0) μ
  · intro hward ε ξ
    rw [softFactor_gauge_shift η g p q hne]
    simp [hward]

end QIQTH.SoftGraviton
