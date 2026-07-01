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

/-! ## B2b — universality on connected components (the equivalence principle)

  With momentum conservation `∑_i η_i p_i = 0`, the Ward sum rule `∑_i η_i g_i p_i = 0` forces all couplings
  EQUAL **provided the process is generic**: the only linear relation among the momenta is momentum conservation
  itself. That genericity (`RichFamily`: the kernel of `c ↦ ∑ c_i p_i` is exactly the `η`-line) is the CARRIED
  "sufficiently rich connected scattering family" hypothesis of Weinberg's argument — supplied here as an explicit
  hypothesis (never an axiom), with a concrete kinematic non-vacuity witness (`witness_rich`). -/

/-- **The rich-family (genericity) hypothesis**: the only linear relation among the momenta is momentum
    conservation — the kernel of `c ↦ ∑_i c_i p_i` is the line `ℝ·η`. CARRIED physics input (generic momenta). -/
def RichFamily {n : ℕ} (η : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ c : Fin n → ℝ, (∀ μ, ∑ i, c i * p i μ = 0) → ∃ lam : ℝ, ∀ i, c i = lam * η i

/-- **B2b — UNIVERSALITY (the equivalence principle):** for a generic process (`RichFamily`) with genuine
    external particles (`η_i ≠ 0`), the Ward sum rule forces ALL couplings equal: `∃ g_U, ∀ i, g_i = g_U`.
    Every species couples to the massless spin-2 field with ONE universal charge. -/
theorem universality {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ)
    (hη : ∀ i, η i ≠ 0) (hRich : RichFamily η p)
    (hWard : ∀ μ, weightedMomentum η g p μ = 0) :
    ∃ gU : ℝ, ∀ i, g i = gU := by
  obtain ⟨lam, hlam⟩ := hRich (fun i => η i * g i) (fun μ => by
    simpa [weightedMomentum] using hWard μ)
  refine ⟨lam, fun i => ?_⟩
  have h := hlam i
  exact mul_left_cancel₀ (hη i) (by rw [h]; ring)

/-- **The converse (consistency):** a universal coupling automatically satisfies the Ward sum rule, given
    momentum conservation `∑_i η_i p_i = 0`. -/
theorem ward_of_universal {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) (gU : ℝ)
    (hUniv : ∀ i, g i = gU) (hcons : ∀ μ, ∑ i, η i * p i μ = 0) (μ : Fin 4) :
    weightedMomentum η g p μ = 0 := by
  simp only [weightedMomentum, hUniv]
  calc ∑ i, η i * gU * p i μ = gU * ∑ i, η i * p i μ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hcons, mul_zero]

/-- **B2 CAPSTONE — the equivalence principle from longitudinal decoupling:** for a generic scattering family,
    gauge invariance of the soft-graviton factor (the consistency of massless spin-2 emission, B2a) forces ONE
    universal coupling for all species. Weinberg's theorem at the algebraic level, end-to-end:
    decoupling ⟹ Ward sum rule ⟹ (generic momenta) ⟹ universality. ⚠ The soft factor and the genericity
    (`RichFamily`) are carried QFT/kinematics inputs; the analytic soft theorem is not claimed. -/
theorem equivalence_principle {n : ℕ} (η g : Fin n → ℝ) (p : Fin n → Fin 4 → ℝ) (q : Fin 4 → ℝ)
    (hne : ∀ i, dot (p i) q ≠ 0) (hη : ∀ i, η i ≠ 0) (hRich : RichFamily η p)
    (ε : Matrix (Fin 4) (Fin 4) ℝ)
    (hinv : ∀ ξ : Fin 4 → ℝ, softFactor η g p q (ε + gaugeShiftK q ξ) = softFactor η g p q ε) :
    ∃ gU : ℝ, ∀ i, g i = gU :=
  universality η g p hη hRich (ward_of_gauge_invariant η g p q hne ε hinv)

/-! ### Non-vacuity: a concrete rich family -/

/-- A concrete 5-particle momentum configuration: the four basis directions and their sum. -/
def pW : Fin 5 → Fin 4 → ℝ := ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1], ![1,1,1,1]]

/-- Its sign vector (four incoming, one outgoing). -/
def etaW : Fin 5 → ℝ := ![1, 1, 1, 1, -1]

/-- Momentum conservation holds for the witness: `∑ η_i p_i = 0`. -/
theorem witness_conserved (μ : Fin 4) : ∑ i, etaW i * pW i μ = 0 := by
  fin_cases μ <;> simp [pW, etaW, Fin.sum_univ_five]

/-- **The rich-family hypothesis is non-vacuous**: the concrete configuration `pW`/`etaW` satisfies it — the only
    linear relation among these momenta is (a multiple of) momentum conservation. ⚠ A kinematic witness (the
    genericity CAN hold), not a claim about physical on-shell processes. -/
theorem witness_rich : RichFamily etaW pW := by
  intro c hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  simp only [pW, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2 h3
  refine ⟨-(c 4), fun i => ?_⟩
  fin_cases i
  · show c 0 = -(c 4) * etaW 0
    simp [etaW]; linarith
  · show c 1 = -(c 4) * etaW 1
    simp [etaW]; linarith
  · show c 2 = -(c 4) * etaW 2
    simp [etaW]; linarith
  · show c 3 = -(c 4) * etaW 3
    simp [etaW]; linarith
  · show c 4 = -(c 4) * etaW 4
    simp [etaW]

end QIQTH.SoftGraviton
