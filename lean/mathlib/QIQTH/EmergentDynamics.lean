/-
  Emergent (linearized) dynamics — the graviton-wall attack. A CONDITIONAL FINITE SKELETON, NOT solved QG.

  ★ SCOPE (read first; GPT-5.5-pro-verified plan `GRAVITON_WALL_PLAN.md`). This attacks the mechanism gap — the
    graviton/dynamics wall — via the FGHMVR "entanglement first law ⟹ linearized Einstein" logic and a QIQT-H-native
    finite null-focusing route. It does **NOT** solve quantum gravity. Every theorem here is a finite/algebraic
    **conditional skeleton**; the decisive continuum physics (continuum ball modular Hamiltonians, RT/extremal-area
    emergence, Iyer–Wald geometry, the actual nonlinear/quantized graviton) is cited research (plan G8–G12). ★

  ★ THE SINGLE MOST IMPORTANT GUARD. Never turn the area–stress link `δA = 8πG·K` into a *derived* theorem from
    packing / first law / min-cut — that hypothesis is exactly where the Einstein-equation content enters (inventory
    §2: "the `δA/4G=2π∫δT_kk` step uses the Einstein equations"). It is always a CARRIED explicit hypothesis.

  Honest rails: NO `sorry`; std-3; NEVER claim QG solved / a real (nonlinear/quantized) graviton / background
  independence / the value of `G`. Linearized ≠ full. Toy ≠ background-independent. `G` relation ≠ `G` value.

  ── G1 — the FGHMVR logical skeleton (all-probes first law ⟺ residual = 0) ──
  The exact formal core of "the entanglement first law at *every* probe ⟺ the linearized field equation." Pure
  linear algebra: given a **separating** family of probe functionals `P B : E →ₗ[ℝ] ℝ` (`E` = the linearized-residual
  space) and a carried Iyer–Wald-shaped identity `δK − δS = ⟨P, residual⟩`, the first law `∀ B, δS B = δK B` holds
  iff the residual vanishes. ⚠ The `∀ B` all-probe family and the `iw` identity are EXPLICIT CARRIED hypotheses —
  the continuum CFT balls (plan G8) and Iyer–Wald geometry (plan G10) are NOT supplied here.
-/
import Mathlib

namespace QIQTH.GravDyn

/-- A family of probe functionals `P B : E →ₗ[ℝ] ℝ` is **separating** if only the zero residual is annihilated by
    every probe. (In FGHMVR `E` is the space of linearized Einstein residuals and the `P B` are the ball/Iyer–Wald
    pairings; separation is the "all ball integrals vanish ⟹ the field vanishes" property — supplied finitely in G2.) -/
def Separating {Ball E : Type*} [AddCommGroup E] [Module ℝ E] (P : Ball → E →ₗ[ℝ] ℝ) : Prop :=
  ∀ e : E, (∀ B : Ball, P B e = 0) → e = 0

/-- **G1a — first law at every probe ⟹ residual = 0.** With the carried Iyer–Wald identity
    `iw : ∀ B, δK B − δS B = P B residual`, if the first law `δS = δK` holds at every probe and the probe family is
    separating, the linearized residual vanishes. -/
theorem residual_eq_zero_of_firstLaw {Ball E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Ball → E →ₗ[ℝ] ℝ) (sep : Separating P) (residual : E) (δS δK : Ball → ℝ)
    (iw : ∀ B, δK B - δS B = P B residual) (fl : ∀ B, δS B = δK B) :
    residual = 0 := by
  apply sep
  intro B
  calc P B residual = δK B - δS B := (iw B).symm
    _ = δK B - δK B := by rw [fl B]
    _ = 0 := sub_self _

/-- **G1 — the FGHMVR skeleton: `(∀ B, δS B = δK B) ↔ residual = 0`.** The entanglement first law at every probe is
    equivalent to the vanishing of the linearized field-equation residual — the exact formal core of FGHMVR, as a
    conditional theorem over the carried separating-probe family + Iyer–Wald identity. Pure linear algebra; NOT a
    physical derivation of Einstein (the continuum ball/Iyer–Wald content is the carried hypothesis, plan G8/G10). -/
theorem allBall_firstLaw_iff_residual_zero {Ball E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Ball → E →ₗ[ℝ] ℝ) (sep : Separating P) (residual : E) (δS δK : Ball → ℝ)
    (iw : ∀ B, δK B - δS B = P B residual) :
    (∀ B, δS B = δK B) ↔ residual = 0 := by
  constructor
  · exact residual_eq_zero_of_firstLaw P sep residual δS δK iw
  · intro h B
    have hzero : δK B - δS B = 0 := by rw [iw B, h, map_zero]
    exact (sub_eq_zero.mp hzero).symm

/-! ## G2 — the finite decoder / Radon inversion (supplies `Separating` for G1) -/

/-- **G2 — the finite decoder / Radon inversion.** If a finite field `f : Cell → ℝ` is *reconstructible* from its
    probe measurements via a decoder — `∀ i, f i = ∑ p, decode i p · measure p f` — and every probe measurement of
    `f` vanishes, then `f = 0`. This is the finite model of "all ball integrals of `f` vanish ⟹ `f = 0`" (the
    separating property, made concrete on a finite cell/probe grid). -/
theorem eq_zero_of_decoder {Cell Probe : Type*} [Fintype Cell] [Fintype Probe]
    (measure : Probe → (Cell → ℝ) → ℝ) (decode : Cell → Probe → ℝ) (f : Cell → ℝ)
    (hdecode : ∀ i, f i = ∑ p, decode i p * measure p f)
    (hzero : ∀ p, measure p f = 0) : f = 0 := by
  funext i
  rw [hdecode i]
  simp [hzero]

/-- **G2 → G1 — the `Separating` instance G1 needs.** If a *linear* probe family `P : Probe → (Cell → ℝ) →ₗ[ℝ] ℝ`
    admits a decoder (`∀ f i, f i = ∑ p, decode i p · P p f`), then it is `Separating`. This supplies the separating
    hypothesis of `allBall_firstLaw_iff_residual_zero` concretely — the residual space is `Cell → ℝ`, the probes are
    the ball/Iyer–Wald pairings, and finite reconstruction closes the "all probes vanish ⟹ residual vanishes" step. -/
theorem separating_of_decoder {Cell Probe : Type*} [Fintype Cell] [Fintype Probe]
    (P : Probe → (Cell → ℝ) →ₗ[ℝ] ℝ) (decode : Cell → Probe → ℝ)
    (hdecode : ∀ (f : Cell → ℝ) (i : Cell), f i = ∑ p, decode i p * P p f) :
    Separating P := by
  intro f hf
  funext i
  rw [hdecode f i]
  simp [hf]

/-! ## G3 — the discrete null modular kernel  `Δ²K = T` (anchors to the existing `T_kk`) -/

/-- The **discrete null modular tail kernel** `K_c = ∑_{i=c}^N (i−c)·T_i` — the finite/discrete analogue of the null
    modular Hamiltonian `K_V = 2π∫(u−V)·T_kk`. Indices over `ℤ` to keep the subtraction genuine (no `Nat` truncation). -/
noncomputable def tailK (N : ℤ) (T : ℤ → ℝ) (c : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc c N, ((i : ℝ) - (c : ℝ)) * T i

/-- The **discrete second difference** `Δ²A_c = A_{c−1} − 2A_c + A_{c+1}`. -/
noncomputable def secondDiff (A : ℤ → ℝ) (c : ℤ) : ℝ := A (c - 1) - 2 * A c + A (c + 1)

/-- **G3 — the discrete null modular shape derivative `Δ²K = T`.** The second difference of the tail kernel recovers
    the local stress: `Δ²(tailK)_c = T_c` for `c < N` — the finite analogue of `δ²K_V/δV² = 2π T_kk`, connecting to
    the *existing* `T_kk` / `wedge_boostCharge_eq_neg_stressFlux`. ⚠ Sign/orientation and the KG/free-field
    instantiation of `T` are carried; this is the discrete kernel identity only, NOT a physical derivation. -/
theorem secondDiff_tailK_eq (N : ℤ) (T : ℤ → ℝ) (c : ℤ) (hcN : c < N) :
    secondDiff (tailK N T) c = T c := by
  have hcle : c ≤ N := le_of_lt hcN
  have e2 : Finset.Icc c N = insert c (Finset.Icc (c + 1) N) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hc_notin : c ∉ Finset.Icc (c + 1) N := by simp only [Finset.mem_Icc]; omega
  -- backward difference: `K_{d-1} − K_d = ∑_{i=d}^N T_i`
  have A : ∀ d : ℤ, d ≤ N → tailK N T (d - 1) - tailK N T d = ∑ i ∈ Finset.Icc d N, T i := by
    intro d _
    have ed : Finset.Icc (d - 1) N = insert (d - 1) (Finset.Icc d N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hd_notin : (d - 1) ∉ Finset.Icc d N := by simp only [Finset.mem_Icc]; omega
    unfold tailK
    rw [ed, Finset.sum_insert hd_notin,
      show (((d - 1 : ℤ) : ℝ) - ((d - 1 : ℤ) : ℝ)) = 0 by ring, zero_mul, zero_add,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast; ring
  have hAc : tailK N T (c - 1) - tailK N T c = ∑ i ∈ Finset.Icc c N, T i := A c hcle
  have hAc1 : tailK N T c - tailK N T (c + 1) = ∑ i ∈ Finset.Icc (c + 1) N, T i := by
    simpa using A (c + 1) (by omega)
  have hsplit : (∑ i ∈ Finset.Icc c N, T i) - (∑ i ∈ Finset.Icc (c + 1) N, T i) = T c := by
    rw [e2, Finset.sum_insert hc_notin]; ring
  unfold secondDiff
  have hcomb : tailK N T (c - 1) - 2 * tailK N T c + tailK N T (c + 1)
      = (tailK N T (c - 1) - tailK N T c) - (tailK N T c - tailK N T (c + 1)) := by ring
  rw [hcomb, hAc, hAc1]
  exact hsplit

end QIQTH.GravDyn
