/-
  DiagNormalFormGatedMatch — J4-813: the DIAGONAL NORMAL-FORM ↔ GATED-GEOMETRY match — the diagonal
  (`i = j`) analogue of `MixedNormalFormGatedMatch` (J4-805).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  "normal-form matching" bookkeeping step: the final geometry-swap that lets the concrete van-Vleck
  DIAGONAL normal form `DiagNormalFormFull.witnessDiag_hNormalForm_full` (J4-809) be consumed by
  `XUniformSliverFull.witness_sliver2_xuniform` under the SAME gated geometry
  (`gateDisp`/`gateJet`/`gateQ`, J4-799) that `MixedSliverGatedEstimates.gated_five_estimates_global`
  supplies for the global `hco`/`hVdisp`/`hJ3`/`hJ3Q` estimates.

  ── THE MISMATCH (and its resolution — identical mechanism to the mixed J4-805, three terms/one index
  instead of four/two).  The diagonal sliver theorem uses the SAME maps `Y/P/Q` in BOTH the geometric
  estimates (which must be GLOBAL `∀z`, hence GATED) AND its `hNormalForm` hypothesis.  But J4-809 produces
  the normal form with the RAW chart geometry (`uniformInverseChart`, raw `P/Q`) and merely gated
  AMPLITUDES.  This file swaps the raw geometry for the gated geometry, valid because every `sTerm` is
  POINTWISE at the field point `ζ`:
    • ON the gate (`ζ ∈ G`): `gateDisp G Y ζ = Y ζ`, `gateJet G P i ζ = P ζ`, `gateQ G Q ζ = Q ζ`
      (`if_pos`), so each gated `sTerm` equals its raw counterpart verbatim.
    • OFF the gate (`ζ ∉ G`): the amplitude vanishes (the gated amplitudes are `0` off `S z₀`, and
      `G ⊇ S z₀`), so `A τ ζ = 0` makes BOTH the raw and the gated `sTerm` collapse to `… · 0 = 0`.

  ── WHAT LANDS (all std-3; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `diag_normalForm_gate_geometry` — the GENERAL diagonal geometry-swap.
    * `witnessDiag_hNormalForm_gated` — the CONCRETE gated-geometry diagonal `hNormalForm` shape
      `witness_sliver2_xuniform` consumes, with `Y := gateDisp G (uniformInverseChart …)`,
      `P := gateJet G P i`, `Q := gateQ G Q` and the concrete gated amplitudes, under the single
      satisfiable geometric residue `S z₀ ⊆ G`.

  Every hypothesis is satisfiable and non-vacuous (`G = S z₀` makes the residue reflexive; the three gated
  amplitudes vanish off `S z₀` by construction), and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DiagNormalFormFull
import QIQTH.MixedSliverGatedEstimates

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.MixedNormalFormFull QIQTH.MixedSliverGatedEstimates QIQTH.DiagNormalFormFull

namespace QIQTH.DiagNormalFormGatedMatch

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ GENERAL geometry-swap for the three-term diagonal normal form — `diag_normalForm_gate_geometry`.**
    Suppose `D2H` has the three-term diagonal normal form with the RAW geometry `Y P Q` and amplitudes
    `A0 A1 A2` that all VANISH off the gate set `G`.  Then the SAME identity holds with the geometry
    replaced by the `gateDisp G Y` / `gateJet G P i` / `gateQ G Q` gated versions — exactly the shape
    `XUniformSliverFull.witness_sliver2_xuniform` consumes when its geometric carries come from
    `MixedSliverGatedEstimates.gated_five_estimates_global`.  ON gate: gated geometry = raw geometry
    pointwise (`if_pos`).  OFF gate: every amplitude is `0`, so both sides collapse to `0`.
    NOT `a₁ = R/6`. -/
theorem diag_normalForm_gate_geometry (G : Set (Point n)) (D2H : ℝ → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ) (i : Fin n) (τ₀ : ℝ)
    (hAmpOff : ∀ τ : ℝ, ∀ ζ : Point n, ζ ∉ G →
        A0 τ ζ = 0 ∧ A1 τ ζ = 0 ∧ A2 τ ζ = 0)
    (hNF : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
        D2H τ ζ = sTerm0 Y P Q A0 τ ζ + sTerm1 Y P A1 τ ζ + sTerm2 Y A2 τ ζ) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
        D2H τ ζ = sTerm0 (gateDisp G Y) (gateJet G P i) (gateQ G Q) A0 τ ζ
          + sTerm1 (gateDisp G Y) (gateJet G P i) A1 τ ζ
          + sTerm2 (gateDisp G Y) A2 τ ζ := by
  intro τ hτ ζ
  rw [hNF τ hτ ζ]
  by_cases hζG : ζ ∈ G
  · -- ON the gate: gated geometry equals raw geometry pointwise.
    have e1 : gateDisp G Y ζ = Y ζ := by unfold gateDisp; rw [if_pos hζG]
    have e2 : gateJet G P i ζ = P ζ := by unfold gateJet; rw [if_pos hζG]
    have e4 : gateQ G Q ζ = Q ζ := by unfold gateQ; rw [if_pos hζG]
    simp only [sTerm0, sTerm1, sTerm2, e1, e2, e4]
  · -- OFF the gate: every amplitude vanishes, so both sides collapse to `0`.
    obtain ⟨h0, h1, h2⟩ := hAmpOff τ ζ hζG
    simp only [sTerm0, sTerm1, sTerm2, h0, h1, h2, mul_zero, add_zero]

/-- **★★ J4-813 — CONCRETE gated-geometry diagonal normal form — `witnessDiag_hNormalForm_gated`.**  The
    exact `hNormalForm` shape `XUniformSliverFull.witness_sliver2_xuniform` consumes, for the concrete
    gated van-Vleck witness, with the GATED geometry `Y := gateDisp G (uniformInverseChart … z₀)`,
    `P := gateJet G P i`, `Q := gateQ G Q` — the SAME gated maps
    `MixedSliverGatedEstimates.gated_five_estimates_global` supplies for the global estimates — and the
    concrete gated amplitudes.  Derived from J4-809's `witnessDiag_hNormalForm_full` (raw geometry) by the
    general geometry-swap, using that the gated amplitudes vanish off `S z₀ ⊆ G`.  The diagonal analogue of
    `MixedNormalFormGatedMatch.witnessMixed_hNormalForm_gated`.  NOT `a₁ = R/6`. -/
theorem witnessDiag_hNormalForm_gated (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ₀ : ℝ) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (P Q : Point n → Point n)
    (hJetV : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (P y k) (y i))
    (hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update ζ i s) k) (Q ζ k) (ζ i))
    (hAmpDi : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ y : Point n,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) i y)
    (hAmpD2 : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) i ζ)
    (hOffNhd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
      pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) i ζ
        = sTerm0 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateJet G P i) (gateQ G Q)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ
          + sTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G P i)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ
          + sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ')) τ ζ := by
  -- The three gated amplitudes vanish off `G` (via `S z₀ ⊆ G` and `gateAmp_of_notMem`).
  have hAmpOff : ∀ τ : ℝ, ∀ ζ : Point n, ζ ∉ G →
      (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ = 0
      ∧ (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
          pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ = 0
      ∧ (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
          pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ')) τ ζ = 0 := by
    intro τ ζ hζG
    have hζS : ζ ∉ S z₀ := fun h => hζG (hSG h)
    exact ⟨gateAmp_of_notMem S z₀ _ τ hζS, gateAmp_of_notMem S z₀ _ τ hζS,
      gateAmp_of_notMem S z₀ _ τ hζS⟩
  -- Apply the general geometry-swap to J4-809's raw-geometry normal form.
  exact diag_normalForm_gate_geometry G
    (fun τ ζ => pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) i ζ)
    (uniformInverseChart g gi hC hK z₀) P Q
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
      pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ'))
    i τ₀ hAmpOff
    (witnessDiag_hNormalForm_full g gi hC hK S a b i τ₀ z₀ hz₀ hSopen P Q
      hJetV hJetQ hAmpDi hAmpD2 hOffNhd)

end QIQTH.DiagNormalFormGatedMatch

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DiagNormalFormGatedMatch
#print axioms diag_normalForm_gate_geometry
#print axioms witnessDiag_hNormalForm_gated
end AxiomChecks
