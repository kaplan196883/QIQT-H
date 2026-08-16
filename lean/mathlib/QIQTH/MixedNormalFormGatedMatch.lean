/-
  MixedNormalFormGatedMatch — J4-805 (item (a)): the NORMAL-FORM ↔ GATED-GEOMETRY match.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  "normal-form matching" bookkeeping step named as item (a) at J4-801/804: the final geometry-swap that
  lets the concrete van-Vleck normal form `witnessMixed_hNormalForm_full` (J4-792) be consumed by
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` under the SAME gated geometry
  (`gateDisp`/`gateJet`/`gateQ`, J4-799) that `MixedSliverGatedEstimates.gated_five_estimates_global`
  supplies for the five global `hco`/`hVdisp`/`hJ3i`/`hJ3j`/`hJ3Q` estimates.

  ── THE MISMATCH (and its resolution).  The sliver theorem uses the SAME maps `V/Pi/Pj/Q` in BOTH the
  five geometric estimates (which must be GLOBAL `∀z`, hence GATED — J4-799) AND its `hNormalForm`
  hypothesis.  But J4-792's `witnessMixed_hNormalForm_full` produces the normal form with the RAW chart
  geometry (`uniformInverseChart`, raw `Pi/Pj/Q`) and merely gated AMPLITUDES.  This file bridges the two:
  it swaps the raw geometry for the gated geometry in the normal form, valid because every `mTerm`/`sTerm`
  is POINTWISE at the field point `z`:
    • ON the gate (`z ∈ G`): `gateDisp G V z = V z`, `gateJet G P i z = P z`, `gateQ G Q z = Q z`
      (`if_pos`), so each gated `mTerm` equals its raw counterpart verbatim.
    • OFF the gate (`z ∉ G`): the amplitude vanishes (the gated amplitudes are `0` off `S z₀`, and the
      geometric gate `G ⊇ S z₀`), so `A τ z = 0` makes BOTH the raw and the gated `mTerm` collapse to
      `… · 0 = 0`.  Hence raw normal form = gated normal form at every `z`.

  ── WHAT LANDS (all abstract; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `mixed_normalForm_gate_geometry` — the GENERAL geometry-swap: given any four-term mixed normal form
      with raw geometry and amplitudes that vanish off `G`, the SAME identity holds with the geometry
      replaced by its `gateDisp/gateJet/gateQ` gated versions.  Decoupled from the concrete witness.
    * `witnessMixed_hNormalForm_gated` — the CONCRETE corollary: the exact gated-geometry `hNormalForm`
      shape `witness_sliver2_xuniform_mixed` consumes, for the concrete gated van-Vleck witness, with
      `V := gateDisp G (uniformInverseChart …)`, `Pi := gateJet G Pi i`, `Pj := gateJet G Pj j`,
      `Q := gateQ G Q`, and the concrete gated amplitudes, under the single satisfiable geometric residue
      `S z₀ ⊆ G` (radial support inside the injectivity ball; recovers the raw form at `G = S z₀`).

  Every hypothesis is satisfiable and non-vacuous (`G = S z₀` makes the residue reflexive; the four
  gated amplitudes vanish off `S z₀` by construction), and none equals the conclusion.  This closes item
  (a) — the normal-form matching — as a clean geometry-swap.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedNormalFormFull
import QIQTH.MixedSliverGatedEstimates
import QIQTH.MixedSliverAssembly

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartJetHessianMixed QIQTH.MixedSliverAssembly
open QIQTH.MixedNormalFormFull QIQTH.MixedSliverGatedEstimates
open QIQTH.MixedNormalFormOnGate

namespace QIQTH.MixedNormalFormGatedMatch

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ GENERAL geometry-swap for the four-term mixed normal form — `mixed_normalForm_gate_geometry`.**
    Suppose `D2H` has the four-term mixed normal form with the RAW geometry `V Pi Pj Q` and amplitudes
    `A0 A1i A1j A2` that all VANISH off the gate set `G`.  Then the SAME identity holds with the geometry
    replaced by the `gateDisp G V` / `gateJet G Pi i` / `gateJet G Pj j` / `gateQ G Q` gated versions —
    exactly the shape `MixedSliverXUniform.witness_sliver2_xuniform_mixed` consumes when its geometric
    carries come from `MixedSliverGatedEstimates.gated_five_estimates_global`.
    ON gate: gated geometry = raw geometry pointwise (`if_pos`), so each term is unchanged.  OFF gate:
    every amplitude is `0`, so both the raw and the gated term collapse to `0`.  NOT `a₁ = R/6`. -/
theorem mixed_normalForm_gate_geometry (G : Set (Point n)) (D2H : ℝ → Point n → ℝ)
    (V Pi Pj Q : Point n → Point n) (A0 A1i A1j A2 : ℝ → Point n → ℝ) (i j : Fin n) (τ₀ : ℝ)
    (hAmpOff : ∀ τ : ℝ, ∀ ζ : Point n, ζ ∉ G →
        A0 τ ζ = 0 ∧ A1i τ ζ = 0 ∧ A1j τ ζ = 0 ∧ A2 τ ζ = 0)
    (hNF : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
        D2H τ ζ = mTerm0 V Pi Pj Q A0 τ ζ + mTerm1 V Pj A1i τ ζ
          + mTerm1 V Pi A1j τ ζ + sTerm2 V A2 τ ζ) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
        D2H τ ζ = mTerm0 (gateDisp G V) (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q) A0 τ ζ
          + mTerm1 (gateDisp G V) (gateJet G Pj j) A1i τ ζ
          + mTerm1 (gateDisp G V) (gateJet G Pi i) A1j τ ζ
          + sTerm2 (gateDisp G V) A2 τ ζ := by
  intro τ hτ ζ
  rw [hNF τ hτ ζ]
  by_cases hζG : ζ ∈ G
  · -- ON the gate: gated geometry equals raw geometry pointwise.
    have e1 : gateDisp G V ζ = V ζ := by unfold gateDisp; rw [if_pos hζG]
    have e2 : gateJet G Pi i ζ = Pi ζ := by unfold gateJet; rw [if_pos hζG]
    have e3 : gateJet G Pj j ζ = Pj ζ := by unfold gateJet; rw [if_pos hζG]
    have e4 : gateQ G Q ζ = Q ζ := by unfold gateQ; rw [if_pos hζG]
    simp only [mTerm0, mTerm1, sTerm2, e1, e2, e3, e4]
  · -- OFF the gate: every amplitude vanishes, so both sides collapse to `0`.
    obtain ⟨h0, h1i, h1j, h2⟩ := hAmpOff τ ζ hζG
    simp only [mTerm0, mTerm1, sTerm2, h0, h1i, h1j, h2, mul_zero, add_zero]

/-- **★★ J4-805 — CONCRETE gated-geometry normal form — `witnessMixed_hNormalForm_gated`.**  The exact
    `hNormalForm` shape `MixedSliverXUniform.witness_sliver2_xuniform_mixed` consumes, for the concrete
    gated van-Vleck witness, with the GATED geometry `V := gateDisp G (uniformInverseChart … z₀)`,
    `Pi := gateJet G Pi i`, `Pj := gateJet G Pj j`, `Q := gateQ G Q` — the SAME gated maps
    `MixedSliverGatedEstimates.gated_five_estimates_global` supplies for the five global estimates — and
    the concrete gated amplitudes.  Derived from J4-792's `witnessMixed_hNormalForm_full` (raw geometry)
    by the general geometry-swap, using that the gated amplitudes vanish off `S z₀ ⊆ G`.  Carries the
    single satisfiable geometric residue `hSG : S z₀ ⊆ G` (radial support inside the injectivity ball;
    reflexive at `G = S z₀`) plus J4-792's per-point chart/amplitude jets and off-gate germ.  This closes
    item (a) of the mixed-sliver chart-surface residue.  NOT `a₁ = R/6`. -/
theorem witnessMixed_hNormalForm_gated (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ₀ : ℝ) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (Pi Pj Q : Point n → Point n)
    (hJetPi : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (Pi y k) (y i))
    (hJetPj : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y j s) k) (Pj y k) (y j))
    (hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
      (fun s : ℝ => Pi (Function.update ζ j s) k) (Q ζ k) (ζ j))
    (hAmpDi : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ y : Point n,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) i y)
    (hAmpDj : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) j ζ)
    (hAmpD2 : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) j ζ)
    (hOffNhd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
      pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ
        = mTerm0 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ
          + mTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pj j)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ
          + mTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pi i)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')) τ ζ
          + sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ')) τ ζ := by
  -- The four gated amplitudes vanish off `G` (via `S z₀ ⊆ G` and `gateAmp_of_notMem`).
  have hAmpOff : ∀ τ : ℝ, ∀ ζ : Point n, ζ ∉ G →
      (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ = 0
      ∧ (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
          pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ = 0
      ∧ (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
          pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')) τ ζ = 0
      ∧ (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
          pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ')) τ ζ = 0 := by
    intro τ ζ hζG
    have hζS : ζ ∉ S z₀ := fun h => hζG (hSG h)
    exact ⟨gateAmp_of_notMem S z₀ _ τ hζS, gateAmp_of_notMem S z₀ _ τ hζS,
      gateAmp_of_notMem S z₀ _ τ hζS, gateAmp_of_notMem S z₀ _ τ hζS⟩
  -- Apply the general geometry-swap to J4-792's raw-geometry normal form.
  exact mixed_normalForm_gate_geometry G
    (fun τ ζ => pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ)
    (uniformInverseChart g gi hC hK z₀) Pi Pj Q
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
      pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ'))
    i j τ₀ hAmpOff
    (witnessMixed_hNormalForm_full g gi hC hK S a b i j τ₀ z₀ hz₀ hSopen Pi Pj Q
      hJetPi hJetPj hJetQ hAmpDi hAmpDj hAmpD2 hOffNhd)

end QIQTH.MixedNormalFormGatedMatch

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedNormalFormGatedMatch
#print axioms mixed_normalForm_gate_geometry
#print axioms witnessMixed_hNormalForm_gated
end AxiomChecks
