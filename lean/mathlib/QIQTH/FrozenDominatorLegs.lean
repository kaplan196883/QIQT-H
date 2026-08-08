/-
  FrozenDominatorLegs — J4-440 (the a₁ = R/6 convergence-trio campaign, diff-under-∫ family):
  THE BASE-`y` GAUSSIAN DOMINATOR — discharging the z-level REDUCED CORE + the outer bound legs
  (5)/(6) of the frozen hQ1 provider remainder.

  J4-439 (`FrozenHdiffLeg`) discharged the outer `HasDerivAt` leg (7) and shrank the provider
  remainder to {snb, the dominator triple `bound`+`hbdd`+`hbound` (legs 5/6)} PLUS the per-`(s,w)`
  base-`y` z-level REDUCED CORE `hRemainderDiff` (nbhd + slice measurabilities + base
  `z`-integrability + integrable dominator + `∀ᵐ z` derivative domination + per-`z` gate dichotomy).
  THIS BRICK discharges BOTH remaining analytic pieces onto strictly-lighter, ENUMERATED base-`y`
  GATE/AMPLITUDE/ENVELOPE carries:

    • the z-level REDUCED CORE — MIRRORING `InnerDataEnvelope.innerData_reducedCore_of_gateData`
      at base `y`, ONE field-derivative order DOWN (`dH → dHH` becomes `W → dH`): the integrable
      Gaussian dominator `C·gaussDdim σ` via the banked `WitnessDerivDomination.envelope_integrable`,
      the base `z`-integrability via the ZEROth-order witness-value product envelope
      `witnessValue_gate_envelope_prod` (built here), and the `∀ᵐ z` derivative domination via the
      BANKED, BASE-GENERAL `InnerDataEnvelope.witnessFieldDeriv_gate_envelope_prod`;
    • the outer bound legs (5)/(6) — the `s`-dominator `bound := const M` (`M` the `u`-capped Gaussian
      peak) with the `∀ᵐ s ∀ w` domination via the capped-ceiling pairing calc `intZ_dH_pairing_le`
      (the per-`s` inner content of `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped`,
      base-generalised to `Function.update y i w`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED, satisfiable analytic data into the exact leg
  shapes.  NONE proves `a₁ = R/6`, and proves NOTHING about `R/6`.  The base-`y` GATE/AMPLITUDE/
  ENVELOPE core is a genuine, satisfiable, non-vacuous INPUT (its Gaussian widths, on-gate sups, Levi
  domination, and gate dichotomy are the analytic content no measurability/integrability engine can
  manufacture), never the conclusion.  No `sorry` (header prose excepted), no `:= True`, no new axioms,
  no existing file edited.

  ── WHAT'S BANKED-vs-ENUMERATED (dont-undercredit findings).
    • THE BASE-`y` GATE ENVELOPE IS ALREADY BASE-GENERAL — NO LIFT NEEDED.  Both product envelopes
      `InnerDataEnvelope.witnessFieldDeriv_gate_envelope_prod` (first-order, for the `∀ᵐ z` derivative
      domination) and `WitnessDerivDomination.witnessFieldDeriv_gate_envelope` are stated at an
      ARBITRARY field point `p` (NOT base `0`); we instantiate `p := Function.update y i w'`, no
      re-proof.  The J4-439 ledger v2's "base-`y` envelope is an enumerated input" note UNDERSOLD the
      banked lemma: the analytic bound is base-general; only its inputs (on-gate sup, Levi Gaussian)
      are enumerated.
    • THE ZEROth-ORDER WITNESS-VALUE PRODUCT ENVELOPE `witnessValue_gate_envelope_prod` is NEW here —
      the mirror of `witnessFieldDeriv_gate_envelope_prod` for the witness VALUE, using the off-gate
      vanishing `vanVleckGatedWitness_offGate_eq_zero` (`gatedKernel_apply_of_notMem`, base-general).
    • THE OUTER BOUND legs (5)/(6) reuse the capped-ceiling pairing calc verbatim (the `s>0` inner body
      of `pairing_intervalIntegrable_lowerCapped`), the Gaussian product-integral + `u`-cap antitone
      lemmas fully banked; base-generalised to `Function.update y i w`.
    • THE THREAD-CONVERGENCE PROBE (the grounded first-order sup `C₁` of the sup family,
      `SupFamilyFirstOrder.baseSlotAmpDeriv1_grounded`).  That `C₁` is the on-gate sup of the base-slot
      first field-derivative at the CENTRE (base `0`), on `closedBall 0 ρ` — a BASE-`0` sup.  The
      on-gate sup this brick needs is at GENERAL base `Function.update y i w'`.  Base mismatch (exactly
      the mismatch pattern the joint carries hit): the grounded base-`0` `C₁` does NOT literally supply
      the base-`y` on-gate sup, so the sup family and the diff family do NOT yet converge at the
      lemma level.  The base-`y` on-gate sup remains an ENUMERATED carry (its base-`0` analogue is
      grounded, so it is groundable by the same compactness route once the base is generalised).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrozenHdiffLeg
import QIQTH.InnerDataEnvelope
import QIQTH.WitnessDerivDomination
import QIQTH.EveryCeilingFamilies
import QIQTH.CConvV2GaussianPairing
import QIQTH.CConvV2WitnessStar

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.WitnessMeasDeriv
open QIQTH.InnerDataEnvelope QIQTH.WitnessDerivDomination QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.FrozenDominatorLegs

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) The ZEROth-order witness-value product envelope (the base `z`-integrability leg).
    ############################################################################### -/

/-- **`vanVleckGatedWitness_offGate_eq_zero`.**  Off the base gate (`z ∉ K`) the witness VALUE is
    identically `0`: `vanVleckGatedWitness … τ p z = 0`, since `vanVleckGatedWitness = gatedKernel K S …`
    and `gatedKernel` vanishes when the base slot `z ∉ K` (`gatedKernel_apply_of_notMem`, base-general).
    The zeroth-order analogue of `witnessFieldDeriv_offGate_eq_zero`.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p z : Point n) (hz : z ∉ K) :
    vanVleckGatedWitness g gi hC hK S a b τ p z = 0 := by
  simp only [vanVleckGatedWitness]
  exact gatedKernel_apply_of_notMem K S _ τ p z (Or.inl hz)

/-- **★ `witnessValue_gate_envelope_prod` — THE ZEROth-ORDER PRODUCT ENVELOPE.**  The Gaussian product
    bound `‖W·L‖ ≤ (C₀·C_L)·G` for the witness VALUE times a scalar Levi factor `L`, by the OFF/ON-GATE
    dichotomy: off-gate (`z ∉ K`) `W … τ p z = 0` so the product is `0 ≤` the nonnegative RHS; on-gate
    (`z ∈ K`) the carried on-gate sup `|W| ≤ C₀` and the Levi Gaussian bound `|L| ≤ C_L·G` multiply to
    `(C₀·C_L)·G`.  One field-derivative order DOWN from `witnessFieldDeriv_gate_envelope_prod`; supplies
    the first-kernel base `z`-integrability of the reduced core.  Base-general (`p` arbitrary).  The
    on-gate sup `C₀` is a NAMED CARRY (the witness-value gate sup).  NOT `a₁ = R/6`. -/
theorem witnessValue_gate_envelope_prod (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p z : Point n) (L C₀ C_L G : ℝ)
    (hC₀ : 0 ≤ C₀) (hC_L : 0 ≤ C_L) (hG : 0 ≤ G)
    (hLev : |L| ≤ C_L * G)
    (hOn : z ∈ K → |vanVleckGatedWitness g gi hC hK S a b τ p z| ≤ C₀) :
    ‖vanVleckGatedWitness g gi hC hK S a b τ p z * L‖ ≤ (C₀ * C_L) * G := by
  by_cases hz : z ∈ K
  · rw [Real.norm_eq_abs, abs_mul]
    calc |vanVleckGatedWitness g gi hC hK S a b τ p z| * |L|
        ≤ C₀ * (C_L * G) := mul_le_mul (hOn hz) hLev (abs_nonneg _) hC₀
      _ = (C₀ * C_L) * G := by ring
  · rw [vanVleckGatedWitness_offGate_eq_zero g gi hC hK S a b τ p z hz, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hC₀ hC_L) hG

/-! ###############################################################################
    ### (B) The base-`y` z-level REDUCED CORE — mirror of `innerData_reducedCore_of_gateData`.
    ############################################################################### -/

/-- **★★ `innerDiffCore_of_gateData` — THE base-`y` z-LEVEL REDUCED CORE, DISCHARGED ONTO GATE/AMP/
    ENVELOPE DATA.**  Produces, a.e.-`s` and `∀ w ∈ snb`, the exact `∃ znb bnd` reduced-core bundle that
    `FrozenHdiffLeg.frozenLeg_hdiff` consumes, from a strictly-lighter base-`y` gate core `hGateCore`
    supplying: the nbhd `znb`, a positive Gaussian width `σ`, the three nonnegative sup constants
    `C₀`/`C₁`/`C_L`, the bare `z`-slice measurabilities of `W`/`Lev`/`dH`, the Levi Gaussian domination
    `|Lev| ≤ C_L·G_σ`, the zeroth-order on-gate sup `|W(update y i w)| ≤ C₀` (for the base
    integrability), the first-order on-gate sup `|dH(update y i w')| ≤ C₁` on `znb` (for the derivative
    domination), and the per-`z` GATE DICHOTOMY (carried).  DISCHARGES: the `∀ w'` product measurability
    (`.mul`), the base integrability (`Integrable.mono'` + `witnessValue_gate_envelope_prod` +
    `envelope_integrable`), the derivative product measurability (`.mul`), the dominator integrability
    (`envelope_integrable`, `bnd := (C₁·C_L)·gaussDdim σ`), and the `∀ᵐ z` derivative domination (the
    BANKED base-general `witnessFieldDeriv_gate_envelope_prod`).  Mirror of
    `InnerDataEnvelope.innerData_reducedCore_of_gateData` at base `y`, ONE order down.  NOT `a₁ = R/6`. -/
theorem innerDiffCore_of_gateData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (y : Point n) (i : Fin n) (m : ℕ) (snb : Set ℝ)
    (hGateCore : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₀ C₁ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, z ∈ K →
            |vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z| ≤ C₀) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z| ≤ C₁) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update y i w'))) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update y i w')) := by
  filter_upwards [hGateCore] with s hcore hmem w hw
  obtain ⟨znb, σ, C₀, C₁, C_L, hznb, hσ, hC₀, hC₁, hC_L,
      hWmeas, hLevimeas, hDHmeas, hLevi, hOn0, hOn1, hzGate⟩ := hcore hmem w hw
  refine ⟨znb, (fun z => (C₁ * C_L) * gaussDdim σ z), hznb, ?_, ?_, ?_, ?_, ?_, hzGate⟩
  · -- `∀ w'` product measurability : `.mul`.
    intro w'
    exact (hWmeas w').mul hLevimeas
  · -- base `z`-integrability : `Integrable.mono'` + the zeroth-order product envelope.
    refine Integrable.mono' (envelope_integrable σ hσ (C₀ * C_L)) ((hWmeas w).mul hLevimeas) ?_
    filter_upwards [hLevi, hOn0] with z hlev hon0
    exact witnessValue_gate_envelope_prod g gi hC hK S a b (u - s) (Function.update y i w) z
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      C₀ C_L (gaussDdim σ z) hC₀ hC_L (gaussDdim_nonneg _ _) hlev hon0
  · -- derivative product measurability : `.mul`.
    exact hDHmeas.mul hLevimeas
  · -- dominator integrability : the Gaussian envelope.
    exact envelope_integrable σ hσ (C₁ * C_L)
  · -- `∀ᵐ z` derivative domination : the BANKED base-general first-order product envelope.
    filter_upwards [hLevi, hOn1] with z hlev hon1
    intro w' hw'
    exact witnessFieldDeriv_gate_envelope_prod g gi hC hK S a b i (u - s)
      (Function.update y i w') z
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      C₁ C_L (gaussDdim σ z) hC₁ hC_L (gaussDdim_nonneg _ _) hlev (hon1 w' hw')

/-! ###############################################################################
    ### (C) The outer bound legs (5)/(6) — the capped-ceiling pairing calc, base-generalised.
    ############################################################################### -/

/-- **★ `intZ_dH_pairing_le` — THE PER-`s` INNER PAIRING BOUND, BASE-GENERALISED.**  For any base point
    `p` and `0 < s < u`, the inner `∫z` pairing of the first field-derivative kernel `dH` with the Levi
    factor is `u`-uniformly bounded:
      `‖∫z dH i (u−s) p z · Lev s z‖ ≤ CA·CF·gaussDdim (min wA wF · u) 0`,
    from the capped Gaussian domination `|dH i (u−s) p z| ≤ CA·gaussDdim (wA(u−s)) (0−z)` and the Levi
    Gaussian `|Lev s z| ≤ CF·gaussDdim (wF s) z`, via the two-Gaussian product integral
    (`gaussDdim_pairing_integral`) + the `u`-cap antitone peak bound (`gaussDdim_zero_antitone`,
    `abLowerW`).  The per-`s` inner body of `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped`
    at base `p` (instead of `0`).  NOT `a₁ = R/6`. -/
theorem intZ_dH_pairing_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (u s : ℝ) (p : Point n) (wA CA wF CF : ℝ)
    (hu : 0 < u) (hs0 : 0 < s) (hsu : s < u)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hAdom : ∀ z : Point n, |witnessFieldDeriv g gi hC hK S a b i (u - s) p z|
        ≤ CA * gaussDdim (wA * (u - s)) (0 - z))
    (hFdom : ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z) :
    ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) p z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
      ≤ CA * CF * gaussDdim (min wA wF * u) (0 : Point n) := by
  have hts : 0 < u - s := by linarith
  set M : ℝ := CA * CF * gaussDdim (min wA wF * u) (0 : Point n) with hMdef
  set Dz : Point n → ℝ :=
    fun z => (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) with hDzdef
  have hDz_int : Integrable Dz volume := by
    rw [hDzdef]
    exact (gaussDdim_pair_integrable (wA * (u - s)) (wF * s)).const_mul (CA * CF)
  have hpt : ∀ z : Point n,
      ‖witnessFieldDeriv g gi hC hK S a b i (u - s) p z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ Dz z := by
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    have hAz := hAdom z
    rw [gaussDdim_zero_sub] at hAz
    have hFz := hFdom z
    rw [hDzdef]
    calc |witnessFieldDeriv g gi hC hK S a b i (u - s) p z|
          * |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
        ≤ (CA * gaussDdim (wA * (u - s)) z) * (CF * gaussDdim (wF * s) z) :=
          mul_le_mul hAz hFz (abs_nonneg _) (mul_nonneg hCA (gaussDdim_nonneg _ _))
      _ = (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) := by ring
  have hpair_le : gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
      ≤ gaussDdim (min wA wF * u) (0 : Point n) :=
    gaussDdim_zero_antitone (min wA wF * u) (wA * (u - s) + wF * s)
      (mul_pos (lt_min hwA hwF) hu) (abLowerW wA u wF s hs0.le hsu.le)
  have hDz_le : ∫ z, Dz z ≤ M := by
    have hval : (∫ z, Dz z) = (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n) := by
      rw [hDzdef, integral_const_mul,
        gaussDdim_pairing_integral (wA * (u - s)) (wF * s) (mul_pos hwA hts) (mul_pos hwF hs0)]
    rw [hval, hMdef]
    calc (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
        ≤ (CA * CF) * gaussDdim (min wA wF * u) (0 : Point n) :=
          mul_le_mul_of_nonneg_left hpair_le (mul_nonneg hCA hCF)
      _ = CA * CF * gaussDdim (min wA wF * u) (0 : Point n) := by ring
  calc ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) p z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
      ≤ ∫ z, ‖witnessFieldDeriv g gi hC hK S a b i (u - s) p z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, Dz z :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hDz_int (ae_of_all _ hpt)
    _ ≤ M := hDz_le

/-- **★★ `frozenLeg_dominator` — FROZEN PROVIDER LEGS (5)/(6), DISCHARGED.**  The outer `s`-level
    dominator `bound := const M` (`M := CA·CF·gaussDdim (min wA wF · u) 0`, the `u`-capped Gaussian
    peak) together with its interval-integrability and the `∀ᵐ s ∀ w ∈ snb` domination
      `‖∫z dH i (u−s) (update y i w) z · Lev‖ ≤ M`,
    from the UNIFORM (over `snb`) capped Gaussian domination `hDHdomCapped` of `dH`, the banked Levi
    envelope `hFdomEvery`, and the Levi source vanishing `hFzero`.  `M` is `w`-independent (the capped
    domination is uniform in `w`), so `bound` is a genuine dominator; interval-integrability is
    `intervalIntegrable_const`.  Per-`s`: `s ≤ 0` kills the integrand (`hFzero`); `s > 0` fires the
    base-generalised pairing calc `intZ_dH_pairing_le`.  NOT `a₁ = R/6`. -/
theorem frozenLeg_dominator (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (y : Point n) (i : Fin n) (m : ℕ) (snb : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hDHdomCapped : ∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
            ≤ CA * gaussDdim (wA * τ) (0 - z)) :
    ∃ bound : ℝ → ℝ,
      IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
      (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
          ≤ bound s) := by
  have hεpos := epsSeq_pos m
  obtain ⟨wA, CA, hwA, hCA, hDom⟩ := hDHdomCapped (epsSeq m) hεpos
  obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
  refine ⟨fun _ => CA * CF * gaussDdim (min wA wF * u) (0 : Point n),
    intervalIntegrable_const, ?_⟩
  refine ae_of_all _ (fun s hmem w hw => ?_)
  rcases le_or_gt s 0 with hs0 | hs0
  · -- `s ≤ 0` : the Levi source vanishes, so the inner integral is `0`.
    have hzeroFun : (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
          (Function.update y i w) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs0 z, mul_zero]
    have hI0 : (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) = 0 := by
      rw [hzeroFun]; exact integral_zero (Point n) ℝ
    rw [hI0, norm_zero]
    exact mul_nonneg (mul_nonneg hCA hCF) (gaussDdim_nonneg _ _)
  · -- `s > 0` : the base-generalised pairing calc.
    have hmax : s ≤ max 0 (u - epsSeq m) := hmem.2
    have hslo : s ≤ u - epsSeq m := by
      rcases le_or_gt 0 (u - epsSeq m) with hd | hd
      · rwa [max_eq_right hd] at hmax
      · rw [max_eq_left hd.le] at hmax; exact absurd hmax (not_le.mpr hs0)
    have hu : 0 < u := by linarith
    have hsu : s < u := by linarith
    have hτlo : epsSeq m ≤ u - s := by linarith
    exact intZ_dH_pairing_le g gi hC hK S a b i u s (Function.update y i w) wA CA wF CF
      hu hs0 hsu hwA hCA hwF hCF
      (fun z => hDom w hw (u - s) hτlo (by linarith) z)
      (fun z => hFdom s hs0 hsu.le z)

/-! ###############################################################################
    ### (D) `frozenRemainderDiff_of_gateData` + `innerDiff_phase4` — the provider remainder shrunk.
    ############################################################################### -/

/-- **★★ `frozenRemainderDiff_of_gateData` — THE PROVIDER REMAINDER `hRemainderDiff`, DISCHARGED ONTO
    ONE base-`y` GATE/AMP/ENVELOPE CARRY.**  Produces the exact `hRemainderDiff` carry of
    `FrozenHdiffLeg.innerDiff_phase3` — the per-`(m,i,u,y)` bundle {snb, the dominator `bound`+`hbdd`
    (leg 5), the `∀ᵐ s` domination `hbound` (leg 6), the a.e.-`s` base-`y` z-level reduced core} — from
    the banked Levi carries `hFzero`/`hFdomEvery` and ONE combined base-`y` gate-data carry `hGateData`
    supplying, per `(m,i,u,y)`: the nbhd `snb`, the UNIFORM-over-`snb` capped Gaussian domination of
    `dH` (for legs 5/6 via `frozenLeg_dominator`), and the a.e.-`s` base-`y` gate core (for the z-level
    reduced core via `innerDiffCore_of_gateData`).  The dominator window and the differentiation
    line-nbhd stay coupled through the shared `snb`.  NOT `a₁ = R/6`. -/
theorem frozenRemainderDiff_of_gateData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n))
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGateData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (σ C₀ C₁ C_L : ℝ),
              znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C_L ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s)
                    (Function.update y i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z)
                volume ∧
              (∀ᵐ z ∂volume,
                |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
                  ≤ C_L * gaussDdim σ z) ∧
              (∀ᵐ z ∂volume, z ∈ K →
                |vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z| ≤ C₀) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
                |witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z| ≤ C₁) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w')))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
              znb ∈ 𝓝 w ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
              Integrable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              Integrable bnd volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w'))) := by
  intro m i u hu y hy
  obtain ⟨snb, hsnb, hDHdom, hGateCore⟩ := hGateData m i u hu y hy
  obtain ⟨bound, hbdd, hbound⟩ :=
    frozenLeg_dominator g gi hC hK S a b u y i m snb hFzero hFdomEvery hDHdom
  exact ⟨snb, bound, hsnb, hbdd, hbound,
    innerDiffCore_of_gateData g gi hC hK S a b u y i m snb hGateCore⟩

/-- **★★★ `innerDiff_phase4`.**  `FrozenHdiffLeg.innerDiff_phase3` with the provider remainder
    `hRemainderDiff` SUPPLIED INTERNALLY by `frozenRemainderDiff_of_gateData`: the frozen `hQ1` provider
    remainder SHRINKS to {snb-implicit} + ONE base-`y` GATE/AMPLITUDE/ENVELOPE carry `hGateData`.  Legs
    (5)/(6) (the outer dominator) and the z-level reduced core are DISCHARGED here; every OTHER carry is
    threaded exactly as `innerDiff_phase3`.  Pure composition; each carry satisfiable, non-vacuous,
    strictly lower level than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem innerDiff_phase4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointY : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ (w d : ℝ),
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update y i w) p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointYbase : ∀ (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWFDjointY : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hWitDomCappedY : ∀ (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V →
        ∀ Tc εₘ : ℝ, 0 < εₘ → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |vanVleckGatedWitness g gi hC hK S a b τ y z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hGateData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (σ C₀ C₁ C_L : ℝ),
              znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C_L ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s)
                    (Function.update y i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z)
                volume ∧
              (∀ᵐ z ∂volume,
                |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
                  ≤ C_L * gaussDdim σ z) ∧
              (∀ᵐ z ∂volume, z ∈ K →
                |vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z| ≤ C₀) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
                |witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z| ≤ C₁) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w')))) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.FrozenHdiffLeg.innerDiff_phase3 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont V hV
    hLeviJoint hWitJointY hWitJointYbase hWFDjointY hFzero hFdomEvery hWitDomCappedY
    (frozenRemainderDiff_of_gateData g gi hC hK S a b U V hFzero hFdomEvery hGateData)

end QIQTH.FrozenDominatorLegs

/-! ## THE PROVIDER LEDGER v3 — the per-leg table for the hQ1 frozen provider, remainder 3 → 1.

  `innerDiff_phase4` reproduces the per-`u` census `Tendsto` (= `innerDiff_phase1`'s conclusion) with
  the seven-leg frozen `hQ1` provider `hFrozenData` SHRUNK 7 → 1 (+ the enumerated GATE/AMP/ENVELOPE
  carry): legs (2)/(3)/(4) by `FrozenProviderLegs`, leg (7) by `FrozenHdiffLeg`, and now legs (5)/(6)
  + the z-level reduced core by this brick.

    leg          role                                        status          supplier
    ──────────   ─────────────────────────────────────────  ──────────────  ────────────────────────
    (1) snb      real-line nbhd 𝓝(y i)                      GATE-DATA       via `hGateData` existential
    (2) hFmeas   `∀w, s↦∫z W(u−s)(update y i w)·F` aesm       ★ DISCHARGED    `frozenLeg_hFmeas` (J4-438)
    (3) hFint    `s↦∫z W(u−s) y·F` interval-integrable        ★ DISCHARGED    `frozenLeg_hFint` (J4-438)
    (4) hF'meas  `s↦∫z dH i (u−s) y·F` aesm                   ★ DISCHARGED    `frozenLeg_hF'meas` (J4-438)
    (5) bound+hbdd  interval-integrable `s`-dominator         ★ DISCHARGED    `frozenLeg_dominator` =
                                                             (this brick)    `intervalIntegrable_const`
                                                                             (bound := const M)
    (6) hbound   `‖∫z dH…(update y i w)·F‖ ≤ bound s`          ★ DISCHARGED    `frozenLeg_dominator` =
                                                             (this brick)    `intZ_dH_pairing_le`
                                                                             (capped-ceiling pairing,
                                                                             base-generalised)
    (7) hdiff    outer `s`-level `HasDerivAt (∫z W)(∫z dH)`    ★ DISCHARGED    `frozenLeg_hdiff` (J4-439)
    z-core   the base-`y` z-level reduced core              ★ DISCHARGED    `innerDiffCore_of_gateData` =
                                                             (this brick)    `witnessValue_gate_envelope_
                                                                             prod` (base integ) +
                                                                             BANKED `witnessFieldDeriv_
                                                                             gate_envelope_prod` (deriv
                                                                             domination) + `envelope_
                                                                             integrable`; the gate
                                                                             dichotomy carried

  ⚠ VERDICT.  The frozen `hQ1` provider is now reducible to ONE enumerated base-`y` GATE/AMPLITUDE/
  ENVELOPE carry `hGateData` (per `(m,i,u,y)`: the nbhd `snb`, the uniform-over-`snb` capped Gaussian
  domination of `dH`, and the a.e.-`s` base-`y` gate core = bare z-slice measurabilities + positive
  width + nonnegative sups `C₀`/`C₁`/`C_L` + Levi Gaussian domination + witness-value / first-derivative
  on-gate sups + the per-`z` gate dichotomy) — the genuine analytic content no measurability /
  integrability / `HasDerivAt` engine can manufacture.

  ── BASE-`y` ENVELOPE OUTCOME (dont-undercredit).  The gate ENVELOPE is BASE-GENERAL, not base-`0`:
  both `InnerDataEnvelope.witnessFieldDeriv_gate_envelope_prod` (banked) and the new
  `witnessValue_gate_envelope_prod` are stated at an arbitrary field point `p := Function.update y i w'`.
  The J4-439 ledger v2's "base-`y` envelope is an enumerated input" note undersold the banked lemma:
  the Gaussian bound is base-general; only its INPUTS (on-gate sups, Levi Gaussian) are enumerated.

  ── THREAD-CONVERGENCE STATUS (the grounded first-order sup `C₁`).  The sup family's grounded first-
  order sup (`SupFamilyFirstOrder.baseSlotAmpDeriv1_grounded`) is the on-gate sup of the base-slot
  first field-derivative at the CENTRE (base `0`, on `closedBall 0 ρ`).  The on-gate sup THIS brick
  needs is at GENERAL base `Function.update y i w'`.  Base mismatch — the SAME pattern the joint
  carries hit — so the grounded base-`0` `C₁` does NOT literally supply the base-`y` on-gate sup: the
  sup family and the diff family do NOT yet converge at the lemma level.  The base-`y` on-gate sup
  stays an ENUMERATED carry inside `hGateData`, groundable by the same compactness route once the base
  is generalised.  (Honest: no fabricated convergence.)

  This brick proves NOTHING about `a₁ = R/6`; it certifies the hQ1 provider as reducible 7 → 1.
-/

section AxiomChecks
open QIQTH.FrozenDominatorLegs
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witnessValue_gate_envelope_prod
#print axioms innerDiffCore_of_gateData
#print axioms intZ_dH_pairing_le
#print axioms frozenLeg_dominator
#print axioms innerDiff_phase4
end AxiomChecks
