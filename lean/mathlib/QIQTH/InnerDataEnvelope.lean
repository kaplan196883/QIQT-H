/-
  InnerDataEnvelope — J4-427 (GROUP (2), the E2 SECOND-KERNEL GATE ENVELOPE, the hard-carry closure):
  the three remaining `hInnerData` carries of J4-426 (`InnerDataInstantiation.innerData_phase1`) —
  conj-1 (the nbhd `znb`), conj-3 (the first-kernel base integrability), conj-6 (the second-kernel
  Gaussian domination on `znb`) — discharged onto strictly-lighter GATE/AMPLITUDE/ENVELOPE data via the
  E2 second-kernel product envelope built here.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING about
  `R/6`.  `a₁ = R/6` remains CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable pointwise analytic data (the
  off-gate vanishing of `witnessFieldDeriv{,2}`, the Gaussian integrability `envelope_integrable`, the
  measurable products) into the exact reduced-core shape `innerData_phase1` consumes.  NONE proves
  `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, and never the conclusion.
  No `sorry` (header prose excepted), no `:= True`, no new axioms, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE E2 ENVELOPE — POWER COUNT.

  The two product kernels of `hInnerData` are `dH·Lev` (first, conj-3) and `dHH·Lev` (second, conj-6),
  with `dH := witnessFieldDeriv`, `dHH := witnessFieldDeriv2`, and
  `Lev z := leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0`.  Both admit the SAME dichotomy:

    • OFF-GATE (`z ∉ K`): the witness is identically `0` in the field slot, so BOTH `dH` and `dHH`
      vanish IDENTICALLY (`witnessFieldDeriv_offGate_eq_zero`, `witnessFieldDeriv2_offGate_eq_zero`,
      banked in `EngineInstantiation`).  The product is `0`, trivially `≤` a nonnegative Gaussian.

    • ON-GATE (`z ∈ K`): the germ-`C²` witness family gives an on-gate pointwise sup — `|dH| ≤ C₁`
      (first-order) / `|dHH| ≤ C₂` (second-order) — a scalar bound on the COMPACT gate.  The Levi
      factor carries the `z`-Gaussian decay `|Lev| ≤ C_L·G_σ(z)`.  So the product dominator is
      `(C₁·C_L)·G_σ(z)` (first) resp. `(C₂·C_L)·G_σ(z)` (second): x-free, Gaussian, INTEGRABLE.

  HONEST STATUS OF THE ON-GATE SUP `C₂` (and `C₁`).  It is a NEW NAMED CARRY, not a banked datum: it is
  the on-gate sup of the second field-derivative kernel over the field nbhd `znb`.  It JOINS the
  amplitude/gate sup family (the L1 `I3` / order-2 §A `witnessFieldDeriv2_gate_abs_le` bounds).  Its
  Levi partner `C_L` is groundable by `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated`
  (`|leviSeries| ≤ C_L·baseKernelW 2 0 = C_L·G_{2s}`).  ⟹  GROUP (2) closes to ENUMERATED CARRIES ONLY.

  ── WHAT LANDS (this file, ns `QIQTH.InnerDataEnvelope`).
    • `witnessFieldDeriv2_gate_envelope` — ★ THE E2 SECOND-KERNEL PRODUCT ENVELOPE.  Off/on-gate
      dichotomy ⟹ `‖dHH·L‖ ≤ (C₂·C_L)·G` from the on-gate sup `|dHH| ≤ C₂` and `|L| ≤ C_L·G`.
    • `witnessFieldDeriv_gate_envelope_prod` — the first-order analogue (for conj-3):
      `‖dH·L‖ ≤ (C₁·C_L)·G`.
    • `innerData_reducedCore_of_gateData` — ★★ conj-1/3/6 DISCHARGED: from the phase-2 gate/amplitude/
      envelope core produces phase 1's reduced core (conj-3 via `Integrable.mono'` + the first-order
      product envelope; conj-6 via the E2 product envelope; conj-1 the carried nbhd).
    • `innerData_phase2` — ★★★ the full `hInnerData` bundle from the phase-2 core (chain through
      `innerData_phase1`).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerDataInstantiation

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.WitnessDerivDomination QIQTH.ResidueBound
open QIQTH.InnerDataInstantiation
open scoped Interval Topology BigOperators

namespace QIQTH.InnerDataEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE E2 SECOND-KERNEL PRODUCT ENVELOPE (and its first-order sibling).
    ############################################################################### -/

/-- **★ `witnessFieldDeriv2_gate_envelope` — THE E2 SECOND-KERNEL PRODUCT ENVELOPE.**  The Gaussian
    product bound `‖dHH·L‖ ≤ (C₂·C_L)·G` for the second field-derivative kernel times a scalar Levi
    factor `L`, by the OFF/ON-GATE DICHOTOMY:
      • `z ∉ K` — `dHH … i τ p z = 0` (`witnessFieldDeriv2_offGate_eq_zero`), so the product is `0`,
        `≤` the nonnegative RHS;
      • `z ∈ K` — the carried on-gate sup `|dHH … i τ p z| ≤ C₂` and the Levi Gaussian bound
        `|L| ≤ C_L·G` multiply to `(C₂·C_L)·G`.
    One field-derivative order up from `witnessFieldDeriv_gate_envelope_prod`.  The on-gate sup `C₂` is a
    NAMED CARRY (the second-order gate sup, joining the amplitude/gate sup family).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_gate_envelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (L C₂ C_L G : ℝ)
    (hC₂ : 0 ≤ C₂) (hC_L : 0 ≤ C_L) (hG : 0 ≤ G)
    (hLev : |L| ≤ C_L * G)
    (hOn : z ∈ K → |witnessFieldDeriv2 g gi hC hK S a b i τ p z| ≤ C₂) :
    ‖witnessFieldDeriv2 g gi hC hK S a b i τ p z * L‖ ≤ (C₂ * C_L) * G := by
  by_cases hz : z ∈ K
  · rw [Real.norm_eq_abs, abs_mul]
    calc |witnessFieldDeriv2 g gi hC hK S a b i τ p z| * |L|
        ≤ C₂ * (C_L * G) := mul_le_mul (hOn hz) hLev (abs_nonneg _) hC₂
      _ = (C₂ * C_L) * G := by ring
  · rw [witnessFieldDeriv2_offGate_eq_zero g gi hC hK S a b i τ p z hz, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hC₂ hC_L) hG

/-- **`witnessFieldDeriv_gate_envelope_prod` — THE FIRST-ORDER PRODUCT ENVELOPE (for conj-3).**  The
    same off/on-gate dichotomy one field-derivative order down: off-gate `dH … i τ p z = 0`
    (`witnessFieldDeriv_offGate_eq_zero`); on-gate the carried sup `|dH| ≤ C₁` times `|L| ≤ C_L·G`.
    Yields `‖dH·L‖ ≤ (C₁·C_L)·G`, the x-free integrable Gaussian dominator for the first-kernel base
    integrability.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_gate_envelope_prod (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (L C₁ C_L G : ℝ)
    (hC₁ : 0 ≤ C₁) (hC_L : 0 ≤ C_L) (hG : 0 ≤ G)
    (hLev : |L| ≤ C_L * G)
    (hOn : z ∈ K → |witnessFieldDeriv g gi hC hK S a b i τ p z| ≤ C₁) :
    ‖witnessFieldDeriv g gi hC hK S a b i τ p z * L‖ ≤ (C₁ * C_L) * G := by
  by_cases hz : z ∈ K
  · rw [Real.norm_eq_abs, abs_mul]
    calc |witnessFieldDeriv g gi hC hK S a b i τ p z| * |L|
        ≤ C₁ * (C_L * G) := mul_le_mul (hOn hz) hLev (abs_nonneg _) hC₁
      _ = (C₁ * C_L) * G := by ring
  · rw [witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i τ p z hz, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hC₁ hC_L) hG

/-! ###############################################################################
    ### conj-1/3/6 DISCHARGE — the phase-2 gate/amplitude/envelope core.
    ############################################################################### -/

/-- **★★ `innerData_reducedCore_of_gateData` — conj-1/3/6 DISCHARGED ONTO GATE/AMPLITUDE/ENVELOPE DATA.**
    Produces the exact reduced core `innerData_phase1` demands (its `hRedCore` argument) from a
    strictly-lighter phase-2 core `hGateCore` supplying, a.e.-`s` and `∀ w ∈ snb`:  the nbhd `znb`
    (conj-1), a positive Gaussian width `σ`, the three nonnegative sup constants `C₁`/`C₂`/`C_L`, the
    bare z-slice measurabilities of `dH`/`Lev`/`dHH` (carried onward to conj-2/4), the Levi Gaussian
    domination `|Lev| ≤ C_L·G_σ`, the first-order on-gate sup `|dH(w)| ≤ C₁` (for conj-3), the
    second-order on-gate sup `|dHH(w')| ≤ C₂` on `znb` (for conj-6), and the per-`z` GATE DICHOTOMY
    (carried onward to conj-7).  DISCHARGES: conj-3 (`Integrable(dH·Lev)` via `Integrable.mono'` +
    `witnessFieldDeriv_gate_envelope_prod` + `envelope_integrable`) and conj-6 (the `dHH·Lev` Gaussian
    domination on `znb` via `witnessFieldDeriv2_gate_envelope`, dominator constant `C := C₂·C_L`).
    Every input is satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem innerData_reducedCore_of_gateData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (snb : Set ℝ)
    (hGateCore : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₁ C₂ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, z ∈ K →
            |witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z| ≤ C₁) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hC hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w'))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (C σ : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          Integrable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ C * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hC hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w')) := by
  intro m i u hu
  filter_upwards [hGateCore m i u hu] with s hcore hmem w hw
  obtain ⟨znb, σ, C₁, C₂, C_L, hznb, hσ, hC₁, hC₂, hC_L,
      hWFDzmeas, hLeviZmeas, hWFD2zmeas, hLevi, hOn1, hOn2, hzGate⟩ := hcore hmem w hw
  refine ⟨znb, C₂ * C_L, σ, hznb, hσ, hWFDzmeas, hLeviZmeas, hWFD2zmeas, ?_, ?_, hzGate⟩
  · -- conj-3 : first-kernel base integrability via `Integrable.mono'` + first-order product envelope.
    refine Integrable.mono' (envelope_integrable σ hσ (C₁ * C_L))
      ((hWFDzmeas w).mul hLeviZmeas) ?_
    filter_upwards [hLevi, hOn1] with z hlev hon1
    exact witnessFieldDeriv_gate_envelope_prod g gi hC hK S a b i (u - s)
      (Function.update (0 : Point n) i w) z
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      C₁ C_L (gaussDdim σ z) hC₁ hC_L (gaussDdim_nonneg _ _) hlev hon1
  · -- conj-6 : second-kernel Gaussian domination on `znb` via the E2 product envelope.
    filter_upwards [hLevi, hOn2] with z hlev hon2
    intro w' hw'
    exact witnessFieldDeriv2_gate_envelope g gi hC hK S a b i (u - s)
      (Function.update (0 : Point n) i w') z
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      C₂ C_L (gaussDdim σ z) hC₂ hC_L (gaussDdim_nonneg _ _) hlev (hon2 w' hw')

/-- **★★★ `innerData_phase2` — THE FULL `hInnerData` BUNDLE FROM THE PHASE-2 GATE/AMPLITUDE/ENVELOPE
    CORE.**  Chains `innerData_reducedCore_of_gateData` (conj-1/3/6) into `innerData_phase1`
    (conj-2/4/5/7) to produce the exact `hInnerData` carry of `W2Finish.w2_hdiff` (equivalently the V2
    carry of `TerminalCoverage.hdiff_threaded` / `truncatedDuhamelCore_threaded_v2`), for the true
    ρ-scaled chart witness, from ONE phase-2 core `hGateCore`.  That core supplies only ENUMERATED gate/
    amplitude/envelope carries (bare z-slice measurabilities, a positive Gaussian width, three
    nonnegative sup constants `C₁`/`C₂`/`C_L`, the Levi Gaussian domination, the first/second-order
    on-gate sups, the per-`z` gate dichotomy).  Every input is satisfiable, non-vacuous, none the
    conclusion.  NOT `a₁ = R/6`. -/
theorem innerData_phase2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (snb : Set ℝ)
    (hGateCore : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₁ C₂ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, z ∈ K →
            |witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z| ≤ C₁) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hC hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w'))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            HasDerivAt (fun w' => witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
              (witnessFieldDeriv2 g gi hC hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w') :=
  innerData_phase1 g gi hC hK S a b U snb
    (innerData_reducedCore_of_gateData g gi hC hK S a b U snb hGateCore)

end QIQTH.InnerDataEnvelope

/-! ## GROUP (2) FINAL — the honest ledger.

  `innerData_phase2` supplies the ENTIRE `hInnerData` bundle (all seven conjuncts, per `(m,i,u,s,w)`)
  that `W2Finish.w2_hdiff` consumes, from ONE phase-2 core `hGateCore`.  Combined with J4-426
  (`innerData_phase1`, which discharged conj-2/4/5/7), GROUP (2) is now reduced to the following
  ENUMERATED INPUT CARRIES ONLY — there is NO remaining analytic conjunct left as an obligation:

    (G2-a)  the bare z-slice measurabilities of `dH`/`Lev`/`dHH`  [measurability family];
    (G2-b)  a positive Gaussian width `σ`                         [width datum];
    (G2-c)  `C₁ ≥ 0` — the FIRST-order on-gate sup `|dH(w)| ≤ C₁` [amplitude/gate sup family, I3];
    (G2-d)  `C₂ ≥ 0` — the SECOND-order on-gate sup `|dHH(w')| ≤ C₂` on `znb`
                                                                   [amplitude/gate sup family, NEW];
    (G2-e)  `C_L ≥ 0` — the Levi Gaussian domination `|Lev| ≤ C_L·G_σ`
                                                    [Levi domination family; groundable by
                                                     `leviSeries_gatedWitnessN1_dominated`];
    (G2-f)  the nbhd `znb ∈ 𝓝 w`                                  [conj-1 nbhd datum];
    (G2-g)  the per-`z` GATE DICHOTOMY (`z ∉ K ∨ on-gate C¹ PdiffAt`)  [gate C¹ family].

  ⚠  GROUP (2) = ENUMERATED INPUT CARRIES ONLY.  This brick does NOT prove `a₁ = R/6`, and makes NO
  claim of unconditionality.  It converts the last three group-(2) `hInnerData` conjuncts (conj-1/3/6)
  from analytic OBLIGATIONS into named gate/amplitude/envelope SUP CARRIES that join the existing sup
  and domination families.  `a₁ = R/6` remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.InnerDataEnvelope
#print axioms witnessFieldDeriv2_gate_envelope
#print axioms witnessFieldDeriv_gate_envelope_prod
#print axioms innerData_reducedCore_of_gateData
#print axioms innerData_phase2
end AxiomChecks
