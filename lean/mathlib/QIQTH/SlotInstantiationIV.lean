/-
  SlotInstantiationIV — J4-421 (Part B, tranche (a) phase 4): the `hcomp` COMPARISON LEG at the true
  ρ-scaled chart witness — the locus of the geometric content in group (1), continuing
  `SlotInstantiationI` (phase 1), `SlotInstantiationII` (phase 2, the `IchartResidual` witness) and
  `SlotInstantiationIII` (phase 3, the Lipschitz/measurability/integrability carries).

  ★ THE `hcomp` SLOT.  `GpowClosure.leviSecondPairing_inner_bound_concrete` demands the comparison-leg
  bound
      ‖∫_{(collar (c√τ))ᶜ} (Ichart z − hessGaussFactor i τ z · qc z)‖ ≤ Bcomp/√τ,
  at `Ichart := IchartResidual` (phase 2) and `qc := chartAmp·F` (phase 1).  The banked discharge is
  `SliverAssemblyMatched.comparison_leg_of_dom` (re-exported as `GpowClosure.hcomp_concrete` /
  `SlotDischarges.hcomp_slot_of_dom`): from an off-collar dominator `D` with
    (i)  `IntegrableOn (Ichart − hessGaussFactor·qc) (collar (c√τ))ᶜ`,
    (ii) `IntegrableOn D (collar (c√τ))ᶜ`,
    (iii) `‖Ichart − hessGaussFactor·qc‖ ≤ D`  a.e. off collar,
    (iv) `∫_{(collar (c√τ))ᶜ} D ≤ Bcomp/√τ`,
  the bound follows.

  ★ WHAT THIS BRICK DISCHARGES (WIRING) vs CARRIES (GEOMETRY).
    • Leg (i) — `hcompDiff_int_residual` — is DISCHARGED as pure WIRING: `IchartResidual` is off-collar
      integrable (phase 3, `hIchart_int_final`), and `hessGaussFactor·qc` is integrable full-space
      (`hessGauss_qc_integrable`: `hessGaussFactor_integrable` × the bounded `qc = chartAmp·F` via
      `Integrable.mul_bdd`), so their difference is off-collar integrable by `IntegrableOn.sub`.
    • Legs (ii)–(iv) — the pointwise dominator `D`, its off-collar integrability, the pointwise domination
      of `IchartResidual − hessGaussFactor·qc` by `D`, and its `Bcomp/√τ` moment — are the genuine
      GEOMETRIC CONTENT and are CARRIED honestly (`hcomp_residual_of_dom` takes them as hypotheses).  The
      moment (iv) is SATISFIABLE via the width-generic cubic-Hessian Gaussian moment
      `SliverAssemblyMatched.cubic_gaussian_moment_witness` (the `‖z‖³·G` family), once the chart-native
      form `IchartResidual =_{off collar} hessCoeff·G^chart·qc` is exhibited — see the obstruction note.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It reduces
  the `hcomp` slot to the three named off-collar geometric carries (dominator `D` + its integrability +
  its domination + its `Bcomp/√τ` moment); leg (i) is the only part that was pure algebra/wiring and it
  is DISCHARGED.  The chart-native off-collar FORM of `IchartResidual` (the true geometric input) is NOT
  banked and is the recorded obstruction.  No `sorry`, no `:= True`, no new axioms; std-3.  See the
  `## PHASE 4 COVERAGE` block for the honest ledger.
-/
import QIQTH.SlotInstantiationIII

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII QIQTH.SlotInstantiationIII
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationIV

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### helper — integrability of `hessGaussFactor·qc` for a bounded comparison amplitude.
    ############################################################################### -/

/-- **★ helper — `hessGauss_qc_integrable`.**  The Hessian-Gaussian factor times ANY GLOBALLY BOUNDED,
    a.e.-strongly-measurable comparison amplitude `qc` is (full-space) integrable:
      `Integrable (fun z => hessGaussFactor i τ z · qc z)`.
    Route: the banked `SliverTailMatched.hessGaussFactor_integrable` (the factor is integrable) combined
    with the `Integrable.mul_bdd` bounded-multiplier rule (`‖qc‖ ≤ Mqc`).  This is the integrability
    supplier for the `hessGaussFactor·qc` half of the comparison-leg difference — pure wiring, no moment
    analysis.  ⚠ NOT `a₁ = R/6`. -/
theorem hessGauss_qc_integrable (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (qc : Point n → ℝ) (Mqc : ℝ)
    (hqcmeas : AEStronglyMeasurable qc volume)
    (hqcbdd : ∀ z, ‖qc z‖ ≤ Mqc) :
    Integrable (fun z => hessGaussFactor i τ z * qc z) volume :=
  (hessGaussFactor_integrable τ hτ i).mul_bdd hqcmeas (ae_of_all _ hqcbdd)

/-! ###############################################################################
    ### B-field 10 — the comparison-leg difference integrability (leg (i), WIRING).
    ############################################################################### -/

/-- **★★ B (leg (i), DISCHARGED) — `hcompDiff_int_residual`.**  THE OFF-COLLAR INTEGRABILITY of the
    comparison-leg difference `IchartResidual − hessGaussFactor·qc`, at the phase-2 witness, discharged
    as pure WIRING:
      • `IchartResidual` is off-collar integrable (phase 3's `hIchart_int_final`, here taken as the input
        `hIchart_int`), AND
      • `hessGaussFactor·qc` is (full-space, hence off-collar) integrable for the bounded `qc`
        (`hessGauss_qc_integrable`),
    so the difference is off-collar integrable by `IntegrableOn.sub`.  This is EXACTLY the
    `hcompDiff_int` leg consumed by `SliverAssemblyMatched.comparison_leg_of_dom` / `hcomp_concrete`,
    with the chart-native `Ichart := IchartResidual`.  ⚠ NOT `a₁ = R/6`. -/
theorem hcompDiff_int_residual (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (qc : Point n → ℝ) (Mqc : ℝ)
    (hqcmeas : AEStronglyMeasurable qc volume) (hqcbdd : ∀ z, ‖qc z‖ ≤ Mqc)
    (hIchart_int : IntegrableOn (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume) :
    IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * qc z) (collar (c * Real.sqrt τ))ᶜ volume :=
  hIchart_int.sub ((hessGauss_qc_integrable τ hτ i qc Mqc hqcmeas hqcbdd).integrableOn)

/-! ###############################################################################
    ### B-field 11 — the `hcomp` comparison-leg slot (leg (i) discharged, (ii)–(iv) carried).
    ############################################################################### -/

/-- **★★★ B (slot `hcomp`, REDUCED) — `hcomp_residual_of_dom`.**  THE COMPARISON-LEG SLOT of
    `GpowClosure.leviSecondPairing_inner_bound_concrete` at the concrete witness
    `Ichart := IchartResidual`, `R := c√τ`:
      ‖∫_{(collar (c√τ))ᶜ} (IchartResidual z − hessGaussFactor i τ z · qc z)‖ ≤ Bcomp/√τ.
    Leg (i) (`hcompDiff_int`) is DISCHARGED internally via `hcompDiff_int_residual` (WIRING: the phase-3
    off-collar integrability of `IchartResidual` + the bounded-`qc` integrability of `hessGaussFactor·qc`).
    Legs (ii)–(iv) — the off-collar dominator `D`, its integrability `hDint`, the a.e. domination `hdom`,
    and the `Bcomp/√τ` moment `hmom` — are the GEOMETRIC CONTENT, CARRIED as hypotheses (the moment
    satisfiable via `SliverAssemblyMatched.cubic_gaussian_moment_witness`).  Route: the banked
    `SlotDischarges.hcomp_slot_of_dom` (= `GpowClosure.hcomp_concrete` at `R := c√τ`).  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_residual_of_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ)
    (qc D : Point n → ℝ) (Mqc Bcomp : ℝ)
    (hqcmeas : AEStronglyMeasurable qc volume) (hqcbdd : ∀ z, ‖qc z‖ ≤ Mqc)
    (hIchart_int : IntegrableOn (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume)
    (hDint : IntegrableOn D (collar (c * Real.sqrt τ))ᶜ volume)
    (hdom : ∀ᵐ z ∂(volume.restrict (collar (c * Real.sqrt τ))ᶜ),
      ‖IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * qc z‖ ≤ D z)
    (hmom : (∫ z in (collar (c * Real.sqrt τ))ᶜ, D z) ≤ Bcomp / Real.sqrt τ) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * qc z)‖ ≤ Bcomp / Real.sqrt τ :=
  QIQTH.SlotDischarges.hcomp_slot_of_dom τ i qc
    (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s) D c Bcomp
    (hcompDiff_int_residual g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ qc Mqc
      hqcmeas hqcbdd hIchart_int)
    hDint hdom hmom

/-! ###############################################################################
    ### PACKAGE — the phase-4 conjunction (phase 3 ∧ the `hcomp` comparison leg).
    ############################################################################### -/

/-- **★★★ B (phase-4 package) — `slotInstantiation_phase4`.**  The conjunction of the group-(1) slot
    carries discharged through phase 4, at the true ρ-scaled chart witness (built on
    `slotInstantiation_phase3`), given the enumerated factor/Gaussian-domination carries AND the three
    off-collar comparison-leg geometric carries `D`/`hDint`/`hdom`/`hmom`:
      • phase 3 (`h0`, `hgate`, `hoff`, `hIchart_int`, `hqz`, `hqc`, `hqzmeas`, `hqcmeas`), AND
      • `hcomp` (the comparison leg — via `hcomp_residual_of_dom`, at `Ichart := IchartResidual`,
        `qc := chartAmp·F`; leg (i) discharged as wiring, legs (ii)–(iv) carried).
    The bounded-`qc` carry `‖chartAmp·F‖ ≤ M_A·M_F` is discharged inline from the phase-3 sup carries
    `hMA`/`hMF`; the off-collar integrability of `IchartResidual` and its measurability are extracted
    from the phase-3 result.  All are VERBATIM arguments of
    `GpowClosure.leviSecondPairing_inner_bound_concrete` at the same concrete witness.  The ONLY
    remaining group-(1) residue is `hf2bound`/`hf3bound` (the gradient/mass Gaussian-moment ABSOLUTE
    dominators — J4-422) plus the three comparison-leg geometric carries here (the chart-native form of
    `IchartResidual` off collar).  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hChr hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ0 : 0 < τ) (hττ₀ : τ < τ₀) (hs0 : 0 < s) (hsT : s ≤ T)
    (hcr : c * Real.sqrt τ < r₀)
    (hKcover : ∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K)
    -- factor sup / Lipschitz carries (feed both `hqz` and `hqc`):
    (M_ρ M_A M_F L_ρ L_A L_F : ℝ)
    (hMρnn : 0 ≤ M_ρ) (hMAnn : 0 ≤ M_A) (hMFnn : 0 ≤ M_F)
    (hLρnn : 0 ≤ L_ρ) (hLAnn : 0 ≤ L_A) (hLFnn : 0 ≤ L_F)
    (hMρ : ∀ τ z, |rhoRatio g gi hChr hK τ z| ≤ M_ρ)
    (hMA : ∀ τ z, |chartAmp g gi hChr hK a b τ z 0| ≤ M_A)
    (hMF : ∀ s w, |F s w 0| ≤ M_F)
    (hLρ : ∀ τ z w, |rhoRatio g gi hChr hK τ z - rhoRatio g gi hChr hK τ w| ≤ L_ρ * dist z w)
    (hLA : ∀ τ z w,
      |chartAmp g gi hChr hK a b τ z 0 - chartAmp g gi hChr hK a b τ w 0| ≤ L_A * dist z w)
    (hLF : ∀ s z w, |F s z 0 - F s w 0| ≤ L_F * dist z w)
    -- the three Gaussian-domination carries (the census shape):
    (Cw w₁ C₂ w₂ C₃ w₃ : ℝ) (hCw : 0 ≤ Cw) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hWmeas : AEStronglyMeasurable
      (fun z => witnessSecondXDeriv g gi hChr hK S a b i τ z * F s z 0) volume)
    (hWdom : ∀ z, |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ Cw * gaussDdim w₁ z)
    (h2dom : ∀ z, |z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z| ≤ C₂ * gaussDdim w₂ z)
    (h3dom : ∀ z, |gaussDdim τ z * data.A2amp τ z| ≤ C₃ * gaussDdim w₃ z)
    -- the comparison-leg geometric carries (legs (ii)–(iv)):
    (D : Point n → ℝ) (Bcomp : ℝ)
    (hDint : IntegrableOn D (collar (c * Real.sqrt τ))ᶜ volume)
    (hdom : ∀ᵐ z ∂(volume.restrict (collar (c * Real.sqrt τ))ᶜ),
      ‖IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hChr hK a b τ z 0 * F s z 0)‖ ≤ D z)
    (hmom : (∫ z in (collar (c * Real.sqrt τ))ᶜ, D z) ≤ Bcomp / Real.sqrt τ) :
    -- phase 3:
    ((((rhoRatio g gi hChr hK τ 0 * chartAmp g gi hChr hK a b τ 0 0) * F s 0 0
        = chartAmp g gi hChr hK a b τ 0 0 * F s 0 0)
    ∧ (∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    ∧ (∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
        witnessSecondXDeriv g gi hChr hK S a b i τ z * F s z 0
          = IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s z
            + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
            + gaussDdim τ z * data.A2amp τ z * F s z 0)
    ∧ IntegrableOn (IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume)
    ∧ (∀ z w : Point n,
        |(rhoRatio g gi hChr hK τ z * chartAmp g gi hChr hK a b τ z 0) * F s z 0
            - (rhoRatio g gi hChr hK τ w * chartAmp g gi hChr hK a b τ w 0) * F s w 0|
          ≤ (M_ρ * M_A * L_F + (M_ρ * L_A + M_A * L_ρ) * M_F) * dist z w)
    ∧ (∀ z w : Point n,
        |chartAmp g gi hChr hK a b τ z 0 * F s z 0 - chartAmp g gi hChr hK a b τ w 0 * F s w 0|
          ≤ (M_A * L_F + M_F * L_A) * dist z w)
    ∧ AEStronglyMeasurable
        (fun z => (rhoRatio g gi hChr hK τ z * chartAmp g gi hChr hK a b τ z 0) * F s z 0) volume
    ∧ AEStronglyMeasurable
        (fun z => chartAmp g gi hChr hK a b τ z 0 * F s z 0) volume)
    -- phase 4 (the comparison leg):
    ∧ ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hChr hK a b τ z 0 * F s z 0))‖
        ≤ Bcomp / Real.sqrt τ := by
  have p3 := slotInstantiation_phase3 g gi hChr hK h0K S a b F i T τ₀ r₀ c data τ s
    hτ0 hττ₀ hs0 hsT hcr hKcover M_ρ M_A M_F L_ρ L_A L_F
    hMρnn hMAnn hMFnn hLρnn hLAnn hLFnn hMρ hMA hMF hLρ hLA hLF
    Cw w₁ C₂ w₂ C₃ w₃ hCw hC₂ hC₃ hWmeas hWdom h2dom h3dom
  refine ⟨p3, ?_⟩
  -- extract the two phase-3 outputs the comparison leg consumes.
  have hIce : IntegrableOn (IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s)
      (collar (c * Real.sqrt τ))ᶜ volume := p3.1.2.2.2
  have hqcme : AEStronglyMeasurable
      (fun z => chartAmp g gi hChr hK a b τ z 0 * F s z 0) volume := p3.2.2.2.2
  -- the bounded-`qc` carry, discharged from the phase-3 sup carries.
  have hqcbdd : ∀ z, ‖chartAmp g gi hChr hK a b τ z 0 * F s z 0‖ ≤ M_A * M_F := fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMA τ z) (hMF s z) (abs_nonneg _) hMAnn
  exact hcomp_residual_of_dom g gi hChr hK S a b F i T τ₀ r₀ c data τ s hτ0
    (fun z => chartAmp g gi hChr hK a b τ z 0 * F s z 0) D (M_A * M_F) Bcomp
    hqcme hqcbdd hIce hDint hdom hmom

end QIQTH.SlotInstantiationIV

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationIV
#print axioms hessGauss_qc_integrable
#print axioms hcompDiff_int_residual
#print axioms hcomp_residual_of_dom
#print axioms slotInstantiation_phase4
end AxiomChecks

/-! ###############################################################################
    ## PHASE 4 COVERAGE  (J4-421, Part B, tranche (a))
    ###############################################################################

  FIELDS DISCHARGED / REDUCED (at the true ρ-scaled chart witness, `S`-generic; building on phases 1-3):
    • `hcomp` (comparison leg) — ★ THE LOCUS OF THE GEOMETRIC CONTENT — REDUCED via
      `hcomp_residual_of_dom` (route: `SlotDischarges.hcomp_slot_of_dom` =
      `GpowClosure.hcomp_concrete` = `SliverAssemblyMatched.comparison_leg_of_dom` at `R := c√τ`), with
      the four legs split as follows:
        (i)   `hcompDiff_int` (off-collar integrability of `IchartResidual − hessGaussFactor·qc`) —
              DISCHARGED as pure WIRING (`hcompDiff_int_residual`): `IntegrableOn.sub` of phase 3's
              `hIchart_int_final` and `hessGauss_qc_integrable` (banked `hessGaussFactor_integrable` ×
              the bounded `qc = chartAmp·F` via `Integrable.mul_bdd`).  The bounded-`qc` carry
              `‖chartAmp·F‖ ≤ M_A·M_F` is discharged inline from the phase-3 sup carries `hMA`/`hMF`.
        (ii)  `hDint` (off-collar integrability of the dominator `D`) — CARRIED (geometric).
        (iii) `hdom` (a.e. `‖IchartResidual − hessGaussFactor·qc‖ ≤ D` off collar) — CARRIED (geometric).
        (iv)  `hmom` (`∫_{(collar (c√τ))ᶜ} D ≤ Bcomp/√τ`) — CARRIED (geometric); SATISFIABLE via the
              width-generic cubic-Hessian Gaussian moment `cubic_gaussian_moment_witness` (the `‖z‖³·G`
              family scaling to `O(τ^{−1/2})`).
    • (carried through from phases 1-3) `h0`, `hgate`, `Ichart`, `hoff`, `hIchart_int`, `hqz`, `hqc`,
      `hqzmeas`, `hqcmeas` — all bundled into the phase-4 package via `slotInstantiation_phase3`.

  DONT-UNDERCREDIT CHECK (the J4-419 note verified).  Grepped the banked sliver machinery
  (`SliverAssemblyMatched`, `SliverOffCollarMatched`) BEFORE building:
    · `SliverAssemblyMatched.comparison_leg_of_dom` / `.sliver_term1_full_matched` thread an ABSTRACT
      `Ichart` and only prove the `hcomp` bound FROM an off-collar dominator `D` — they do NOT bound the
      difference for the CONCRETE `IchartResidual`.  So the banked bounds do NOT instantiate at
      `IchartResidual` for free; `hcomp_residual_of_dom` genuinely wires `IchartResidual` into that
      abstract discharge (the only free part is leg (i), the integrability, which IS pure wiring).
    · `SliverOffCollarMatched.chartNative_leading_sub_hess`(`_norm_le`) bounds
      `H^chart·q − H·q = hessCoeff·(G^chart − G)·q` where `H^chart·q := (z_i²−2τ)/(4τ²)·G_τ(w)·q` is the
      CHART-NATIVE LEADING integrand — a DIFFERENT object from `IchartResidual`.  It supplies the cubic
      dominator/moment for legs (iii)/(iv) ONLY ONCE the identity `IchartResidual =_{off collar}
      hessCoeff·G^chart·qc` is available.  That identity is NOT banked — see the obstruction below.

  ─────────────────────────────────────────────────────────────────────────────
  ★ RECORDED OBSTRUCTION (for a Sol consult) — the chart-native off-collar form of `IchartResidual`.
  ─────────────────────────────────────────────────────────────────────────────
  Legs (iii)/(iv) require the pointwise dominator `D` with `‖IchartResidual − hessGaussFactor·qc‖ ≤ D`
  off collar AND `∫ D ≤ Bcomp/√τ`.  The banked cubic machinery (`chartNative_leading_sub_hess_norm_le`
  + `cubic_gaussian_moment_witness`) delivers exactly this IF one first proves the OFF-COLLAR IDENTITY
      `IchartResidual z = (z_i²−2τ)/(4τ²)·gaussDdim τ (chartArg z)·qc z`   (= `H^chart·qc`, chart-native),
  i.e. that `witnessSecondXDeriv·F − f₂ − f₃` equals the chart-native LEADING term off the collar.  The
  ON-collar analogue is banked (`SliverBoundOnCollar.sliverIntegrand_on_collar` /
  `GpowClosure.hon_concrete`, giving `witnessSecondXDeriv·F = hessGaussFactor·qz + f₂ + f₃` on the
  collar).  The OFF-collar chart-native expansion of `witnessSecondXDeriv` is NOT banked and is the
  genuine geometric input.  Recommended Sol consult: either (a) prove the off-collar chart-native form
  of `witnessSecondXDeriv` (a van-Vleck jet identity), then wire `D := |hessCoeff|·C·(‖z‖³/τ)·G_{C'τ}·|qc|`
  + `cubic_gaussian_moment_witness`; or (b) keep legs (ii)–(iv) as the three enumerated satisfiable
  carries (the honest reduction landed here) and move the geometric identity to the terminal geometric
  wiring tranche.  Option (b) is IN FORCE.

  REMAINING GROUP-(1) RESIDUE (honest; J4-422+):
    • `hf2bound`/`hf3bound` (gradient/mass Gaussian-moment ABSOLUTE dominators) — the odd-moment `√τ`
      extraction for `hf2bound` + the `τ`-uniform mass for `hf3bound` (see the J4-420 scoping block).
      Route: `SlotDischarges.hf2bound_slot_of_dom`/`hf3bound_slot_of_dom` + `abs_integral_le_of_dom` +
      the cubic/mass Gaussian-moment family.  Recommended as J4-422.
    • the three comparison-leg geometric carries `D`/`hdom`/`hmom` here (option (b), the chart-native
      off-collar form of `IchartResidual`).
  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.
-/
