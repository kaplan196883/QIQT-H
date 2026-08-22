/-
  AmpFieldBaseSlotGlobalTruncation — J4-1027: FIXES a genuine slot-mismatch discovered in J4-1024/1026's
  globalization of `chartFieldAmp` — those files globalized regularity in the FIELD slot `x'` (with base
  `z` fixed), but `nb`'s literal `Bfac` term1 (`HCompNearCarryKPrimeBaseFieldCoV`, J4-1010) needs `A :=
  chartFieldAmp … z x` with `z` VARYING as the CoV base-slot integration variable and `x` FIXED as the
  field point — the OTHER slot.  This file builds the BASE-SLOT mirror of the entire J4-1025/1026 chain
  (ContDiffAt → local Lipschitz+bound → global coordClamp truncation) and re-instantiates
  `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s §E capstone at the CORRECTLY-SLOTTED
  weight, so that `AmpExt v = P (V v)` (inside the agreement ball) is LITERALLY `chartFieldAmp g gi hChr
  hK a b τ z x` with `z = V v` the CoV-recovered base point — the EXACT shape `nb`'s BRICK1 factor `A`
  needs, module the still-separate `Levi(s,z)` prefactor and `hfac`/`S'` domain reconciliation.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of the
  `a₁ = R/6` heat-kernel campaign.

  ## THE BUG THIS FIXES.
  `chartFieldAmp g gi hC hK a b τ z x'`'s own docstring (`NormalFormDischarge.lean`) says: "For fixed
  base `z` and time `τ`, the smooth amplitude … as a function of the FIELD slot `x'`."  Every downstream
  regularity fact built on it before this file (`OnGateJets.ampField_contDiffAt`,
  `AmpFieldGeneralPointBoundLipschitz.chartFieldAmp_bound_lipschitz_generalPoint`,
  `AmpFieldGlobalTruncation.AmpGlobal`/`ampGlobal_bound_lipschitz_agree`) globalizes regularity in `x'`
  (field slot), holding `z` FIXED.  But `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s §C/§D/
  §E machinery (J4-1024) recovers, via the local IFT inverse `V`, a point in the BASE slot of `W p :=
  uniformInverseChart g gi hC hK p q₀` (`q₀` FIXED = the field point) — i.e. `V v` plays the role of `z`,
  NOT `x'`.  Plugging `AmpGlobal` (regular in `x'`, `z` fixed) in as `P` therefore builds
  `P (V v) = chartFieldAmp … z_FIXED (clamp (V v))` — `V v` lands in the WRONG (field) slot, `z` stays a
  constant baked into `P` — this is NOT `nb`'s `A = chartFieldAmp … z x` with `z` varying.  J4-1026's own
  honest-scope note flagged "does NOT identify this with `nb`'s actual … integrand" but did not diagnose
  the mismatch was a wrong-slot globalization, not merely a missing final identification step.

  Sol (`gpt-5.6-sol`, high, 2026-08-23) plan-reviewed BEFORE Lean: confirmed `ampField_contDiffAt`'s proof
  is mechanically slot-agnostic (it only uses `ContDiffAt` of the SINGLE composite point
  `uniformInverseChart g gi hC hK z x'`, via generic `.comp` through `radialCutoff`/`vanVleck`/
  `transportCoeff`, and never inspects which literal argument plays which role), so a literal
  argument-swapped mirror is sound; confirmed no `ContDiffAt.comp` gotcha; confirmed this is worth
  banking even though it does not discharge `Levi(s,z)` or the `hfac`/`S'` reconciliation.

  ## WHAT LANDS (ns `QIQTH.AmpFieldBaseSlotGlobalTruncation`).
    • `ampField_contDiffAt_baseSlot` — mirror of `OnGateJets.ampField_contDiffAt`: `chartFieldAmp` is `C²`
      as a function of the BASE slot `z'` at a general `w`, field point `x` FIXED, from the base-slot
      chart regularity hypothesis `hWx : ContDiffAt ℝ 2 (fun z' => uniformInverseChart … z' x) w` (the
      exact analogue of `AmpFieldGeneralPointBoundLipschitz`'s carried `hWz`, now in the other slot).
    • `chartFieldAmp_bound_lipschitz_generalPoint_baseSlot` — mirror of `AmpFieldGeneralPointBoundLipschitz`:
      LOCAL bound + pairwise Lipschitz on `ball w r`, base slot.
    • `AmpGlobalBase` / `ampGlobalBase_bound_lipschitz_agree` — mirror of `AmpFieldGlobalTruncation`: the
      base slot `chartFieldAmp … · x` precomposed with `coordClamp w ρ`, GLOBALLY bounded + globally
      pairwise Lipschitz, agreeing with the literal `chartFieldAmp … z x` on `closedBall w ρ`.
    • `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_baseSlot_global` — ★★★★★
      instantiates J4-1024's §E capstone at `P := AmpGlobalBase … x w ρ`, `q₀ := x` — giving `nb`'s
      BRICK-2 domain-restricted bound with `AmpExt v` LITERALLY EQUAL (inside the agreement ball, i.e.
      whenever `V v ∈ closedBall w ρ`) to `chartFieldAmp g gi hChr hK a b τx (V v) x` — the CORRECTLY
      slotted shape matching `nb`'s BRICK1 factor `A`.

  ## HONEST SCOPE — WHAT THIS DOES **NOT** DO.
  This corrects the slot of the globalized weight but does NOT discharge: (a) the `Levi(s,z)` prefactor
  multiplying `hsMixed·A` in `Bfac` — NOT bounded/Lipschitz here, so this is progress on the `hsMixed·A`
  SUB-piece of term1, not the whole `Levi(s,z)·hsMixed·A` term1; (b) `hfac`'s literal carry over the
  IFT-selected domain `S'` and BRICK1's on-gate jet bundle uniformly over `S'` (residuals r1/r2 of
  `HCompNearCarryKPrimeBaseFieldCoV`); (c) the coordinate-clamp truncation caveat (the bound only agrees
  with the literal `chartFieldAmp` exactly inside `closedBall w ρ`, `ρ` determined by the base-slot chart
  regularity at `w`, not the whole domain). `Bfac`'s other 3 summands (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`) and
  `fb` (far carry) remain entirely untouched / SEPARATELY open. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`. Do NOT read this as "`nb`'s term1 closes" —
  it does not.

  NO `sorry`, NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, none equal to the
  conclusion. NEW FILE — no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.OnGateJets
import QIQTH.AmpFieldGeneralPointBoundLipschitz
import QIQTH.BaseFlowGlobalContraction
import QIQTH.AmpFieldGlobalTruncation
import QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.FlatHeatEquation
open QIQTH.OnGateJets QIQTH.AmpFieldGeneralPointBoundLipschitz
open QIQTH.BaseFlowGlobalContraction QIQTH.AmpFieldGlobalTruncation
open QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
open scoped Topology BigOperators ContDiff NNReal

namespace QIQTH.AmpFieldBaseSlotGlobalTruncation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ############################################################################
    ### 1. `chartFieldAmp` is `C²` as a function of the BASE slot `z'`, field
    ### point `x` fixed, general basepoint `w` — the slot-swapped mirror of
    ### `OnGateJets.ampField_contDiffAt`.
    ############################################################################ -/

/-- **★ `ampField_contDiffAt_baseSlot`.**  Mirror of `OnGateJets.ampField_contDiffAt`, slots swapped:
    `chartFieldAmp` is `C²` as a function of the BASE slot `z'` at a general point `w`, field point `x`
    FIXED, given the base-slot chart regularity `hWx` and Riemannian positivity `hdetx`.  Route: LITERAL
    argument-swap of the original proof — each factor of `chartFieldAmp` is a function of the SINGLE
    composite point `uniformInverseChart … z' x`, so the same `ContDiffAt.comp` chain fires with `hWx` in
    place of `hWz`.  Sol (`gpt-5.6-sol`, high) confirmed this is mechanically sound before any Lean was
    written. NOT `a₁ = R/6`. -/
theorem ampField_contDiffAt_baseSlot (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (x w : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWx : ContDiffAt ℝ 2 (fun z' => uniformInverseChart g gi hChr hK z' x) w)
    (hdetx : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK w x))) :
    ContDiffAt ℝ 2 (fun z' => chartFieldAmp g gi hChr hK a b τ z' x) w := by
  set W : Point n → Point n := fun z' => uniformInverseChart g gi hChr hK z' x with hWdef
  have hWx' : ContDiffAt ℝ 2 W w := hWx
  have hcut : ContDiffAt ℝ 2 (fun z' => radialCutoff a b (W z')) w :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp w hWx'
  have hvv : ContDiffAt ℝ 2 (fun z' => vanVleck g (W z')) w :=
    (vanVleck_contDiffAt g hg (W w) hdetx (k := 2)).comp w hWx'
  have hne : (fun z' => vanVleck g (W z')) w ≠ 0 :=
    ne_of_gt (vanVleck_pos g (W w) hdetx)
  have hrpow : ContDiffAt ℝ 2 (fun z' => vanVleck g (W z') ^ (-(1 : ℝ) / 2)) w :=
    hvv.rpow_const_of_ne hne
  have hu0 : ContDiffAt ℝ 2
      (fun z' => transportCoeff (transportOp (vanVleck g) g gi) 0 (W z')) w :=
    (((hu 0).contDiffAt).of_le le_top).comp w hWx'
  have hu1 : ContDiffAt ℝ 2
      (fun z' => transportCoeff (transportOp (vanVleck g) g gi) 1 (W z')) w :=
    (((hu 1).contDiffAt).of_le le_top).comp w hWx'
  have hsum : ContDiffAt ℝ 2
      (fun z' => transportCoeff (transportOp (vanVleck g) g gi) 0 (W z')
        + transportCoeff (transportOp (vanVleck g) g gi) 1 (W z') * τ) w :=
    hu0.add (hu1.mul contDiffAt_const)
  have hfinal : ContDiffAt ℝ 2
      (fun z' => radialCutoff a b (W z')
        * (vanVleck g (W z') ^ (-(1 : ℝ) / 2)
            * (transportCoeff (transportOp (vanVleck g) g gi) 0 (W z')
              + transportCoeff (transportOp (vanVleck g) g gi) 1 (W z') * τ))) w :=
    hcut.mul (hrpow.mul hsum)
  simpa [chartFieldAmp, hWdef] using hfinal

/-! ############################################################################
    ### 2. Local bound + pairwise Lipschitz on `ball w r`, BASE slot — the
    ### slot-swapped mirror of `AmpFieldGeneralPointBoundLipschitz`.
    ############################################################################ -/

/-- **★★★ `chartFieldAmp_bound_lipschitz_generalPoint_baseSlot`.**  Mirror of
    `AmpFieldGeneralPointBoundLipschitz.chartFieldAmp_bound_lipschitz_generalPoint`, BASE slot: for a
    general fixed base point `w`, field point `x` FIXED, given the same two carries §1 needs, there is a
    ball `ball w r` on which `z' ↦ chartFieldAmp … z' x` is pairwise Lipschitz with constant `L` and
    bounded by `M`. NOT `a₁ = R/6`. -/
theorem chartFieldAmp_bound_lipschitz_generalPoint_baseSlot (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (x w : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWx : ContDiffAt ℝ 2 (fun z' => uniformInverseChart g gi hChr hK z' x) w)
    (hdetx : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK w x))) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∃ M : ℝ,
      (∀ z1 ∈ Metric.ball w r, ∀ z2 ∈ Metric.ball w r,
        |chartFieldAmp g gi hChr hK a b τ z1 x - chartFieldAmp g gi hChr hK a b τ z2 x|
          ≤ L * dist z1 z2) ∧
      (∀ z1 ∈ Metric.ball w r, |chartFieldAmp g gi hChr hK a b τ z1 x| ≤ M) := by
  have hC2 : ContDiffAt ℝ 2 (fun z' => chartFieldAmp g gi hChr hK a b τ z' x) w :=
    ampField_contDiffAt_baseSlot g gi hChr hK a b τ x w hg hu hWx hdetx
  have hC1 : ContDiffAt ℝ 1 (fun z' => chartFieldAmp g gi hChr hK a b τ z' x) w :=
    hC2.of_le (by norm_num)
  obtain ⟨r, hr, L, hL, hlip⟩ :=
    contDiffAt_one_lipschitzOn_ball_atPoint (fun z' => chartFieldAmp g gi hChr hK a b τ z' x) w hC1
  refine ⟨r, hr, L, hL, |chartFieldAmp g gi hChr hK a b τ w x| + L * r, ?_, ?_⟩
  · intro z1 hz1 z2 hz2
    have h := hlip z1 hz1 z2 hz2
    simpa [Real.norm_eq_abs] using h
  · intro z1 hz1
    have hz1w : dist z1 w < r := Metric.mem_ball.mp hz1
    have hlipz1w : |chartFieldAmp g gi hChr hK a b τ z1 x - chartFieldAmp g gi hChr hK a b τ w x|
        ≤ L * dist z1 w := by
      have h := hlip z1 hz1 w (Metric.mem_ball_self hr)
      simpa [Real.norm_eq_abs] using h
    have hkey := abs_sub_abs_le_abs_sub
      (chartFieldAmp g gi hChr hK a b τ z1 x) (chartFieldAmp g gi hChr hK a b τ w x)
    have htri : |chartFieldAmp g gi hChr hK a b τ z1 x|
        ≤ |chartFieldAmp g gi hChr hK a b τ w x|
          + |chartFieldAmp g gi hChr hK a b τ z1 x - chartFieldAmp g gi hChr hK a b τ w x| := by
      linarith
    have hLr : L * dist z1 w ≤ L * r := mul_le_mul_of_nonneg_left (le_of_lt hz1w) hL
    linarith

/-! ############################################################################
    ### 3. `AmpGlobalBase` — `chartFieldAmp … · x` precomposed with the
    ### sup-norm clamp on the BASE slot — the slot-swapped mirror of
    ### `AmpFieldGlobalTruncation.AmpGlobal`.
    ############################################################################ -/

/-- **`AmpGlobalBase`.**  The concrete on-gate amplitude `chartFieldAmp`, field point `x` FIXED, base
    slot `z'` pulled back through the metric-projection clamp `coordClamp w ρ`.  Agrees with
    `chartFieldAmp … z x` exactly on `closedBall w ρ`, and is globally bounded + globally pairwise
    Lipschitz everywhere (see `ampGlobalBase_bound_lipschitz_agree`). NOT `a₁ = R/6`. -/
noncomputable def AmpGlobalBase (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (x w : Point n) (ρ : ℝ)
    (z' : Point n) : ℝ :=
  chartFieldAmp g gi hChr hK a b τ (coordClamp w ρ z') x

/-- **★★★★★ `ampGlobalBase_bound_lipschitz_agree`.**  Mirror of `AmpFieldGlobalTruncation.
    ampGlobal_bound_lipschitz_agree`, BASE slot: for a general fixed base point `w`, field point `x`
    FIXED, there is `ρ > 0` and moduli `L, M ≥ 0` such that `AmpGlobalBase … x w ρ` is (i) GLOBALLY
    bounded by `M`; (ii) GLOBALLY PAIRWISE Lipschitz with constant `L`; (iii) AGREES with the literal
    `chartFieldAmp … · x` on `closedBall w ρ`.  Route: identical to `ampGlobal_bound_lipschitz_agree`,
    with `coordClamp` composed on the BASE-slot argument instead of the field-slot argument (both
    `coordClamp` facts used are slot-agnostic). NOT `a₁ = R/6`. -/
theorem ampGlobalBase_bound_lipschitz_agree (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (x w : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWx : ContDiffAt ℝ 2 (fun z' => uniformInverseChart g gi hChr hK z' x) w)
    (hdetx : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK w x))) :
    ∃ ρ > (0 : ℝ), ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      (∀ z1 z2 : Point n,
        |AmpGlobalBase g gi hChr hK a b τ x w ρ z1 - AmpGlobalBase g gi hChr hK a b τ x w ρ z2|
          ≤ L * dist z1 z2) ∧
      (∀ z1 : Point n, |AmpGlobalBase g gi hChr hK a b τ x w ρ z1| ≤ M) ∧
      (∀ z1 ∈ Metric.closedBall w ρ,
        AmpGlobalBase g gi hChr hK a b τ x w ρ z1 = chartFieldAmp g gi hChr hK a b τ z1 x) := by
  classical
  obtain ⟨r, hr, L, hL, M, hlip, hbd⟩ :=
    chartFieldAmp_bound_lipschitz_generalPoint_baseSlot g gi hChr hK a b τ x w hg hu hWx hdetx
  set F : Point n → ℝ := fun z' => chartFieldAmp g gi hChr hK a b τ z' x with hFdef
  set ρ : ℝ := r / 2 with hρdef
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := by rw [hρdef]; linarith
  refine ⟨ρ, hρpos, L, M, hL, le_trans (abs_nonneg _) (hbd w (Metric.mem_ball_self hr)), ?_, ?_, ?_⟩
  · -- global pairwise Lipschitz.
    set Kc : ℝ≥0 := ⟨L, hL⟩ with hKcdef
    have hKcoe : (Kc : ℝ) = L := rfl
    have hFlip : LipschitzOnWith Kc F (Metric.ball w r) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro z1 hz1 z2 hz2
      have h := hlip z1 hz1 z2 hz2
      simpa [hFdef, hKcoe, Real.dist_eq] using h
    have hballsub : Metric.closedBall w ρ ⊆ Metric.ball w r := Metric.closedBall_subset_ball hρr
    have hMaps : Set.MapsTo (coordClamp w ρ) Set.univ (Metric.ball w r) :=
      coordClamp_mapsTo w ρ (le_of_lt hρpos) hballsub
    have hcomp_on : LipschitzOnWith (Kc * 1) (F ∘ coordClamp w ρ) Set.univ :=
      hFlip.comp ((lipschitzOnWith_univ).2 (coordClamp_lipschitzWith_one w ρ)) hMaps
    rw [mul_one] at hcomp_on
    have hglobal : LipschitzWith Kc (F ∘ coordClamp w ρ) := lipschitzOnWith_univ.1 hcomp_on
    intro z1 z2
    have h := hglobal.dist_le_mul z1 z2
    have hcompeq : (F ∘ coordClamp w ρ) z1 = AmpGlobalBase g gi hChr hK a b τ x w ρ z1 := by
      simp [AmpGlobalBase, hFdef, Function.comp]
    have hcompeq' : (F ∘ coordClamp w ρ) z2 = AmpGlobalBase g gi hChr hK a b τ x w ρ z2 := by
      simp [AmpGlobalBase, hFdef, Function.comp]
    rw [hcompeq, hcompeq'] at h
    rwa [hKcoe, Real.dist_eq] at h
  · -- global bound.
    intro z1
    have hmemclosed : coordClamp w ρ z1 ∈ Metric.closedBall w ρ :=
      coordClamp_mem_closedBall w ρ (le_of_lt hρpos) z1
    have hmemball : coordClamp w ρ z1 ∈ Metric.ball w r :=
      Metric.closedBall_subset_ball hρr hmemclosed
    have h := hbd (coordClamp w ρ z1) hmemball
    simpa [AmpGlobalBase, hFdef] using h
  · -- agreement on `closedBall w ρ`.
    intro z1 hz1
    have hclamp : coordClamp w ρ z1 = z1 :=
      QIQTH.AmpFieldGlobalTruncation.coordClamp_eq_self_of_mem_closedBall w ρ z1 hz1
    simp [AmpGlobalBase, hclamp]

/-! ############################################################################
    ### 4. Instantiating J4-1024's §E capstone at the CORRECTLY-SLOTTED weight.
    ############################################################################ -/

/-- **★★★★★ `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_baseSlot_global`.**
    Instantiates `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s §E capstone
    (`hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio`, J4-1024) at
    `P := AmpGlobalBase g gi hChr hK a b τx x w ρ`, `q₀ := x` — the globally bounded + globally
    Lipschitz weight (§3) built from the LITERAL `chartFieldAmp` in the BASE slot, field point `x` fixed.
    Since `q₀ = x` and `W p := uniformInverseChart … p x`, the CoV-recovered `V v` lands in the SAME
    (base) slot `AmpGlobalBase` is regular in, so `AmpExt v = AmpGlobalBase … (V v)` equals the LITERAL
    `chartFieldAmp g gi hChr hK a b τx (V v) x` whenever `V v ∈ closedBall w ρ` — the CORRECTLY slotted
    shape matching `nb`'s BRICK1 factor `A` (`HCompNearCarryKPrimeBaseFieldCoV`).  Does NOT discharge the
    `Levi(s,z)` prefactor or `hfac`/`S'`'s domain reconciliation (residuals r1/r2) — see file docstring.
    `Bfac`'s other 3 summands untouched; `fb` remains SEPARATELY open. NOT `a₁ = R/6`. -/
theorem hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_baseSlot_global
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Ka : Set (Point n)} (hKa : IsCompact Ka) (ampA ampB τx : ℝ) (x w : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWx : ContDiffAt ℝ 2 (fun z' => uniformInverseChart g gi hChr hKa z' x) w)
    (hdetx : 0 < Matrix.det (g (uniformInverseChart g gi hChr hKa w x)))
    {K : Set (Point n)} (hK : IsCompact K) (hxK : x ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n) :
    ∃ (S' : Set (Point n)) (ρSp : ℝ) (AmpExt : Point n → ℝ) (L : ℝ), IsOpen S' ∧ x ∈ S' ∧ 0 < ρSp ∧
      0 ≤ L ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hChr hK p x) '' S',
          gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * AmpExt v)|
        ≤ (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ
              + (n : ℝ) ^ 2 * L * ‖Q‖)
          + (Real.exp (-(ρSp ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|AmpExt 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
              + Real.exp (-(ρSp ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                  * (|AmpExt 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                      + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
  obtain ⟨ρamp, hρamp, L, M, hL, hM, hlip, hbd, _hagree⟩ :=
    ampGlobalBase_bound_lipschitz_agree g gi hChr hKa ampA ampB τx x w hg hu hWx hdetx
  exact hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio g gi hChr hK hxK
    τ hτ PI PJ Q (AmpGlobalBase g gi hChr hKa ampA ampB τx x w ρamp) M L hM hL hbd hlip

end QIQTH.AmpFieldBaseSlotGlobalTruncation

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.AmpFieldBaseSlotGlobalTruncation
#print axioms ampField_contDiffAt_baseSlot
#print axioms chartFieldAmp_bound_lipschitz_generalPoint_baseSlot
#print axioms ampGlobalBase_bound_lipschitz_agree
#print axioms hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_baseSlot_global
end AxiomChecks
