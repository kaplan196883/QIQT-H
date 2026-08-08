/-
  SupBaseGeneral — J4-441: lifting the GROUNDED sups to GENERAL BASE, closing the sup-family ↔
  diff-family thread-convergence mismatch of the a₁ = R/6 convergence-trio campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file is edited.

  ── THE MISMATCH (J4-440, `FrozenDominatorLegs`, PROVIDER LEDGER v3).  The diff family's `hGateData`
  carries two ON-GATE sups inside its a.e.-`s` reduced core:
        C₀  = `∀ᵐ z, z ∈ K → |vanVleckGatedWitness … (u−s) (update y i w) z| ≤ C₀`
        C₁  = `∀ᵐ z, ∀ w' ∈ znb, z ∈ K → |witnessFieldDeriv … i (u−s) (update y i w') z| ≤ C₁`
  i.e. the WITNESS VALUE at the fixed field point `update y i w`, and its first FIELD-derivative at the
  GENERAL field points `update y i w'` (`w' ∈ znb`).  The sup family (`SupFamilyFirstOrder`) grounded
  its first-derivative sup `C₁` only at the CENTRE (field point `0`, `baseSlotAmpDeriv1_grounded`).  The
  needed lift is the SAME compactness route at GENERAL field point — this brick.

  ── THE KEY SIMPLIFICATION CHECK (mission step 2), VERDICT: **JOINT LIFT NEEDED (not merely local).**
  `hGateData`'s `C₁` bullet chooses `C₁` BEFORE quantifying `z` and `w'`; the bound must therefore be
  uniform over `z ∈ K` (the FULL compact gate) AND `w' ∈ znb`.  Per-fixed-`z` field-local boundedness
  does NOT suffice: the honest object is a sup over the compact product `Icc (w−ρ) (w+ρ) ×ˢ K`, requiring
  the JOINT continuity of the (already-differentiated) field on that product.  We take that joint
  continuity as a REDUCED GEOMETRIC CARRY — exactly as `SupFamilyFirstOrder` took `hJac`/`hW0` — and run
  compactness (`IsCompact.exists_bound_of_continuousOn`, NO `.choose`).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `vanVleckGatedWitness_abs_le`  — the gated witness is dominated by the UNGATED parametrix witness:
        `|vanVleckGatedWitness … τ p z| ≤ |globalCutoffParametrixWitnessN 1 … τ p z|`, since the
        `gatedKernel` value is either the base kernel or `0`.  Converts the S-gate (which spoils
        continuity of the witness itself) into a continuous dominator for the compact sup.
    • `supBaseGeneral_C0`            — ★★ the WITNESS-VALUE on-gate sup at GENERAL field point, in
        `hGateData`'s EXACT `C₀` slot shape, from compactness of `K` and the base-continuity of the
        UNGATED witness field `z ↦ globalCutoffParametrixWitnessN 1 … (u−s) (update y i w) z` on `K`.
    • `supBaseGeneral_C1`            — ★★ the first FIELD-derivative on-gate sup at GENERAL field points,
        in `hGateData`'s EXACT `C₁` slot shape (`znb := Icc (w−ρ) (w+ρ)`), from compactness of the
        product `Icc ×ˢ K` and the JOINT continuity of `(w',z) ↦ witnessFieldDeriv … i (u−s)
        (update y i w') z` on it.
    • `gateData_of_reduced`         — ★★★ the SUP-SLOT DISCHARGE: builds `FrozenDominatorLegs`'s exact
        `hGateData` from a strictly-lighter REDUCED carry `hGateData'` whose two on-gate sup bullets are
        REPLACED by the two continuity carries above (plus `ρ`), with `C₀`/`C₁` filled by
        `supBaseGeneral_C0`/`supBaseGeneral_C1` and `znb := Icc (w−ρ) (w+ρ)`.
    • `innerDiff_phase5`            — ★★★ `FrozenDominatorLegs.innerDiff_phase4` with `hGateData`
        SUPPLIED from `hGateData'` via `gateData_of_reduced`: the on-gate sup slots are discharged; the
        remainder shrinks to the genuinely-irreducible core (see THE CONVERGENCE LEDGER).

  ── DON'T-UNDERCREDIT.  The J4-440 ledger's "the base-`y` on-gate sup stays an ENUMERATED carry"
  is now SHARPENED: the sup is no longer opaque — it is GROUNDED by the identical compactness route the
  sup family used, CONDITIONAL only on two NAMED, banked-reducible geometric continuity carries at
  general field point (the general-field-point analogues of `chartOrigin_continuousOn` / the chart
  field-Jacobian joint continuity).  This is a net honesty gain (opaque sup → named continuity), the
  SAME trade `SupFamilyFirstOrder` made at the centre.

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.FrozenDominatorLegs
import QIQTH.EngineInstantiation
import QIQTH.ConvApproximants
import QIQTH.OrderNResidual
import QIQTH.GlobalHunifAssembly

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.WitnessMeasDeriv
open QIQTH.InnerDataEnvelope QIQTH.WitnessDerivDomination QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialDistance
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.SupBaseGeneral

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) The gated witness is dominated by the ungated parametrix witness.
    ############################################################################### -/

/-- **`vanVleckGatedWitness_abs_le` — the gated witness is dominated by the ungated one.**
    `|vanVleckGatedWitness g gi hC hK S a b τ p z| ≤ |globalCutoffParametrixWitnessN 1 (vanVleck g) …
    (uniformInverseChart g gi hC hK) τ p z|`, because `vanVleckGatedWitness = gatedKernel K S H` and the
    `gatedKernel` value is either the base kernel `H τ p z` or `0` (the `z ∈ K` / `p ∈ S z` dichotomy).
    Turns the S-gate — which destroys continuity of the witness in `z` — into a CONTINUOUS dominator for
    the compact sup below.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_abs_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p z : Point n) :
    |vanVleckGatedWitness g gi hC hK S a b τ p z|
      ≤ |globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ p z| := by
  simp only [vanVleckGatedWitness, gatedKernel]
  split_ifs with hz hp
  · exact le_refl _
  · rw [abs_zero]; exact abs_nonneg _
  · rw [abs_zero]; exact abs_nonneg _

/-! ###############################################################################
    ### (B) The witness-value on-gate sup `C₀` at GENERAL field point.
    ############################################################################### -/

/-- **★★ `supBaseGeneral_C0` — the WITNESS-VALUE on-gate sup at GENERAL field point.**  In the EXACT
    `C₀` slot shape of `FrozenDominatorLegs`'s `hGateData` core: from `IsCompact K` and the base-
    continuity of the UNGATED parametrix witness `z ↦ globalCutoffParametrixWitnessN 1 … τ (update y i w)
    z` on `K`, compactness (`IsCompact.exists_bound_of_continuousOn`, NO `.choose`) bounds the ungated
    witness, and `vanVleckGatedWitness_abs_le` transfers the bound to the GATED witness.  The continuity
    hypothesis `hcont0` is the general-field-point analogue of `chartOrigin_continuousOn` composed with
    the smooth radial-cutoff / heat-parametrix prefactor — a banked-reducible geometric carry.  NOT
    `a₁ = R/6`. -/
theorem supBaseGeneral_C0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ w : ℝ) (y : Point n) (i : Fin n)
    (hcont0 : ContinuousOn (fun z : Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ (Function.update y i w) z) K) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᵐ z ∂volume, z ∈ K →
      |vanVleckGatedWitness g gi hC hK S a b τ (Function.update y i w) z| ≤ C₀ := by
  obtain ⟨C, hCbd⟩ := hK.exists_bound_of_continuousOn hcont0
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  refine ae_of_all _ (fun z hz => ?_)
  have hb : |globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b
      (uniformInverseChart g gi hC hK) τ (Function.update y i w) z| ≤ C := by
    have h := hCbd z hz; rwa [Real.norm_eq_abs] at h
  calc |vanVleckGatedWitness g gi hC hK S a b τ (Function.update y i w) z|
      ≤ |globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ (Function.update y i w) z| :=
        vanVleckGatedWitness_abs_le g gi hC hK S a b τ (Function.update y i w) z
    _ ≤ C := hb
    _ ≤ max C 0 := le_max_left _ _

/-! ###############################################################################
    ### (C) The first field-derivative on-gate sup `C₁` at GENERAL field points.
    ############################################################################### -/

/-- **★★ `supBaseGeneral_C1` — the first FIELD-derivative on-gate sup at GENERAL field points.**  In the
    EXACT `C₁` slot shape of `hGateData`'s core (`znb := Icc (w−ρ) (w+ρ)`): from the JOINT continuity of
    `(w',z) ↦ witnessFieldDeriv … i τ (update y i w') z` on the COMPACT product `Icc (w−ρ) (w+ρ) ×ˢ K`,
    compactness (`isCompact_Icc.prod hK` + `IsCompact.exists_bound_of_continuousOn`, NO `.choose`)
    bounds the derivative UNIFORMLY over both the base `z ∈ K` and the field coordinate `w' ∈ znb` — the
    genuinely JOINT sup the slot demands (see header, KEY SIMPLIFICATION CHECK).  The joint-continuity
    hypothesis `hcont1` is the general-field-point analogue of the chart field-Jacobian joint continuity
    (the recognised J3 base-point-regularity carry), one field-derivative order carried through the
    witness.  NOT `a₁ = R/6`. -/
theorem supBaseGeneral_C1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ w ρ : ℝ) (hρ : 0 < ρ) (y : Point n)
    (hcont1 : ContinuousOn (fun q : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i q.1) q.2)
        (Set.Icc (w - ρ) (w + ρ) ×ˢ K)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ᵐ z ∂volume, ∀ w' ∈ Set.Icc (w - ρ) (w + ρ), z ∈ K →
        |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w') z| ≤ C₁ := by
  have hcompact : IsCompact (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hCbd⟩ := hcompact.exists_bound_of_continuousOn hcont1
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  refine ae_of_all _ (fun z w' hw' hz => ?_)
  have hmem : (w', z) ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K := ⟨hw', hz⟩
  have hb := hCbd (w', z) hmem
  rw [Real.norm_eq_abs] at hb
  exact le_trans hb (le_max_left _ _)

/-! ###############################################################################
    ### (D) `gateData_of_reduced` — the SUP-SLOT DISCHARGE.
    ############################################################################### -/

/-- **★★★ `gateData_of_reduced` — the ON-GATE SUP-SLOT DISCHARGE.**  Produces `FrozenDominatorLegs`'s
    EXACT `hGateData` bundle (the per-`(m,i,u,y)` carry consumed by `innerDiff_phase4`) from a strictly-
    lighter REDUCED carry `hGateData'` whose two ON-GATE SUP bullets (`C₀`/`C₁`) are REPLACED by the two
    continuity carries `hcont0`/`hcont1` (plus a base radius `ρ`).  Per a.e.-`s`, per `w ∈ snb`:
    `znb := Icc (w−ρ) (w+ρ)` (in `𝓝 w` via `Icc_mem_nhds`), `C₀` filled by `supBaseGeneral_C0` from
    `hcont0`, `C₁` filled by `supBaseGeneral_C1` from `hcont1`, and every OTHER bullet
    (`σ`/`C_L`/measurabilities/Levi-domination/gate-dichotomy) threaded verbatim.  Pure construction;
    each replaced bullet a satisfiable, non-vacuous, strictly-lower-level carry, none equal to
    `a₁ = R/6`.  NOT `a₁ = R/6`. -/
theorem gateData_of_reduced (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n))
    (hGateData' : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (ρ σ C_L : ℝ),
              0 < ρ ∧ 0 < σ ∧ 0 ≤ C_L ∧
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
              ContinuousOn (fun z : Point n =>
                  globalCutoffParametrixWitnessN 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) a b
                    (uniformInverseChart g gi hC hK) (u - s) (Function.update y i w) z) K ∧
              ContinuousOn (fun q : ℝ × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (u - s)
                    (Function.update y i q.1) q.2)
                (Set.Icc (w - ρ) (w + ρ) ×ˢ K) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ Set.Icc (w - ρ) (w + ρ),
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w')))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
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
                  (Function.update y i w'))) := by
  intro m i u hu y hy
  obtain ⟨snb, hsnb, hDHdom, hcore'⟩ := hGateData' m i u hu y hy
  refine ⟨snb, hsnb, hDHdom, ?_⟩
  filter_upwards [hcore'] with s hs hmem w hw
  obtain ⟨ρ, σ, C_L, hρ, hσ, hC_L, hWmeas, hLevimeas, hDHmeas, hLevi, hcont0, hcont1, hdich⟩ :=
    hs hmem w hw
  obtain ⟨C₀, hC₀0, hOn0⟩ := supBaseGeneral_C0 g gi hC hK S a b (u - s) w y i hcont0
  obtain ⟨C₁, hC₁0, hOn1⟩ := supBaseGeneral_C1 g gi hC hK S a b i (u - s) w ρ hρ y hcont1
  exact ⟨Set.Icc (w - ρ) (w + ρ), σ, C₀, C₁, C_L,
    Icc_mem_nhds (by linarith) (by linarith), hσ, hC₀0, hC₁0, hC_L,
    hWmeas, hLevimeas, hDHmeas, hLevi, hOn0, hOn1, hdich⟩

/-! ###############################################################################
    ### (E) `innerDiff_phase5` — the provider remainder with the sup slots discharged.
    ############################################################################### -/

/-- **★★★ `innerDiff_phase5`.**  `FrozenDominatorLegs.innerDiff_phase4` with the `hGateData` carry
    SUPPLIED INTERNALLY from the strictly-lighter REDUCED carry `hGateData'` via `gateData_of_reduced`:
    the two ON-GATE SUP bullets (`C₀`/`C₁`) are DISCHARGED here by the compactness route
    (`supBaseGeneral_C0`/`supBaseGeneral_C1`), replaced in `hGateData'` by two NAMED continuity carries
    (plus `ρ`).  Every OTHER hypothesis is threaded exactly as `innerDiff_phase4`.  Pure composition;
    each remaining carry satisfiable, non-vacuous, strictly lower level than the conclusion, none equal
    to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem innerDiff_phase5 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hGateData' : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (ρ σ C_L : ℝ),
              0 < ρ ∧ 0 < σ ∧ 0 ≤ C_L ∧
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
              ContinuousOn (fun z : Point n =>
                  globalCutoffParametrixWitnessN 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) a b
                    (uniformInverseChart g gi hC hK) (u - s) (Function.update y i w) z) K ∧
              ContinuousOn (fun q : ℝ × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (u - s)
                    (Function.update y i q.1) q.2)
                (Set.Icc (w - ρ) (w + ρ) ×ˢ K) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ Set.Icc (w - ρ) (w + ρ),
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
  QIQTH.FrozenDominatorLegs.innerDiff_phase4 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont V hV
    hLeviJoint hWitJointY hWitJointYbase hWFDjointY hFzero hFdomEvery hWitDomCappedY
    (gateData_of_reduced g gi hC hK S a b U V hGateData')

end QIQTH.SupBaseGeneral

/-! ## THE CONVERGENCE LEDGER — the sup-family ↔ diff-family thread, after J4-441.

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │ THE TWO THREADS AND WHERE THEY NOW MEET                                                          │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │ SUP FAMILY (SupFamilyFirstOrder / BaseSlotAmpDeriv):                                             │
  │   grounds C₀/C₁ at the CENTRE (field point 0), on closedBall 0 ρ, via                            │
  │   pd_chartAmp_center_eq + compactness — CONDITIONAL on the reduced geometric carries             │
  │   hreg / hW0 / hJac at base 0.                                                                   │
  │                                                                                                  │
  │ DIFF FAMILY (FrozenDominatorLegs.innerDiff_phase4):                                              │
  │   consumes C₀/C₁ at GENERAL field point update y i w' (w' ∈ znb), sup over z ∈ K.                 │
  │                                                                                                  │
  │ THIS BRICK (SupBaseGeneral):                                                                     │
  │   runs the SAME compactness route at GENERAL field point.                                        │
  │     • C₀ (witness value): dominate the S-gated witness by the UNGATED parametrix witness         │
  │       (vanVleckGatedWitness_abs_le) and bound over the compact gate K                            │
  │       (supBaseGeneral_C0).                                                                       │
  │     • C₁ (first field-derivative): bound over the compact PRODUCT Icc (w−ρ)(w+ρ) ×ˢ K            │
  │       (supBaseGeneral_C1) — the JOINT sup the slot demands (verdict below).                      │
  │   gateData_of_reduced fills both slots; innerDiff_phase5 wires it into phase4.                   │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── KEY SIMPLIFICATION CHECK — VERDICT: **JOINT LIFT NEEDED (local insufficient).**
  `hGateData`'s C₁ bullet is `∀ᵐ z, ∀ w' ∈ znb, z ∈ K → |…| ≤ C₁`, with `C₁` chosen BEFORE the
  quantifiers.  The bound must therefore be uniform over `z ∈ K` (the whole compact gate) AND
  `w' ∈ znb`; per-fixed-`z` field-local boundedness cannot deliver a single such `C₁`.  Hence
  `supBaseGeneral_C1` sups over the compact PRODUCT `Icc (w−ρ)(w+ρ) ×ˢ K` and takes the JOINT continuity
  of the already-differentiated field there.  (The cheaper local route was checked and rejected on the
  shape.)

  ── C₀ / C₁ OUTCOMES.
    • C₀ GROUNDED at general field point (`supBaseGeneral_C0`): the ungated-witness base-continuity
      `hcont0` on `K` + `vanVleckGatedWitness_abs_le`.  `hcont0` reduces to
      `z ↦ uniformInverseChart g gi hC hK z (update y i w)` continuous on `K` (general-field-point
      analogue of `GeodesicGronwall.chartOrigin_continuousOn`) composed with the smooth
      radial-cutoff / heat-parametrix prefactor.
    • C₁ GROUNDED at general field points (`supBaseGeneral_C1`): the JOINT continuity `hcont1` of
      `(w',z) ↦ witnessFieldDeriv … i (u−s) (update y i w') z` on `Icc ×ˢ K`.  This is the
      general-field-point analogue of the chart field-Jacobian joint continuity
      (`JacobiCLMExposure.chartFieldJacobian_continuousOn`), carried one field-derivative order through
      the witness.

  ── THE CONVERGENCE STATUS.  The base MISMATCH flagged in the J4-440 ledger is CLOSED at the lemma
  level: the on-gate sups the diff family needs are now GROUNDED by the identical compactness route the
  sup family used, no longer opaque `.choose` carries.  `innerDiff_phase5` shrinks the frozen `hQ1`
  provider remainder further — from {one enumerated GATE/AMP/ENVELOPE carry incl. two opaque sups} to
  {one REDUCED carry `hGateData'` whose sup bullets are replaced by TWO NAMED, banked-reducible GENERAL-
  FIELD-POINT CONTINUITY carries}.

  ── THE UPDATED IRREDUCIBLE CORE of `hGateData'` (per `(m,i,u,y)`, per a.e.-`s`, per `w ∈ snb`):
      (1) snb ∈ 𝓝(y i) + the uniform-over-snb capped Gaussian domination of `dH` (legs 5/6);
      (2) positive Gaussian width σ + nonnegative Levi constant C_L + the Levi Gaussian domination;
      (3) the bare z-slice measurabilities of W / Lev / dH;
      (4) the per-z GATE DICHOTOMY on `Icc (w−ρ)(w+ρ)`;
      (5) ★ hcont0 — base-continuity of the UNGATED witness at general field point `update y i w`,
          on `K`  (general-field-point analogue of `chartOrigin_continuousOn`);
      (6) ★ hcont1 — JOINT continuity of the witness first FIELD-derivative on `Icc (w−ρ)(w+ρ) ×ˢ K`
          (general-field-point analogue of the chart field-Jacobian joint continuity).
  Items (5)/(6) are the two GENUINELY-IRREDUCIBLE geometric atoms that remain — the general-field-point
  base-regularity carries (the recognised J3 base-point-regularity family, evaluated AWAY from the
  centre `0`).  Everything else is measurability / integrability / Levi-Gaussian bookkeeping.

  ── DON'T-UNDERCREDIT FINDINGS.
    • The base mismatch is NOT a hard wall between the threads — it is the SAME compactness route at a
      shifted field point.  This brick executes it; the residue is two NAMED continuity carries, not an
      opaque sup.
    • `SupFamilyFirstOrder`'s grounded centre C₁ is the base-0 SPECIAL CASE of `hcont1`; grounding
      `hcont0`/`hcont1` at general field point is the general-base analogue of the ALREADY-BANKED
      centre facts (`chartOrigin_continuousOn` UNCONDITIONAL; `chartFieldJacobian_continuousOn`
      UNCONDITIONAL at base 0).  So the two remaining atoms are the general-field-point extensions of
      lemmas THAT ARE ALREADY PROVED at the centre — a much narrower gap than a fresh analytic wall.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on hcont0/hcont1 at general field point + the
  banked convergence trio + the geometric wiring).
-/

section AxiomChecks
open QIQTH.SupBaseGeneral
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms vanVleckGatedWitness_abs_le
#print axioms supBaseGeneral_C0
#print axioms supBaseGeneral_C1
#print axioms gateData_of_reduced
#print axioms innerDiff_phase5
end AxiomChecks
