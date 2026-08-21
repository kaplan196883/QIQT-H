/-
  BaseVaryingIFTCommonWitness — J4-943: the COMMON-WITNESS MONOLITH resolving structural gap G1
  ("common-witness incoherence") of the J4-930..942 `hCross` chain.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure STRUCTURAL / ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE STRUCTURAL BUG (G1).  A full-assembly audit found that the 12-piece `hCross` chain does NOT
  literally compose into one theorem, because four consumer lemmas each independently `obtain … :=
  baseVaryingIFTPackage …` (or `… := inverseChart_lipschitz_package …`), yielding INDEPENDENT
  existential witnesses `V, f', ρ, σ, r` that Lean CANNOT identify as equal across separate
  ∃-eliminations — even though, internally, they are the SAME term (`V = ⇑Φ.symm`,
  `f' = fderiv ℝ Wbv`, for the one Mathlib IFT `OpenPartialHomeomorph`
  `Φ = hbaseC2.toOpenPartialHomeomorph Wbv hW'0 hn2`).  Definitional equality of the hidden witnesses
  is NOT a usable interface across two separate ∃-eliminations.

  ## THE FIX (construct once, eliminate once).  This file bundles the base-varying IFT/CoV data into a
  single `structure BaseVaryingIFTData`, constructed EXACTLY ONCE by `baseVaryingIFTData_of_hbaseC2`
  (inlining the `Φ` construction of `baseVaryingIFTPackage` AND the `V`-Lipschitz derivation of
  `inverseChart_lipschitz_package`, so `V := ⇑Φ.symm` and the canonical derivative `fderiv ℝ Wbv` are
  the SAME concrete terms across ALL fields).  Every downstream fact — the change of variables, the
  weight-matching identity, the open-map superset, and the `∘V` transported regularity — is then a
  lemma PARAMETERIZED by that ONE structure `D`, so all consumers share EXACTLY `D.V` and
  `fderiv ℝ Wbv`.  The `f'`-vs-`fderiv` mismatch is dissolved outright: the structure never carries an
  abstract `f'`; it states every derivative/CoV fact directly in terms of `fderiv ℝ Wbv`.

  ## WHAT LANDS (all conditional on `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, discharged unconditionally by
     `wbv_contDiffAt_two` — J4-941 — in `baseVaryingIFTData`).
    • `BaseVaryingIFTData` — the common-witness structure (shared `ρ, V, σ, L_V` + the primitive
        IFT facts M1–M4, `himg`, `V 0 = 0`, `V`-Lipschitz).
    • `baseVaryingIFTData_of_hbaseC2` / `baseVaryingIFTData` — the SINGLE construction (conditional /
        unconditional respectively).  `baseVaryingIFTData` shows the structure is INHABITED from the
        standing geometry alone — the strongest non-vacuity statement.
    • `commonWitness_cov` (★★) — the CoV identity about `D.V`, `fderiv ℝ Wbv`.
    • `commonWitness_weightMatch` (★) — `∀ w ∈ image, Wbv (D.V w) = w`, about the SAME `D.V`.
    • `commonWitness_superset` (★) — `∃ r>0, ball 0 r ⊆ image`.
    • `commonWitness_mapsTo` (★) — `∀ w ∈ image, D.V w ∈ ball 0 D.ρ` (the membership the assembly needs
        to evaluate `fderiv ℝ Wbv (D.V w)` inside the CoV domain).
    • `commonWitness_transport` (★★) — the GENERIC `∘V` transport about `D.V`: any ball-local
        bounded+Lipschitz weight `Q` gives `Q ∘ D.V` bounded+Lipschitz on an image ball.
    • `commonWitness_ampF_transport` / `commonWitness_CfieldF_transport` (★★) — the CONCRETE census
        integrands `(chartFieldAmp·F0)/|det|` and `(censusAmpTauDeriv·F0)/|det|` transported along the
        SAME `D.V` (composing `census_ampF_ratio_regularity` through the generic transport).
    • `commonWitness_transport_slot_satisfiable` — non-vacuity of the `Q`-slot (TEETH: `cos‖·‖`).

  ## HONEST STATUS.  This CLOSES structural gap G1 (common-witness incoherence): the CoV, the
  weight-match, the superset, and the transported regularity are now provably about the SAME `D.V` and
  the SAME `fderiv ℝ Wbv`, extracted from ONE construction, hence genuinely composable.  It does NOT
  close `hCross`/`hCensusBound`: gap G2 (the `ball 0 r ⊆ {z : 0 ∈ S z}` S-gate carry) and gap G3 (the
  F-factor Levi carries `{hDuhamel, hDConv, hCConv}`) REMAIN and are NOT touched here.
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseVaryingIFTPackage
import QIQTH.ChartGaussianChangeVar
import QIQTH.AmpQuantBundle
import QIQTH.CensusHbaseC2Discharge
import QIQTH.CensusAmpConcreteRegularity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators

namespace QIQTH.BaseVaryingIFTCommonWitness

open QIQTH.HeatResidualBound QIQTH.CensusTauDerivGateSplit
open QIQTH.CensusAmpConcreteRegularity QIQTH.CensusHbaseC2Discharge
open QIQTH.BaseVaryingIFTPackage

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### §0 — the common-witness structure.
    ############################################################################### -/

/-- **★★★ `BaseVaryingIFTData` — the common-witness structure.**  Bundles, for the base-varying chart
    `Wbv z = uniformInverseChart g gi hC hK z 0`, the SHARED radius `ρ` (CoV domain), the SHARED local
    inverse `V`, the SHARED Lipschitz radius `σ`/constant `L_V`, together with the primitive
    IFT/CoV facts:  the within-derivative field (M1) with the CANONICAL derivative `fderiv ℝ Wbv`
    (NO abstract `f'`), injectivity (M2), the left inverse (M3), the positive Jacobian (M4), the image
    neighbourhood, `V 0 = 0`, and the `V`-Lipschitz bound.  Constructing this ONCE and having every
    downstream fact consume the SAME `D` is the fix for G1.  NOT `a₁ = R/6`. -/
structure BaseVaryingIFTData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : Type where
  ρ : ℝ
  hρ : 0 < ρ
  V : Point n → Point n
  σ : ℝ
  hσ : 0 < σ
  L_V : ℝ
  hLV : 0 ≤ L_V
  measurable_ball : MeasurableSet (Metric.ball (0 : Point n) ρ)
  hderiv : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0)
        (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z)
        (Metric.ball (0 : Point n) ρ) z
  hinj : Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)
  hleftInv : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      V (uniformInverseChart g gi hC hK z 0) = z
  hdetPos : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      0 < |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|
  himg : (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
      ∈ 𝓝 (0 : Point n)
  hV0 : V 0 = 0
  hVlip : ∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
      ‖V x - V y‖ ≤ L_V * dist x y

/-! ###############################################################################
    ### §1 — the SINGLE construction (inlining `Φ` once).
    ############################################################################### -/

/-- **★★★ `baseVaryingIFTData_of_hbaseC2` — the common-witness construction (one `Φ`, once).**  Given
    the geometry (`hC`, `hK`, `K ∈ 𝓝 0`) and the honest regularity residual `hbaseC2`, constructs the
    Mathlib IFT `OpenPartialHomeomorph` `Φ` EXACTLY ONCE and bundles ALL primitive facts about the SAME
    `V := ⇑Φ.symm` and the canonical `fderiv ℝ Wbv`.  This inlines `baseVaryingIFTPackage` (M1–M4,
    `himg`) and `inverseChart_lipschitz_package` (`V`-Lipschitz) into a single construction so their
    witnesses coincide by construction.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFTData_nonempty_of_hbaseC2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    Nonempty (BaseVaryingIFTData g gi hC hK) := by
  classical
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbvdef
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hWbv0 : Wbv 0 = 0 := uniformInverseChart_zero g gi hC hK h0K
  set e : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.neg ℝ with hedef
  have hW'0 : HasFDerivAt Wbv ((e : Point n →L[ℝ] Point n)) 0 := by
    rw [hWbvdef, hedef]
    exact baseVaryingChart_hasFDerivAt_center g gi hC hK h0Kmem
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hfderiv0 : fderiv ℝ Wbv 0 = (e : Point n →L[ℝ] Point n) := hW'0.fderiv
  set Φ := hbaseC2.toOpenPartialHomeomorph Wbv hW'0 hn2 with hΦdef
  have hΦcoe : (⇑Φ : Point n → Point n) = Wbv := by
    rw [hΦdef]; exact hbaseC2.toOpenPartialHomeomorph_coe hW'0 hn2
  have h0src : (0 : Point n) ∈ Φ.source := by
    rw [hΦdef]; exact hbaseC2.mem_toOpenPartialHomeomorph_source hW'0 hn2
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp Φ.open_source 0 h0src
  have hevC2 : ∀ᶠ y in 𝓝 (0 : Point n), ContDiffAt ℝ 2 Wbv y := hbaseC2.eventually (by norm_num)
  have hevdiff : ∀ᶠ y in 𝓝 (0 : Point n), DifferentiableAt ℝ Wbv y :=
    hevC2.mono (fun _ hy => hy.differentiableAt (by norm_num))
  have hfderiv_cont : ContinuousAt (fun y => fderiv ℝ Wbv y) 0 :=
    (hbaseC2.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hdetabs_cont : ContinuousAt (fun y => |(fderiv ℝ Wbv y).det|) 0 :=
    (continuous_abs.continuousAt).comp
      ((ContinuousLinearMap.continuous_det.continuousAt).comp hfderiv_cont)
  have hdet0_ne : (fderiv ℝ Wbv 0).det ≠ 0 := by
    rw [hfderiv0]
    have hcoe : (e : Point n →L[ℝ] Point n) = -ContinuousLinearMap.id ℝ (Point n) := by
      ext x; simp [hedef]
    rw [hcoe]
    show LinearMap.det (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) ≠ 0
    have hL : (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
        Point n →ₗ[ℝ] Point n) = (-1 : ℝ) • LinearMap.id := by
      ext x; simp
    rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have hdet0abs : (0 : ℝ) < |(fderiv ℝ Wbv 0).det| := abs_pos.mpr hdet0_ne
  have hevdet : ∀ᶠ y in 𝓝 (0 : Point n),
      |(fderiv ℝ Wbv 0).det| / 2 < |(fderiv ℝ Wbv y).det| :=
    hdetabs_cont.tendsto.eventually (eventually_gt_nhds (by linarith [hdet0abs]))
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp (hevdiff.and hevdet)
  -- The `V = Φ.symm` Lipschitz data (mirroring `inverseChart_lipschitz_package`).
  have hVc2 : ContDiffAt ℝ 2 (⇑Φ.symm) (0 : Point n) := by
    have hti := hbaseC2.to_localInverse hW'0 hn2
    rw [hWbv0] at hti
    exact hti
  have hV1 : ContDiffAt ℝ 1 (⇑Φ.symm) (0 : Point n) := hVc2.of_le (by norm_num)
  have hV0 : (⇑Φ.symm) (0 : Point n) = 0 := by
    have h := Φ.left_inv h0src
    have hc0 : (⇑Φ : Point n → Point n) 0 = 0 := by rw [hΦcoe]; exact hWbv0
    rw [hc0] at h; exact h
  obtain ⟨rlip, hrlip, Llip, hLlip, hlip⟩ :=
    QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball (⇑Φ.symm) hV1
  -- Assemble the structure (one construction, shared witnesses).
  refine ⟨
    { ρ := min δ₁ ε
      hρ := lt_min hδ₁ hε
      V := ⇑Φ.symm
      σ := rlip
      hσ := hrlip
      L_V := Llip
      hLV := hLlip
      measurable_ball := measurableSet_ball
      hderiv := ?_
      hinj := ?_
      hleftInv := ?_
      hdetPos := ?_
      himg := ?_
      hV0 := hV0
      hVlip := ?_ }⟩
  · -- M1: within-derivative field with the canonical `fderiv ℝ Wbv`.
    intro z hz
    have hzε : dist z (0 : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    exact ((hεspec hzε).1.hasFDerivAt).hasFDerivWithinAt
  · -- M2: injectivity on the ball, from `Φ.injOn`.
    have hinjS : Set.InjOn (⇑Φ) Φ.source := Φ.injOn
    rw [hΦcoe] at hinjS
    exact hinjS.mono (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
  · -- M3: `Φ.symm` left inverse on the ball.
    intro z hz
    have hzsrc : z ∈ Φ.source :=
      hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz)
    have h := Φ.left_inv hzsrc
    have hcz : (⇑Φ : Point n → Point n) z = Wbv z := congrFun hΦcoe z
    rw [hcz] at h; exact h
  · -- M4: positive Jacobian.
    intro z hz
    have hzε : dist z (0 : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have hb := (hεspec hzε).2
    linarith [hdet0abs, hb]
  · -- image neighbourhood glue.
    have hopen : IsOpen ((⇑Φ) '' Metric.ball (0 : Point n) (min δ₁ ε)) :=
      Φ.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
    rw [hΦcoe] at hopen
    have hmem : (0 : Point n) ∈ Wbv '' Metric.ball (0 : Point n) (min δ₁ ε) :=
      ⟨0, Metric.mem_ball_self (lt_min hδ₁ hε), hWbv0⟩
    exact hopen.mem_nhds hmem
  · -- V-Lipschitz on `ball 0 rlip`.
    intro x hx y hy
    have hxb : ‖x‖ < rlip := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hyb : ‖y‖ < rlip := by simpa [Metric.mem_ball, dist_zero_right] using hy
    have h := hlip x y hxb hyb
    rwa [dist_eq_norm]

/-- **`baseVaryingIFTData_of_hbaseC2` — a concrete common-witness inhabitant (conditional).**  A
    `Classical.choice` projection of `baseVaryingIFTData_nonempty_of_hbaseC2`, for consumers that want
    a named `D` rather than to destructure the `Nonempty`.  NOT `a₁ = R/6`. -/
noncomputable def baseVaryingIFTData_of_hbaseC2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    BaseVaryingIFTData g gi hC hK :=
  (baseVaryingIFTData_nonempty_of_hbaseC2 g gi hC hK h0Kmem hbaseC2).some

/-- **★★ `baseVaryingIFTData_nonempty` — the UNCONDITIONAL common-witness inhabitance.**  Discharges the
    `hbaseC2` residual via `wbv_contDiffAt_two` (J4-941), so the common-witness structure is INHABITED
    from the standing geometry (`hC`, `hK`, `K ∈ 𝓝 0`) ALONE — the strongest non-vacuity witness for
    the whole common-witness API below.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFTData_nonempty (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    Nonempty (BaseVaryingIFTData g gi hC hK) :=
  baseVaryingIFTData_nonempty_of_hbaseC2 g gi hC hK h0Kmem (wbv_contDiffAt_two g gi hC hK h0Kmem)

/-- **`baseVaryingIFTData` — the UNCONDITIONAL concrete common-witness inhabitant.**  A
    `Classical.choice` projection of `baseVaryingIFTData_nonempty`.  NOT `a₁ = R/6`. -/
noncomputable def baseVaryingIFTData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    BaseVaryingIFTData g gi hC hK :=
  (baseVaryingIFTData_nonempty g gi hC hK h0Kmem).some

/-! ###############################################################################
    ### §2 — the four downstream facts, ALL parameterized by the SAME `D`.
    ############################################################################### -/

variable {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K}

/-- **★★ `commonWitness_cov` — the base-slot Gaussian change of variables about `D.V`.**  For the ONE
    common-witness `D`, any `τ` and weight `B`:
        `∫ z in ball 0 D.ρ, gauss τ (Wbv z) · B z
           = ∫ w in Wbv '' (ball 0 D.ρ), gauss τ w · (B (D.V w) / |det (fderiv Wbv (D.V w))|)`.
    Mirrors J4-930 but with the SHARED `D.V` and the canonical `fderiv ℝ Wbv` (no abstract `f'`).
    NOT `a₁ = R/6`. -/
theorem commonWitness_cov (D : BaseVaryingIFTData g gi hC hK) (τ : ℝ) (B : Point n → ℝ) :
    (∫ z in Metric.ball (0 : Point n) D.ρ,
        gaussDdim τ (uniformInverseChart g gi hC hK z 0) * B z)
      = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) D.ρ),
          gaussDdim τ w * (B (D.V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) :=
  QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
    τ (Metric.ball (0 : Point n) D.ρ) (fun z => uniformInverseChart g gi hC hK z 0) D.V
    (fun z => fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z)
    (fun z => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) B
    D.measurable_ball D.hderiv D.hinj D.hleftInv (fun _ _ => rfl) D.hdetPos

/-- **★ `commonWitness_weightMatch` — the exact left-inverse weight-matching identity about `D.V`.**
    `∀ w ∈ Wbv '' (ball 0 D.ρ), Wbv (D.V w) = w`, from `D.hleftInv` (M3).  Same `D.V` as the CoV.
    NOT `a₁ = R/6`. -/
theorem commonWitness_weightMatch (D : BaseVaryingIFTData g gi hC hK) :
    ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) D.ρ),
      uniformInverseChart g gi hC hK (D.V w) 0 = w := by
  rintro w ⟨z, hz, rfl⟩
  rw [D.hleftInv z hz]

/-- **★ `commonWitness_superset` — the IFT open-map superset about the SAME image.**
    `∃ r>0, ball 0 r ⊆ Wbv '' (ball 0 D.ρ)`, from `D.himg` via `Metric.mem_nhds_iff`.
    NOT `a₁ = R/6`. -/
theorem commonWitness_superset (D : BaseVaryingIFTData g gi hC hK) :
    ∃ r > (0 : ℝ), Metric.ball (0 : Point n) r
      ⊆ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) D.ρ) := by
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp D.himg
  exact ⟨r, hr, hrsub⟩

/-- **★ `commonWitness_mapsTo` — `D.V` maps the CoV image back into the CoV domain.**  For
    `w ∈ Wbv '' (ball 0 D.ρ)`, `D.V w ∈ ball 0 D.ρ` (write `w = Wbv z`, then `D.V w = z ∈ ball` by M3).
    This is the membership the literal assembly needs to evaluate `fderiv Wbv (D.V w)` inside the CoV
    domain.  NOT `a₁ = R/6`. -/
theorem commonWitness_mapsTo (D : BaseVaryingIFTData g gi hC hK) :
    ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) D.ρ),
      D.V w ∈ Metric.ball (0 : Point n) D.ρ := by
  rintro w ⟨z, hz, rfl⟩
  rw [D.hleftInv z hz]; exact hz

/-! ###############################################################################
    ### §3 — the GENERIC `∘V` transport about `D.V`, and its CONCRETE census instances.
    ############################################################################### -/

/-- **★★ `commonWitness_transport` — the GENERIC ball-local `∘V` transport about `D.V`.**  For ANY real
    weight `Q` bounded (`M_Q`) + pairwise-Lipschitz (`L_Q`) on a base ball `ball 0 rQ`, the composite
    `w ↦ Q (D.V w)` is bounded (`M_Q`) + pairwise-Lipschitz (`L_Q·D.L_V`) on an image ball `ball 0 σ'`,
    with `D.V` mapping `ball 0 σ'` into `ball 0 rQ`.  Uses ONLY `D.V0`/`D.hVlip` — the SAME `D.V` as the
    CoV.  (Mirrors `transport_ballLocal_regularity` but consumes the common-witness `D`.)  NOT
    `a₁ = R/6`. -/
theorem commonWitness_transport (D : BaseVaryingIFTData g gi hC hK)
    (Q : Point n → ℝ) (rQ M_Q L_Q : ℝ) (hrQ : 0 < rQ) (_hMQ : 0 ≤ M_Q) (hLQ : 0 ≤ L_Q)
    (hQb : ∀ z ∈ Metric.ball (0 : Point n) rQ, |Q z| ≤ M_Q)
    (hQl : ∀ x ∈ Metric.ball (0 : Point n) rQ, ∀ y ∈ Metric.ball (0 : Point n) rQ,
      |Q x - Q y| ≤ L_Q * dist x y) :
    ∃ σ' > (0 : ℝ), ∃ Lc : ℝ, 0 ≤ Lc ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ', D.V w ∈ Metric.ball (0 : Point n) rQ) ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ', |Q (D.V w)| ≤ M_Q) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ', ∀ y ∈ Metric.ball (0 : Point n) σ',
        |Q (D.V x) - Q (D.V y)| ≤ Lc * dist x y) := by
  have hLV : (0 : ℝ) ≤ D.L_V := D.hLV
  have hσ0 : (0 : ℝ) < D.σ := D.hσ
  have hmaps : ∀ w ∈ Metric.ball (0 : Point n) (min D.σ (rQ / (D.L_V + 1))),
      D.V w ∈ Metric.ball (0 : Point n) rQ := by
    intro w hw
    have hwσ : w ∈ Metric.ball (0 : Point n) D.σ :=
      Metric.ball_subset_ball (min_le_left _ _) hw
    have h0σ : (0 : Point n) ∈ Metric.ball (0 : Point n) D.σ := Metric.mem_ball_self hσ0
    have hlip0 := D.hVlip w hwσ 0 h0σ
    rw [D.hV0] at hlip0
    have hVwnorm : ‖D.V w‖ ≤ D.L_V * ‖w‖ := by
      simpa [dist_zero_right, sub_zero] using hlip0
    have hwr : ‖w‖ < rQ / (D.L_V + 1) := by
      have hd : dist w (0 : Point n) < min D.σ (rQ / (D.L_V + 1)) := Metric.mem_ball.mp hw
      rw [dist_zero_right] at hd
      exact lt_of_lt_of_le hd (min_le_right _ _)
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖D.V w‖ ≤ D.L_V * ‖w‖ := hVwnorm
      _ ≤ (D.L_V + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
      _ < (D.L_V + 1) * (rQ / (D.L_V + 1)) := by
            apply mul_lt_mul_of_pos_left hwr (by positivity)
      _ = rQ := by field_simp
  refine ⟨min D.σ (rQ / (D.L_V + 1)), lt_min hσ0 (by positivity), L_Q * D.L_V,
    mul_nonneg hLQ hLV, hmaps, ?_, ?_⟩
  · intro w hw
    exact hQb (D.V w) (hmaps w hw)
  · intro x hx y hy
    have hVx := hmaps x hx
    have hVy := hmaps y hy
    have h1 := hQl (D.V x) hVx (D.V y) hVy
    have h2 := D.hVlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
                        y (Metric.ball_subset_ball (min_le_left _ _) hy)
    calc |Q (D.V x) - Q (D.V y)| ≤ L_Q * dist (D.V x) (D.V y) := h1
      _ = L_Q * ‖D.V x - D.V y‖ := by rw [dist_eq_norm]
      _ ≤ L_Q * (D.L_V * dist x y) := mul_le_mul_of_nonneg_left h2 hLQ
      _ = L_Q * D.L_V * dist x y := by ring

/-- **★★ `commonWitness_ampF_transport` — the CONCRETE census integrand `(amp·F0)/|det|` transported
    along the SAME `D.V`.**  Composes `census_ampF_ratio_regularity` (the base-ball bounded+Lipschitz
    regularity of `q₁ = (chartFieldAmp·F0)/|det (fderiv Wbv)|`) through `commonWitness_transport`, so
    the transported integrand `w ↦ (chartFieldAmp … τ (D.V w) 0 · F0 (D.V w)) / |det (fderiv Wbv (D.V
    w))|` is bounded + pairwise-Lipschitz on an image ball — about the SAME `D.V` as `commonWitness_cov`.
    Amplitude concrete, only `F0` carried.  NOT `a₁ = R/6`. -/
theorem commonWitness_ampF_transport (D : BaseVaryingIFTData g gi hC hK) (a b τ : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ σ' > (0 : ℝ), ∃ M Lc : ℝ, 0 ≤ M ∧ 0 ≤ Lc ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ',
        abs (chartFieldAmp g gi hC hK a b τ (D.V w) 0 * F0 (D.V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ', ∀ y ∈ Metric.ball (0 : Point n) σ',
        abs (chartFieldAmp g gi hC hK a b τ (D.V x) 0 * F0 (D.V x)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V x)).det|
            - chartFieldAmp g gi hC hK a b τ (D.V y) 0 * F0 (D.V y)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨ρ0, hρ0, M, L, hM, hL, hb, hl⟩ :=
    census_ampF_ratio_regularity g gi hC hK a b τ h0Kmem hbaseC2 hg hg0 hu
      F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl
  obtain ⟨σ', hσ', Lc, hLc, _, htqb, htql⟩ :=
    commonWitness_transport D
      (fun z => chartFieldAmp g gi hC hK a b τ z 0 * F0 z
          / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|)
      ρ0 M L hρ0 hM hL hb hl
  exact ⟨σ', hσ', M, Lc, hM, hLc, htqb, htql⟩

/-- **★★ `commonWitness_CfieldF_transport` — the CONCRETE `∂_τ`-slope census integrand
    `(censusAmpTauDeriv·F0)/|det|` transported along the SAME `D.V`.**  As
    `commonWitness_ampF_transport` but for `q₂`.  NOT `a₁ = R/6`. -/
theorem commonWitness_CfieldF_transport (D : BaseVaryingIFTData g gi hC hK) (a b : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ σ' > (0 : ℝ), ∃ M Lc : ℝ, 0 ≤ M ∧ 0 ≤ Lc ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ',
        abs (censusAmpTauDeriv g gi hC hK a b (D.V w) * F0 (D.V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ', ∀ y ∈ Metric.ball (0 : Point n) σ',
        abs (censusAmpTauDeriv g gi hC hK a b (D.V x) * F0 (D.V x)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V x)).det|
            - censusAmpTauDeriv g gi hC hK a b (D.V y) * F0 (D.V y)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨ρ0, hρ0, M, L, hM, hL, hb, hl⟩ :=
    census_CfieldF_ratio_regularity g gi hC hK a b h0Kmem hbaseC2 hg hg0 hu
      F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl
  obtain ⟨σ', hσ', Lc, hLc, _, htqb, htql⟩ :=
    commonWitness_transport D
      (fun z => censusAmpTauDeriv g gi hC hK a b z * F0 z
          / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|)
      ρ0 M L hρ0 hM hL hb hl
  exact ⟨σ', hσ', M, Lc, hM, hLc, htqb, htql⟩

/-! ###############################################################################
    ### §4 — non-vacuity of the generic `Q`-slot (TEETH).
    ############################################################################### -/

/-- **Non-vacuity of the `Q`-slot of `commonWitness_transport`.**  The bounded + pairwise-Lipschitz
    weight hypotheses (on a GENUINE ball `rQ>0`) are satisfiable with TEETH by `Q z := cos ‖z‖`
    (bounded by `1`, genuinely varying, Lipschitz `1`), `rQ = 1`.  Confirms the transport `Q`-slot is
    not vacuous.  NOT `a₁ = R/6`. -/
theorem commonWitness_transport_slot_satisfiable :
    ∃ (Q : Point n → ℝ) (rQ M_Q L_Q : ℝ), 0 < rQ ∧ 0 ≤ M_Q ∧ 0 ≤ L_Q ∧
      (∀ z ∈ Metric.ball (0 : Point n) rQ, |Q z| ≤ M_Q) ∧
      (∀ x ∈ Metric.ball (0 : Point n) rQ, ∀ y ∈ Metric.ball (0 : Point n) rQ,
        |Q x - Q y| ≤ L_Q * dist x y) := by
  refine ⟨fun z => Real.cos ‖z‖, 1, 1, 1, one_pos, zero_le_one, zero_le_one, ?_, ?_⟩
  · intro z _
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · intro x _ y _
    have h1 : |Real.cos ‖x‖ - Real.cos ‖y‖| ≤ |‖x‖ - ‖y‖| := by
      have hlip := Real.lipschitzWith_cos.dist_le_mul ‖x‖ ‖y‖
      simpa [Real.dist_eq, one_mul] using hlip
    have h2 : |‖x‖ - ‖y‖| ≤ dist x y := by
      rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y
    calc |Real.cos ‖x‖ - Real.cos ‖y‖| ≤ |‖x‖ - ‖y‖| := h1
      _ ≤ dist x y := h2
      _ = 1 * dist x y := (one_mul _).symm

end QIQTH.BaseVaryingIFTCommonWitness

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseVaryingIFTCommonWitness
#print axioms baseVaryingIFTData_nonempty_of_hbaseC2
#print axioms baseVaryingIFTData_of_hbaseC2
#print axioms baseVaryingIFTData_nonempty
#print axioms baseVaryingIFTData
#print axioms commonWitness_cov
#print axioms commonWitness_weightMatch
#print axioms commonWitness_superset
#print axioms commonWitness_mapsTo
#print axioms commonWitness_transport
#print axioms commonWitness_ampF_transport
#print axioms commonWitness_CfieldF_transport
#print axioms commonWitness_transport_slot_satisfiable
end AxiomChecks
