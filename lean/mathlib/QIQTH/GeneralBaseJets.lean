/-
  GeneralBaseJets — J4-156: the general-base SECOND field line-jet (J1b) existence brick.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of
  the `a₁ = R/6` heat-kernel campaign — the F3-frontier item (3): the general-base SECOND field
  line-jet existence (`J1b`) of the K-uniform inverse chart
  `V_z := uniformInverseChart g gi hC hK z` (base `z` FIXED, field slot, field centre `0`).  It
  supplies the `hJetP`/`Q`-existence half of the exact `gaussComp_pd_pd` / `gaussComp_amp_pd_pd`
  jet interface consumed by `NormalFormDischarge.hNormalForm_concrete`, at a GENERAL base `z`,
  from the honest field-chart-centre `C²` carry `ContDiffAt ℝ 2 (V_z) 0`.

  ── THE 30-MINUTE ASSESSMENT (all three F3-frontier items, per the J4-156 charge).

    (1) hEgrad (LeviLipschitz's carried E-gradient bound
        `|pd (fun p => E τ p w) i ζ| ≤ C_g·τ^{−1/2}·G-shape`, `E := heatOp g gi H`).  The field-slot
        derivative `∂ᵢ(∂_τH − Δ_pH)` is a MIXED THIRD jet of `H`.  The exp/chart tower is
        `ContDiffOn ℝ 4` in the VELOCITY slot (`expMap_contDiffOn_four`, C⁴) but the FIELD-slot
        chart regularity (`uniformInverseChart_huniformChart`) is only `ContDiffAt ℝ 2` at image
        points; a third FIELD jet of `V_z` is NOT in the tower.  The `∂_τ`/`Δ_p` mix further needs a
        `gaussComp`-style third-derivative chain rule (there is only `gaussComp_pd_pd` = second
        order) plus a τ^{−1/2}-shaped Gaussian-moment bound on the third jet.  ⇒ VERDICT: GENUINE
        MULTI-BRICK LAYER (needs a chart third-jet provider + a `gaussComp_pd_pd_pd` normal form +
        the Gaussian third-moment bound).  Effort estimate: 3–5 bricks; NOT this file.

    (2) the m-uniform `C_R` (`SliverSumPlumbing`/`EngineInstantiation` `hbnd` upstream; the per-
        application `∃ C_R` of `witness_sliver2_grand`/`_concrete`).  `witness_sliver2_concrete`
        returns `∃ C_R, 0 ≤ C_R ∧ …` where the ONLY genuinely per-application-hidden constant is
        `C_R` (the term-0 √ε coefficient); the explicit term-1/term-2 constants `C_E1`/`C_E2` are
        already strip-level, built from `(τ₀/aT/T/n/M₁/M₂/C_L/C_W/C_P/C_Q)` VERBATIM in the bound.
        Extracting an m-UNIFORM `C_R` is therefore PURE BOOKKEEPING (re-run `witness_sliver2_grand`'s
        `∃ C_R` with the strip constants exposed and take the `⨆`/max over the finite jet range), NOT
        blocked — but it is a re-plumbing exercise that touches the sliver-sum layer, larger than a
        single clean lemma.  ⇒ VERDICT: TRACTABLE-but-plumbing (bookkeeping, not blocked).

    (3) general-base `J1b` SECOND field jets (the `hAmp2`-analogue at the CHART, second field jet at
        general base).  `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general` already gives
        the honest `ContDiffAt ℝ 2 (V_z) 0` for every base `z` whose field centre is an exp-image
        point; `ChartJetBounds.chartField_firstJet_of_contDiffAt` shows the FIRST jet exists from that
        `C²`.  The SECOND jet is exactly the line-derivative at `0` of the first-jet function
        `P x k := DV_z(x)(eᵢ) k`, and `P` is `C¹` near `0` (from `ContDiffAt ℝ 2 ⟹
        ContDiffAt ℝ 1 (fderiv V_z)`, `ContDiffAt.fderiv_right`), so the second line-jet `Q` EXISTS
        by the `ContDiffAt → HasDerivAt` extraction (the `ChartJetBounds` `z = 0` pattern lifted to
        general base).  ⇒ VERDICT: TRACTABLE — this file.  (The z-slot MODULUS `‖Q z‖ ≤ C_Q` needs
        base-point regularity of the `.choose`-built chart, the recognized J3 blocker; only the
        EXISTENCE is the J1b discharge, so the bound stays CARRIED.)

  ── WHAT LANDS (this file executes item (3)).
    • `hasDerivAt_update_line`                 — the general-base coordinate line
        `s ↦ update x i s` has `HasDerivAt` value `eᵢ = Pi.single i 1` at `s = x i`.
    • `chartField_firstJet_nhds_of_contDiffAt` — ★ from `ContDiffAt ℝ 2 (V_z) 0`, the FIRST field
        jet `HasDerivAt (fun s ↦ V_z (update x i s) k) (DV_z(x)(eᵢ) k) (x i)` holds for ALL `x` in a
        NEIGHBOURHOOD of the field centre `0` (the `hJetV` shape, near-`0` form).
    • `chartField_secondJet_of_contDiffAt`     — ★★ the SECOND field jet EXISTS at the centre:
        `∃ Q, ∀ k, HasDerivAt (fun s ↦ DV_z(update 0 i s)(eᵢ) k) (Q k) ((0:Point n) i)` — the exact
        `hJetP` line shape of `gaussComp_pd_pd`, from the `C¹` regularity of `fderiv V_z` at `0`.
    • `chartField_secondJet_general`           — ★★ the bundle: an explicit first-jet function `P`
        (the `fderiv`-column of `V_z`) and a second-jet `Q` with the near-`0` `hJetV` AND the `hJetP`
        at `0`, in the EXACT shapes consumed by `hNormalForm_concrete`.
    • `chartField_secondJet_center`            — the base-`z = 0` specialisation, UNCONDITIONAL
        (given `0 ∈ K`), via `ChartJetBounds.chartField_contDiffAt_center`.
    • `chartField_secondJet_domain`            — the "∀ z ∈ domain" existence: a single radius
        `δ₀ > 0` over `K` such that whenever `0` is an exp-image point of base `z` with pre-image
        `‖v‖ < δ₀`, the second field jet exists — via
        `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, never the conclusion).
    • The `∀ x` GLOBAL `hJetV` form (this file gives only the near-`0` neighbourhood form; the field
      chart is known `C²` only near image points, so global first-jet existence is carried).
    • The z-slot MODULUS `‖Q z‖ ≤ C_Q` (`hJ3Q` of `witness_sliver2_concrete`) — the recognized J3
      base-point-regularity blocker; only jet EXISTENCE is the J1b discharge here.
    • The deeper VALUE `D²V_0(0) = 0` (already reduced in `ChartJetBounds` to `D²φ_0(0)=0` under the
      gauge `christoffel(0)=0`); this file proves EXISTENCE of `Q`, not that it vanishes.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetBounds
import QIQTH.AmplitudeFamilyDischarge

open Filter Finset
open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    The general-base coordinate line derivative.
    ############################################################################### -/

/-- **General-base line derivative.**  The coordinate line `s ↦ update x i s` has `HasDerivAt`
    value `eᵢ = Pi.single i 1` at the base `s = x i` (componentwise: component `i` is `s ↦ s`
    with derivative `1`, every other component is the constant `x j` with derivative `0`). -/
theorem hasDerivAt_update_line (x : Point n) (i : Fin n) :
    HasDerivAt (fun s : ℝ => Function.update x i s) (Pi.single i (1 : ℝ)) (x i) := by
  refine hasDerivAt_pi.mpr (fun j => ?_)
  by_cases h : j = i
  · subst h
    have he : (fun s : ℝ => Function.update x j s j) = fun s => s := by
      funext s; simp
    have hv : (Pi.single j (1 : ℝ) : Point n) j = 1 := by simp
    rw [he, hv]; exact hasDerivAt_id (x j)
  · have he : (fun s : ℝ => Function.update x i s j) = fun _ => x j := by
      funext s; simp only [Function.update_apply, if_neg h]
    have hv : (Pi.single i (1 : ℝ) : Point n) j = 0 := by
      simp only [Pi.single_apply, if_neg h]
    rw [he, hv]; exact hasDerivAt_const (x i) (x j)

/-! ###############################################################################
    ★ The near-`0` FIRST field jet (the `hJetV` shape) from the `C²` centre carry.
    ############################################################################### -/

/-- **★ `chartField_firstJet_nhds_of_contDiffAt`.**  From the honest field-chart-centre carry
    `hreg : ContDiffAt ℝ 2 (V_z) 0`, the FIRST field line-jet of `V_z` exists — in the exact
    `gaussComp_pd_pd` `hV1` shape — at EVERY base `x` in a NEIGHBOURHOOD of the field centre `0`,
    with value the `i`-th column of the inverse-chart Jacobian `DV_z(x)`:
        `HasDerivAt (fun s ↦ V_z (update x i s) k) ((DV_z(x)) eᵢ k) (x i)`.
    (Near-`0` neighbourhood form; the GLOBAL `∀ x` form is carried.)  NOT `a₁ = R/6`. -/
theorem chartField_firstJet_nhds_of_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) 0) :
    ∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
      HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k)
        (fderiv ℝ (uniformInverseChart g gi hC hK z) x (Pi.single i (1 : ℝ)) k) (x i) := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  have hdiff : ∀ᶠ x in 𝓝 (0 : Point n), DifferentiableAt ℝ W x := by
    filter_upwards [hreg.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  filter_upwards [hdiff] with x hx
  intro k
  have hWfd : HasFDerivAt W (fderiv ℝ W x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self i x]; exact hx.hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => W (Function.update x i s))
      (fderiv ℝ W x (Pi.single i (1 : ℝ))) (x i) := by
    have h := hWfd.comp_hasDerivAt (x i) (hasDerivAt_update_line x i)
    simpa using h
  exact (hasDerivAt_pi.mp hcomp) k

/-! ###############################################################################
    ★★ The SECOND field jet EXISTS at the centre (the `hJetP` shape).
    ############################################################################### -/

/-- **★★ `chartField_secondJet_of_contDiffAt` (J1b existence, general base).**  From the honest
    field-chart-centre carry `hreg : ContDiffAt ℝ 2 (V_z) 0`, the SECOND field line-jet of `V_z`
    EXISTS at the field centre `0`, in the exact `gaussComp_pd_pd` `hP1` line shape:
        `∃ Q, ∀ k, HasDerivAt (fun s ↦ DV_z(update 0 i s)(eᵢ) k) (Q k) ((0:Point n) i)`.
    Route: `ContDiffAt ℝ 2 (V_z) 0 ⟹ ContDiffAt ℝ 1 (fderiv V_z) 0` (`ContDiffAt.fderiv_right`), so
    the map `x ↦ DV_z(x)(eᵢ)` is differentiable at `0`; composing with the coordinate line
    (`hasDerivAt_update_zero_line`) gives the line-derivative `Q`.  This is the J1b discharge — the
    EXISTENCE of the second jet; its VALUE (`= 0`) and z-MODULUS are carried elsewhere.
    NOT `a₁ = R/6`. -/
theorem chartField_secondJet_of_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) 0) :
    ∃ Q : Point n, ∀ k,
      HasDerivAt (fun s : ℝ =>
          fderiv ℝ (uniformInverseChart g gi hC hK z) (Function.update 0 i s) (Pi.single i (1 : ℝ)) k)
        (Q k) ((0 : Point n) i) := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  -- `fderiv W` is `C¹` at `0`; hence `G x := DW(x)(eᵢ)` is differentiable at `0`.
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ W y) (0 : Point n) :=
    hreg.fderiv_right (m := 1) (by norm_num)
  have hΦ : DifferentiableAt ℝ (fun y => fderiv ℝ W y) (0 : Point n) :=
    hfd.differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ (fun y => (fderiv ℝ W y) (Pi.single i (1 : ℝ))) (0 : Point n) :=
    hΦ.clm_apply (differentiableAt_const _)
  have hGfd : HasFDerivAt (fun y => (fderiv ℝ W y) (Pi.single i (1 : ℝ)))
      (fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single i (1 : ℝ))) 0)
      (Function.update (0 : Point n) i (0 : ℝ)) := by
    rw [update_zero_zero]; exact hG.hasFDerivAt
  -- compose with the coordinate line `s ↦ update 0 i s` (derivative `eᵢ` at `s = 0`).
  have hcomp : HasDerivAt
      (fun s : ℝ => (fderiv ℝ W (Function.update (0 : Point n) i s)) (Pi.single i (1 : ℝ)))
      (fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single i (1 : ℝ))) 0 (Pi.single i (1 : ℝ)))
      (0 : ℝ) := by
    have h := hGfd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_zero_line i)
    simpa using h
  refine ⟨fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single i (1 : ℝ))) 0 (Pi.single i (1 : ℝ)),
    fun k => ?_⟩
  exact (hasDerivAt_pi.mp hcomp) k

/-! ###############################################################################
    ★★ The bundle: first jet (near `0`) + second jet (at `0`) in the exact jet shapes.
    ############################################################################### -/

/-- **★★ `chartField_secondJet_general` (the J1b bundle).**  From the honest field-chart-centre
    carry `hreg : ContDiffAt ℝ 2 (V_z) 0`, there exist an explicit first-jet function `P` (the
    `fderiv`-column of `V_z`) and a second-jet `Q` such that BOTH the near-`0` `hJetV` shape and the
    `hJetP`-at-`0` shape of `gaussComp_pd_pd`/`hNormalForm_concrete` hold:
      • `∀ᶠ x in 𝓝 0, ∀ k, HasDerivAt (fun s ↦ V_z (update x i s) k) (P x k) (x i)`,
      • `∀ k, HasDerivAt (fun s ↦ P (update 0 i s) k) (Q k) ((0:Point n) i)`.
    Packages `chartField_firstJet_nhds_of_contDiffAt` (with `P x k := DV_z(x)(eᵢ) k`) and
    `chartField_secondJet_of_contDiffAt`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJet_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) 0) :
    ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
      (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
          HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k)
            (P x k) (x i))
      ∧ (∀ k, HasDerivAt
          (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) := by
  obtain ⟨Q, hQ⟩ := chartField_secondJet_of_contDiffAt g gi hC hK z i hreg
  refine ⟨fun x k => fderiv ℝ (uniformInverseChart g gi hC hK z) x (Pi.single i (1 : ℝ)) k, Q,
    ?_, ?_⟩
  · exact chartField_firstJet_nhds_of_contDiffAt g gi hC hK z i hreg
  · intro k; exact hQ k

/-! ###############################################################################
    The base-`z = 0` (unconditional) specialisation and the "∀ z ∈ domain" form.
    ############################################################################### -/

/-- **`chartField_secondJet_center` (unconditional at the assembly base).**  At `z = 0 ∈ K`, the
    field-chart-centre `C²` is TOWER-DERIVED unconditionally
    (`ChartJetBounds.chartField_contDiffAt_center`), so the second field jet EXISTS at the field
    centre with no carry.  NOT `a₁ = R/6`. -/
theorem chartField_secondJet_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (i : Fin n) :
    ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
      (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
          HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK 0 (Function.update x i s) k)
            (P x k) (x i))
      ∧ (∀ k, HasDerivAt
          (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) :=
  chartField_secondJet_general g gi hC hK 0 i (chartField_contDiffAt_center g gi hC hK h0K)

/-- **`chartField_secondJet_domain` (∀ z ∈ domain).**  A single radius `δ₀ > 0` over `K` such that
    whenever the field centre `0` is an exp-image point of base `z` with pre-image `‖v‖ < δ₀`, the
    second field line-jet of `V_z` EXISTS at `0` (in both jet shapes).  Combines
    `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general` (the `hreg` provider) with
    `chartField_secondJet_general`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJet_domain (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n,
      uniformFlowExp g gi hC hK z v = 0 → ‖v‖ < δ₀ →
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
            HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k)
              (P x k) (x i))
        ∧ (∀ k, HasDerivAt
            (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := chartField_contDiffAt_center_general g gi hC hK
  refine ⟨δ₀, hδ₀, fun z hz v hexp hvlt => ?_⟩
  exact chartField_secondJet_general g gi hC hK z i (hspec z hz v hexp hvlt)

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.hasDerivAt_update_line
#print axioms QIQTH.HeatResidualBound.chartField_firstJet_nhds_of_contDiffAt
#print axioms QIQTH.HeatResidualBound.chartField_secondJet_of_contDiffAt
#print axioms QIQTH.HeatResidualBound.chartField_secondJet_general
#print axioms QIQTH.HeatResidualBound.chartField_secondJet_center
#print axioms QIQTH.HeatResidualBound.chartField_secondJet_domain
