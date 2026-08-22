/-
  GeneralBaseJetsMixed — J4-1030: the general-base MIXED second field line-jet (r2, off-diagonal)
  existence brick.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  Continuing cp983's
  chain (`HCompNearCarryKPrimeGateRestrictedCoV`'s residual r2 — the 2nd-order field-variable jet
  existence for `uniformInverseChart` needed by `hJetVi`/`hJetVj`/`hJetQ`, DIAGNOSED as genuinely
  unbuilt, orthogonal to any local/global-in-`z` quantifier reframe).  This file does NOT close r2
  as literally stated (the `∀ y : Point n`-unrestricted, `∀ z ∈ K`-uniform-in-`x` shape) — see the
  firewall below — but supplies the GENUINE MIXED-DIRECTION analogue of the ALREADY-BANKED
  `GeneralBaseJets.chartField_secondJet_of_contDiffAt`/`_general`/`_domain` (which only handles the
  DIAGONAL case, differentiating the SAME direction `i` twice), extending it to two DIFFERENT
  directions `i ≠ j` (or `i = j`, unified) — i.e. the actual OFF-DIAGONAL Hessian entry `∂ᵢ∂ⱼ`
  `ChartJetHessianMixed`'s `hJetVi`/`hJetVj`/`hJetQ` need, at the field CENTRE `0`.

  ── THE FINDING (gpt-5.6-sol high, 2026-08-23, consulted BEFORE this file).  Candidate (a)
  ("explicit affine unfolding of `uniformInverseChart`") does NOT exist: `uniformInverseChart` is a
  `Classical.choice`-selected `OpenPartialHomeomorph.symm` from an `ApproximatesLinearOn` IFT
  argument (`UniformChartRadius.uniformChart_exists`), with NO closed-form formula and junk
  off-target values.  The genuinely CHEAP alternative Sol flagged instead is a pure Mathlib
  COMPOSITION cp983 did not check against the PRIMITIVE `ContDiffAt ℝ 2` fact itself (only against
  auxiliary Lipschitz/continuity lemmas): `ContDiffAt.fderiv_right` (`ContDiffAt 𝕜 n f x₀ →
  m+1≤n → ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀`) composed with `.differentiableAt`/`.hasFDerivAt` and the
  campaign's own `hasDerivAt_update_line`/`comp_hasDerivAt` coordinate-line idiom, turns the
  ALREADY-BANKED `ContDiffAt ℝ 2 (uniformInverseChart z) 0` (`ChartJetBounds`/`AmplitudeFamilyDischarge`)
  into genuine SECOND-order jet EXISTENCE — MECHANICALLY, with ZERO new derivative-existence theory.
  This EXACT route is already executed in-repo for the DIAGONAL case
  (`GeneralBaseJets.chartField_secondJet_of_contDiffAt`, i twice) and one order deeper for the THIRD
  jet (`ChartThirdJet.chartField_thirdJet_of_contDiffAt`).  Sol confirmed: (b) the original 5-dispatch
  size estimate for r2 was based on NOT knowing this bridge applies to the OFF-DIAGONAL case too — the
  purely-LOCAL calculus piece is now ~1 lemma, not a multi-dispatch campaign; (c) banking the
  restricted (field-centre `0`, near-`0` first jet) mixed version is honest, non-vacuous, reusable
  progress that isolates the REMAINING gap precisely (chart-coverage: the literal downstream
  hypothesis in `HCompNearCarryKPrimeGateRestrictedCoV` needs the SAME `x` to be the field-centre
  reachable point from EVERY `z ∈ K` — an unestablished, separate geometric fact, NOT a calculus
  gap).

  ── WHAT LANDS (mirrors `GeneralBaseJets` verbatim, generalized from one direction `i` to two `i j`).
    • `chartField_secondJetMixed_of_contDiffAt` — ★★ from `hreg : ContDiffAt ℝ 2 (V_z) 0`, the MIXED
        second field jet EXISTS at the field centre `0`:
          `∃ Q, ∀ k, HasDerivAt (fun s ↦ DV_z(update 0 i s)(eⱼ) k) (Q k) ((0:Point n) i)`
        — the exact `hJetQ`-at-`(i,j)` line shape of `gaussComp_pd_pd_mixed`/`ChartJetHessianMixed`,
        with `i = j` recovering `GeneralBaseJets.chartField_secondJet_of_contDiffAt` verbatim.
    • `chartField_secondJetMixed_general` — ★★ the bundle: explicit first-jet functions `PI`/`PJ`
        (the `i`-th and `j`-th `fderiv`-columns of `V_z`, each valid on a near-`0` neighbourhood via
        `GeneralBaseJets.chartField_firstJet_nhds_of_contDiffAt`) and a mixed second-jet `Q`, in the
        EXACT hypothesis shapes (`hJetVi`/`hJetVj`/`hJetQ`) of `ChartJetHessianMixed.witnessMixed_gate_eq`
        / `HCompNearCarryKPrimeGateRestrictedCoV.kPrime_baseField_CoV_of_jetBundle_gateRestricted`,
        RESTRICTED to the field CENTRE `x = 0` (`hJetQ`) and a near-`0` neighbourhood (`hJetVi`/`hJetVj`).
    • `chartField_secondJetMixed_center`  — the base-`z = 0` specialisation, UNCONDITIONAL.
    • `chartField_secondJetMixed_domain`  — the "∀ z ∈ domain" existence: a single radius `δ₀ > 0`
        over `K` such that whenever the field centre `0` is an exp-image point of base `z` with
        pre-image `‖v‖ < δ₀`, the mixed second field jet EXISTS at `0` (both jet shapes).

  ── WHAT REMAINS CARRIED / NOT CLAIMED (honest scope; do NOT over-claim).
    • The `∀ y : Point n` GLOBAL-unrestricted form of `hJetVi`/`hJetVj` (this file gives only the
      near-`0` neighbourhood form, same honest limitation as `GeneralBaseJets`).
    • The field point being a GENERAL fixed `x` shared uniformly across `∀ z ∈ K` (this file's `Q`
      lives at the field CENTRE `0` specifically, reachable per-`z` via a per-`z` pre-image `v`; it
      does NOT establish that one fixed `x` is reachable from every `z ∈ K` — the chart-coverage gap
      Sol identified as the actual remaining blocker for
      `HCompNearCarryKPrimeGateRestrictedCoV.kPrime_baseField_CoV_of_jetBundle_gateRestricted`).
    • `Bfac`'s other summands, `fb` (far carry) — untouched, as always.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited (NEW FILE).
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GeneralBaseJets

open Filter Finset
open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ★★ The MIXED SECOND field jet EXISTS at the centre — off-diagonal generalization of
    `chartField_secondJet_of_contDiffAt` (which is the `i = j` special case).
    ############################################################################### -/

/-- **★★ `chartField_secondJetMixed_of_contDiffAt` (r2 mixed existence, general base, field centre).**
    From the honest field-chart-centre carry `hreg : ContDiffAt ℝ 2 (V_z) 0`, the MIXED second field
    line-jet of `V_z` EXISTS at the field centre `0`, in the exact `gaussComp_pd_pd_mixed`/`hJetQ` line
    shape for TWO (possibly distinct) directions `i j`:
        `∃ Q, ∀ k, HasDerivAt (fun s ↦ DV_z(update 0 i s)(eⱼ) k) (Q k) ((0:Point n) i)`.
    Route: `ContDiffAt ℝ 2 (V_z) 0 ⟹ ContDiffAt ℝ 1 (fderiv V_z) 0` (`ContDiffAt.fderiv_right`), so
    the map `x ↦ DV_z(x)(eⱼ)` is differentiable at `0`; composing with the coordinate line in
    direction `i` (`hasDerivAt_update_zero_line`) gives the mixed line-derivative `Q`.  Reduces to
    `GeneralBaseJets.chartField_secondJet_of_contDiffAt` when `i = j`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJetMixed_of_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i j : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) 0) :
    ∃ Q : Point n, ∀ k,
      HasDerivAt (fun s : ℝ =>
          fderiv ℝ (uniformInverseChart g gi hC hK z) (Function.update 0 i s) (Pi.single j (1 : ℝ)) k)
        (Q k) ((0 : Point n) i) := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  -- `fderiv W` is `C¹` at `0`; hence `G x := DW(x)(eⱼ)` is differentiable at `0`.
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ W y) (0 : Point n) :=
    hreg.fderiv_right (m := 1) (by norm_num)
  have hΦ : DifferentiableAt ℝ (fun y => fderiv ℝ W y) (0 : Point n) :=
    hfd.differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) (0 : Point n) :=
    hΦ.clm_apply (differentiableAt_const _)
  have hGfd : HasFDerivAt (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ)))
      (fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) 0)
      (Function.update (0 : Point n) i (0 : ℝ)) := by
    rw [update_zero_zero]; exact hG.hasFDerivAt
  -- compose with the coordinate line `s ↦ update 0 i s` (derivative `eᵢ` at `s = 0`).
  have hcomp : HasDerivAt
      (fun s : ℝ => (fderiv ℝ W (Function.update (0 : Point n) i s)) (Pi.single j (1 : ℝ)))
      (fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) 0 (Pi.single i (1 : ℝ)))
      (0 : ℝ) := by
    have h := hGfd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_zero_line i)
    simpa using h
  refine ⟨fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) 0 (Pi.single i (1 : ℝ)),
    fun k => ?_⟩
  exact (hasDerivAt_pi.mp hcomp) k

/-! ###############################################################################
    ★★ The bundle: two first jets (near `0`, directions `i` and `j`) + mixed second jet (at `0`)
    in the EXACT `hJetVi`/`hJetVj`/`hJetQ` shapes.
    ############################################################################### -/

/-- **★★ `chartField_secondJetMixed_general` (the r2-mixed bundle).**  From the honest
    field-chart-centre carry `hreg : ContDiffAt ℝ 2 (V_z) 0`, there exist explicit first-jet functions
    `PI`/`PJ` (the `i`-th/`j`-th `fderiv`-columns of `V_z`) and a mixed second-jet `Q` such that ALL
    THREE of the `ChartJetHessianMixed`/`HCompNearCarryKPrimeGateRestrictedCoV` `hJetVi`/`hJetVj`/`hJetQ`
    shapes hold, RESTRICTED to a near-`0` neighbourhood (`hJetVi`/`hJetVj`) and the centre `0`
    (`hJetQ`):
      • `∀ᶠ x in 𝓝 0, ∀ k, HasDerivAt (fun s ↦ V_z (update x i s) k) (PI x k) (x i)`,
      • `∀ᶠ x in 𝓝 0, ∀ k, HasDerivAt (fun s ↦ V_z (update x j s) k) (PJ x k) (x j)`,
      • `∀ k, HasDerivAt (fun s ↦ PJ (update 0 i s) k) (Q k) ((0:Point n) i)`.
    Packages `chartField_firstJet_nhds_of_contDiffAt` (twice, at `i` and `j`) with
    `chartField_secondJetMixed_of_contDiffAt`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJetMixed_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i j : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) 0) :
    ∃ (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
      (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
          HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k)
            (PI x k) (x i))
      ∧ (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
          HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x j s) k)
            (PJ x k) (x j))
      ∧ (∀ k, HasDerivAt
          (fun s : ℝ => PJ (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) := by
  obtain ⟨Q, hQ⟩ := chartField_secondJetMixed_of_contDiffAt g gi hC hK z i j hreg
  refine ⟨fun x k => fderiv ℝ (uniformInverseChart g gi hC hK z) x (Pi.single i (1 : ℝ)) k,
    fun x k => fderiv ℝ (uniformInverseChart g gi hC hK z) x (Pi.single j (1 : ℝ)) k, Q,
    ?_, ?_, ?_⟩
  · exact chartField_firstJet_nhds_of_contDiffAt g gi hC hK z i hreg
  · exact chartField_firstJet_nhds_of_contDiffAt g gi hC hK z j hreg
  · intro k; exact hQ k

/-! ###############################################################################
    The base-`z = 0` (unconditional) specialisation and the "∀ z ∈ domain" form.
    ############################################################################### -/

/-- **`chartField_secondJetMixed_center` (unconditional at the assembly base).**  At `z = 0 ∈ K`, the
    field-chart-centre `C²` is TOWER-DERIVED unconditionally
    (`ChartJetBounds.chartField_contDiffAt_center`), so the mixed second field jet EXISTS at the field
    centre with no carry.  NOT `a₁ = R/6`. -/
theorem chartField_secondJetMixed_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) (i j : Fin n) :
    ∃ (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
      (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
          HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK 0 (Function.update x i s) k)
            (PI x k) (x i))
      ∧ (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
          HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK 0 (Function.update x j s) k)
            (PJ x k) (x j))
      ∧ (∀ k, HasDerivAt
          (fun s : ℝ => PJ (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) :=
  chartField_secondJetMixed_general g gi hC hK 0 i j (chartField_contDiffAt_center g gi hC hK h0K)

/-- **`chartField_secondJetMixed_domain` (∀ z ∈ domain).**  A single radius `δ₀ > 0` over `K` such
    that whenever the field centre `0` is an exp-image point of base `z` with pre-image `‖v‖ < δ₀`,
    the mixed second field line-jet EXISTS at `0` (all three jet shapes).  Combines
    `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general` (the `hreg` provider) with
    `chartField_secondJetMixed_general`.  NOT `a₁ = R/6`. -/
theorem chartField_secondJetMixed_domain (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n,
      uniformFlowExp g gi hC hK z v = 0 → ‖v‖ < δ₀ →
      ∃ (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
            HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k)
              (PI x k) (x i))
        ∧ (∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
            HasDerivAt (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x j s) k)
              (PJ x k) (x j))
        ∧ (∀ k, HasDerivAt
            (fun s : ℝ => PJ (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := chartField_contDiffAt_center_general g gi hC hK
  refine ⟨δ₀, hδ₀, fun z hz v hexp hvlt => ?_⟩
  exact chartField_secondJetMixed_general g gi hC hK z i j (hspec z hz v hexp hvlt)

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.chartField_secondJetMixed_of_contDiffAt
#print axioms QIQTH.HeatResidualBound.chartField_secondJetMixed_general
#print axioms QIQTH.HeatResidualBound.chartField_secondJetMixed_center
#print axioms QIQTH.HeatResidualBound.chartField_secondJetMixed_domain
