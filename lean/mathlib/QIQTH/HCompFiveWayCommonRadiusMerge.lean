/-
  HCompFiveWayCommonRadiusMerge — J4-1051: the FIVE-WAY common-radius merge flagged by J4-1050's own
  report ("the flagged future dispatch — mirroring `ChartEvalSlotRadiusMerge.nb_common_chart_radius`").

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1050 lifted J4-1046's `kPrime` base-slot CoV capstone to hold UNIFORMLY for every
  `0 < R' ≤ R` (its own existential radius `R`).  `ChartEvalSlotRadiusMerge.nb_common_chart_radius`
  (J4-1015) already merges THREE independent eval-slot existential radii — J4-1012's IFT-package `ρ`,
  J4-1013's reversal-link `r`, J4-1014's domain-containment `ρ_dom` — into ONE `ρstar := min(min ρ1 r)
  ρ3`, via `.mono`/subset monotonicity of each ingredient in its own radius. `EvalBaseSlotCoordinateBridge`
  (J4-1048/1049) supplies a further independent radius `r` at which the RAW base-slot/eval-slot
  coordinate identity `w_b(z) = -T_x(w_e(z))` holds pointwise, hence (via `bridge_image_eq`) its image-set
  corollary on any `D ⊆ ball x r`.

  This dispatch asked (and had `gpt-5.6-sol`, high, confirm BEFORE writing any Lean): is a further `min`
  merging ALL FIVE radii — J4-1050's `R`, J4-1015's already-merged `ρstar` (itself 3 radii), and the
  bridge's `r` — into ONE common radius `ρ** := min(min R ρstar) r` a valid PURE BOOKKEEPING step, exactly
  mirroring `nb_common_chart_radius`'s own technique?

  Sol's verdict (Q1): **GO**, pure `min`/`le_trans` bookkeeping — no hidden obstruction, since (A)
  (J4-1050) already quantifies over every `R' ≤ R`, (B) (`nb_common_chart_radius`) already quantifies
  over every `ρ' ≤ ρstar`, and (C) (the bridge) restricts pointwise / by subset composition to any smaller
  ball; none of the three secretly fails to restrict.

  Sol's verdict (Q2, the substantive question — does this ALSO let the antisymmetrized-difference bound
  compose?): **NO-GO**. The common radius synchronizes DOMAINS only, not WITNESSES. J4-1050's `V_base`
  (from the `K ∩ U` wrapper's own tuple) and `nb_common_chart_radius`'s `V_eval, f'` (from
  `ChartIFTPackageGeneralQ0`'s M1–M4 tuple) remain two independently-packaged existential bundles that the
  radius merge does NOT identify or relate; the bridge's abstract facts (`bridge_hasFDerivAt`,
  `bridge_det_abs`, `bridge_left_inverse`) are still not instantiated at those two SPECIFIC bundles — that
  instantiation, exactly as J4-1048/1049 already flagged, remains a separate, substantial, unattempted
  task. Confirmed unchanged by this dispatch's radius merge.

  THIS FILE supplies exactly the bookkeeping payoff Sol GO'd: `fiveway_common_chart_radius` — a single
  `ρstar` such that for EVERY `0 < ρ'' ≤ ρstar`, ALL FIVE original ingredients (J4-1050's literal `kPrime`
  CoV identity on `K ∩ ball x ρ''`; J4-1015's uniform eval-slot weighted CoV; the reversal-link ball
  integral; the eval-slot domain-containment `MapsTo`; and the bridge's image-set identity on
  `ball x ρ''`) hold SIMULTANEOUSLY — built by black-box reuse of the three already-proven theorems
  (`kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge_uniform`, `nb_common_chart_radius`,
  `evalBase_slot_coordinate_bridge_image_ball`), NOT by re-deriving any of their internals.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`. It resolves
  ONLY the FIVE-WAY radius-merge bookkeeping (per Sol's Q1 GO). It does **NOT**:
    • identify, relate, or reconcile J4-1050's `V_base`/`PI`/`PJ`/`Q` with `nb_common_chart_radius`'s
      `V_eval`/`f'` — the two existential CoV bundles remain SEPARATE tuples, conjoined only by holding on
      the SAME ball, not composed into one identity;
    • instantiate `EvalBaseSlotCoordinateBridge`'s abstract `bridge_hasFDerivAt` / `bridge_det_abs` /
      `bridge_left_inverse` at those two bundles' actual `V`/`f'` objects (per Sol's Q2 NO-GO, confirmed
      unchanged);
    • establish any Jacobian/weight DOMINATION or compose any of the five ingredients into a literal
      difference-form bound on `nb`'s `term1`, i.e. `G_τ(T_x v) − G_τ(v)`;
    • discharge `hxmem`'s GENERAL discharge over all of `K` (remains DEFINITIVELY CLOSED OFF, cp988–991,
      unchanged — J4-1050's ingredient still only ever works on `K ∩ (a ball)`).
  `Bfac`'s other 3 summands and `fb` remain untouched. No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited (NEW FILE).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryFullLocalDischargeUniform
import QIQTH.ChartEvalSlotRadiusMerge
import QIQTH.EvalBaseSlotCoordinateBridge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.ExpMap QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ConcreteGateAssembly QIQTH.OnGateFieldRegularity QIQTH.HFdCoreContinuityClosed
open QIQTH.HCompNearCarryFullLocalDischargeUniform
open QIQTH.JointRNCRegularityLocalGeneralK
open QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.ChartGeneralChangeVarEvalSlot
open QIQTH.ReversalLinkBallIntegral
open QIQTH.ChartEvalSlotDomainContainment
open QIQTH.ChartEvalSlotRadiusMerge
open QIQTH.EvalBaseSlotCoordinateBridge
open scoped Topology Interval BigOperators

namespace QIQTH.HCompFiveWayCommonRadiusMerge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `fiveway_common_chart_radius`.**  A SINGLE common radius `ρstar` at which J4-1050's literal
    `kPrime` base-slot CoV capstone, `nb_common_chart_radius`'s uniform eval-slot weighted CoV, the
    reversal-link ball integral, the eval-slot domain-containment `MapsTo`, and the base/eval
    coordinate-bridge image identity ALL hold simultaneously, for EVERY `0 < ρ'' ≤ ρstar`. Pure
    `min`/`le_trans` bookkeeping over the three already-proven black-box theorems — confirmed GO
    (Q1) by `gpt-5.6-sol` (high) before this file was written. Does NOT relate the two independently
    packaged CoV witness bundles (Q2 NO-GO, confirmed unchanged) and does NOT compose into any bound on
    `nb`. NOT `a₁ = R/6`. -/
theorem fiveway_common_chart_radius
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (i j : Fin n) (t s : ℝ) (Rtgt : ℝ) (hRtgt : 0 < Rtgt) :
    ∃ δ₀ > (0 : ℝ), ∃ δ₀' > (0 : ℝ), ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧
    ∀ c : ℝ, b < c → c < δ₀ → 0 < c → c < δ₀' → c ≤ ρ₀ → C_L * c < 1 →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
    ∀ {x : Point n}, x ∈ interior K →
    ∀ _hτ : 0 < t - s,
    ∃ ρstar > (0 : ℝ), ∃ (Veval : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      ∀ ρ'' : ℝ, 0 < ρ'' → ρ'' ≤ ρstar →
        (∃ (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
            (S'' : Set (Point n)) (Vbase : Point n → Point n),
          IsOpen S'' ∧ x ∈ S'' ∧ S'' ⊆ K ∩ Metric.ball x ρ'' ∧
          (∫ z in S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
            = ∫ w in (fun p => uniformInverseChart g gi hC hK p x) '' S'',
                gaussDdim (t - s) w
                  * ((fun z =>
                        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
                          * (((∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                                  * (∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                                  / (4 * (t - s) ^ 2)
                                - ((∑ k, PI z x k * PJ z x k)
                                    + (∑ k, uniformInverseChart g gi hC hK z x k * Q z k))
                                  / (2 * (t - s)))
                                * chartFieldAmp g gi hC hK a b (t - s) z x
                              + (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                                    / (2 * (t - s)))
                                  * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
                              + (-(∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                                    / (2 * (t - s)))
                                  * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
                              + pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x))
                      (Vbase w)
                      / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p x) (Vbase w)).det|))
        ∧ (∀ B : Point n → ℝ,
          (∫ z in Metric.ball x ρ'',
              gaussDdim (t - s) (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
            = ∫ w in (uniformInverseChart g gi hC hK x) '' (Metric.ball x ρ''),
                gaussDdim (t - s) (terminalVelAt g gi hC hK x w) * (B (Veval w) / |(f' (Veval w)).det|))
        ∧ (∀ B : Point n → ℝ,
          (∫ z in Metric.ball x ρ'', gaussDdim (t - s) (uniformInverseChart g gi hC hK z x) * B z)
            = ∫ z in Metric.ball x ρ'',
                gaussDdim (t - s) (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
        ∧ Set.MapsTo (uniformInverseChart g gi hC hK x) (Metric.ball x ρ'') (Metric.ball 0 Rtgt)
        ∧ ∀ D : Set (Point n), D ⊆ Metric.ball x ρ'' →
            (fun z => uniformInverseChart g gi hC hK z x) '' D
              = (fun w => -terminalVelAt g gi hC hK x w) ''
                  ((fun z => uniformInverseChart g gi hC hK x z) '' D) := by
  obtain ⟨δ₀, hδ₀, δ₀', hδ₀', ρ₀, hρ₀, C_L, hCL0, hspecA⟩ :=
    QIQTH.HCompNearCarryFullLocalDischargeUniform.kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge_uniform
      g gi hC hK a b ha hab hg hgpos hu i j t s
  refine ⟨δ₀, hδ₀, δ₀', hδ₀', ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro c hbc hcδ hc0 hcδ' hcρ hCLc S hSeq x hxint hτ
  obtain ⟨R_A, hR_A, hAspec⟩ := hspecA c hbc hcδ hc0 hcδ' hcρ hCLc S hSeq hxint
  have hAat := hAspec hτ
  have hxKnhds : K ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨ρstarB, hρstarB, Veval, f', hBspec⟩ :=
    QIQTH.ChartEvalSlotRadiusMerge.nb_common_chart_radius g gi hC hK hxint (t - s) Rtgt hRtgt
  obtain ⟨rC, hrC, hCspec⟩ :=
    QIQTH.EvalBaseSlotCoordinateBridge.evalBase_slot_coordinate_bridge_image_ball g gi hC hK hxKnhds
  refine ⟨min (min R_A ρstarB) rC, lt_min (lt_min hR_A hρstarB) hrC, Veval, f',
    fun ρ'' hρ''0 hρ''le => ?_⟩
  have hle1 : ρ'' ≤ R_A := le_trans hρ''le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle2 : ρ'' ≤ ρstarB := le_trans hρ''le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle3 : ρ'' ≤ rC := le_trans hρ''le (min_le_right _ _)
  obtain ⟨hcov, hrev, hmaps⟩ := hBspec ρ'' hρ''0 hle2
  exact ⟨hAat ρ'' hρ''0 hle1, hcov, hrev, hmaps,
    fun D hD => hCspec D (hD.trans (Metric.ball_subset_ball hle3))⟩

end QIQTH.HCompFiveWayCommonRadiusMerge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompFiveWayCommonRadiusMerge
#print axioms fiveway_common_chart_radius
end AxiomChecks
