/-
  DiagSliverGatedCoInstantiation — J4-814: THE SINGLE SHARED-WITNESS CO-INSTANTIATION of the closed
  x-uniform DIAGONAL sliver rate `XUniformSliverFull.witness_sliver2_xuniform`, at ONE concrete gated
  van-Vleck witness tuple.  The diagonal (`i = j`) twin of
  `MixedSliverGatedCoInstantiation.witness_sliver2_xuniform_mixed_gated` (J4-811).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  ASSEMBLY step: the diagonal sliver rate theorem `witness_sliver2_xuniform` carries ~30 abstract
  hypotheses over abstract data `(D2H, F, Y, P, Q, A0, A1, A2, …)`.  This file INSTANTIATES all of them at
  the ONE shared concrete tuple

    • `Y   := gateDisp G (uniformInverseChart g gi hC hK z₀)`     (gated raw inverse-chart displacement)
    • `P   := gateJet G P i`,  `Q := gateQ G Q`                   (gated raw chart jets, single index `i`)
    • `A0  := gateAmp S z₀ (chartFieldAmp …)`, `A1 := gateAmp S z₀ (pd …)`, `A2 := gateAmp S z₀ (pd pd …)`
    • `F   := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))`
    • `D2H := fun τ ζ => pd (fun y => pd (fun x' => vanVleckGatedWitness … τ x' z₀) i y) i ζ`

  and DISCHARGES the nine cleanly-matching slots directly from the already-banked suppliers:
    • the FOUR global geometric estimates `hco/hYdisp/hJ3/hJ3Q`
        ← `MixedSliverGatedEstimates.gateDisp_hco_global` / `gateDisp_hVdisp_global` / `gateJet_hJ3_global`
          / `gateQ_bound_global` (J4-799), from ball/on-gate data;
    • the THREE amplitude sup bounds `hA0bdd/hA1bdd/hA2bdd`
        ← `DiagSliverAmpBounds.witnessDiag_amplitude_sup_bounds` (J4-810), from on-gate data;
    • the Gaussian domination `hFdom` (with its constant `C_L`)
        ← `MixedSliverFdom.leviSeries_hFdom_gated` (J4-794), from the banked `LeviSeriesLocalData` package;
    • the three-term diagonal `hNormalForm`
        ← `DiagNormalFormGatedMatch.witnessDiag_hNormalForm_gated` (J4-813, from J4-809).

  ── HONEST SCOPE OF THE CARRIED RESIDUE (the same two classes as the mixed J4-811).  Two classes of the
  sliver's carries are passed THROUGH as hypotheses of this co-instantiation, not discharged here:
    (1)  `hqLip` — the per-slice product-Lipschitz/measurability/bound triple for `A0·F` at the GENERAL
         field point `x` with a SINGLE uniform constant `L`.  The supplier
         `MixedSliverGateAmpLipschitz.mixedSliver_hqLip_triple_via_gateAmp` (index-free, reusable) delivers
         this triple only at the FIXED field point `0` with the `s`-dependent constant `M_A·L_F + M_F·L_A`,
         so the single `x`-and-`s`-uniform `L` triple is carried as `hqLip`.
    (2)  the five integrand integrabilities `hIntT1/hIntT2/hIntT3/hInt1/hInt2`.  The diagonal suppliers
         `DiagSliverIntegrands.integrable_*_onGate` (J4-812) discharge these from on-gate data per field
         point `x`; carrying the five `Integrable … volume` conclusions is the honest terminal interface.

  The `Q`-slot is filled with the SAME raw jet `Q` used by the normal form (via `gateQ`), and its bound
  `hJ3Q` is derived from the carried on-gate `hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q` — the same design choice as
  the mixed J4-811 (sidestepping the J4-803 `Qfield ↔ fderiv∘fderiv` component identity).

  Every hypothesis is satisfiable and non-vacuous (all off-gate/zero placeholders satisfy the on-gate legs
  trivially; the flat model gives a genuinely-nonzero witness), and none equals the conclusion.  No
  `sorry`, no new axioms.  NOT `a₁ = R/6` (the diagonal sliver rate is one input to the CLM operator-norm
  sliver, itself one census member of the still-CONDITIONAL `a₁ = R/6` chain).
-/
import Mathlib
import QIQTH.XUniformSliverFull
import QIQTH.DiagNormalFormGatedMatch
import QIQTH.DiagSliverAmpBounds
import QIQTH.MixedSliverGatedEstimates
import QIQTH.MixedSliverFdom

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.MixedSliverGatedEstimates QIQTH.DiagSliverAmpBounds QIQTH.MixedSliverFdom
open QIQTH.DiagNormalFormGatedMatch QIQTH.MixedNormalFormFull
open QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData
open scoped Interval Topology BigOperators

namespace QIQTH.DiagSliverGatedCoInstantiation

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★★★ J4-814 — THE SINGLE SHARED-WITNESS CO-INSTANTIATION OF THE DIAGONAL SLIVER RATE.**  For the
    concrete gated van-Vleck witness tuple (see the file header), the terminal `√ε` diagonal-sliver rate
    holds at EVERY field point `x`, with the domination constant `C_L` produced by the banked
    `LeviSeriesLocalData` package.  The nine geometric/amplitude/domination/normal-form slots of
    `XUniformSliverFull.witness_sliver2_xuniform` are discharged from the already-banked suppliers
    (J4-794/799/810/813) at this ONE tuple; the `hqLip` triple (uniform `L`, general field point) and the
    five integrand integrabilities are carried as the honest terminal interface.  The diagonal twin of
    `MixedSliverGatedCoInstantiation.witness_sliver2_xuniform_mixed_gated`.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_diag_gated
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (P Q : Point n → Point n)
    (L M₀ M₁ M₂ C T aₗ τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (u ε : ℝ) (haₗ : 0 < aₗ) (hau : aₗ ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aₗ / 2) (hετ₀ : ε ≤ τ₀)
    -- ── (I) the four geometric on-gate estimates (ball forms; J4-796/797/798).
    (hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z₀ z))
    (hVdisp_on : ∀ z ∈ G, ‖uniformInverseChart g gi hC hK z₀ z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3_on : ∀ z ∈ G, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q)
    -- ── (II) the three amplitude on-gate sup bounds (J4-810 base inputs).
    (hg0 : ∀ τ, ∀ w ∈ S z₀, |chartFieldAmp g gi hC hK a b τ z₀ w| ≤ M₀)
    (hg1 : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) i w| ≤ M₁)
    (hg2 : ∀ τ, ∀ w ∈ S z₀,
        |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) i w| ≤ M₂)
    -- ── (III) the normal-form chart/amplitude jets (J4-809/813 inputs).
    (hJetV : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (P y k) (y i))
    (hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update ζ i s) k) (Q ζ k) (ζ i))
    (hAmpDi : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ y : Point n,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) i y)
    (hAmpD2 : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) i ζ)
    (hOffNhd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0)
    -- ── (IV) the banked Levi domination package for the gated van-Vleck source (J4-794 input).
    (data : LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C T)
    -- ── (V) the CARRIED per-slice Lipschitz triple `hqLip` (uniform `L`, general field point).
    (hqLip : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n,
          |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x
            - gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) w
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s w x|
          ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n =>
            gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume
        ∧ ∃ M, ∀ z : Point n,
            |gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M)
    -- ── (VI) the five CARRIED integrand integrabilities (J4-812 discharges from on-gate data).
    (hIntT1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (gateDisp G (uniformInverseChart g gi hC hK z₀) z)
              - gaussDdim (u - s) z)
            * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G P i z k) ^ 2
                / (4 * (u - s) ^ 2)
                - ((∑ k, gateJet G P i z k * gateJet G P i z k)
                    + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                  / (2 * (u - s)))
            * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)) volume)
    (hIntT2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G P i z k) ^ 2
                / (4 * (u - s) ^ 2)
                - ((∑ k, gateJet G P i z k * gateJet G P i z k)
                    + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                  / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)) volume)
    (hIntT3 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)) volume)
    (hInt1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G P i)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume)
    (hInt2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ')) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ x : Point n,
      |∫ s in (u - ε)..u, ∫ z,
          (fun τ ζ => pd (fun y => pd (fun x' =>
              vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) i ζ) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x|
        ≤ ((15 / 2 * (n : ℝ) * L
              + (sliverRateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀
                  + tE2RateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀))
            + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim aₗ (0 : Point n))
                * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                  + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                  + ((n : ℝ) * C_W * C_P)
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))))
            * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim aₗ (0 : Point n)) * ε := by
  -- ── hFdom + its constant `C_L`, from the banked Levi package (J4-794).
  obtain ⟨C_L, hCL0, hFdom⟩ := leviSeries_hFdom_gated g gi hC hK S a b C T data
  refine ⟨C_L, hCL0, ?_⟩
  -- ── the four global geometric estimates, from the gating layer (J4-799).
  have hco := gateDisp_hco_global G (uniformInverseChart g gi hC hK z₀) hco_on
  have hYdisp := gateDisp_hVdisp_global G (uniformInverseChart g gi hC hK z₀) C_W hC_W hVdisp_on
  have hJ3 := gateJet_hJ3_global G P i C_P hC_P hJ3_on
  have hJ3Q := gateQ_bound_global G Q C_Q hC_Q hJ3Q_on
  -- ── the three amplitude sup bounds, from the gate-localization (J4-810).
  obtain ⟨hA0bdd, hA1bdd, hA2bdd⟩ :=
    witnessDiag_amplitude_sup_bounds g gi hC hK S a b i z₀ M₀ M₁ M₂ hM₀ hM₁ hM₂ hg0 hg1 hg2
  -- ── the three-term diagonal normal form under the gated geometry (J4-813).
  have hNF := witnessDiag_hNormalForm_gated g gi hC hK S a b i τ₀ z₀ hz₀ hSopen G hSG
    P Q hJetV hJetQ hAmpDi hAmpD2 hOffNhd
  -- ── the single fully-instantiated call.
  exact witness_sliver2_xuniform
    (fun τ ζ => pd (fun y => pd (fun x' =>
        vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) i ζ)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G P i) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ'))
    i L M₀ M₁ M₂ C_L T aₗ τ₀ C_W C_P C_Q
    hL hM₀ hM₁ hM₂ hCL0 hC_W hC_P hC_Q
    u ε haₗ hau huT hε0 hεu hεa hετ₀
    hco hYdisp hJ3 hJ3Q hA0bdd hA1bdd hA2bdd hFdom hNF
    hqLip hIntT1 hIntT2 hIntT3 hInt1 hInt2

end QIQTH.DiagSliverGatedCoInstantiation

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DiagSliverGatedCoInstantiation
#print axioms witness_sliver2_xuniform_diag_gated
end AxiomChecks
