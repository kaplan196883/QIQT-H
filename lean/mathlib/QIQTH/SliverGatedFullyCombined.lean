/-
  SliverGatedFullyCombined — J4-817: the FULLY-COMBINED gated sliver co-instantiations, with BOTH
  residue classes DISCHARGED for the mixed AND diagonal legs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the final
  ASSEMBLY step that composes the two independently-built residue discharges of J4-815/816 into a single
  call, for each of the mixed (`witness_sliver2_xuniform_mixed`) and diagonal (`witness_sliver2_xuniform`)
  gated sliver rates:

    (A) the `hqLip` residue — DISCHARGED by `MixedSliverHqLipUniform.gateAmpLevi_hqLip_uniform` (the
        `√s`-sup that manufactures the single uniform Lipschitz constant `M₀·(L_E + K_F·2√u) + M_F·L_A`
        from the raw amplitude Lipschitz/bound/off-gate data and the Levi kernel's `s`-dependent spatial
        Lipschitz slot at the general field point);  this is what `..._hqLipUniform` (J4-816) already does.
    (B) the integrand-integrability residue — DISCHARGED by `SliverIntegrandXUniform.uniform_*` (J4-815),
        which turn the per-slice `∀ x, ∀ s ∈ Ioo (u−ε) u, Integrable …` conclusions the two sliver rate
        theorems consume into PRIMITIVE on-gate data (finite measurable gate + off-gate amplitude
        vanishing + per-`(x,s)` on-gate measurability + per-`(x,s)` on-gate sup bounds).

  Because `..._hqLipUniform` was built INDEPENDENTLY of `SliverIntegrandXUniform`, it STILL carries the
  seven (mixed) / five (diagonal) `Integrable` slots as hypotheses.  This file feeds the `uniform_*`
  outputs into exactly those slots, so the resulting theorems carry NEITHER `hqLip` NOR any `Integrable`
  carry: the ONLY residues are standard on-gate geometric/gauge/measurability/boundedness premises.

  ── WHAT LANDS (all std-3; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `witness_sliver2_xuniform_mixed_gated_fullyCombined` — the mixed sliver rate at the gated van-Vleck
      witness tuple, with BOTH residue classes discharged; residue = primitive on-gate data only.
    * `witness_sliver2_xuniform_diag_gated_fullyCombined`  — the diagonal twin.

  ── HONEST SCOPE.  The off-gate amplitude-vanishing `hAsupp` slots of the integrand suppliers are proved
  INTERNALLY (a gated amplitude vanishes off its gate, `gateAmp_of_notMem`), so they are NOT carried.  The
  finite-measurable gate `(hSmeas, hSfin)`, the geometric-factor measurabilities of `V/Pi/Pj/Q` (resp.
  `Y/P`), the amplitude/Levi on-gate measurabilities, and the per-`(x,s)` on-gate sup bounds are carried
  as the honest terminal interface — exactly the primitive on-gate data of J4-808/812/815.  Every such
  hypothesis is satisfiable and non-vacuous (`V=Pi=Pj=Q=0`, `A0=A1i=A1j=A2=F=0` on the gate, per-`(x,s)`
  `M=0` gives the constant-0 integrand, trivially bounded/measurable/integrable; any continuous gated data
  on a bounded gate is a genuine witness), and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverHqLipUniform
import QIQTH.SliverIntegrandXUniform

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.MixedSliverAssembly QIQTH.MixedGradientSlice
open QIQTH.MixedSliverGatedEstimates QIQTH.MixedSliverAmpBounds QIQTH.MixedSliverFdom
open QIQTH.MixedNormalFormGatedMatch QIQTH.MixedNormalFormFull QIQTH.MixedSliverXUniform
open QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData
open QIQTH.MixedSliverHqLipUniform QIQTH.SliverIntegrandXUniform
open QIQTH.MixedSliverIntegrandFull QIQTH.DiagSliverIntegrands
open scoped Interval Topology BigOperators ENNReal

namespace QIQTH.SliverGatedFullyCombined

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ############################################################################
    ### MIXED — both residue classes discharged.
    ############################################################################ -/

/-- **★★★ J4-817 — the MIXED gated sliver rate with BOTH residue classes discharged.**  Same terminal
    `√ε` mixed-sliver rate as `witness_sliver2_xuniform_mixed_gated_hqLipUniform`, but the seven integrand
    integrabilities are ALSO no longer carried: they are manufactured internally by the `uniform_*_mixed`
    suppliers (J4-815) from primitive on-gate data.  Residue = standard on-gate geometric/gauge/
    measurability/boundedness premises only.  ⚠ NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_mixed_gated_fullyCombined
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (hij : i ≠ j) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (Pi Pj Q : Point n → Point n)
    (M₀ M₁i M₁j M₂ C T aₗ τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁i : 0 ≤ M₁i) (hM₁j : 0 ≤ M₁j) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (L_E K_F L_A M_F : ℝ) (hLE : 0 ≤ L_E) (hK_F : 0 ≤ K_F) (hLA : 0 ≤ L_A) (hM_F : 0 ≤ M_F)
    (u ε : ℝ) (haₗ : 0 < aₗ) (hau : aₗ ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aₗ / 2) (hετ₀ : ε ≤ τ₀)
    (hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z₀ z))
    (hVdisp_on : ∀ z ∈ G, ‖uniformInverseChart g gi hC hK z₀ z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i_on : ∀ z ∈ G, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j_on : ∀ z ∈ G, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q)
    (hg0 : ∀ τ, ∀ w ∈ S z₀, |chartFieldAmp g gi hC hK a b τ z₀ w| ≤ M₀)
    (hg1i : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) i w| ≤ M₁i)
    (hg1j : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) j w| ≤ M₁j)
    (hg2 : ∀ τ, ∀ w ∈ S z₀,
        |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) j w| ≤ M₂)
    (hJetPi : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (Pi y k) (y i))
    (hJetPj : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y j s) k) (Pj y k) (y j))
    (hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
      (fun s : ℝ => Pi (Function.update ζ j s) k) (Q ζ k) (ζ j))
    (hAmpDi : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ y : Point n,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) i y)
    (hAmpDj : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) j ζ)
    (hAmpD2 : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) j ζ)
    (hOffNhd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0)
    (data : LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C T)
    (hoffAmp : ∀ τ : ℝ, ∀ ζ ∉ S z₀, chartFieldAmp g gi hC hK a b τ z₀ ζ = 0)
    (hALipAmp : ∀ τ : ℝ, ∀ ζ ζ' : Point n,
        |chartFieldAmp g gi hC hK a b τ z₀ ζ - chartFieldAmp g gi hC hK a b τ z₀ ζ'|
          ≤ L_A * dist ζ ζ')
    (hFLipLevi : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s w x|
          ≤ (L_E + K_F * (2 * Real.sqrt s)) * dist z w)
    (hFbndLevi : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M_F)
    (hmeasLevi : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        AEStronglyMeasurable (fun z : Point n =>
          gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume)
    -- ── (INT) primitive on-gate integrand data (replacing the seven `Integrable` carries).
    (hSmeas : MeasurableSet (S z₀)) (hSfin : volume (S z₀) < ∞)
    (hVmeas : AEStronglyMeasurable (gateDisp G (uniformInverseChart g gi hC hK z₀))
      ((volume : Measure (Point n)).restrict (S z₀)))
    (hPimeas : AEStronglyMeasurable (gateJet G Pi i) ((volume : Measure (Point n)).restrict (S z₀)))
    (hPjmeas : AEStronglyMeasurable (gateJet G Pj j) ((volume : Measure (Point n)).restrict (S z₀)))
    (hQmeas : AEStronglyMeasurable (gateQ G Q) ((volume : Measure (Point n)).restrict (S z₀)))
    (hA0meas : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable
      (fun z : Point n => gateAmp S z₀
        (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z)
      ((volume : Measure (Point n)).restrict (S z₀)))
    (hA1imeas : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable
      (fun z : Point n => gateAmp S z₀
        (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ') (u - s) z)
      ((volume : Measure (Point n)).restrict (S z₀)))
    (hA1jmeas : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable
      (fun z : Point n => gateAmp S z₀
        (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ') (u - s) z)
      ((volume : Measure (Point n)).restrict (S z₀)))
    (hA2meas : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable
      (fun z : Point n => gateAmp S z₀
        (fun (τ' : ℝ) (ζ' : Point n) =>
          pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ') (u - s) z)
      ((volume : Measure (Point n)).restrict (S z₀)))
    (hFmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable
      (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)
      ((volume : Measure (Point n)).restrict (S z₀)))
    (hbndE1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |(gaussDdim (u - s) (gateDisp G (uniformInverseChart g gi hC hK z₀) z)
            - gaussDdim (u - s) z)
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pi i z k)
              * (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pj j z k)
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G Pi i z k * gateJet G Pj j z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s)))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)| ≤ M)
    (hbndPlain : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |gaussDdim (u - s) z
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pi i z k)
              * (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pj j z k)
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G Pi i z k * gateJet G Pj j z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s)))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)| ≤ M)
    (hbndRem : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |gaussDdim (u - s) z
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pi i z k)
              * (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pj j z k)
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G Pi i z k * gateJet G Pj j z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s))
              - (z i * z j) / (4 * (u - s) ^ 2))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)| ≤ M)
    (hbnd0 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |mTerm0 (gateDisp G (uniformInverseChart g gi hC hK z₀))
            (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
            (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M)
    (hbnd1i : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |mTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pj j)
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M)
    (hbnd1j : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |mTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pi i)
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M)
    (hbnd2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ x : Point n,
      |∫ s in (u - ε)..u, ∫ z,
          (fun τ ζ => pd (fun y => pd (fun x' =>
              vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x|
        ≤ ((sliverRateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀
              + (tE2RateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀
                  + (M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A) * (n : ℝ)))
            + mTerm1RateConst n M₁i C_L aₗ τ₀ C_W C_P
            + mTerm1RateConst n M₁j C_L aₗ τ₀ C_W C_P) * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim aₗ (0 : Point n)) * ε := by
  -- off-gate amplitude vanishing (a gated amplitude vanishes off its gate).
  have hAsupp0 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  have hAsupp1i : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')
        (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  have hAsupp1j : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')
        (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  have hAsupp2 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ') (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  -- the seven integrand integrabilities, manufactured from the primitive on-gate data.
  have hIntE1 := uniform_hIntE1_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp0 hVmeas hPimeas hPjmeas hQmeas hA0meas hFmeas hbndE1
  have hIntPlain := uniform_hIntPlain_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp0 hVmeas hPimeas hPjmeas hQmeas hA0meas hFmeas hbndPlain
  have hIntRem := uniform_hIntRem_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) i j u ε (S z₀) hSmeas hSfin
    hAsupp0 hVmeas hPimeas hPjmeas hQmeas hA0meas hFmeas hbndRem
  have hInt0 := uniform_hInt0_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp0 hVmeas hPimeas hPjmeas hQmeas hA0meas hFmeas hbnd0
  have hInt1i := uniform_hInt1i_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G Pj j)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp1i hVmeas hPjmeas hA1imeas hFmeas hbnd1i
  have hInt1j := uniform_hInt1j_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G Pi i)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp1j hVmeas hPimeas hA1jmeas hFmeas hbnd1j
  have hInt2 := uniform_hInt2_mixed (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
      pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp2 hVmeas hA2meas hFmeas hbnd2
  -- the hqLip-discharged co-instantiation, now with the integrabilities also supplied.
  exact witness_sliver2_xuniform_mixed_gated_hqLipUniform g gi hC hK S a b i j hij z₀ hz₀ hSopen G hSG
    Pi Pj Q M₀ M₁i M₁j M₂ C T aₗ τ₀ C_W C_P C_Q hM₀ hM₁i hM₁j hM₂ hC_W hC_P hC_Q
    L_E K_F L_A M_F hLE hK_F hLA hM_F u ε haₗ hau huT hε0 hεu hεa hετ₀
    hco_on hVdisp_on hJ3i_on hJ3j_on hJ3Q_on hg0 hg1i hg1j hg2
    hJetPi hJetPj hJetQ hAmpDi hAmpDj hAmpD2 hOffNhd data
    hoffAmp hALipAmp hFLipLevi hFbndLevi hmeasLevi
    hIntE1 hIntPlain hIntRem hInt0 hInt1i hInt1j hInt2

/-! ############################################################################
    ### DIAGONAL — both residue classes discharged.
    ############################################################################ -/

/-- **★★★ J4-817 — the DIAGONAL gated sliver rate with BOTH residue classes discharged.**  Same terminal
    `√ε` diagonal-sliver rate as `witness_sliver2_xuniform_diag_gated_hqLipUniform`, but the five integrand
    integrabilities are ALSO no longer carried: they are manufactured internally by the `uniform_*_diag`
    suppliers (J4-815) from primitive on-gate data.  Residue = standard on-gate geometric/gauge/
    measurability/boundedness premises only.  The diagonal twin of
    `witness_sliver2_xuniform_mixed_gated_fullyCombined`.  ⚠ NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_diag_gated_fullyCombined
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (P Q : Point n → Point n)
    (M₀ M₁ M₂ C T aₗ τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (L_E K_F L_A M_F : ℝ) (hLE : 0 ≤ L_E) (hK_F : 0 ≤ K_F) (hLA : 0 ≤ L_A) (hM_F : 0 ≤ M_F)
    (u ε : ℝ) (haₗ : 0 < aₗ) (hau : aₗ ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aₗ / 2) (hετ₀ : ε ≤ τ₀)
    (hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z₀ z))
    (hVdisp_on : ∀ z ∈ G, ‖uniformInverseChart g gi hC hK z₀ z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3_on : ∀ z ∈ G, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q)
    (hg0 : ∀ τ, ∀ w ∈ S z₀, |chartFieldAmp g gi hC hK a b τ z₀ w| ≤ M₀)
    (hg1 : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) i w| ≤ M₁)
    (hg2 : ∀ τ, ∀ w ∈ S z₀,
        |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) i w| ≤ M₂)
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
    (data : LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C T)
    (hoffAmp : ∀ τ : ℝ, ∀ ζ ∉ S z₀, chartFieldAmp g gi hC hK a b τ z₀ ζ = 0)
    (hALipAmp : ∀ τ : ℝ, ∀ ζ ζ' : Point n,
        |chartFieldAmp g gi hC hK a b τ z₀ ζ - chartFieldAmp g gi hC hK a b τ z₀ ζ'|
          ≤ L_A * dist ζ ζ')
    (hFLipLevi : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s w x|
          ≤ (L_E + K_F * (2 * Real.sqrt s)) * dist z w)
    (hFbndLevi : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M_F)
    (hmeasLevi : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        AEStronglyMeasurable (fun z : Point n =>
          gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume)
    -- ── (INT) primitive on-gate integrand data (replacing the five `Integrable` carries).
    (hSmeas : MeasurableSet (S z₀)) (hSfin : volume (S z₀) < ∞)
    (hmeasT1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        (gaussDdim (u - s) (gateDisp G (uniformInverseChart g gi hC hK z₀) z) - gaussDdim (u - s) z)
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G P i z k) ^ 2
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G P i z k * gateJet G P i z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s)))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x))
        ((volume : Measure (Point n)).restrict (S z₀)))
    (hbndT1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |(gaussDdim (u - s) (gateDisp G (uniformInverseChart g gi hC hK z₀) z)
            - gaussDdim (u - s) z)
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G P i z k) ^ 2
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G P i z k * gateJet G P i z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s)))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)| ≤ M)
    (hmeasT2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G P i z k) ^ 2
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G P i z k * gateJet G P i z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s))
              - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x))
        ((volume : Measure (Point n)).restrict (S z₀)))
    (hbndT2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |gaussDdim (u - s) z
          * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G P i z k) ^ 2
              / (4 * (u - s) ^ 2)
              - ((∑ k, gateJet G P i z k * gateJet G P i z k)
                  + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                / (2 * (u - s))
              - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)| ≤ M)
    (hmeasT3 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x))
        ((volume : Measure (Point n)).restrict (S z₀)))
    (hbndT3 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
          * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)| ≤ M)
    (hmeasI1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        sTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G P i)
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)
        ((volume : Measure (Point n)).restrict (S z₀)))
    (hbndI1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |sTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G P i)
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M)
    (hmeasI2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)
        ((volume : Measure (Point n)).restrict (S z₀)))
    (hbndI2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S z₀, |sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
            (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ')) (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x| ≤ M) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ x : Point n,
      |∫ s in (u - ε)..u, ∫ z,
          (fun τ ζ => pd (fun y => pd (fun x' =>
              vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) i ζ) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x|
        ≤ ((15 / 2 * (n : ℝ) * (M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A)
              + (sliverRateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀
                  + tE2RateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀))
            + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim aₗ (0 : Point n))
                * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                  + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                  + ((n : ℝ) * C_W * C_P)
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))))
            * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim aₗ (0 : Point n)) * ε := by
  have hAsupp0 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  have hAsupp1 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')
        (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  have hAsupp2 : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S z₀,
      gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ') (u - s) z = 0 :=
    fun s _ z hz => gateAmp_of_notMem S z₀ _ (u - s) hz
  -- the five integrand integrabilities, manufactured from the primitive on-gate data.
  have hIntT1 := uniform_hIntT1_diag (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G P i) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp0 hmeasT1 hbndT1
  have hIntT2 := uniform_hIntT2_diag (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateJet G P i) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) i u ε (S z₀) hSmeas hSfin
    hAsupp0 hmeasT2 hbndT2
  have hIntT3 := uniform_hIntT3_diag
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) i u ε (S z₀) hSmeas hSfin
    hAsupp0 hmeasT3 hbndT3
  have hInt1 := uniform_hInt1_diag (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G P i)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp1 hmeasI1 hbndI1
  have hInt2 := uniform_hInt2_diag (gateDisp G (uniformInverseChart g gi hC hK z₀))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
      pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) i ζ'))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u ε (S z₀) hSmeas hSfin
    hAsupp2 hmeasI2 hbndI2
  -- the hqLip-discharged diagonal co-instantiation, now with the integrabilities also supplied.
  exact witness_sliver2_xuniform_diag_gated_hqLipUniform g gi hC hK S a b i z₀ hz₀ hSopen G hSG
    P Q M₀ M₁ M₂ C T aₗ τ₀ C_W C_P C_Q hM₀ hM₁ hM₂ hC_W hC_P hC_Q
    L_E K_F L_A M_F hLE hK_F hLA hM_F u ε haₗ hau huT hε0 hεu hεa hετ₀
    hco_on hVdisp_on hJ3_on hJ3Q_on hg0 hg1 hg2
    hJetV hJetQ hAmpDi hAmpD2 hOffNhd data
    hoffAmp hALipAmp hFLipLevi hFbndLevi hmeasLevi
    hIntT1 hIntT2 hIntT3 hInt1 hInt2

end QIQTH.SliverGatedFullyCombined

/-! ## Axiom checks — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SliverGatedFullyCombined
#print axioms witness_sliver2_xuniform_mixed_gated_fullyCombined
#print axioms witness_sliver2_xuniform_diag_gated_fullyCombined
end AxiomChecks
