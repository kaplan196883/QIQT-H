/-
  MixedSliverGatedCoInstantiation — J4-811: THE SINGLE SHARED-WITNESS CO-INSTANTIATION of the closed
  x-uniform MIXED sliver rate `MixedSliverXUniform.witness_sliver2_xuniform_mixed`, at ONE concrete
  gated van-Vleck witness tuple.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  ASSEMBLY step named at J4-808 as "PURE co-instantiation wiring across ~7 files": the mixed sliver rate
  theorem `witness_sliver2_xuniform_mixed` carries ~40 abstract hypotheses over abstract data
  `(D2H, F, V, Pi, Pj, Q, A0, A1i, A1j, A2, …)`.  Every one of the geometric / amplitude / domination /
  normal-form slots was independently built by an earlier increment at a DIFFERENT abstract witness.  This
  file INSTANTIATES all of them at the ONE shared concrete tuple

    • `V   := gateDisp G (uniformInverseChart g gi hC hK z₀)`        (gated raw inverse-chart displacement)
    • `Pi  := gateJet G Pi i`,  `Pj := gateJet G Pj j`,  `Q := gateQ G Q`   (gated raw chart jets)
    • `A0  := gateAmp S z₀ (chartFieldAmp …)`, `A1i/A1j := gateAmp S z₀ (pd …)`, `A2 := gateAmp S z₀ (pd pd …)`
    • `F   := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))`
    • `D2H := fun τ ζ => pd (fun y => pd (fun x' => vanVleckGatedWitness … τ x' z₀) i y) j ζ`

  and DISCHARGES the eleven cleanly-matching slots directly from the already-banked suppliers:
    • the FIVE global geometric estimates `hco/hVdisp/hJ3i/hJ3j/hJ3Q`
        ← `MixedSliverGatedEstimates.gated_five_estimates_global` (J4-799), from ball/on-gate data;
    • the FOUR amplitude sup bounds `hA0bdd/hA1ibdd/hA1jbdd/hA2bdd`
        ← `MixedSliverAmpBounds.witnessMixed_amplitude_sup_bounds` (J4-793), from on-gate data;
    • the Gaussian domination `hFdom` (with its constant `C_L`)
        ← `MixedSliverFdom.leviSeries_hFdom_gated` (J4-794), from the banked `LeviSeriesLocalData` package;
    • the four-term mixed `hNormalForm`
        ← `MixedNormalFormGatedMatch.witnessMixed_hNormalForm_gated` (J4-805), from chart/amplitude jets.

  ── HONEST SCOPE OF THE CARRIED RESIDUE.  Two classes of the sliver's carries are passed THROUGH as
  hypotheses of this co-instantiation, not discharged here:
    (1)  `hqLip` — the per-slice product-Lipschitz/measurability/bound triple for `A0·F` at the GENERAL
         field point `x` with a SINGLE uniform constant `L`.  The supplier
         `MixedSliverGateAmpLipschitz.mixedSliver_hqLip_triple_via_gateAmp` delivers this triple only at the
         FIXED field point `0` and with the `s`-dependent constant `M_A·L_F + M_F·L_A` (`L_F = O(√s)`), so
         it does not yield a single `x`-and-`s`-uniform `L`; the uniform-`L` triple is carried as `hqLip`.
    (2)  the seven integrand integrabilities `hIntE1/…/hInt2`.  The suppliers
         `MixedSliverIntegrandFull.integrable_*_full` (J4-808) discharge these from PRIMITIVE on-gate data
         (finite measurable gate + off-gate vanishing + on-gate measurability + on-gate bound), per field
         point `x`; carrying the seven `Integrable … volume` conclusions is the honest terminal interface.

  The `Q`-slot is filled with the SAME raw jet `Q` used by the normal form (via `gateQ`), and its bound
  `hJ3Q` is derived from the carried on-gate `hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q`.  We deliberately DO NOT
  route `hJ3Q` through `MixedSliverFieldQGlobal.gatedFieldSecondJet_global_bound` (the `fderiv∘fderiv`
  field-point second-jet), because matching THAT object to the normal form's `HasDerivAt`-built jet `Q` is
  precisely the still-open J4-803 `Qfield ↔ fderiv∘fderiv` component identity; carrying `hJ3Q_on` on the
  same `Q` sidesteps that bridge with a satisfiable on-gate hypothesis.

  Every hypothesis is satisfiable and non-vacuous (all off-gate/zero placeholders satisfy the on-gate
  legs trivially; the flat model gives a genuinely-nonzero witness), and none equals the conclusion.
  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverXUniform
import QIQTH.MixedNormalFormGatedMatch
import QIQTH.MixedSliverGatedEstimates
import QIQTH.MixedSliverAmpBounds
import QIQTH.MixedSliverFdom

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.MixedSliverAssembly QIQTH.MixedGradientSlice
open QIQTH.MixedSliverGatedEstimates QIQTH.MixedSliverAmpBounds QIQTH.MixedSliverFdom
open QIQTH.MixedNormalFormGatedMatch QIQTH.MixedNormalFormFull QIQTH.MixedSliverXUniform
open QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData
open scoped Interval Topology BigOperators

namespace QIQTH.MixedSliverGatedCoInstantiation

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★★★ J4-811 — THE SINGLE SHARED-WITNESS CO-INSTANTIATION OF THE MIXED SLIVER RATE.**  For the
    concrete gated van-Vleck witness tuple (see the file header), the terminal `√ε` mixed-sliver rate
    `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z x| ≤ (C₀+C₁+C₁')·2√ε + C₂·ε` holds at EVERY field point
    `x`, with the domination constant `C_L` produced by the banked `LeviSeriesLocalData` package.  The
    eleven geometric/amplitude/domination/normal-form slots of
    `MixedSliverXUniform.witness_sliver2_xuniform_mixed` are discharged from the already-banked suppliers
    (J4-793/794/799/805) at this ONE tuple; the `hqLip` triple (uniform `L`, general field point) and the
    seven integrand integrabilities are carried as the honest terminal interface.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_mixed_gated
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (hij : i ≠ j) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (Pi Pj Q : Point n → Point n)
    (L M₀ M₁i M₁j M₂ C T aₗ τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁i : 0 ≤ M₁i) (hM₁j : 0 ≤ M₁j) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (u ε : ℝ) (haₗ : 0 < aₗ) (hau : aₗ ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aₗ / 2) (hετ₀ : ε ≤ τ₀)
    -- ── (I) the five geometric on-gate estimates (ball forms; J4-796/797/798).
    (hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z₀ z))
    (hVdisp_on : ∀ z ∈ G, ‖uniformInverseChart g gi hC hK z₀ z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i_on : ∀ z ∈ G, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j_on : ∀ z ∈ G, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q)
    -- ── (II) the four amplitude on-gate sup bounds (J4-793 base inputs).
    (hg0 : ∀ τ, ∀ w ∈ S z₀, |chartFieldAmp g gi hC hK a b τ z₀ w| ≤ M₀)
    (hg1i : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) i w| ≤ M₁i)
    (hg1j : ∀ τ, ∀ w ∈ S z₀, |pd (chartFieldAmp g gi hC hK a b τ z₀) j w| ≤ M₁j)
    (hg2 : ∀ τ, ∀ w ∈ S z₀,
        |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) j w| ≤ M₂)
    -- ── (III) the normal-form chart/amplitude jets (J4-792/805 inputs).
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
    -- ── (VI) the seven CARRIED integrand integrabilities (J4-808 discharges from on-gate data).
    (hIntE1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (gateDisp G (uniformInverseChart g gi hC hK z₀) z)
              - gaussDdim (u - s) z)
            * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pi i z k)
                * (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pj j z k)
                / (4 * (u - s) ^ 2)
                - ((∑ k, gateJet G Pi i z k * gateJet G Pj j z k)
                    + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                  / (2 * (u - s)))
            * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)) volume)
    (hIntPlain : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pi i z k)
                * (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pj j z k)
                / (4 * (u - s) ^ 2)
                - ((∑ k, gateJet G Pi i z k * gateJet G Pj j z k)
                    + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                  / (2 * (u - s)))
            * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)) volume)
    (hIntRem : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pi i z k)
                * (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateJet G Pj j z k)
                / (4 * (u - s) ^ 2)
                - ((∑ k, gateJet G Pi i z k * gateJet G Pj j z k)
                    + (∑ k, gateDisp G (uniformInverseChart g gi hC hK z₀) z k * gateQ G Q z k))
                  / (2 * (u - s))
                - (z i * z j) / (4 * (u - s) ^ 2))
            * (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ') (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x)) volume)
    (hInt0 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm0 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
              (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume)
    (hInt1i : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pj j)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume)
    (hInt1j : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm1 (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pi i)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume)
    (hInt2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 (gateDisp G (uniformInverseChart g gi hC hK z₀))
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ')) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x) volume) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ x : Point n,
      |∫ s in (u - ε)..u, ∫ z,
          (fun τ ζ => pd (fun y => pd (fun x' =>
              vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ) (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z x|
        ≤ ((sliverRateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀
              + (tE2RateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀ + L * (n : ℝ)))
            + mTerm1RateConst n M₁i C_L aₗ τ₀ C_W C_P
            + mTerm1RateConst n M₁j C_L aₗ τ₀ C_W C_P) * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim aₗ (0 : Point n)) * ε := by
  -- ── hFdom + its constant `C_L`, from the banked Levi package (J4-794).
  obtain ⟨C_L, hCL0, hFdom⟩ := leviSeries_hFdom_gated g gi hC hK S a b C T data
  refine ⟨C_L, hCL0, ?_⟩
  -- ── the five global geometric estimates, from the gating layer (J4-799).
  obtain ⟨hco, hVdisp, hJ3i, hJ3j, hJ3Q⟩ :=
    gated_five_estimates_global G (uniformInverseChart g gi hC hK z₀) Pi Pj Q i j
      C_W C_P C_Q hC_W hC_P hC_Q hco_on hVdisp_on hJ3i_on hJ3j_on hJ3Q_on
  -- ── the four amplitude sup bounds, from the gate-localization (J4-793).
  obtain ⟨hA0bdd, hA1ibdd, hA1jbdd, hA2bdd⟩ :=
    witnessMixed_amplitude_sup_bounds g gi hC hK S a b i j z₀
      M₀ M₁i M₁j M₂ hM₀ hM₁i hM₁j hM₂ hg0 hg1i hg1j hg2
  -- ── the four-term mixed normal form under the gated geometry (J4-805).
  have hNF := witnessMixed_hNormalForm_gated g gi hC hK S a b i j τ₀ z₀ hz₀ hSopen G hSG
    Pi Pj Q hJetPi hJetPj hJetQ hAmpDi hAmpDj hAmpD2 hOffNhd
  -- ── the single fully-instantiated call.
  exact witness_sliver2_xuniform_mixed
    (fun τ ζ => pd (fun y => pd (fun x' =>
        vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    (gateDisp G (uniformInverseChart g gi hC hK z₀)) (gateJet G Pi i) (gateJet G Pj j) (gateQ G Q)
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ'))
    (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ'))
    i j hij L M₀ M₁i M₁j M₂ C_L T aₗ τ₀ C_W C_P C_Q
    hL hM₀ hM₁i hM₁j hM₂ hCL0 hC_W hC_P hC_Q
    u ε haₗ hau huT hε0 hεu hεa hετ₀
    hco hVdisp hJ3i hJ3j hJ3Q hA0bdd hA1ibdd hA1jbdd hA2bdd hFdom hNF
    hqLip hIntE1 hIntPlain hIntRem hInt0 hInt1i hInt1j hInt2

end QIQTH.MixedSliverGatedCoInstantiation

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverGatedCoInstantiation
#print axioms witness_sliver2_xuniform_mixed_gated
end AxiomChecks
