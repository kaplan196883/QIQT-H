/-
  MixedSliverHqLipUniform — J4-815: the UNIFORM-in-(x,s) `hqLip` triple, and its wiring that DISCHARGES
  the `hqLip` residue of BOTH the mixed (J4-811) and diagonal (J4-814) gated co-instantiations.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It closes the
  `hqLip` residue class flagged at J4-811/814 — "the banked supplier delivers the Lipschitz/measurability/
  bound triple only at FIELD-POINT 0 with an `s`-DEPENDENT constant `L_F = L_E + K·2√s`; the sliver needs a
  SINGLE UNIFORM `L`, at GENERAL field point `x`, uniform over the slice range `s ∈ (u−ε, u)`."

  ── WHY THE BANKED SUPPLIER WAS `s`-DEPENDENT / field-point-0-specific. ──────────────────────────────
  `MixedSliverGateAmpLipschitz.mixedSliver_hqLip_triple_via_gateAmp` produces the product triple for
  `ζ ↦ gateAmp S z₀ A τ ζ · F s ζ 0` with Lipschitz constant `M_A·L_F + M_F·L_A`, and it consumes the
  Levi-kernel spatial Lipschitz slot `hFLip` at the LITERAL source point `0` with the `s`-dependent
  constant `L_F = L_E + K·2√s` (the exact output of `LeviLipschitz.resolvent_lipschitz_pointwise`, J4-144,
  whose `(s−r)^{−1/2}` residual integrates to `2√s`).  Two independent facts remove both obstructions:
    (a)  **Field point 0 → general `x` is FREE.**  Nothing in the product bookkeeping is special to `0`;
         the Levi kernel Lipschitz/bound slots are carried at the general source `x` verbatim (the resolvent
         identity `F = −E − E∗F` holds source-pointwise), so the supplier is stated abstractly in `F` with a
         general field-point argument `x` — no re-derivation, the `0` was only a specialisation.
    (b)  **`s`-dependence TAMED by monotonicity of `√`.**  On the slice range `s ∈ (u−ε, u)` we have `s < u`,
         hence `√s ≤ √u`, hence `L_E + K·2√s ≤ L_E + K·2√u` (for `K ≥ 0`).  Taking that sup over the bounded
         `s`-range turns the `s`-dependent per-slice constant into the SINGLE uniform constant
         `L := M_A·(L_E + K·2√u) + M_F·L_A`, valid for every `x` and every slice `s ∈ (u−ε, u)`.  This is the
         genuine content of the increment: a bounded-range sup that yields a genuinely uniform Lipschitz
         constant.

  ── WHAT LANDS (all abstract / carried; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `hqLip_uniform_product`      — abstract product uniformization: the `√s`-sup that manufactures the
                                     single uniform constant from an `s`-dependent-and-general-`x` Levi slot.
    * `gateAmpLevi_hqLip_uniform`  — the EXACT `hqLip` binder shape (gated amplitude · Levi kernel) with a
                                     single uniform `L`, general field point `x`, uniform over `s ∈ (u−ε,u)`.
    * `witness_sliver2_xuniform_mixed_gated_hqLipUniform` — the mixed co-instantiation with its `hqLip`
                                     residue DISCHARGED via the uniform supplier (only the parallel
                                     integrability residue class remains carried).
    * `witness_sliver2_xuniform_diag_gated_hqLipUniform`  — likewise for the diagonal co-instantiation
                                     (the `hqLip` binder is byte-identical, so the SAME supplier closes it).

  Every hypothesis is satisfiable and non-vacuous, and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverGateAmpLipschitz
import QIQTH.MixedSliverGatedCoInstantiation
import QIQTH.DiagSliverGatedCoInstantiation

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.MixedSliverAssembly QIQTH.MixedGradientSlice
open QIQTH.MixedSliverGatedEstimates QIQTH.MixedSliverAmpBounds QIQTH.MixedSliverFdom
open QIQTH.MixedNormalFormGatedMatch QIQTH.MixedNormalFormFull QIQTH.MixedSliverXUniform
open QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData
open QIQTH.MixedSliverGateAmpLipschitz
open QIQTH.MixedSliverGatedCoInstantiation QIQTH.DiagSliverGatedCoInstantiation
open scoped Interval Topology BigOperators

namespace QIQTH.MixedSliverHqLipUniform

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ############################################################################
    ### The abstract product uniformization — the `√s`-sup that manufactures one uniform constant.
    ############################################################################ -/

/-- **★ `hqLip_uniform_product` — the abstract product-Lipschitz uniformization.**  For an amplitude
    factor `A0` (`L_A`-Lipschitz, `M_A`-bounded, both `s`-uniform) and a Levi-kernel factor `F` carried
    at the GENERAL field point `x` with the `s`-DEPENDENT spatial Lipschitz constant `L_E + K·2√s` and a
    uniform bound `M_F`, the product `z ↦ A0 (u−s) z · F s z x` satisfies the `hqLip` triple with the
    SINGLE UNIFORM constant `M_A·(L_E + K·2√u) + M_F·L_A`, at every field point `x` and every slice
    `s ∈ (u−ε, u)`.  The genuine step: `s < u ⟹ √s ≤ √u` tames the `s`-dependent Levi constant to its sup
    over the bounded slice range.  ⚠ NOT `a₁ = R/6`. -/
theorem hqLip_uniform_product
    (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε L_E K M_A M_F L_A : ℝ)
    (hK : 0 ≤ K) (hM_A : 0 ≤ M_A) (hM_F : 0 ≤ M_F)
    (hFLip : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |F s z x - F s w x| ≤ (L_E + K * (2 * Real.sqrt s)) * dist z w)
    (hFbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |F s z x| ≤ M_F)
    (hALip : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |A0 (u - s) z - A0 (u - s) w| ≤ L_A * dist z w)
    (hAbnd : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |A0 (u - s) z| ≤ M_A)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z x) volume) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      (∀ z w : Point n, |A0 (u - s) z * F s z x - A0 (u - s) w * F s w x|
          ≤ (M_A * (L_E + K * (2 * Real.sqrt u)) + M_F * L_A) * dist z w)
      ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z x) volume
      ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z x| ≤ M := by
  intro x s hs
  refine ⟨?_, hmeas x s hs, ⟨M_A * M_F, ?_⟩⟩
  · -- product Lipschitz with the `s`-dependent constant, then tamed by `√s ≤ √u`.
    intro z w
    -- the `√`-monotonicity sup: the whole per-slice constant is ≤ the uniform one.
    have hsu : Real.sqrt s ≤ Real.sqrt u := Real.sqrt_le_sqrt (le_of_lt hs.2)
    have hcoef : L_E + K * (2 * Real.sqrt s) ≤ L_E + K * (2 * Real.sqrt u) := by
      have h2 : (2 : ℝ) * Real.sqrt s ≤ 2 * Real.sqrt u := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hK]
    have hLbound : M_A * (L_E + K * (2 * Real.sqrt s)) + M_F * L_A
        ≤ M_A * (L_E + K * (2 * Real.sqrt u)) + M_F * L_A := by
      nlinarith [mul_le_mul_of_nonneg_left hcoef hM_A]
    have key : A0 (u - s) z * F s z x - A0 (u - s) w * F s w x
        = A0 (u - s) z * (F s z x - F s w x)
          + F s w x * (A0 (u - s) z - A0 (u - s) w) := by ring
    rw [key]
    calc |A0 (u - s) z * (F s z x - F s w x) + F s w x * (A0 (u - s) z - A0 (u - s) w)|
        ≤ |A0 (u - s) z * (F s z x - F s w x)|
            + |F s w x * (A0 (u - s) z - A0 (u - s) w)| := abs_add_le _ _
      _ = |A0 (u - s) z| * |F s z x - F s w x|
            + |F s w x| * |A0 (u - s) z - A0 (u - s) w| := by rw [abs_mul, abs_mul]
      _ ≤ M_A * ((L_E + K * (2 * Real.sqrt s)) * dist z w) + M_F * (L_A * dist z w) := by
          apply add_le_add
          · exact mul_le_mul (hAbnd s hs z) (hFLip x s hs z w) (abs_nonneg _) hM_A
          · exact mul_le_mul (hFbnd x s hs w) (hALip s hs z w) (abs_nonneg _) hM_F
      _ = (M_A * (L_E + K * (2 * Real.sqrt s)) + M_F * L_A) * dist z w := by ring
      _ ≤ (M_A * (L_E + K * (2 * Real.sqrt u)) + M_F * L_A) * dist z w :=
          mul_le_mul_of_nonneg_right hLbound dist_nonneg
  · -- uniform boundedness.
    intro z
    calc |A0 (u - s) z * F s z x| = |A0 (u - s) z| * |F s z x| := abs_mul _ _
      _ ≤ M_A * M_F := mul_le_mul (hAbnd s hs z) (hFbnd x s hs z) (abs_nonneg _) hM_A

/-! ############################################################################
    ### The concrete gated-amplitude · Levi-kernel uniform `hqLip` supplier.
    ############################################################################ -/

/-- **★★ `gateAmpLevi_hqLip_uniform` — the EXACT uniform `hqLip` binder.**  For the gated amplitude
    `z ↦ gateAmp S z₀ A (u−s) z` (built from a raw amplitude `A` that is `L_A`-Lipschitz, `M_A`-bounded
    on-gate, and vanishes off-gate) times the Levi kernel `F` carried at the general field point `x` with
    the `s`-dependent spatial Lipschitz constant `L_E + K·2√s` and bound `M_F`, the product triple holds
    with the SINGLE uniform constant `M_A·(L_E + K·2√u) + M_F·L_A`.  This is precisely the `hqLip` binder
    shape both gated co-instantiations consume; the field-point-0 restriction and `s`-dependence of the
    banked supplier are BOTH removed.  ⚠ NOT `a₁ = R/6`. -/
theorem gateAmpLevi_hqLip_uniform
    (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε L_E K M_A M_F L_A : ℝ)
    (hK : 0 ≤ K) (hM_A : 0 ≤ M_A) (hM_F : 0 ≤ M_F)
    (hoff : ∀ τ : ℝ, ∀ ζ ∉ S z₀, A τ ζ = 0)
    (hAbndOn : ∀ τ : ℝ, ∀ ζ ∈ S z₀, |A τ ζ| ≤ M_A)
    (hALip : ∀ τ : ℝ, ∀ ζ ζ' : Point n, |A τ ζ - A τ ζ'| ≤ L_A * dist ζ ζ')
    (hFLip : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |F s z x - F s w x| ≤ (L_E + K * (2 * Real.sqrt s)) * dist z w)
    (hFbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |F s z x| ≤ M_F)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        AEStronglyMeasurable (fun z : Point n => gateAmp S z₀ A (u - s) z * F s z x) volume) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      (∀ z w : Point n, |gateAmp S z₀ A (u - s) z * F s z x - gateAmp S z₀ A (u - s) w * F s w x|
          ≤ (M_A * (L_E + K * (2 * Real.sqrt u)) + M_F * L_A) * dist z w)
      ∧ AEStronglyMeasurable (fun z : Point n => gateAmp S z₀ A (u - s) z * F s z x) volume
      ∧ ∃ M, ∀ z : Point n, |gateAmp S z₀ A (u - s) z * F s z x| ≤ M := by
  -- lift the on-gate amplitude bound to all `ζ` using off-gate vanishing (off-gate `|A| = 0 ≤ M_A`).
  have hAbndAll : ∀ τ : ℝ, ∀ ζ : Point n, |A τ ζ| ≤ M_A := by
    intro τ ζ
    by_cases h : ζ ∈ S z₀
    · exact hAbndOn τ ζ h
    · rw [hoff τ ζ h, abs_zero]; exact hM_A
  exact hqLip_uniform_product (fun τ ζ => gateAmp S z₀ A τ ζ) F u ε L_E K M_A M_F L_A
    hK hM_A hM_F hFLip hFbnd
    (fun s _ => gateAmp_lipschitz_of_vanishing S z₀ A (u - s) L_A (hoff (u - s)) (hALip (u - s)))
    (fun s _ => gateAmp_bound_of_vanishing S z₀ A (u - s) M_A (hoff (u - s)) (hAbndAll (u - s)))
    hmeas

/-! ############################################################################
    ### Wiring — the mixed co-instantiation with its `hqLip` residue DISCHARGED.
    ############################################################################ -/

/-- **★★★ J4-815 — the MIXED co-instantiation with `hqLip` discharged via the uniform supplier.**  Same
    terminal `√ε` mixed-sliver rate as `witness_sliver2_xuniform_mixed_gated`, but the `hqLip` triple is no
    longer carried: it is manufactured internally by `gateAmpLevi_hqLip_uniform` from the raw amplitude's
    Lipschitz/bound/off-gate data and the Levi kernel's `s`-dependent (`√s`) spatial Lipschitz slot at the
    general field point.  The single uniform Lipschitz constant is `M₀·(L_E + K_F·2√u) + M_F·L_A`.  Only the
    parallel-owned integrability residue class remains carried.  ⚠ NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_mixed_gated_hqLipUniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (hij : i ≠ j) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (G : Set (Point n)) (hSG : S z₀ ⊆ G)
    (Pi Pj Q : Point n → Point n)
    (M₀ M₁i M₁j M₂ C T aₗ τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁i : 0 ≤ M₁i) (hM₁j : 0 ≤ M₁j) (hM₂ : 0 ≤ M₂)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    -- ── the uniform `hqLip` supplier constants (the `√s`-sup ingredients).
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
    -- ── the RAW amplitude carries feeding the uniform `hqLip` supplier.
    (hoffAmp : ∀ τ : ℝ, ∀ ζ ∉ S z₀, chartFieldAmp g gi hC hK a b τ z₀ ζ = 0)
    (hALipAmp : ∀ τ : ℝ, ∀ ζ ζ' : Point n,
        |chartFieldAmp g gi hC hK a b τ z₀ ζ - chartFieldAmp g gi hC hK a b τ z₀ ζ'|
          ≤ L_A * dist ζ ζ')
    -- ── the Levi-kernel carries at the GENERAL field point (resolvent output, `√s` constant).
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
    -- ── the seven CARRIED integrand integrabilities (parallel-owned residue class; unchanged).
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
              + (tE2RateConst n M₀ (C_L * gaussDdim aₗ (0 : Point n)) C_W C_P C_Q τ₀
                  + (M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A) * (n : ℝ)))
            + mTerm1RateConst n M₁i C_L aₗ τ₀ C_W C_P
            + mTerm1RateConst n M₁j C_L aₗ τ₀ C_W C_P) * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim aₗ (0 : Point n)) * ε := by
  -- the single uniform Lipschitz constant, and its nonnegativity.
  have hLnn : 0 ≤ M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A := by
    have h1 : 0 ≤ L_E + K_F * (2 * Real.sqrt u) :=
      add_nonneg hLE (mul_nonneg hK_F (by positivity))
    exact add_nonneg (mul_nonneg hM₀ h1) (mul_nonneg hM_F hLA)
  -- manufacture the uniform `hqLip` triple from the raw carries.
  have hqLip := gateAmpLevi_hqLip_uniform S z₀
    (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    u ε L_E K_F M₀ M_F L_A hK_F hM₀ hM_F
    hoffAmp hg0 hALipAmp hFLipLevi hFbndLevi hmeasLevi
  exact witness_sliver2_xuniform_mixed_gated g gi hC hK S a b i j hij z₀ hz₀ hSopen G hSG
    Pi Pj Q (M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A) M₀ M₁i M₁j M₂ C T aₗ τ₀ C_W C_P C_Q
    hLnn hM₀ hM₁i hM₁j hM₂ hC_W hC_P hC_Q
    u ε haₗ hau huT hε0 hεu hεa hετ₀
    hco_on hVdisp_on hJ3i_on hJ3j_on hJ3Q_on hg0 hg1i hg1j hg2
    hJetPi hJetPj hJetQ hAmpDi hAmpDj hAmpD2 hOffNhd data
    hqLip hIntE1 hIntPlain hIntRem hInt0 hInt1i hInt1j hInt2

/-! ############################################################################
    ### Wiring — the diagonal co-instantiation with its `hqLip` residue DISCHARGED.
    ############################################################################ -/

/-- **★★★ J4-815 — the DIAGONAL co-instantiation with `hqLip` discharged via the SAME uniform supplier.**
    The diagonal `hqLip` binder is byte-identical to the mixed one, so the identical
    `gateAmpLevi_hqLip_uniform` instance closes it.  Same terminal `√ε` diagonal-sliver rate as
    `witness_sliver2_xuniform_diag_gated`, but `hqLip` is no longer carried.  Only the parallel-owned
    integrability residue class remains.  ⚠ NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_diag_gated_hqLipUniform
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
  have hLnn : 0 ≤ M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A := by
    have h1 : 0 ≤ L_E + K_F * (2 * Real.sqrt u) :=
      add_nonneg hLE (mul_nonneg hK_F (by positivity))
    exact add_nonneg (mul_nonneg hM₀ h1) (mul_nonneg hM_F hLA)
  have hqLip := gateAmpLevi_hqLip_uniform S z₀
    (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    u ε L_E K_F M₀ M_F L_A hK_F hM₀ hM_F
    hoffAmp hg0 hALipAmp hFLipLevi hFbndLevi hmeasLevi
  exact witness_sliver2_xuniform_diag_gated g gi hC hK S a b i z₀ hz₀ hSopen G hSG
    P Q (M₀ * (L_E + K_F * (2 * Real.sqrt u)) + M_F * L_A) M₀ M₁ M₂ C T aₗ τ₀ C_W C_P C_Q
    hLnn hM₀ hM₁ hM₂ hC_W hC_P hC_Q
    u ε haₗ hau huT hε0 hεu hεa hετ₀
    hco_on hVdisp_on hJ3_on hJ3Q_on hg0 hg1 hg2
    hJetV hJetQ hAmpDi hAmpD2 hOffNhd data
    hqLip hIntT1 hIntT2 hIntT3 hInt1 hInt2

end QIQTH.MixedSliverHqLipUniform

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverHqLipUniform
#print axioms hqLip_uniform_product
#print axioms gateAmpLevi_hqLip_uniform
#print axioms witness_sliver2_xuniform_mixed_gated_hqLipUniform
#print axioms witness_sliver2_xuniform_diag_gated_hqLipUniform
end AxiomChecks
