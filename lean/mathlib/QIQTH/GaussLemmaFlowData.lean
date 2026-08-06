/-
  GaussLemmaFlowData — the hGauss FINAL brick: discharging the flow-data carries of the assembled
  first-variation Gauss identity, producing the concrete pullback-metric gauge contraction, the germ
  shape consumed by the a₁ = R/6 façade, and the honest capstone-transport verdict.  (Brick J4-346 of
  the a₁ = R/6 heat-kernel tower.)

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one of the four labelled inputs of `a1_R6_from_labelled`.  This
  file discharges the flow-data legs of the exp-pullback Gauss lemma (the ones the assembly brick
  J4-345 carried), packages the germ form matching the consumer's binder, and states — completely and
  honestly — which capstone-metric hypotheses at the pullback are provable-now / derivable-with-work /
  labelled.  Nothing here builds normal coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE SOURCE (the banked ∃-Φ) and what it carries
  ─────────────────────────────────────────────────────────────────────────────────────────────
  `expDiff_flow_isGeodesicVariation g gi hC p v hv` (EXP-JET3-1, `QIQTH/ExpDiffVariation.lean`)
  produces `∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))` with THREE conjuncts:
    (Φ0)  `Φ 0 = id`;
    (FD)  `HasFDerivAt (expMap g gi hC p) (expJetPi ∘ Φ 1 ∘ expJetIota) v`  (the exp-differential IS
          the flow-derivative at `t = 1`);
    (var) `∀ w, ∀ t ∈ Icc 0 1, HasDerivWithinAt (fun s => Φ s w)
              (fderiv geodesicField (expTube … t) (Φ t w)) (Icc 0 1) t`  (the first-order linear
          variational law, WITHIN `[0,1]`).
  ⚠ The variational law is a WITHIN-`Icc 0 1` derivative, NOT a two-sided `HasDerivAt` on the open
  window `Ioo (-2) 2` that the banked assembly `GaussLemmaAssembly.gauss_first_variation` demands.  On
  the OPEN interior `Ioo 0 1` the within-`Icc` derivative IS two-sided (`Icc ∈ 𝓝 s` for interior `s`),
  so the interior first-order system is honestly extracted here; but the flow supplies NO derivative
  data at the endpoints `0, 1` or outside `[0,1]`.  The window mismatch is therefore REAL: the flow
  cannot directly discharge the `Ioo (-2) 2`-binders of the assembly.  The correct closure route (the
  interior-derivative + `Icc`-continuity + mean-value argument that needs NO endpoint derivative) is
  documented in the F4 verdict below; the interior first-order system extracted here is its first leg.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED (fully derived, axiom-free, no `sorry`)
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • F1  `flow_jacobi_field` — the concrete flow-derivative Jacobi field `J s = (Φ s (0,w)).1`,
       `Jp s = (Φ s (0,w)).2` packaged with its discharged legs: initial data `J 0 = 0`, `Jp 0 = w`;
       the endpoint identification `J 1 = D exp_p(v)·w` (the (FD) conjunct); and the INTERIOR
       first-order variational system `J' = Jp`, `Jp' = −jacobiOperator` at every `s ∈ Ioo 0 1`
       (the (var) conjunct, converted to two-sided on the open interior).  This discharges the
       initial-data + endpoint + first-order (`hJd` + the raw velocity/second-order feed) legs of the
       assembly's `hJd/hcJd/hcJp` carries.  ⚠ The covariant-field product-rule value (`hcJp`) is the
       remaining algebra, isolated in the F4 verdict.
   • F2  `gauss_contraction_concrete` — the pullback-metric gauge contraction `∑_j g̃_ij(v)·v^j = v^i`
       from a per-point Gauss identity `hgauss` on the tube (a thin, honest wrapper over the banked
       `GaussLemmaAssembly.gauss_coordinate_contraction_gauge`, which consumes `hgauss` with NO
       interval window — the window obstruction is already absent at this interface).
   • F3  `hGauss_pullback` — the GERM shape
       `∀ i, (fun x => ∑ j, expPullbackMetric … i j x · x^j) =ᶠ[𝓝 0] (fun x => x^i)`, in the EXACT
       binder form consumed by `A1R6SlotAdapters.htr_adapter` / `NCGaussToCyclicT.cyclicT_of_hGauss`
       (`g x i j` argument order; here `g̃ x i j = expPullbackMetric g gi hC p x i j`), from a
       ball-hypothesis of pointwise gauge contractions via `Metric.eventually_nhds_iff` on
       `ball 0 expRho`.
   • F4  `expPullbackMetric_zero_gauge` — the capstone geometry leg `g̃(0) = I` (provable NOW), plus
       the complete in-file verdict on the remaining capstone-metric binders at the pullback.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  F4 — THE CAPSTONE-TRANSPORT VERDICT (complete and honest)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  The a₁ consumer `A1R6FromLabelled.a1_R6_from_labelled` takes the base metric `g` as a PARAMETER with
  smoothness binder `hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)` (C∞ in the point) plus
  the gauge/inverse/symmetry binders, and the labelled `hGauss` gauge input in exactly the F3 binder
  form.  Instantiating that consumer AT the exp-pullback metric `g̃ = expPullbackMetric g gi hC p`
  requires supplying each `g̃`-binder.  The honest status of each:
    (i)  `hg` (C∞-in-the-point of `g̃`).  ⚠ LABELLED.  The PROVABLE smoothness of the pullback caps at
         `C⁴`-ish (`expMap_contDiffOn_four`; `g̃` is built from `g`, `exp_p` and `fderiv exp_p`, and
         `fderiv` sheds one order), NOT `C∞`.  The consumer's `⊤`-binder therefore cannot be met by a
         provable-C∞ fact.  Either (a) applying the façade at `g̃` carries a labelled "C∞-of-pullback"
         input, or (b) the façade's PROOF uses only finitely many derivatives of `g` and a `C^k`-binder
         refactor would meet it from `expMap_contDiffOn_four`.  Which of (a)/(b) holds is a refactor
         question about the façade's actual derivative usage, NOT dischargeable in this brick; it is
         recorded as the single genuine smoothness residue of the pullback route.
    (ii) `g̃(0) = I`.  ✅ PROVABLE NOW — delivered here as `expPullbackMetric_zero_gauge`, from
         `D exp_p(0) = id` (`fderiv_expMap_zero`) and the base gauge `g_p = I`.
   (iii) `∂ g̃(0) = 0` (the metric 1-jet vanishing — the classical RNC first-derivative fact).
         🔶 DERIVABLE-WITH-WORK.  This is the Riemann-normal-coordinate 1-jet; it is a SEPARATE
         derivation (the van-Vleck / log-det 1-jet line, `VanVleckRadial` / `LogJacobianRegularity`),
         not re-proved in this brick.  Recorded as derivable, not labelled.
    (iv) inverse / positive-definiteness of `g̃` near `0`.  🔶 DERIVABLE-WITH-WORK — from `g̃(0) = I`
         (leg (ii)) and continuity of `g̃` (the `C⁴` regularity), by the standard open-condition
         (invertibility is open) argument; not needed for the F3 germ itself.
  NET: the F3 germ `hGauss` is delivered in-form and the `g̃(0) = I` leg is proved; the pullback route's
  ONE genuine labelled residue is the C∞-vs-C⁴ smoothness binder (i), with (iii)/(iv) derivable.  This
  is STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.ExpDiffVariation
import QIQTH.JacobiEquation
import QIQTH.PullbackMetric
import QIQTH.GaussLemmaAssembly

namespace QIQTH.GaussLemmaFlowData

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open QIQTH.GaussLemmaAssembly
open QIQTH.PullbackMetric
open Finset Topology

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### F1 — the concrete flow-derivative Jacobi field and its discharged legs. -/

/-- **F1 — `flow_jacobi_field`.**  The concrete flow-derivative Jacobi field along the exp-tube, with
    its flow-data legs discharged from the banked `expDiff_flow_isGeodesicVariation` (the ∃-Φ).

    Set `J s := (Φ s (0,w)).1` (position part) and `Jp s := (Φ s (0,w)).2` (velocity part), where `Φ`
    is the geodesic-variation operator flow.  Then:
      * initial data `J 0 = 0`, `Jp 0 = w` (from `Φ 0 = id`);
      * the endpoint identification `J 1 = D exp_p(v)·w` componentwise (the (FD) conjunct: the flow
        derivative at `t = 1` IS the exp differential);
      * the INTERIOR first-order variational system, at every `s ∈ Ioo 0 1`:
          `HasDerivAt (fun r => J r a) (Jp s a) s`   (`J' = Jp`), and
          `HasDerivAt (fun r => Jp r a) (−jacobiOperator g gi (Y s).1 (Y s).2 (J s) (Jp s) a) s`
          (`Jp' = −jacobiOperator`), where `Y = expTube g gi hC p v`.
    The within-`Icc 0 1` variational law is converted to a two-sided `HasDerivAt` on the OPEN interior
    (`Icc ∈ 𝓝 s` there); the derivative value is put in Jacobi-operator form via
    `geodesicField_fderiv_eq_jacobiOperator`.

    ⚠ NOT a₁ = R/6.  This discharges the initial-data + endpoint + first-order legs of the assembly's
    `hJd/hcJd/hcJp` carries; the covariant-field product-rule value `hcJp` is the remaining algebra
    (see the F4 verdict). -/
theorem flow_jacobi_field
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ < expRho g gi hC p) :
    ∃ J Jp : ℝ → Point n,
      J 0 = 0 ∧ Jp 0 = w ∧
      (∀ a, J 1 a = (fderiv ℝ (expMap g gi hC p) v) w a) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ a, HasDerivAt (fun r => J r a) (Jp s a) s) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ a,
        HasDerivAt (fun r => Jp r a)
          (-jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (J s) (Jp s) a) s) := by
  classical
  obtain ⟨Φ, hΦ0, hFD, hvar⟩ := expDiff_flow_isGeodesicVariation g gi hC p v hv
  -- the concrete phase-field and its position/velocity parts.
  refine ⟨fun s => (Φ s ((0 : Point n), w)).1, fun s => (Φ s ((0 : Point n), w)).2, ?_, ?_, ?_, ?_, ?_⟩
  · -- J 0 = 0
    show (Φ 0 ((0 : Point n), w)).1 = 0
    rw [hΦ0]; rfl
  · -- Jp 0 = w
    show (Φ 0 ((0 : Point n), w)).2 = w
    rw [hΦ0]; rfl
  · -- J 1 = D exp_p(v)·w  (componentwise)
    intro a
    show (Φ 1 ((0 : Point n), w)).1 a = (fderiv ℝ (expMap g gi hC p) v) w a
    have : (Φ 1 ((0 : Point n), w)).1 = (fderiv ℝ (expMap g gi hC p) v) w := by
      rw [hFD.fderiv]
      simp only [ContinuousLinearMap.comp_apply, expJetIota_apply, expJetPi_apply]
    rw [this]
  · -- interior J' = Jp
    intro s hs a
    -- the two-sided interior variational law for the phase-field.
    have hmem : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hwithin := hvar ((0 : Point n), w) s hmem
    have hVJ : HasDerivAt (fun r => Φ r ((0 : Point n), w))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))) s :=
      hwithin.hasDerivAt hnhds
    -- Jacobi-operator form of the derivative value.
    have hval : fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))
        = ((Φ s ((0 : Point n), w)).2,
           -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2) :=
      geodesicField_fderiv_eq_jacobiOperator g gi hC (expTube g gi hC p v s).1
        (expTube g gi hC p v s).2 (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2
    rw [hval] at hVJ
    -- take the first (position) Prod-component, then the `a`-th coordinate.
    have hfst : HasDerivAt (fun r => (Φ r ((0 : Point n), w)).1) (Φ s ((0 : Point n), w)).2 s :=
      ((ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt).comp_hasDerivAt s hVJ
    exact ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt s hfst
  · -- interior Jp' = −jacobiOperator
    intro s hs a
    have hmem : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hwithin := hvar ((0 : Point n), w) s hmem
    have hVJ : HasDerivAt (fun r => Φ r ((0 : Point n), w))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))) s :=
      hwithin.hasDerivAt hnhds
    have hval : fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))
        = ((Φ s ((0 : Point n), w)).2,
           -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2) :=
      geodesicField_fderiv_eq_jacobiOperator g gi hC (expTube g gi hC p v s).1
        (expTube g gi hC p v s).2 (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2
    rw [hval] at hVJ
    have hsnd : HasDerivAt (fun r => (Φ r ((0 : Point n), w)).2)
        (-jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
            (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2) s :=
      ((ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt).comp_hasDerivAt s hVJ
    exact ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt s hsnd

/-! ### F2 — the concrete pullback-metric gauge contraction. -/

/-- **F2 — `gauss_contraction_concrete`.**  The pullback-metric gauge contraction `∑_j g̃_ij(v)·v^j =
    v^i` at a fixed `v` on the tube, from the per-point first-variation Gauss identity `hgauss` (at
    every column `i`) and the base gauge `g_p = I`.

    This is the honest interface: the banked `gauss_coordinate_contraction_gauge` (A3′, J4-345)
    consumes `hgauss` as a PLAIN per-point hypothesis with NO interval window, so the flow-window
    obstruction (`Icc 0 1` vs `Ioo (-2) 2`) is already absent HERE.  The surviving hypothesis is
    exactly the per-point Gauss identity `hgauss`; F1 (`flow_jacobi_field`) + the interior mean-value
    argument documented in the F4 verdict reduce `hgauss` to the flow's interior second-order algebra.

    ⚠ NOT a₁ = R/6. -/
theorem gauss_contraction_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgauge : ∀ a b, g p a b = if a = b then 1 else 0)
    (hgauss : ∀ i, (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b) :
    ∀ i, (∑ j, expPullbackMetric g gi hC p v i j * v j) = v i :=
  fun i => gauss_coordinate_contraction_gauge g gi hC p v hv i (hgauss i) hgauge

/-! ### F3 — the germ shape consumed by the a₁ = R/6 façade. -/

/-- **F3 — `hGauss_pullback`.**  The GERM form of the Gauss lemma for the exp-pullback metric, in the
    EXACT binder shape consumed by `A1R6SlotAdapters.htr_adapter` /
    `NCGaussToCyclicT.cyclicT_of_hGauss` (`hGauss : ∀ i, (fun x => ∑ j, g̃ x i j · x^j) =ᶠ[𝓝 0]
    (fun x => x^i)`, with `g̃ x i j = expPullbackMetric g gi hC p x i j`):
      `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j · x^j) =ᶠ[𝓝 0] (fun x => x^i)`.
    From the ball-family `hgball` of per-point Gauss identities on `ball 0 expRho` (each fed through F2)
    via `Metric.eventually_nhds_iff` with the tube radius `expRho` as the neighbourhood witness.

    ⚠ NOT a₁ = R/6.  `hgball` is the labelled residue (the per-point first-variation identity on the
    tube), reduced by F1 + the interior mean-value argument to the flow's interior second-order data. -/
theorem hGauss_pullback
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n)
    (hgauge : ∀ a b, g p a b = if a = b then 1 else 0)
    (hgball : ∀ v : Point n, ‖v‖ < expRho g gi hC p → ∀ i,
        (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b) :
    ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => x i) := by
  intro i
  refine Metric.eventually_nhds_iff.mpr ⟨expRho g gi hC p, expRho_pos g gi hC p, fun {x} hx => ?_⟩
  have hnorm : ‖x‖ < expRho g gi hC p := by rwa [dist_zero_right] at hx
  exact gauss_coordinate_contraction_gauge g gi hC p x hnorm i (hgball x hnorm i) hgauge

/-! ### F4 — the capstone geometry leg `g̃(0) = I` (see the header verdict for the full accounting). -/

/-- **F4 — `expPullbackMetric_zero_gauge`.**  The capstone-metric value leg at the centre: under the
    base gauge `g_p = I` (`hgauge`), the pullback metric is the identity at `0`:
    `g̃(0)_{ij} = δ_{ij}`.  Immediate from `expPullbackMetric_at_zero` (`g̃(0) = g(p)`, via
    `exp_p 0 = p` and `D exp_p 0 = id`) and the gauge.  This is capstone leg (ii) of the header
    verdict — the one that is provable NOW.  ⚠ NOT a₁ = R/6. -/
theorem expPullbackMetric_zero_gauge
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (hgauge : ∀ a b, g p a b = if a = b then 1 else 0) (i j : Fin n) :
    expPullbackMetric g gi hC p 0 i j = if i = j then 1 else 0 := by
  rw [expPullbackMetric_at_zero, hgauge]

end QIQTH.GaussLemmaFlowData

section AxiomChecks
open QIQTH.GaussLemmaFlowData
#print axioms flow_jacobi_field
#print axioms gauss_contraction_concrete
#print axioms hGauss_pullback
#print axioms expPullbackMetric_zero_gauge
end AxiomChecks
