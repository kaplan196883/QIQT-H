/-
  CConvV2Contracts — J4-323 (facade-v2 brick 1 of 14): the V2 DATA CONTRACTS that replace the
  ADJUDICATED-FALSE fields of the `hCConv` facade (`CConvFacade.lean`).  ONE brick of the
  `a₁ = R/6` heat-kernel campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It defines
  three `: Prop` data structures + their satisfiability guards.  NO `sorry` (header prose excepted),
  NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis in this file's own theorems, no
  existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY V2 — the two adjudicated-FALSE fields these contracts retire.

  ── (B5) `CConvEnvelopeData.hGateData` / `.hGateData'` (`CConvFacade.lean`, lines 157–182) demand a
     CONSTANT `Bs` bounding the bare Gaussian log-gradient `|∂ᵢ log G| = |∑ₖ Wₖ Pvalₖ|/(2(t−s))`.
     This is FALSE: the numerator is `s`-independent and generically ≠ 0, so the quotient blows up as
     `s → t⁻` on a positive-measure `s`-set.  Falsification theorem:
        `QIQTH.GaussianJetTheorem.gateData_numerator_shape_unsat`
     (the `τ→0` poison, an `s`-power−0-vs−1/2 facade artefact).  The TRUE cost is `(t−s)^{−1/2}`
     (heat-kernel gradient estimate `|∇ₓG_τ| ≤ C·τ^{−1/2}·G_{2τ}`, brick β1 =
        `QIQTH.GaussianJetTheorem.gaussian_beats_linear`).
     ⟹ REPLACED by `CConvWitnessEnvelopeDataV2.hStar` (the value-level `(t−s)^{−1/2}`-weighted
        Gaussian domination — the `(⋆)` spec, still `s`-integrable since `∫₀ᵗ (t−s)^{−1/2} ds < ∞`).

  ── (B3) `CConvSourceData.hFbd` (`CConvFacade.lean`, line 121) demands a UNIFORM `|F s z| ≤ Cf`.
     This is FALSE for the concrete Levi/Duhamel source near `(s,z) → (0,0)` (the source carries its
     own `s^γ·G_{cF·s}(z)` Gaussian, unbounded at the diagonal).
     ⟹ REPLACED by `CConvSourceDataV2.hFpair` (the paired `s`-integrability of the Gaussian-weighted
        `L¹`-in-`z` mass — exactly what the downstream `∫₀ᵗ` differentiation-under-∫ needs).  The
        concrete discharge of `hFpair` from a source Gaussian bound is brick 2
        (`CConvV2GaussianPairing.sourcePair_of_gaussian_bound`).

  ── The `SliceChartData` package (this file) is the chart-PARAMETRIC carrier of the SATISFIABLE
     conjuncts that survived the `hGateData` falsification (the `Pval` chart-Jacobian derivative family,
     the amplitude partial-differentiability, and the two-sided radial comparison).  It is generic in
     the chart `W'` and amplitude family `Amp`, to be instantiated later (bricks 3/4/7) at BOTH the
     raw `uniformInverseChart` AND the piecewise `Wg` chart.

  ## SATISFIABILITY GUARDS (this file).
    • `sourceDataV2_zero`     — `CConvSourceDataV2` inhabited at `F ≡ 0` (trivial witness).
    • `sliceChartData_trivial`— `SliceChartData` inhabited at `W' := fun z _ ↦ z`, `Amp := 0`
                                (trivial witness).
    • `hStar` (envelope):  NO generic trivial witness — a trivial witness would require
      `witnessFieldDeriv ≡ 0` (not a new-file object).  Its concrete discharge is the `(⋆)` theorem
      of brick 9 (`WitnessStarConcrete`, from α₂ + β1); the field is NON-vacuous (it is the genuine
      heat-kernel gradient estimate).  Honest header note in lieu of a trivial witness.  `hcoef` and
      `hC2fam` are VERBATIM survivors (not new fields) — their satisfiability is unchanged from
      `CConvFacade.CConvEnvelopeData`.

  NOT `a₁ = R/6`.
-/
import QIQTH.CConvFacade

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.RadialDistance
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CConvV2Contracts

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — `CConvSourceDataV2` : hFjoint + hFmeas (VERBATIM) + hFpair (NEW, replaces hFbd).
    ############################################################################### -/

/-- **★ `CConvSourceDataV2`.**  The V2 source-term contract.  Fields `hFjoint` (joint
    measurability) and `hFmeas` (per-slice measurability) are copied VERBATIM from
    `CConvFacade.CConvSourceData`.  The new field `hFpair` REPLACES the adjudicated-false
    `hFbd : ∀ s z, |F s z| ≤ Cf`:
      `hFpair : IntegrableOn (fun s ↦ (t−s)^{−1/2} · ∫ z, gaussDdim (2(t−s)) z · |F s z|) (Ioc 0 t)`.
    This is the exact `s`-integrability the downstream differentiation-under-∫ consumes; it is
    discharged from a source Gaussian bound in brick 2.  ⚠ NOT `a₁ = R/6`. -/
structure CConvSourceDataV2 (F : ℝ → Point n → ℝ) (t : ℝ) : Prop where
  hFjoint : AEStronglyMeasurable (fun p : ℝ × Point n => F p.1 p.2)
      ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n)))
  hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z) (volume : Measure (Point n))
  hFpair : IntegrableOn
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      (Set.Ioc 0 t) (volume : Measure ℝ)

/-! ###############################################################################
    ### §2 — `CConvWitnessEnvelopeDataV2` : hcoef + hC2fam (VERBATIM) + hStar (NEW,
    ###        replaces hGateData/hGateData').
    ############################################################################### -/

/-- **★ `CConvWitnessEnvelopeDataV2`.**  The V2 envelope contract.  Fields `hcoef` (coefficient
    positivity) and `hC2fam` (the `C²` field-slot family) are copied VERBATIM from
    `CConvFacade.CConvEnvelopeData`.  The single new field `hStar` REPLACES the adjudicated-false
    order-distinct pair `hGateData` (`∀ᶠ x → ∀ᵐ s`) / `hGateData'` (`∀ᵐ s → ∀ᶠ x`), each of which
    demanded a CONSTANT `Bs` bounding the Gaussian log-gradient (refuted by
    `GaussianJetTheorem.gateData_numerator_shape_unsat`).  `hStar` is POINTWISE/UNIFORM on `u`
    (no `∀ᶠ`/`∀ᵐ` reorder duplication), carrying the TRUE `(t−s)^{−1/2}` cost:
      `∃ C ≥ 0, ∀ x ∈ u, ∀ i, ∀ s ∈ Ioc 0 t, ∀ z,
         |witnessFieldDeriv … i (t−s) x z| ≤ C · (t−s)^{−1/2} · gaussDdim (2(t−s)) z`.
    (The off-gate `z ∉ K` branch is subsumed: there `witnessFieldDeriv = 0 ≤ RHS`.)  ⚠ NOT
    `a₁ = R/6`. -/
structure CConvWitnessEnvelopeDataV2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ) : Prop where
  hcoef : 0 ≤ Bs * Ba + Bd
  hC2fam : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
      ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀
  hStar : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
        ≤ C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z

/-! ###############################################################################
    ### §3 — `SliceChartData` : the chart-PARAMETRIC carrier of the survivor conjuncts.
    ###        (Feeds bricks 3/4/7; instantiate `W'` at `uniformInverseChart` AND `Wg`, `Amp` at
    ###        `chartFieldAmp`.)
    ############################################################################### -/

/-- **★★ `SliceChartData` — the chart-PARAMETRIC survivor package.**  Generic in the chart
    `W' : Point n → Point n → Point n` and amplitude family `Amp : ℝ → Point n → Point n → ℝ`
    (`Amp τ z` is the field-slot amplitude at time-window `τ`, base point `z`).  Packages the
    SATISFIABLE conjuncts that survived the `hGateData` falsification (`GaussianJetTheorem`), split
    per-purpose and SMALL:
      • `hWjoint`    — joint measurability of the gated chart representative (`update`-slice); the
                       B3-style measurability leg used by bricks 3/4;
      • `hDeriv`     — the on-gate chart-Jacobian derivative family: `∃ Pval, ∀ k,
                       HasDerivAt (r ↦ W' z (update x i r) k) (Pval k) (x i)` (the `Pval` family
                       is `s`-INDEPENDENT — the chart Jacobian column);
      • `hAmpDiff`   — the on-gate amplitude partial-differentiability `PdiffAt (Amp τ z) i x`;
      • `hRadialLower` — the coercive HALF-radius lower comparison `½·rncRadialSq z ≤ rncRadialSq (W' z x)`;
      • `hRadialUpper` — its two-sided UPPER counterpart `rncRadialSq (W' z x) ≤ 2·rncRadialSq z`.
    ⚠ NOT `a₁ = R/6`. -/
structure SliceChartData (K : Set (Point n)) (S : Point n → Set (Point n)) (u : Set (Point n))
    (W' : Point n → Point n → Point n) (Amp : ℝ → Point n → Point n → ℝ) : Prop where
  hWjoint : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      Measurable (fun p : ℝ × Point n => W' p.2 (Function.update x i w))
  hDeriv : ∀ x ∈ u, ∀ i : Fin n, ∀ z ∈ K, x ∈ S z →
      ∃ Pval : Fin n → ℝ, ∀ k : Fin n,
        HasDerivAt (fun r : ℝ => W' z (Function.update x i r) k) (Pval k) (x i)
  hAmpDiff : ∀ x ∈ u, ∀ i : Fin n, ∀ τ : ℝ, ∀ z ∈ K, x ∈ S z →
      PdiffAt (fun x' => Amp τ z x') i x
  hRadialLower : ∀ x ∈ u, ∀ z ∈ K, x ∈ S z →
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W' z x)
  hRadialUpper : ∀ x ∈ u, ∀ z ∈ K, x ∈ S z →
      rncRadialSq (W' z x) ≤ 2 * rncRadialSq z

/-! ###############################################################################
    ### §4 — SATISFIABILITY GUARDS (non-vacuity audit; each a genuine inhabitant).
    ############################################################################### -/

/-- **`sourceDataV2_zero` — `CConvSourceDataV2` is inhabited (trivial witness `F ≡ 0`).**  With the
    zero source the paired integrand collapses to the constant `0` (mass · `|0| = 0`), which is
    `IntegrableOn` any set; `hFjoint`/`hFmeas` are `aestronglyMeasurable_const`.  Confirms `hFpair`
    is a SATISFIABLE (non-vacuous, non-`False`) contract.  ⚠ NOT `a₁ = R/6`. -/
theorem sourceDataV2_zero (t : ℝ) :
    CConvSourceDataV2 (fun (_ : ℝ) (_ : Point n) => (0 : ℝ)) t where
  hFjoint := aestronglyMeasurable_const
  hFmeas := fun _ => aestronglyMeasurable_const
  hFpair := by
    have hfun : (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (2 * (t - s)) z * |(0 : ℝ)| ∂(volume : Measure (Point n)))
        = (fun _ : ℝ => (0 : ℝ)) := by
      funext s
      simp
    rw [hfun]
    exact integrableOn_zero

/-- **`sliceChartData_trivial` — `SliceChartData` is inhabited (trivial witness).**  At the
    projection chart `W' := fun z _ ↦ z` (so `W' z x = z`, ignoring the field slot) and the zero
    amplitude `Amp := fun _ _ _ ↦ 0`:
      • `hWjoint`      = `measurable_snd` (`W' p.2 · = p.2`);
      • `hDeriv`       = the constant chart column `Pval := 0` (`r ↦ z k` is constant);
      • `hAmpDiff`     = `differentiableAt_const` (`Amp ≡ 0`);
      • `hRadialLower/Upper` = `½·r ≤ r ≤ 2·r` from `rncRadialSq_nonneg` (`W' z x = z`).
    Confirms every `SliceChartData` field is SATISFIABLE.  ⚠ NOT `a₁ = R/6`. -/
theorem sliceChartData_trivial (K : Set (Point n)) (S : Point n → Set (Point n))
    (u : Set (Point n)) :
    SliceChartData K S u (fun z (_ : Point n) => z) (fun (_ : ℝ) (_ : Point n) (_ : Point n) => (0 : ℝ)) where
  hWjoint := fun _ _ _ =>
    Filter.Eventually.of_forall (fun _ _ => measurable_snd)
  hDeriv := fun x _ i z _ _ =>
    ⟨fun _ => 0, fun k => by
      simpa using (hasDerivAt_const (x i) (z k))⟩
  hAmpDiff := fun x _ i _ z _ _ => by
    simp [PdiffAt]
  hRadialLower := fun x _ z _ _ => by
    have h := rncRadialSq_nonneg z
    linarith
  hRadialUpper := fun x _ z _ _ => by
    have h := rncRadialSq_nonneg z
    linarith

end QIQTH.CConvV2Contracts

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2Contracts
#print axioms sourceDataV2_zero
#print axioms sliceChartData_trivial
end AxiomChecks
