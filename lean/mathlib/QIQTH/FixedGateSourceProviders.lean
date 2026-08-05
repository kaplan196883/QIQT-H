/-
  FixedGateSourceProviders — J4-257: wide-route bricks 8+4, the LEVI SOURCE SLICE builder plus the
  FIXED-GATE wide-domination re-exports.  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It performs two
  pieces of MECHANICAL plumbing on top of already-banked machinery:

  ── PART A — `sourceData_of_leviLocalData` — THE `CConvSourceData` LEVI-SOURCE-SLICE BUILDER.
     `CConvFacade.CConvSourceData F t Cf` has three fields (copied verbatim from `CConvFacade`):
       • `hFjoint : AEStronglyMeasurable (fun p ↦ F p.1 p.2) ((volume.restrict (uIoc 0 t)).prod volume)`
       • `hFbd    : ∀ s z, |F s z| ≤ Cf`
       • `hFmeas  : ∀ s, AEStronglyMeasurable (fun z ↦ F s z) volume`
     At the concrete source slice `F := fun s z ↦ leviSeries E s z 0`, this builder DISCHARGES:
       • `hFjoint`  — FULLY from the banked `LeviSeriesLocalData E C t` package: the termwise JOINT
         strong measurability `data.htermMeas` gives each term measurable on the product; the a.e.
         SUMMABILITY on the restricted product holds pointwise on `Ioc 0 t` from `data.hmajor` +
         `data.hmajorSum`; `LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise` concludes.
       • `hFmeas`   — from the package's termwise spatial measurability `iterE_zmeas` (all `s`) + the
         CARRIED all-`s` a.e. convergence `hFsum` (the honest Levi-convergence input), via the same
         generic `tsum` strong-measurability lemma.
     and CARRIES:
       • `hFbd`     — the uniform-constant bound `|leviSeries E s z 0| ≤ Cf`.  This is a genuine,
         satisfiable, non-vacuous carry: the banked machinery only delivers the GAUSSIAN domination
         `≤ C_L·baseKernelW 2 0` (which is NOT a `τ`-uniform constant), so the uniform bound is an
         honest still-open analytic input — NEVER the conclusion.
       • `hFsum`    — the all-`s` a.e. summability of the signed Levi terms (the convergence fact); the
         package proves it only on the `(0,t]` window, so the all-`s` version is carried.

  ── PART B/C — `fixedGateProviders_bundle` — THE PRE-ASSEMBLY BUNDLE (everything at ONE gate).
     Conjoins Part A's source slice with the two FIXED-GATE WIDE DOMINATIONS re-exported straight from
     the banked `FixedGateDichotomy.{zeroth_global_of_package, second_global_of_package}` fed a
     `WideWitnessAmplitude.WideAmplitudePackage` at the fixed gate `S` (radii `P.a, P.b`, dilation
     `P.lam`, radius `P.r`, cap `P.τ₀`).  The zeroth `|H_G τ 0 z| ≤ C·gaussDdim (lam·τ) z` and second
     `|D²H … i τ z| ≤ C·τ⁻¹·gaussDdim (lam·τ) z` dominations are COMPOSED, not re-proved (the wide
     analogues of `hAdom`/`hBdom` were already delivered by bricks 5/7).  The support carries
     `hSupp0`/`hSupp2` are the honest satisfiable geometry inputs (never the conclusion).

  ── NOT BUILT (honest, recorded).  The `τ≤t` Gaussian envelope provider `hEboundFull`
     (`EboundWiringHD1.hEboundW_from_geometry`) chooses its OWN existential `(a,b,S)` internally (its
     proof calls `gatedWitnessN1_hEboundW_le_vanVleck_final`, which pins the gate), so it CANNOT be
     re-instantiated at an externally-fixed gate without a fixed-gate version of that base lemma — the
     W3 gate-compatibility wall.  It stays a carry for brick 11.

  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the conclusion.  NO `sorry`.
  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvFacade
import QIQTH.LeviSeriesLocalData
import QIQTH.FixedGateDichotomy

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.GaussianWidthTolerant
open QIQTH.CConvFacade QIQTH.LeviSeriesLocalData
open QIQTH.WideWitnessAmplitude QIQTH.FixedGateDichotomy
open scoped Interval Topology BigOperators

namespace QIQTH.FixedGateSourceProviders

set_option maxHeartbeats 3200000

variable {n : ℕ}

/-! ###############################################################################
    ### PART A — the `CConvSourceData` Levi-source-slice builder.
    ############################################################################### -/

/-- The spatial `z`-slice strong measurability of the Levi source `leviSeries E s · 0` at every `s`,
    from the package's termwise `iterE_zmeas` + the carried convergence `hFsum`. -/
theorem leviSource_zslice_aesm
    (E : ℝ → Point n → Point n → ℝ) (C t : ℝ)
    (data : LeviSeriesLocalData E C t)
    (hFsum : ∀ s : ℝ, ∀ᵐ z ∂(volume : Measure (Point n)),
        Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0))
    (s : ℝ) :
    AEStronglyMeasurable (fun z : Point n => leviSeries E s z 0) (volume : Measure (Point n)) := by
  have hmeas : ∀ k : ℕ,
      AEStronglyMeasurable (fun z : Point n => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0)
        (volume : Measure (Point n)) :=
    fun k => (iterE_zmeas E data.hEmeas (k + 1) (by omega) s 0).const_mul _
  have hrw : (fun z : Point n => leviSeries E s z 0)
      = fun z : Point n => ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0 := rfl
  rw [hrw]
  exact leviSeries_stronglyMeasurable_of_termwise
    (fun k z => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0) hmeas (hFsum s)

/-- The joint `(s,z)` strong measurability of the Levi source on the restricted product
    `(volume.restrict (uIoc 0 t)).prod volume` — from the package's termwise joint measurability
    `htermMeas` and the a.e. summability on `Ioc 0 t` (`hmajor` + `hmajorSum`). -/
theorem leviSource_joint_aesm
    (E : ℝ → Point n → Point n → ℝ) (C t : ℝ)
    (data : LeviSeriesLocalData E C t) :
    AEStronglyMeasurable (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n))) := by
  have hmeas : ∀ k : ℕ,
      AEStronglyMeasurable
        (fun p : ℝ × Point n => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0)
        ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n))) :=
    fun k => ((data.htermMeas (k + 1) (by omega) 0).aestronglyMeasurable).const_mul _
  have hset : MeasurableSet (Set.uIoc (0 : ℝ) t ×ˢ (Set.univ : Set (Point n))) := by
    refine MeasurableSet.prod ?_ MeasurableSet.univ
    rw [Set.uIoc_of_le data.hT.le]; exact measurableSet_Ioc
  have hsum : ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n))),
      Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    refine ae_restrict_of_forall_mem hset (fun p hp => ?_)
    have hp1 : p.1 ∈ Set.uIoc 0 t := (Set.mem_prod.1 hp).1
    rw [Set.uIoc_of_le data.hT.le] at hp1
    obtain ⟨hpos, hle⟩ := hp1
    refine Summable.of_norm_bounded (data.hmajorSum p.1 p.2 0 hpos) (fun k => ?_)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    exact data.hmajor k p.1 p.2 0 hpos hle
  have hrw : (fun p : ℝ × Point n => leviSeries E p.1 p.2 0)
      = fun p : ℝ × Point n => ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0 := rfl
  rw [hrw]
  exact @leviSeries_stronglyMeasurable_of_termwise (ℝ × Point n) _
    ((volume.restrict (Set.uIoc 0 t)).prod (volume : Measure (Point n)))
    (fun k p => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) p.1 p.2 0) hmeas hsum

/-- **★★★ `sourceData_of_leviLocalData` — THE LEVI-SOURCE-SLICE BUILDER (wide-route brick 8).**  From
    the banked `LeviSeriesLocalData E C t` package (the `(0,t]`-window Levi packaging), builds the
    `CConvFacade.CConvSourceData` at the concrete source slice `F := fun s z ↦ leviSeries E s z 0`:
      • `hFjoint` — DISCHARGED from the package (`leviSource_joint_aesm`: `htermMeas` + `hmajor`/
        `hmajorSum` on `Ioc 0 t` + `leviSeries_stronglyMeasurable_of_termwise` on the restricted product);
      • `hFmeas`  — DISCHARGED (`leviSource_zslice_aesm`: `iterE_zmeas` + the CARRIED convergence `hFsum`);
      • `hFbd`    — CARRIED (the uniform-constant bound; the machinery only gives the non-uniform
        Gaussian domination).
    Each carry is satisfiable, non-vacuous, never the conclusion.  NOT `a₁ = R/6`. -/
theorem sourceData_of_leviLocalData
    (E : ℝ → Point n → Point n → ℝ) (C t Cf : ℝ)
    (data : LeviSeriesLocalData E C t)
    (hFbd : ∀ s z, |leviSeries E s z 0| ≤ Cf)
    (hFsum : ∀ s : ℝ, ∀ᵐ z ∂(volume : Measure (Point n)),
        Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0)) :
    CConvSourceData (fun s z => leviSeries E s z 0) t Cf :=
  ⟨leviSource_joint_aesm E C t data, hFbd, leviSource_zslice_aesm E C t data hFsum⟩

/-! ###############################################################################
    ### PART B — the fixed-gate wide dominations (re-exported from the banked bricks).
    ############################################################################### -/

/-- **★★ `fixedGateWideDominations` — THE FIXED-GATE WIDE DOMINATIONS (wide-route brick 4 re-export).**
    From a `WideAmplitudePackage` at the fixed gate `S` (the brick-5 output) and the two honest support
    carries, re-exports BOTH global wide dominations — the zeroth `hAdom`-analogue and the second
    `hBdom`-analogue — as one conjunction.  COMPOSED from `FixedGateDichotomy.zeroth_global_of_package`
    and `second_global_of_package`; nothing is re-proved.  NOT `a₁ = R/6`. -/
theorem fixedGateWideDominations
    {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudePackage g gi hC hK S i)
    (hSupp0 : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r)
    (hSupp2 : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      witnessSecondXDeriv g gi hC hK S P.a P.b i τ z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r) :
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
        |vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z|
          ≤ C₀ * gaussDdim (P.lam * τ) z)
    ∧ (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
        |witnessSecondXDeriv g gi hC hK S P.a P.b i τ z|
          ≤ C₁ * τ⁻¹ * gaussDdim (P.lam * τ) z) :=
  ⟨zeroth_global_of_package P hSupp0, second_global_of_package P hSupp2⟩

/-! ###############################################################################
    ### PART C — the pre-assembly bundle (everything at the ONE gate).
    ############################################################################### -/

/-- **★★★ `fixedGateProviders_bundle` — THE PRE-ASSEMBLY BUNDLE (wide-route brick 8+4, ready for brick
    11).**  Everything the source/domination side provides at the ONE fixed gate `S`:
      • the Levi source slice `CConvSourceData (fun s z ↦ leviSeries E s z 0) t Cf` (Part A);
      • the zeroth fixed-gate wide domination (`hAdom` analogue);
      • the second fixed-gate wide domination (`hBdom` analogue).
    Part A is built from `LeviSeriesLocalData E C t` + the two source carries; Parts B are re-exported
    from `FixedGateDichotomy` fed the fixed-gate `WideAmplitudePackage P` + the support carries.  The
    caller ties `E` to the concrete gated-witness residual `heatOp g gi (vanVleckGatedWitness … P.a P.b)`
    at brick 11; the bundle keeps `E` explicit so the source builder stays reusable.  NOT `a₁ = R/6`. -/
theorem fixedGateProviders_bundle
    {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (E : ℝ → Point n → Point n → ℝ) (C t Cf : ℝ)
    (data : LeviSeriesLocalData E C t)
    (hFbd : ∀ s z, |leviSeries E s z 0| ≤ Cf)
    (hFsum : ∀ s : ℝ, ∀ᵐ z ∂(volume : Measure (Point n)),
        Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z 0))
    (P : WideAmplitudePackage g gi hC hK S i)
    (hSupp0 : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r)
    (hSupp2 : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      witnessSecondXDeriv g gi hC hK S P.a P.b i τ z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r) :
    CConvSourceData (fun s z => leviSeries E s z 0) t Cf
    ∧ (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
        |vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z|
          ≤ C₀ * gaussDdim (P.lam * τ) z)
    ∧ (∃ C₁ : ℝ, 0 < C₁ ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
        |witnessSecondXDeriv g gi hC hK S P.a P.b i τ z|
          ≤ C₁ * τ⁻¹ * gaussDdim (P.lam * τ) z) :=
  ⟨sourceData_of_leviLocalData E C t Cf data hFbd hFsum,
   (fixedGateWideDominations P hSupp0 hSupp2).1,
   (fixedGateWideDominations P hSupp0 hSupp2).2⟩

end QIQTH.FixedGateSourceProviders

section AxiomChecks
open QIQTH.FixedGateSourceProviders
#print axioms leviSource_zslice_aesm
#print axioms leviSource_joint_aesm
#print axioms sourceData_of_leviLocalData
#print axioms fixedGateWideDominations
#print axioms fixedGateProviders_bundle
end AxiomChecks
