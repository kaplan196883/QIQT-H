/-
  OffGateCutoffDischarge — discharging the off-gate witness-vanishing germ `hOffNhd`
  (the sole carried residue of `MixedNormalFormFull.witnessMixed_hNormalForm_full`, J4-792)
  from PURE CUTOFF-SUPPORT GEOMETRY.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a pure
  support/germ manipulation of the gated van-Vleck witness.  No `sorry`, no new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT J4-792 LEFT.  `witnessMixed_hNormalForm_full` carried ONE hypothesis:
      `hOffNhd : ∀ τ ∈ Ioo 0 τ₀, ∀ ζ ∉ S z₀, ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness … τ w z₀ = 0`,
  the "witness ≡ 0 on a neighborhood of each off-gate field point."  As stated this germ mentions the
  FULL witness (parametrix × Levi × hard gate), so it reads as conclusion-flavored.  This file replaces
  it, everywhere, by a **manifestly geometric** germ that mentions ONLY the smooth radial cutoff bump
  composed with the chart:
      `hCut : ∀ᶠ w in 𝓝 ζ, w ∈ S z₀ → radialCutoff a b (uniformInverseChart … z₀ w) = 0`.
  This is the honest "`radialCutoff` kills the parametrix before the gate boundary" condition (memory
  [[qiqth_jet4_tower_complete]], J4-792 note), stripped of everything about the heat parametrix, the
  amplitude `Θ^{−1/2}(u₀+u₁τ)`, and the Levi series.

  ## WHAT IS GENUINELY DISCHARGED (from geometry, not carried).
  • `witness_offGate_eventuallyZero` — the REDUCTION: from `hCut` (+ `z₀ ∈ K`) the witness germ `hOffNhd`
    follows OUTRIGHT, for every `τ` (`τ`-uniform, the hard gate being `τ`-independent).  On-gate field
    points `w ∈ S z₀` use `vanVleckGatedWitness_gate_apply` — whose value has `radialCutoff` as an
    OUTRIGHT factor, killed to `0` by `hCut` (`zero_mul`); off-gate `w ∉ S z₀` use
    `gatedKernel_apply_of_notMem`.
  • `cutoffGerm_of_notMem_closure` — the FAR / open-exterior case of `hCut` is discharged from geometry
    with NOTHING carried: for `ζ ∉ closure (S z₀)` a whole neighborhood is off-gate, so the antecedent
    `w ∈ S z₀` is impossible and `hCut` holds vacuously.  So the residue is confined to the FRONTIER
    collar `∂(S z₀)` — exactly where the cutoff-support margin (`b < c`, banked pointwise as
    `B2MeasurabilityDissolution.radialCutoff_zero_on_frontier_collar`) lives.

  ## HONEST RESIDUE (what is NOT closed here).  At FRONTIER points `ζ ∈ ∂(S z₀)` the neighborhood form of
  `hCut` needs the pointwise cutoff-vanishing (banked, margin `b < c`) UPGRADED to a germ, i.e. continuity
  of `w ↦ radialCutoff a b (uniformInverseChart … z₀ w)` at the frontier — a chart-regularity fact that
  is only banked LOCALLY (on inner balls `ContDiffOn ℝ 2 … (ball w ρc)`), NOT at the frontier radius.
  So `hCut` is carried at frontier points as the clean geometric germ; it is NOT the conclusion, mentions
  only the cutoff bump, and is satisfiable (vacuous when `S z₀ = univ`, or true whenever the cutoff
  support sits strictly inside the gate).  The improvement over J4-792 is real: the residue is now a
  parametrix-free radial-cutoff-support germ, with the entire far region discharged.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedNormalFormFull
import QIQTH.AmplitudePackage

open Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.MixedNormalFormFull QIQTH.MixedSliverAssembly

namespace QIQTH.OffGateCutoffDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ `witness_offGate_eventuallyZero` — the REDUCTION `hCut ⟹ hOffNhd`.**  For a base point
    `z₀ ∈ K` and ANY field point `ζ`, if the radial cutoff vanishes on the ON-GATE points of a
    neighborhood of `ζ` (`hCut`), then the gated van-Vleck witness is `0` on a neighborhood of `ζ`, for
    EVERY time `τ` (the hard gate being `τ`-independent).  On-gate `w ∈ S z₀`:
    `vanVleckGatedWitness_gate_apply` factors the witness with `radialCutoff` as an outright leading
    factor, killed by `hCut` (`zero_mul`).  Off-gate `w ∉ S z₀`: `gatedKernel_apply_of_notMem`.
    Discharges the geometric off-gate germ residue `hOffNhd` of
    `MixedNormalFormFull.witnessMixed_hNormalForm_full` from the parametrix-free cutoff germ.
    NOT `a₁ = R/6`. -/
theorem witness_offGate_eventuallyZero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b τ : ℝ)
    {z₀ : Point n} (hz₀ : z₀ ∈ K) (ζ : Point n)
    (hCut : ∀ᶠ w in 𝓝 ζ, w ∈ S z₀ →
      radialCutoff a b (uniformInverseChart g gi hC hK z₀ w) = 0) :
    ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0 := by
  filter_upwards [hCut] with w hw
  by_cases hwS : w ∈ S z₀
  · rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hz₀ hwS, hw hwS, zero_mul]
  · unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ w z₀ (Or.inr hwS)

/-- **★ `cutoffGerm_of_notMem_closure` — the FAR / open-exterior case, discharged from geometry.**  For
    a field point `ζ ∉ closure (S z₀)` the complement of the closure is an open neighborhood of `ζ` that
    is ENTIRELY off-gate, so the antecedent `w ∈ S z₀` is impossible on it and the cutoff germ `hCut`
    holds VACUOUSLY — nothing carried.  This confines the genuine residue of `hCut` (and hence of the
    off-gate germ `hOffNhd`) to the FRONTIER collar `∂(S z₀)`.  NOT `a₁ = R/6`. -/
theorem cutoffGerm_of_notMem_closure (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (z₀ ζ : Point n) (hζ : ζ ∉ closure (S z₀)) :
    ∀ᶠ w in 𝓝 ζ, w ∈ S z₀ →
      radialCutoff a b (uniformInverseChart g gi hC hK z₀ w) = 0 := by
  have hopen : (closure (S z₀))ᶜ ∈ 𝓝 ζ :=
    (isClosed_closure).isOpen_compl.mem_nhds hζ
  filter_upwards [hopen] with w hw hwS
  exact absurd (subset_closure hwS) hw

/-- **★★ `witnessMixed_hNormalForm_full_geom` — THE FULL `∀ζ` MIXED `hNormalForm`, carrying only the
    PARAMETRIX-FREE cutoff-support germ.**  Identical conclusion to
    `MixedNormalFormFull.witnessMixed_hNormalForm_full`, but the sole geometric residue is the
    manifestly-geometric radial-cutoff germ `hCutAll` (vanishing of `radialCutoff a b (chart …)` on the
    on-gate points of a neighborhood of each off-gate field point) INSTEAD of the conclusion-flavored
    witness germ `hOffNhd`.  Proof: supply `hOffNhd` from `witness_offGate_eventuallyZero` pointwise.
    The far / open-exterior part of `hCutAll` is itself free (`cutoffGerm_of_notMem_closure`); only the
    frontier collar remains.  NOT `a₁ = R/6`. -/
theorem witnessMixed_hNormalForm_full_geom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ₀ : ℝ) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (Pi Pj Q : Point n → Point n)
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
    (hCutAll : ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, w ∈ S z₀ →
        radialCutoff a b (uniformInverseChart g gi hC hK z₀ w) = 0) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
      pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ
        = mTerm0 (uniformInverseChart g gi hC hK z₀) Pi Pj Q
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ
          + mTerm1 (uniformInverseChart g gi hC hK z₀) Pj
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ
          + mTerm1 (uniformInverseChart g gi hC hK z₀) Pi
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')) τ ζ
          + sTerm2 (uniformInverseChart g gi hC hK z₀)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ')) τ ζ :=
  witnessMixed_hNormalForm_full g gi hC hK S a b i j τ₀ z₀ hz₀ hSopen Pi Pj Q
    hJetPi hJetPj hJetQ hAmpDi hAmpDj hAmpD2
    (fun τ _ ζ hζ =>
      witness_offGate_eventuallyZero g gi hC hK S a b τ hz₀ ζ (hCutAll ζ hζ))

end QIQTH.OffGateCutoffDischarge

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.OffGateCutoffDischarge
#print axioms witness_offGate_eventuallyZero
#print axioms cutoffGerm_of_notMem_closure
#print axioms witnessMixed_hNormalForm_full_geom
end AxiomChecks
