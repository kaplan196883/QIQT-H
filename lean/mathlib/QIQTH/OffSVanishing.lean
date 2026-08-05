/-
# J4-235 — Ladder step 2: the `hOffS` geometric brick (off-gate witness vanishing).

The v7 capstone's `hcarField` / `hcarField2` existentials (GatedRepSFix's v4 forms) each carry an
`hOffS` / `hOffS2` conjunct: for a field point `p ∉ S q` (with base `q ∈ K`, time `τ > 0`) the raw
field-`pd` (first and mixed-second) of the gated van-Vleck witness vanish.  At the CONCRETE flow-ball
gate `S q = uniformFlowExp g gi hC hK q '' Metric.ball 0 c` these are genuine geometric facts.

## The clean collar route (no frontier analysis)

For `q ∈ K` the field-slot function `x ↦ vanVleckGatedWitness g gi hC hK S a b τ x q` is supported in
`S q ∩ {x : radialCutoff a b (W q x) ≠ 0}`, where `W = uniformInverseChart …` is the germ
left-inverse of `φ_q = uniformFlowExp …` (`W q (φ_q v) = v` for `‖v‖ < δ₀`, from `huniformChart`).
On `S q` we have `x = φ_q v` with `W q x = v`, and `radialCutoff a b v ≠ 0 ⟹ rncRadialSq v < b²
⟹ ‖v‖ < b` (via `norm_le_rncRadial`).  Hence the support sits inside `φ_q '' ball 0 b`, whose
CLOSURE is contained in `φ_q '' ball 0 c = S q` (via `huniformChart`'s closed-map conjunct at radius
`b`, and `closedBall 0 b ⊆ ball 0 c` for `b < c`).  So every `p ∉ S q` lies in the OPEN complement
`U = (closure (φ_q '' ball 0 b))ᶜ`, on which the witness is identically `0`.  Local vanishing on an
open neighbourhood ⟹ all field-`pd`'s (first and mixed second) vanish (`pd` of a locally-zero
function is `0`; iterate for the second).

Radii carried HONESTLY: `0 < a < b < c < δ₀`, with `δ₀` the single uniform chart radius from
`uniformInverseChart_huniformChart`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedRepSFix
import QIQTH.ConvApproximants
import QIQTH.UniformChartRadius
import QIQTH.ConcreteGateInstantiation
import QIQTH.RNCDecay
import QIQTH.NormalFormDischarge

open Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.RadialDistance QIQTH.RNCDecay QIQTH.ExpMap
open scoped Topology

namespace QIQTH.OffSVanishing

variable {n : ℕ}

/-! ### The trivial `pd`-of-zero helper. -/

/-- The coordinate partial of the constant-`0` function is `0` (`deriv` of a constant). -/
theorem pd_zero_fun (i : Fin n) (x : Point n) :
    pd (fun _ : Point n => (0 : ℝ)) i x = 0 := by
  simp only [pd]
  simp

/-! ### The collar lemma — local vanishing of the witness off the concrete gate. -/

/-- **★★ J4-235 (collar) — `witness_eventuallyEq_zero_offGate`.**  At the concrete flow-ball gate
    `S q = uniformFlowExp g gi hC hK q '' Metric.ball 0 c` (`0 < a < b < c < δ₀`), for every `q ∈ K`
    and every field point `p ∉ S q`, the field-slot function
    `x ↦ vanVleckGatedWitness g gi hC hK S a b τ x q` is identically `0` on a NEIGHBOURHOOD of `p`.

    Via the support-closure argument: the witness support (in the field slot) lies inside
    `φ_q '' ball 0 b`, whose closure `⊆ S q`; so `p ∉ S q` sits in the open set
    `(closure (φ_q '' ball 0 b))ᶜ`, on which the gate kills the off-`S q` part and the radial cutoff
    kills the collar `{φ_q v : b ≤ ‖v‖ < c}` (germ left-inverse `W q (φ_q v) = v` +
    `radialCutoff_eq_zero`).  Radii `0 < a < b < c < δ₀` carried; `δ₀` from
    `uniformInverseChart_huniformChart`.  NOT `a₁ = R/6`. -/
theorem witness_eventuallyEq_zero_offGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (q : Point n), q ∈ K → ∀ p : Point n, p ∉ S q →
          (fun x => vanVleckGatedWitness g gi hC hK S a b τ x q) =ᶠ[nhds p] (fun _ => 0) := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq τ q hq p hpS
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hbδ : b < δ₀ := lt_trans hbc hcδ
  -- per-`q` chart data.
  obtain ⟨hgerm, hball⟩ := hspec q hq
  obtain ⟨_hOpenb, hclosb⟩ := hball b hb0 hbδ
  -- `S q = φ_q '' ball 0 c`.
  have hSq : S q = uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c := by rw [hSeq]
  -- closure of the `b`-support-ball image `⊆ S q`.
  have hsub : closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b) ⊆ S q := by
    rw [hSq]
    exact hclosb.trans (Set.image_mono (Metric.closedBall_subset_ball hbc))
  -- `p` is in the OPEN complement of that closure.
  set U := (closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b))ᶜ with hUdef
  have hUopen : IsOpen U := isOpen_compl_iff.mpr isClosed_closure
  have hpU : p ∈ U := fun h => hpS (hsub h)
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) ?_
  intro x hxU
  -- `x ∉ φ_q '' ball 0 b`.
  have hxNotBall : x ∉ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b :=
    fun h => hxU (subset_closure h)
  -- compute the witness value.
  show vanVleckGatedWitness g gi hC hK S a b τ x q = 0
  unfold vanVleckGatedWitness
  by_cases hxS : x ∈ S q
  · -- on the gate: the radial cutoff kills the value.
    rw [gatedKernel_apply_of_mem K S _ τ hq hxS]
    rw [hSq] at hxS
    obtain ⟨v, hv, hvx⟩ := hxS
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    -- germ left-inverse: `W q x = v`.
    have hWqv : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
      have hh := ((hgerm v (lt_trans hvc hcδ)).1).eq_of_nhds
      simpa using hh
    have hWqx : uniformInverseChart g gi hC hK q x = v := by rw [← hvx]; exact hWqv
    -- the cutoff at `v` vanishes (else `x ∈ φ_q '' ball 0 b`).
    have hcut0 : radialCutoff a b v = 0 := by
      by_contra hne
      have hlt : rncRadialSq v < b ^ 2 := by
        by_contra hge
        exact hne (radialCutoff_eq_zero ha hab (not_lt.mp hge))
      have hsqle : ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
        mul_le_mul (norm_le_rncRadial v) (norm_le_rncRadial v) (norm_nonneg v)
          (rncRadial_nonneg v)
      have hnv2 : ‖v‖ ^ 2 < b ^ 2 := by
        have hsq := rncRadial_sq v
        nlinarith [hsqle, hlt, hsq]
      have hnvb : ‖v‖ < b := lt_of_pow_lt_pow_left₀ 2 hb0.le hnv2
      exact hxNotBall ⟨v, mem_ball_zero_iff.mpr hnvb, hvx⟩
    unfold globalCutoffParametrixWitnessN
    rw [hWqx, hcut0, zero_mul]
  · -- off the gate: the `S`-gate kills the value.
    rw [gatedKernel_apply_of_notMem K S _ τ x q (Or.inr hxS)]

/-! ### The `hOffS` / `hOffS2` producers (exact GatedRepSFix conjunct shapes). -/

/-- **★★ J4-235 — `hOffS_concrete`.**  At the concrete flow-ball gate the EXACT `hcarField` off-`S`
    conjunct (`GatedRepSFix.…_v4`, line-for-line): for every `k`, every `w` with `w.2.2 ∈ K`,
    `0 < w.1`, `w.2.1 ∉ S w.2.2`, the raw first field-`pd`
    `witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0`.  From the collar lemma via
    `pd_congr_of_eventuallyEq` + `pd_zero_fun`.  Radii `0 < a < b < c < δ₀`.  NOT `a₁ = R/6`. -/
theorem hOffS_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (k : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := witness_eventuallyEq_zero_offGate g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq k w hzK hτ hpS
  have hEq := hcollar c hbc hcδ S hSeq w.1 w.2.2 hzK w.2.1 hpS
  show pd (fun x' => vanVleckGatedWitness g gi hC hK S a b w.1 x' w.2.2) k w.2.1 = 0
  rw [pd_congr_of_eventuallyEq _ _ k w.2.1 hEq]
  exact pd_zero_fun k w.2.1

/-- **★★ J4-235 — `hOffS2_concrete`.**  At the concrete flow-ball gate the EXACT `hcarField2` off-`S`
    conjunct: for every `i j`, every `w` with `w.2.2 ∈ K`, `0 < w.1`, `w.2.1 ∉ S w.2.2`, the raw
    MIXED second field-`pd`
    `pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1 = 0`.
    From the collar lemma one level up (`eventually_eventually_nhds` + `pd_congr_of_eventuallyEq`
    twice + `pd_zero_fun`).  Radii `0 < a < b < c < δ₀`.  NOT `a₁ = R/6`. -/
theorem hOffS2_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i j : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
            = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := witness_eventuallyEq_zero_offGate g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro c hbc hcδ S hSeq i j w hzK hτ hpS
  have hEq := hcollar c hbc hcδ S hSeq w.1 w.2.2 hzK w.2.1 hpS
  -- one level up: the first `pd` is `0` on a neighbourhood of `w.2.1`.
  have hEq2 : (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y)
      =ᶠ[nhds w.2.1] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun x =>
      (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) x = (fun _ => (0 : ℝ)) x)).mpr hEq
    filter_upwards [hnest] with y hy
    rw [pd_congr_of_eventuallyEq _ _ j y hy]
    exact pd_zero_fun j y
  rw [pd_congr_of_eventuallyEq _ _ i w.2.1 hEq2]
  exact pd_zero_fun i w.2.1

/-! ### The extended concrete-gate discharge bundle (extends J4-234). -/

/-- **★★★ J4-235 — `concreteGate_carriers_discharged_v2`.**  At the concrete flow-ball gate
    `S z = uniformFlowExp g gi hChr hK z '' Metric.ball 0 c` (`0 < a < b < c < δ₀`), the J4-234 bundle
    (`ConcreteGateInstantiation.concreteGate_carriers_discharged`: the three v7 supplier binders
    `hKSmeas`, `hS0`, `hchrMeas`) PLUS the off-`S` conjuncts of BOTH jet existentials now hold
    SIMULTANEOUSLY under a single radius `δ₀`:
      • the three measurability / basepoint binders (J4-234);
      • `hOffS` — `∀ k`, the raw first field-`pd` vanishes off `S q` (this file);
      • `hOffS2` — `∀ i j`, the raw mixed second field-`pd` vanishes off `S q` (this file).
    This is exactly what LADDER STEP 2 discharges from the `hcarField` / `hcarField2` existentials at
    the concrete gate: the whole off-`S` conjunct of each drops out.  What REMAINS inside those
    existentials is the measurability block (chart / amplitude / jet-coefficient Borel measurability)
    and the on-gate `hgate` C² chart/amplitude jet block — other ladder steps.  NOT `a₁ = R/6`. -/
theorem concreteGate_carriers_discharged_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) →
      -- J4-234: the three v7 supplier binders.
      (MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
        ∧ (0 : Point n) ∈ S 0
        ∧ (∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)))
      -- J4-235: the two off-`S` jet conjuncts.
      ∧ (∀ (k : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          witnessFieldDeriv g gi hChr hK S a b k w.1 w.2.1 w.2.2 = 0)
      ∧ (∀ (i j : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b w.1 x w.2.2) j y)
              i w.2.1 = 0) := by
  obtain ⟨δ₁, hδ₁pos, h234⟩ :=
    QIQTH.ConcreteGateInstantiation.concreteGate_carriers_discharged g gi hChr hK hK0
  obtain ⟨δ₂, hδ₂pos, hoff1⟩ := hOffS_concrete g gi hChr hK a b ha hab
  obtain ⟨δ₃, hδ₃pos, hoff2⟩ := hOffS2_concrete g gi hChr hK a b ha hab
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁pos (lt_min hδ₂pos hδ₃pos), ?_⟩
  intro c hbc hcδ S hSeq
  have hc0 : 0 < c := lt_trans hb0 hbc
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ₃ : c < δ₃ := lt_of_lt_of_le hcδ ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨h234 c hc0 hcδ₁ S hSeq, hoff1 c hbc hcδ₂ S hSeq, hoff2 c hbc hcδ₃ S hSeq⟩

end QIQTH.OffSVanishing

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.OffSVanishing
#print axioms pd_zero_fun
#print axioms witness_eventuallyEq_zero_offGate
#print axioms hOffS_concrete
#print axioms hOffS2_concrete
#print axioms concreteGate_carriers_discharged_v2
end AxiomChecks
