/-
  WitnessTimeHasDerivAt — J4-915: DISCHARGING the `z`-pointwise TIME `HasDerivAt` carry of `hpardiff`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  ONE named analytic carry: the `z`-POINTWISE TIME `HasDerivAt` family that J4-912
  (`HpardiffZTimeDerivReduction`) left as the sole DIFFERENTIABILITY residue inside its inner `z`-level
  family `hZ` (the differentiability sibling of J4-911's crude-envelope BOUND `hAcrude`).  No `sorry`
  (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none
  equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DISCHARGE (not a carry).  J4-912 flagged the `z`-pointwise time `HasDerivAt`
      `∀ᵐ z, ∀ c' ∈ V, HasDerivAt (fun c' => A (c'−s) 0 z · F s z 0) (…) c'`
  (`A := vanVleckGatedWitness`) as a genuine geometric input, noting `GatedTauDerivRep` banks only the
  deriv-EQUALITY representative CONDITIONAL on a carried amplitude `HasDerivAt hgate`.  This file shows
  that carried amplitude `HasDerivAt` is in fact **BANKED and UNCONDITIONAL**
  (`OnGateJets.chartFieldAmp_hasDerivAt_tau` — the amplitude is affine in `τ`), and the Gaussian's
  time-derivative is banked too (`heatKernel1D_hasDerivAt_t`).  Hence the CONCRETE gated van-Vleck
  witness is TIME-differentiable at every `τ > 0`, UNCONDITIONALLY (gate `by_cases`: on-gate = product
  of the Gaussian and the affine amplitude; off-gate = the constant `0`).  Because the differentiation
  neighbourhood `V` is chosen to avoid the `τ = 0` diagonal singularity (`∀ c' ∈ V, 0 < c'−s`), the
  full `z`-pointwise time `HasDerivAt` family holds for EVERY `z` (stronger than a.e.) with NO gate
  carry — so the differentiability sibling of `hAcrude` is genuinely DISCHARGED, not merely reduced.

  What still remains inside J4-912's `hZ` (honest, unchanged): the `z`-integrable dominator `Dz` and
  the `z`-slice measurabilities (the F2-pile / `gaussDdim_pair_integrable` analogues) — DATA-still.

  ⚠  STILL NOT `a₁ = R/6`.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import QIQTH.GatedTauDerivRep
import QIQTH.OnGateJets

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas QIQTH.OnGateJets
open scoped Topology BigOperators ContDiff

namespace QIQTH.WitnessTimeDeriv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the CONCRETE witness is TIME-differentiable at every `τ > 0` (unconditional).
    ############################################################################### -/

/-- **★ `witnessTime_differentiableAt` — the concrete gated van-Vleck witness is `DifferentiableAt` in
    its TIME argument at every `τ > 0`, UNCONDITIONALLY.**  Gate `by_cases`:
      • ON gate (`q ∈ K`, `p ∈ S q`) — the `τ`-independent gate lets the witness factor (for every `u`)
        as `gaussDdim u (W q p) · chartFieldAmp … u q p` (`vanVleckGatedWitness_gate_apply`); the
        Gaussian is `DifferentiableAt` at `τ > 0` (`heatKernel1D_hasDerivAt_t` product), the amplitude
        is `DifferentiableAt` UNCONDITIONALLY (`OnGateJets.chartFieldAmp_hasDerivAt_tau` — affine in
        `τ`), so the product is `DifferentiableAt`;
      • OFF gate (`q ∉ K` or `p ∉ S q`) — the witness is `≡ 0` (`gatedKernel_apply_of_notMem`), hence
        `DifferentiableAt`.
    No gate hypothesis is carried — only `0 < τ` (avoiding the on-gate `τ = 0` diagonal singularity
    where the witness is genuinely non-differentiable).  NOT `a₁ = R/6`. -/
theorem witnessTime_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (p q : Point n) (τ : ℝ) (hτ : 0 < τ) :
    DifferentiableAt ℝ (fun u : ℝ => vanVleckGatedWitness g gi hC hK S a b u p q) τ := by
  by_cases hgate : q ∈ K ∧ p ∈ S q
  · obtain ⟨hzK, hpS⟩ := hgate
    set v := uniformInverseChart g gi hC hK q p with hvdef
    have hfe : (fun u : ℝ => vanVleckGatedWitness g gi hC hK S a b u p q)
        = (fun u : ℝ => gaussDdim u v * chartFieldAmp g gi hC hK a b u q p) := by
      funext u
      rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK hpS]
      simp only [chartFieldAmp, hvdef]
      ring
    rw [hfe]
    have hgd : DifferentiableAt ℝ (fun u : ℝ => gaussDdim u v) τ := by
      have h := HasDerivAt.fun_finsetProd
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => heatKernel1D_hasDerivAt_t τ (v i) hτ)
      simpa only [gaussDdim] using h.differentiableAt
    have hampd : DifferentiableAt ℝ (fun u : ℝ => chartFieldAmp g gi hC hK a b u q p) τ :=
      (chartFieldAmp_hasDerivAt_tau g gi hC hK a b q p τ).differentiableAt
    exact hgd.mul hampd
  · rcases not_and_or.mp hgate with h | h
    · have hzero : (fun u : ℝ => vanVleckGatedWitness g gi hC hK S a b u p q) = fun _ => (0 : ℝ) := by
        funext u
        unfold vanVleckGatedWitness
        exact gatedKernel_apply_of_notMem K S _ u p q (Or.inl h)
      rw [hzero]; exact differentiableAt_const 0
    · have hzero : (fun u : ℝ => vanVleckGatedWitness g gi hC hK S a b u p q) = fun _ => (0 : ℝ) := by
        funext u
        unfold vanVleckGatedWitness
        exact gatedKernel_apply_of_notMem K S _ u p q (Or.inr h)
      rw [hzero]; exact differentiableAt_const 0

/-! ###############################################################################
    ### §B — the GENERIC bridge `DifferentiableAt ⟹ z-pointwise time HasDerivAt`.
    ############################################################################### -/

/-- **★ `zTime_hasDerivAt_of_differentiableAt` — the GENERIC `(A,F)` bridge.**  For any kernels
    `A, F`, if the base-`0` time slice `r ↦ A r 0 z` is `DifferentiableAt` at `c'−s`, then the exact
    `hpardiff` integrand
      `c' ↦ A (c'−s) 0 z · F s z 0`
    has the census-shaped derivative `deriv (fun r => A r 0 z) (c'−s) · F s z 0` at `c'`.  Route: the
    inner slice's `HasDerivAt` (from `DifferentiableAt.hasDerivAt`) composed with the affine shift
    `c' ↦ c'−s` (derivative `1`), then `.mul_const (F s z 0)`.  The `F s z 0` factor is constant in
    `c'`.  NOT `a₁ = R/6`. -/
theorem zTime_hasDerivAt_of_differentiableAt
    (A F : ℝ → Point n → Point n → ℝ) (s : ℝ) (z : Point n) (c' : ℝ)
    (hd : DifferentiableAt ℝ (fun r : ℝ => A r 0 z) (c' - s)) :
    HasDerivAt (fun c' : ℝ => A (c' - s) 0 z * F s z 0)
      (deriv (fun r : ℝ => A r 0 z) (c' - s) * F s z 0) c' := by
  have hshift : HasDerivAt (fun c' : ℝ => c' - s) 1 c' := (hasDerivAt_id c').sub_const s
  have hcomp := (hd.hasDerivAt).comp c' hshift
  simp only [Function.comp_def, mul_one] at hcomp
  exact hcomp.mul_const (F s z 0)

/-! ###############################################################################
    ### §C — the DISCHARGED `z`-pointwise TIME `HasDerivAt` family for the concrete witness.
    ############################################################################### -/

/-- **★★★ `witnessZTime_hasDerivAt` — J4-912's `hZ` DIFFERENTIABILITY conjunct, DISCHARGED.**  For the
    concrete gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S a b`, ANY frozen field `F`,
    and any differentiation neighbourhood `V` that avoids the `τ = 0` diagonal (`∀ c' ∈ V, 0 < c'−s`),
    the exact last conjunct of J4-912's inner `z`-level family holds for **EVERY** `z` (stronger than
    the `∀ᵐ z` the census asks for), with NO gate carry:
      `∀ z, ∀ c' ∈ V, HasDerivAt (c' ↦ A (c'−s) 0 z · F s z 0)`
      `                        (deriv (fun r => A r 0 z) (c'−s) · F s z 0) c'`.
    Composition of §B (`zTime_hasDerivAt_of_differentiableAt` at `A := witness`) and §A
    (`witnessTime_differentiableAt` at field point `0`, base `z`, time `c'−s > 0`).  This DISCHARGES
    the differentiability sibling of `hAcrude` that J4-912 carried; the remaining `hZ` residue (the
    `z`-integrable dominator `Dz` + `z`-slice measurabilities) is unchanged.  NOT `a₁ = R/6`. -/
theorem witnessZTime_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (s : ℝ) (V : Set ℝ) (hV : ∀ c' ∈ V, 0 < c' - s) :
    ∀ (z : Point n), ∀ c' ∈ V,
      HasDerivAt
        (fun c' : ℝ => vanVleckGatedWitness g gi hC hK S a b (c' - s) 0 z * F s z 0)
        (deriv (fun r : ℝ => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c' - s) * F s z 0) c' := by
  intro z c' hc'
  exact zTime_hasDerivAt_of_differentiableAt (vanVleckGatedWitness g gi hC hK S a b) F s z c'
    (witnessTime_differentiableAt g gi hC hK S a b 0 z (c' - s) (hV c' hc'))

/-- **Non-vacuity witness.**  The `witnessZTime_hasDerivAt` hypothesis `hV` is satisfiable non-trivially
    at `V := Set.Ioi s` (every `c' > s` has `0 < c'−s`), so the discharge fires on a genuine open
    differentiation window, not an empty one.  NOT `a₁ = R/6`. -/
theorem witnessZTime_hasDerivAt_window_nonempty (s : ℝ) :
    (∀ c' ∈ Set.Ioi s, 0 < c' - s) ∧ (s + 1) ∈ Set.Ioi s := by
  refine ⟨fun c' hc' => by simpa using sub_pos.mpr (Set.mem_Ioi.mp hc'), ?_⟩
  simp

end QIQTH.WitnessTimeDeriv

section AxiomChecks
open QIQTH.WitnessTimeDeriv
#print axioms witnessTime_differentiableAt
#print axioms zTime_hasDerivAt_of_differentiableAt
#print axioms witnessZTime_hasDerivAt
#print axioms witnessZTime_hasDerivAt_window_nonempty
end AxiomChecks
