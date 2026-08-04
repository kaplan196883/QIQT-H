/-
  InnerKernelJointMeas — J4-178: the inner-kernel joint `(s,z)`-measurability `hinnerJ`, the LAST
  minimized carry left open by J4-177 (`QIQTH.JointMeasurability.hjoint_concrete`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It discharges the
  single remaining `hinnerJ` slot of J4-177's `hjoint_concrete` — the JOINT `(s,z)`-ae-measurability
  of the ungated order-`1` global-cutoff parametrix witness

      (s, z) ↦ globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff …) a b
                 (uniformInverseChart g gi hC hK) (t − s) (Function.update x i w) z
             = radialCutoff a b (V z p) · heatParametrix 1 Θ u (t − s) (V z p)

  (`V := uniformInverseChart`, `p := Function.update x i w` a fixed field point; the `z`-dependence
  enters ONLY through the chart `w = V z p`, the `s`-dependence ONLY through `τ = t − s`) — reducing
  it to strictly lighter, satisfiable, non-vacuous carries: the coefficient measurability
  (`Θ`-continuity + non-vanishing, `u`-continuity — a fortiori from the geometric hypotheses via
  `transportCoeff_continuous_of_preserve`) and the honest `ν`-level chart measurability carry
  `hVmapMeas` (the `ν` analogue of the `volume.restrict K` chart carries of J4-167/168).  Never the
  fibrewise-integrated conclusion.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    VANISHING (τ ≤ 0).
      • `heatKernel1D_eq_zero_of_nonpos` — `G_τ(x) = 0` for `τ ≤ 0` (`√` of a nonpositive is `0`,
          `(0:ℝ)⁻¹ = 0`).
      • `gaussDdim_eq_zero_of_nonpos` — `gaussDdim τ x = 0` for `τ ≤ 0`, `0 < n` (an empty product
          over `Fin 0` is `1`, so `0 < n` is honestly required — the `a₁` story is `n`-dimensional).
      • `heatParametrix_eq_zero_of_nonpos` — `H_N(τ,·) = 0` for `τ ≤ 0`, `0 < n` (the `gaussDdim`
          factor kills the whole product).

    JOINT CONTINUITY on `{τ > 0}` (the genuine analytic content behind measurability).
      • `heatKernel1D_continuousOn_pos` / `gaussDdim_continuousOn_pos` — joint `(τ,x)` continuity of
          the 1-D and `d`-D heat kernels on `{0 < τ}` (across `τ = 0` the kernel blows up, so `{τ>0}`
          is the honest domain).
      • `witnessInner_jointContinuousOn_pos` — joint `(τ,w)` continuity of
          `radialCutoff a b w · heatParametrix 1 Θ u τ w` on `{0 < τ}` from `Θ`-continuity /
          non-vanishing and `u`-continuity.

    GLOBAL MEASURABILITY (the direct Borel route — every building block is measurable).
      • `heatKernel1D_uncurry_measurable` / `gaussDdim_uncurry_measurable` — the uncurried heat
          kernels are Borel-measurable on ALL of `ℝ × ·` (sqrt / inv / exp / div are measurable even
          across `τ = 0`, no continuity needed).
      • `witnessInner_measurable_uncurry` — ★ `Measurable (fun q => radialCutoff a b q.2 ·
          heatParametrix 1 Θ u q.1 q.2)` from coefficient measurability, the outer function the
          chart composition feeds.

    THE DISCHARGE.
      • `aemeasurable_chart_snd` — the `ν`-level chart carry lifted to the product via
          `map_snd_prod`.
      • `hinnerJ_discharged` — ★★ the EXACT `hinnerJ` shape of J4-177's `hjoint_concrete`, via
          `Measurable.comp_aemeasurable` of the outer measurable kernel with the product-measurable
          map `(s,z) ↦ (t−s, V z p)`.  NOT `a₁ = R/6`.
      • `hjoint_final` — ★★ threads `hinnerJ_discharged` into `hjoint_concrete`, closing the last
          open `hinnerJ` slot of the `hjoint` capstone.  NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hΘc` / `hΘne` / `huc` — continuity / non-vanishing of the van-Vleck determinant and the
      transport coefficients (a fortiori from the geometric hypotheses; the `Θ^{−1/2}` factor is
      genuinely only well-behaved for `Θ ≠ 0`).
    • `hVmapMeas` — the honest `ν`-level `(z ↦ V z p)` ae-measurability, the `ν` analogue of the
      `volume.restrict K` chart carries of J4-167/168.
    • the remaining `hjoint_concrete` carries (`hKmeasSet` / `hSmeasSet` / `hFjoint` / `hWdiffJ`) —
      unchanged from J4-177.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.JointMeasurability

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixAnsatz QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.InnerKernelJointMeas

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### VANISHING (τ ≤ 0).
    ############################################################################### -/

/-- **`heatKernel1D_eq_zero_of_nonpos`.**  `G_τ(x) = 0` for `τ ≤ 0`: `√(4πτ)` of a nonpositive
    argument is `0`, and `(0:ℝ)⁻¹ = 0`.  NOT `a₁ = R/6`. -/
theorem heatKernel1D_eq_zero_of_nonpos (τ x : ℝ) (hτ : τ ≤ 0) :
    heatKernel1D τ x = 0 := by
  unfold heatKernel1D
  have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have h4 : 4 * Real.pi * τ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpi hτ
  rw [Real.sqrt_eq_zero_of_nonpos h4, inv_zero, zero_mul]

/-- **`gaussDdim_eq_zero_of_nonpos`.**  `gaussDdim τ x = 0` for `τ ≤ 0`, `0 < n`: every factor of
    the product `∏ₖ G_τ(xₖ)` vanishes, and (`0 < n`) the index set is nonempty.  The empty product
    over `Fin 0` is `1`, so `0 < n` is honestly required — the `a₁` heat-kernel story is about
    `n`-dimensional manifolds, `n ≥ 1`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_eq_zero_of_nonpos (hn : 0 < n) (τ : ℝ) (x : Point n) (hτ : τ ≤ 0) :
    gaussDdim τ x = 0 := by
  unfold gaussDdim
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    (heatKernel1D_eq_zero_of_nonpos τ (x ⟨0, hn⟩) hτ)

/-- **`heatParametrix_eq_zero_of_nonpos`.**  `H_N(τ,x) = 0` for `τ ≤ 0`, `0 < n`: the leading
    `gaussDdim τ x` factor vanishes, killing the whole product.  NOT `a₁ = R/6`. -/
theorem heatParametrix_eq_zero_of_nonpos (hn : 0 < n) (N : ℕ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (τ : ℝ) (x : Point n) (hτ : τ ≤ 0) :
    heatParametrix N Θ u τ x = 0 := by
  unfold heatParametrix
  rw [gaussDdim_eq_zero_of_nonpos hn τ x hτ, zero_mul, zero_mul]

/-! ###############################################################################
    ### JOINT CONTINUITY on `{τ > 0}`.
    ############################################################################### -/

/-- **`heatKernel1D_continuousOn_pos`.**  Joint `(τ,x)` continuity of the 1-D heat kernel on
    `{0 < τ}`: `√(4πτ)` is continuous and `> 0` there (so its inverse is continuous), and the
    Gaussian exponent `−x²/(4τ)` is continuous where `4τ ≠ 0`.  Across `τ = 0` the kernel blows up
    (`G_τ(0) = (√(4πτ))⁻¹ → ∞`), so `{τ>0}` is the honest continuity domain.  NOT `a₁ = R/6`. -/
theorem heatKernel1D_continuousOn_pos :
    ContinuousOn (fun q : ℝ × ℝ => heatKernel1D q.1 q.2) {q : ℝ × ℝ | 0 < q.1} := by
  simp only [heatKernel1D]
  apply ContinuousOn.mul
  · apply ContinuousOn.inv₀
    · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
    · intro q hq
      have hq' : (0 : ℝ) < q.1 := hq
      have : (0 : ℝ) < 4 * Real.pi * q.1 := mul_pos (by positivity) hq'
      exact ne_of_gt (Real.sqrt_pos.mpr this)
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro q hq
      have hq' : (0 : ℝ) < q.1 := hq
      exact (mul_pos (by norm_num : (0 : ℝ) < 4) hq').ne'

/-- **`gaussDdim_continuousOn_pos`.**  Joint `(τ,x)` continuity of the `d`-D heat kernel on
    `{0 < τ}`: a finite product of the per-coordinate 1-D kernels, each continuous on `{0<τ}` by
    `heatKernel1D_continuousOn_pos` composed with the (first-coordinate-preserving) projection.
    NOT `a₁ = R/6`. -/
theorem gaussDdim_continuousOn_pos :
    ContinuousOn (fun q : ℝ × Point n => gaussDdim q.1 q.2) {q : ℝ × Point n | 0 < q.1} := by
  simp only [gaussDdim]
  apply continuousOn_finsetProd
  intro k _
  exact heatKernel1D_continuousOn_pos.comp
    (by fun_prop : ContinuousOn (fun q : ℝ × Point n => (q.1, q.2 k)) {q : ℝ × Point n | 0 < q.1})
    (fun q hq => hq)

/-- **`witnessInner_jointContinuousOn_pos`.**  Joint `(τ,w)` continuity of the inner kernel
    `radialCutoff a b w · heatParametrix 1 Θ u τ w` on `{0 < τ}`, from `Θ`-continuity /
    non-vanishing (the `Θ^{−1/2}` factor is continuous for `Θ ≠ 0`) and `u`-continuity.  The
    `radialCutoff` and DeWitt-polynomial factors are continuous everywhere.  NOT `a₁ = R/6`. -/
theorem witnessInner_jointContinuousOn_pos (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k)) :
    ContinuousOn
      (fun q : ℝ × Point n => radialCutoff a b q.2 * heatParametrix 1 Θ u q.1 q.2)
      {q : ℝ × Point n | 0 < q.1} := by
  have hrad : ContinuousOn (fun q : ℝ × Point n => radialCutoff a b q.2)
      {q : ℝ × Point n | 0 < q.1} :=
    (((radialCutoff_contDiff a b).continuous).comp continuous_snd).continuousOn
  have hΘpow : ContinuousOn (fun q : ℝ × Point n => (Θ q.2) ^ (-(1 : ℝ) / 2))
      {q : ℝ × Point n | 0 < q.1} :=
    ((hΘc.comp continuous_snd).rpow_const (fun q => Or.inl (hΘne q.2))).continuousOn
  have hsum : ContinuousOn
      (fun q : ℝ × Point n => ∑ k ∈ Finset.range (1 + 1), u k q.2 * q.1 ^ k)
      {q : ℝ × Point n | 0 < q.1} := by
    apply continuousOn_finsetSum
    intro k _
    exact (((huc k).comp continuous_snd).mul ((continuous_fst).pow k)).continuousOn
  have hHP : ContinuousOn (fun q : ℝ × Point n => heatParametrix 1 Θ u q.1 q.2)
      {q : ℝ × Point n | 0 < q.1} := by
    have hrw : (fun q : ℝ × Point n => heatParametrix 1 Θ u q.1 q.2)
        = fun q => gaussDdim q.1 q.2 * (Θ q.2) ^ (-(1 : ℝ) / 2)
            * ∑ k ∈ Finset.range (1 + 1), u k q.2 * q.1 ^ k := rfl
    rw [hrw]
    exact (gaussDdim_continuousOn_pos.mul hΘpow).mul hsum
  exact hrad.mul hHP

/-! ###############################################################################
    ### GLOBAL MEASURABILITY (the direct Borel route).
    ############################################################################### -/

/-- **`heatKernel1D_uncurry_measurable`.**  The uncurried 1-D heat kernel is Borel-measurable on
    ALL of `ℝ × ℝ` — no continuity or positivity needed: `√`, `⁻¹`, `exp`, `/` are measurable even
    across `τ = 0` (division by `0` is the measurable junk `0`).  NOT `a₁ = R/6`. -/
theorem heatKernel1D_uncurry_measurable :
    Measurable (fun q : ℝ × ℝ => heatKernel1D q.1 q.2) := by
  simp only [heatKernel1D]
  fun_prop

/-- **`gaussDdim_uncurry_measurable`.**  The uncurried `d`-D heat kernel is Borel-measurable on
    `ℝ × Point n`: a finite product of the per-coordinate 1-D kernels.  NOT `a₁ = R/6`. -/
theorem gaussDdim_uncurry_measurable :
    Measurable (fun q : ℝ × Point n => gaussDdim q.1 q.2) := by
  simp only [gaussDdim]
  refine Finset.measurable_prod Finset.univ (fun k _ => ?_)
  exact heatKernel1D_uncurry_measurable.comp
    (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))

/-- **★ `witnessInner_measurable_uncurry`.**  `Measurable (fun q => radialCutoff a b q.2 ·
    heatParametrix 1 Θ u q.1 q.2)` from coefficient measurability (`Θ` continuous / non-vanishing,
    `u` continuous).  This is the OUTER function the chart composition feeds in the discharge —
    genuinely globally Borel-measurable (not merely `AEStronglyMeasurable`), so
    `Measurable.comp_aemeasurable` applies.  NOT `a₁ = R/6`. -/
theorem witnessInner_measurable_uncurry (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k)) :
    Measurable (fun q : ℝ × Point n => radialCutoff a b q.2 * heatParametrix 1 Θ u q.1 q.2) := by
  have hrad : Measurable (fun q : ℝ × Point n => radialCutoff a b q.2) :=
    (((radialCutoff_contDiff a b).continuous).comp continuous_snd).measurable
  have hΘpow : Measurable (fun q : ℝ × Point n => (Θ q.2) ^ (-(1 : ℝ) / 2)) :=
    ((hΘc.comp continuous_snd).rpow_const (fun q => Or.inl (hΘne q.2))).measurable
  have hsum : Measurable
      (fun q : ℝ × Point n => ∑ k ∈ Finset.range (1 + 1), u k q.2 * q.1 ^ k) := by
    refine Finset.measurable_sum (Finset.range (1 + 1)) (fun k _ => ?_)
    exact (((huc k).measurable).comp measurable_snd).mul (measurable_fst.pow_const k)
  have hHP : Measurable (fun q : ℝ × Point n => heatParametrix 1 Θ u q.1 q.2) := by
    have hrw : (fun q : ℝ × Point n => heatParametrix 1 Θ u q.1 q.2)
        = fun q => gaussDdim q.1 q.2 * (Θ q.2) ^ (-(1 : ℝ) / 2)
            * ∑ k ∈ Finset.range (1 + 1), u k q.2 * q.1 ^ k := rfl
    rw [hrw]
    exact (gaussDdim_uncurry_measurable.mul hΘpow).mul hsum
  exact hrad.mul hHP

/-! ###############################################################################
    ### THE DISCHARGE — `hinnerJ` and `hjoint_final`.
    ############################################################################### -/

/-- **`aemeasurable_chart_snd`.**  The `ν`-level chart ae-measurability `(z ↦ V z p)` lifted to
    the product `μ.prod ν` via `Measure.map_snd_prod` (`(μ.prod ν).map Prod.snd = (μ univ) • ν`) and
    `AEMeasurable.comp_measurable`.  The honest carry-unification of the `ν` chart slice into the
    joint `(s,z)`-domain.  NOT `a₁ = R/6`. -/
theorem aemeasurable_chart_snd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ν : Measure (Point n)) [SFinite μ] [SFinite ν]
    (V : Point n → Point n → Point n) (p : Point n)
    (hV : AEMeasurable (fun z => V z p) ν) :
    AEMeasurable (fun q : α × Point n => V q.2 p) (μ.prod ν) := by
  have hmap : AEMeasurable (fun z => V z p) ((μ.prod ν).map Prod.snd) := by
    rw [Measure.map_snd_prod]
    exact hV.smul_measure _
  exact hmap.comp_measurable measurable_snd

/-- **★★ `hinnerJ_discharged`.**  THE EXACT `hinnerJ` SHAPE of J4-177's `hjoint_concrete`: the joint
    `(s,z)`-ae-measurability of the ungated order-`1` global-cutoff parametrix witness, per field
    point `Function.update x i w`.  Route: the outer kernel `(τ,w) ↦ radialCutoff a b w ·
    heatParametrix 1 Θ u τ w` is globally Borel-measurable (`witnessInner_measurable_uncurry`), and
    `(s,z) ↦ (t−s, V z p)` is product-ae-measurable (`s`-affine measurable ×
    `aemeasurable_chart_snd`), so `Measurable.comp_aemeasurable` closes it — the witness is
    definitionally that composition.  Reduces `hinnerJ` to `{hΘc, hΘne, huc, hVmapMeas}`.
    NOT `a₁ = R/6`. -/
theorem hinnerJ_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t : ℝ)
    (ν : Measure (Point n)) [SFinite ν] (u₀ : Set (Point n))
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmapMeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEMeasurable (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update x i w)) ν) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK) (t - p.1) (Function.update x i w) p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) := by
  intro x₀ hx₀ i
  filter_upwards [hVmapMeas x₀ hx₀ i] with x hV w
  have houter := witnessInner_measurable_uncurry (n := n)
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b hΘc hΘne huc
  have hchart : AEMeasurable
      (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 (Function.update x i w))
      ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
    aemeasurable_chart_snd (volume.restrict (Set.uIoc 0 t)) ν
      (uniformInverseChart g gi hC hK) (Function.update x i w) (hV w)
  have hpair : AEMeasurable
      (fun p : ℝ × Point n =>
        (t - p.1, uniformInverseChart g gi hC hK p.2 (Function.update x i w)))
      ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
    ((measurable_const.sub measurable_fst).aemeasurable).prodMk hchart
  have hcomp := houter.comp_aemeasurable hpair
  exact hcomp.aestronglyMeasurable

/-- **★★ `hjoint_final`.**  Threads `hinnerJ_discharged` into J4-177's `hjoint_concrete`, closing
    the LAST open `hinnerJ` slot: the concrete `hjoint` of `g2_bundle_assembled` for
    `dH := witnessFieldDeriv`, now carrying only `{hΘc, hΘne, huc, hVmapMeas}` (for the inner
    kernel) plus the unchanged `hKmeasSet / hSmeasSet / hFjoint / hWdiffJ`.  NOT `a₁ = R/6`. -/
theorem hjoint_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) [SFinite ν] (u₀ : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hFjoint : AEStronglyMeasurable (fun p : ℝ × Point n => F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν))
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmapMeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEMeasurable (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update x i w)) ν)
    (hWdiffJ : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
            (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
  QIQTH.JointMeasurability.hjoint_concrete g gi hC hK S a b t F ν u₀
    hKmeasSet hSmeasSet hFjoint
    (hinnerJ_discharged g gi hC hK a b t ν u₀ hΘc hΘne huc hVmapMeas)
    hWdiffJ

end QIQTH.InnerKernelJointMeas

section AxiomChecks
open QIQTH.InnerKernelJointMeas
#print axioms heatKernel1D_eq_zero_of_nonpos
#print axioms gaussDdim_eq_zero_of_nonpos
#print axioms heatParametrix_eq_zero_of_nonpos
#print axioms heatKernel1D_continuousOn_pos
#print axioms gaussDdim_continuousOn_pos
#print axioms witnessInner_jointContinuousOn_pos
#print axioms heatKernel1D_uncurry_measurable
#print axioms gaussDdim_uncurry_measurable
#print axioms witnessInner_measurable_uncurry
#print axioms aemeasurable_chart_snd
#print axioms hinnerJ_discharged
#print axioms hjoint_final
end AxiomChecks
