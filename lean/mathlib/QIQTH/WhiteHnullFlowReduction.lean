/-
  WhiteHnullFlowReduction — J4-719: THE LAST ANALYTIC RESIDUAL (`hnull`) OF THE WHITENED
  `hInnerCont` CAMPAIGN, REDUCED to a geometrically-transparent, dimension-correct
  Lipschitz-solvability certificate — plus the FULLY PROVEN measure-theoretic core.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` stays a
  labelled carrier, untouched).  It addresses the SOLE surviving analytic residual of
  `WhiteHBaseGateCollarDischarge.white_hInnerCont_closed_final6`, namely the flow-gate null-frontier
  certificate
        `hnull : ∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0`.
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE STRUCTURE (the geometric content of `hnull` at the flow gate `S w = flowExpₓ_w '' ball 0 c`).
    The gate frontier is carried by the image of the *sphere*: `frontier (S w) ⊆ flowExp_w '' sphere 0 c`
    (frontier of an open homeomorphic image; base-`w` injectivity on the closed ball).  For FIXED `z₀`,
    the bad base set `{w | z₀ ∈ frontier (S w)}` is therefore contained in `{w | ∃ v ∈ sphere 0 c,
    flowExp_w v = z₀}`.  Solving `flowExp_w v = z₀` for the base `w` as a function of the direction
    `v` (a near-translation `w ≈ z₀ − v`, Lipschitz on the sphere) exhibits the bad set as a
    **Lipschitz image of the codimension-1 sphere**, hence Lebesgue-null in dimension `n ≥ 1`.

  ── WHAT IS FULLY PROVEN HERE (the measure-theoretic core — NO residual, std-3 axioms).
    * `dimH_hyperplane` — a coordinate hyperplane `{x | x j = a}` in `Point n = Fin n → ℝ` has
      `dimH ≤ n − 1` (convex set, `vectorSpan ⊆ ker (proj j) ≠ ⊤`, `Submodule.finrank_lt`).
    * `sphere_subset_hyperplanes` — the sup-norm sphere is covered by the `2n` coordinate hyperplanes
      `{x | x j = ±c}` (the sup norm is attained at some coordinate).
    * `dimH_sphere_lt` — hence `dimH (sphere 0 c) < n`.
    * `lipschitzOn_sphere_image_null` — ★ a `LipschitzOnWith` image of `sphere 0 c` is Lebesgue-null
      (`LipschitzOnWith.dimH_image_le` + `measure_zero_of_dimH_lt`, using `μH[n] = volume` on `ℝⁿ`).
    * `hnull_of_lipschitzSolver` — ★★ THE REDUCTION: from a per-`z₀` Lipschitz solver landing the bad
      base set inside `H_{z₀} '' sphere 0 c`, the raw null-frontier certificate `hnull` FOLLOWS.
    * `white_hInnerCont_closed_final7` — ★★★ `final6` with the raw `hnull` residual REPLACED by the
      transparent Lipschitz-solvability certificate `hsolveFlow`.

  ── HONEST VERDICT ON WHAT REMAINS.  The base-point (`w`) invertibility/Lipschitz-regularity of
    `w ↦ flowExp_w v` (the "solver") is NOT re-derived here from the banked base-`0` displacement data;
    it is carried as the explicit named input `hsolveFlow`.  This is the honest geometric residue: the
    campaign's banked displacement/reach machinery is stated at base `0`, whereas the solver needs the
    base-varying chart.  The measure-theoretic heart (codim-1 ⇒ null) is fully discharged.

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHBaseGateCollarDischarge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open QIQTH.WhiteHBaseGateCollarDischarge
open scoped Topology ENNReal NNReal

namespace QIQTH.WhiteHnullFlowReduction

variable {n : ℕ}

/-! ### §A — the measure-theoretic core: a Lipschitz image of the codim-1 sphere is null. -/

/-- A coordinate hyperplane `{x | x j = a}` in `Point n = Fin n → ℝ` has Hausdorff dimension
`≤ n − 1`: it is convex, and its `vectorSpan` is contained in the proper submodule `ker (proj j)`. -/
theorem dimH_hyperplane (j : Fin n) (a : ℝ) :
    dimH ({x : Point n | x j = a}) ≤ ((n - 1 : ℕ) : ℝ≥0∞) := by
  set s : Set (Point n) := {x : Point n | x j = a} with hs
  have hne : s.Nonempty := ⟨Pi.single j a, by simp [hs]⟩
  have hcvx : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq
    simp only [hs, Set.mem_setOf_eq] at hx hy ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx, hy]
    linear_combination a * hpq
  have hle : vectorSpan ℝ s ≤ LinearMap.ker (LinearMap.proj j : (Point n) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    simp only [hs, Set.mem_setOf_eq] at hx hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply,
      vsub_eq_sub, Pi.sub_apply, hx, hy, sub_self]
  have hkerne : (LinearMap.ker (LinearMap.proj j : (Point n) →ₗ[ℝ] ℝ)) ≠ ⊤ := by
    intro h
    have hmem : (Pi.single j (1 : ℝ)) ∈ LinearMap.ker (LinearMap.proj j : (Point n) →ₗ[ℝ] ℝ) := by
      rw [h]; trivial
    simp [LinearMap.mem_ker] at hmem
  have hvne : vectorSpan ℝ s ≠ ⊤ := fun h => hkerne (top_le_iff.mp (h ▸ hle))
  have hlt : Module.finrank ℝ (vectorSpan ℝ s) < Module.finrank ℝ (Point n) :=
    Submodule.finrank_lt hvne
  have hdim : Module.finrank ℝ (Point n) = n := by simp [Point]
  rw [Real.Convex.dimH_eq_finrank_vectorSpan hcvx hne]
  have hle' : Module.finrank ℝ (vectorSpan ℝ s) ≤ n - 1 := by omega
  exact_mod_cast hle'

/-- The sup-norm sphere in `Point n` (`n ≥ 1`) is contained in the union of the `2n` coordinate
hyperplanes `{x | x j = ±c}` — the sup norm is attained at some coordinate. -/
theorem sphere_subset_hyperplanes (hn : 0 < n) (c : ℝ) :
    Metric.sphere (0 : Point n) c ⊆
      ⋃ j : Fin n, ({x : Point n | x j = c} ∪ {x : Point n | x j = -c}) := by
  intro x hx
  rw [Metric.mem_sphere, dist_zero_right] at hx
  have hc0 : 0 ≤ c := hx ▸ norm_nonneg x
  have hfin : (Finset.univ : Finset (Fin n)).Nonempty := by
    rw [Finset.univ_nonempty_iff]; exact ⟨⟨0, hn⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n)) hfin
    (fun i => ‖x i‖₊)
  have hnorm : ‖x‖₊ = ‖x j‖₊ := by rw [Pi.nnnorm_def]; exact hj
  have hxj : ‖x j‖ = c := by
    have h := congrArg NNReal.toReal hnorm
    simp only [coe_nnnorm] at h
    rw [← h]; exact hx
  have hcase : x j = c ∨ x j = -c := by
    rcases (abs_eq hc0).mp (by rw [← Real.norm_eq_abs]; exact hxj) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rw [Set.mem_iUnion]
  exact ⟨j, hcase.elim (fun h => Or.inl h) (fun h => Or.inr h)⟩

/-- The sup-norm sphere in `Point n` (`n ≥ 1`) is codimension-1: `dimH (sphere 0 c) < n`. -/
theorem dimH_sphere_lt (hn : 0 < n) (c : ℝ) :
    dimH (Metric.sphere (0 : Point n) c) < (n : ℝ≥0∞) := by
  have hsub := sphere_subset_hyperplanes (n := n) hn c
  calc dimH (Metric.sphere (0 : Point n) c)
      ≤ dimH (⋃ j : Fin n, ({x : Point n | x j = c} ∪ {x : Point n | x j = -c})) :=
        dimH_mono hsub
    _ ≤ ((n - 1 : ℕ) : ℝ≥0∞) := by
        rw [dimH_iUnion]
        refine iSup_le fun j => ?_
        rw [dimH_union]
        exact max_le (dimH_hyperplane j c) (dimH_hyperplane j (-c))
    _ < (n : ℝ≥0∞) := by
        have hlt : (n - 1 : ℕ) < n := by omega
        exact_mod_cast hlt

/-- **★ Null-image lemma.**  A `LipschitzOnWith` image of the sup-norm sphere in `Point n` (`n ≥ 1`)
is Lebesgue-null: `sphere 0 c` is codimension-1 (`dimH < n`), Lipschitz maps do not increase
Hausdorff dimension, so the image has `dimH < n = finrank`, hence Lebesgue measure `0`
(`μH[n] = volume` on `ℝⁿ`). -/
theorem lipschitzOn_sphere_image_null (hn : 0 < n) {H : Point n → Point n} {c : ℝ} {K : ℝ≥0}
    (hH : LipschitzOnWith K H (Metric.sphere 0 c)) :
    volume (H '' Metric.sphere (0 : Point n) c) = 0 := by
  have hvol : (μH[(n : ℝ)] : Measure (Point n)) = volume := by
    have h := hausdorffMeasure_pi_real (ι := Fin n)
    simpa using h
  have hac : (volume : Measure (Point n)) ≪ μH[((n : ℝ≥0) : ℝ)] := by
    rw [show ((n : ℝ≥0) : ℝ) = (n : ℝ) by push_cast; ring, hvol]
  have hd : dimH (H '' Metric.sphere (0 : Point n) c) < ((n : ℝ≥0) : ℝ≥0∞) := by
    rw [show ((n : ℝ≥0) : ℝ≥0∞) = (n : ℝ≥0∞) by simp]
    exact lt_of_le_of_lt hH.dimH_image_le (dimH_sphere_lt hn c)
  exact measure_zero_of_dimH_lt hac hd

/-! ### §B — the reduction: `hnull` from a per-`z₀` Lipschitz solver. -/

/-- **★★ THE REDUCTION.**  For ANY gate family `S`, if for every observation point `z₀` the bad base
set `{w | z₀ ∈ frontier (S w)}` is contained in a `LipschitzOnWith` image of the sphere `sphere 0 c`
(the "solver": `w ≈ z₀ − v`, Lipschitz in the direction `v ∈ sphere 0 c`), then the raw null-frontier
certificate `hnull` holds — the bad set is a Lipschitz image of a codimension-1 null set. -/
theorem hnull_of_lipschitzSolver (hn : 0 < n) {S : Point n → Set (Point n)} {c : ℝ}
    (hsolve : ∀ z₀ : Point n, ∃ (H : Point n → Point n) (K : ℝ≥0),
        LipschitzOnWith K H (Metric.sphere 0 c) ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆ H '' Metric.sphere (0 : Point n) c) :
    ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0 := by
  intro z₀
  obtain ⟨H, K, hLip, hsub⟩ := hsolve z₀
  exact measure_mono_null hsub (lipschitzOn_sphere_image_null hn hLip)

/-! ### §C — the terminal feed: `final6` with `hnull` replaced by the Lipschitz solver. -/

/-- **★★★ `white_hInnerCont_closed_final7` (THE TERMINAL FEED, `hnull` DISSOLVED).**  Identical
conclusion and hypotheses to `WhiteHBaseGateCollarDischarge.white_hInnerCont_closed_final6`, except
the raw analytic residual
    `hnull : ∀ z₀, volume {w | z₀ ∈ frontier (S w)} = 0`
is REPLACED by the geometrically-transparent Lipschitz-solvability certificate `hsolveFlow`: for each
`z₀`, the bad base set is contained in a `LipschitzOnWith` image of the codimension-1 sphere
`sphere 0 c`.  `hnull` is then discharged internally by `hnull_of_lipschitzSolver` (the measure core
`lipschitzOn_sphere_image_null` is fully proven).  ⚠ NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final7 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (whiteLam κ hκ hKc) 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hWmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S a b w.1 w.2.1 w.2.2))
    (wA Cpre A₀ A₁ : ℝ) (hwA0 : 0 < wA) (hCpre0 : 0 ≤ Cpre) (hA₀0 : 0 ≤ A₀) (hA₁0 : 0 ≤ A₁)
    (hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S a b τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (c δ₀ : ℝ) (hcδ : c < δ₀)
    -- B'. the LIPSCHITZ-SOLVER certificate (replaces the raw `hnull`)
    (hsolveFlow : ∀ z₀ : Point n, ∃ (H : Point n → Point n) (K : ℝ≥0),
        LipschitzOnWith K H (Metric.sphere 0 c) ∧
        {w : Point n | z₀ ∈ frontier (S w)} ⊆ H '' Metric.sphere (0 : Point n) c)
    (hSopen : ∀ w : Point n, w ∈ Kset → IsOpen (S w))
    (hSreach : ∀ w : Point n, w ∈ Kset →
        S w ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w ''
          Metric.ball (0 : Point n) c)
    (hspec : ∀ w : Point n, w ∈ Kset →
        (∀ v : Point n, ‖v‖ < δ₀ →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)))
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (C_D : ℝ) (hCD0 : 0 ≤ C_D)
    (hdisp0 : ∀ v : Point n, ‖v‖ ≤ c →
        ‖uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v - v‖
          ≤ C_D * ‖v‖ * ‖v‖)
    (hclosclause : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0 '' Metric.ball 0 c)
      ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.closedBall 0 c)
    (hbR : b * (1 + C_D * c) < R)
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) :=
  white_hInnerCont_closed_final6 hn κ hκ hKc S a b ha hab C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval (hnull_of_lipschitzSolver hn hsolveFlow) Wg hagree
    c δ₀ hcδ hSopen hSreach hspec R h0K hballS hballC C_D hCD0 hdisp0 hclosclause hbR Uwin hU1

end QIQTH.WhiteHnullFlowReduction

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHnullFlowReduction
#check @dimH_hyperplane
#check @dimH_sphere_lt
#check @lipschitzOn_sphere_image_null
#check @hnull_of_lipschitzSolver
#check @white_hInnerCont_closed_final7
#print axioms dimH_hyperplane
#print axioms dimH_sphere_lt
#print axioms lipschitzOn_sphere_image_null
#print axioms hnull_of_lipschitzSolver
#print axioms white_hInnerCont_closed_final7
end AxiomChecks
