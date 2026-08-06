/-
  SdomHnearDischarge — J4-297: the last two Levi-continuity carries — `hSdom` (the `p`-uniform
  integrable spatial dominator) and `hnear` (the per-`w∈K` origin-ball near-cover).

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `GapASdomInstantiation`
  (J4-296) gave the concrete Levi `0`-slice joint continuity
  `leviSlice_jointContinuousOn_concrete_final` carrying, beyond the banked
  `hEbound`/`hInt`/`hEmeas`/`hbase` + the summable termwise envelope, exactly TWO remaining
  analytic carries:
    • `hSdom` — for each rung `m ≥ 1`, a `p`-uniform (over the positive-time compact) integrable
      spatial dominator of the convolution integrand `‖E (s−s·u) z w · iterE E m (s·u) w 0‖`;
    • `hnear` — for each base `w ∈ K`, the un-reparametrized origin-ball slice continuity of
      `E(·,·,w)`.
  This file DISCHARGES `hSdom` OUTRIGHT for the concrete gated van-Vleck witness (the S1 deliverable),
  packages the honest minimal carry for `hnear` (the H1 deliverable), and composes them into the
  fully S-dom-discharged Levi `0`-slice continuity (the C1 capstone).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * (S1) `hSdom_concrete` — ★★★ THE S-DOM DISCHARGE.  For the concrete gated van-Vleck witness heat
      operator `E := heatOp g gi (vanVleckGatedWitness …)`, produces the EXACT `hSdom` slot of
      `iterE_jointContinuousOn_concrete_final` / `leviSlice_jointContinuousOn_concrete_final`, from ONLY
      the banked `hEbound` + `hInt` (and `0 < κ`, `0 ≤ C`, `K` compact).  The dominator is
        `bnd u w = M(u) · 𝟙_K(w)`,   `M(u) = (C·G_{κ·t₁·(1−u)}(0))·(C^m·Γ(m)⁻¹·(t₂·u)^{m−1}·G_{κ·t₁·u}(0))`,
      an EXPLICIT `(s,z,w)`-free constant on the compact `w`-set `K`.  The two ingredients:
        · the FIRST factor `E (s−s·u) z w` VANISHES for base `w ∉ K` (`heatOpWitness_baseNotMem_eq_zero`,
          the hard `K`-gate) — so the product vanishes off the COMPACT `K`, localizing the dominator to
          a finite-measure set (⟹ `bnd u` integrable);
        · on `K`, the pointwise majorants `|E (s−s·u) z w| ≤ C·baseKernelW κ 0 (s−s·u) z w` (`hEbound`)
          and `|iterE E m (s·u) w 0| ≤ C^m·iterKernelW κ 0 m (s·u) w 0` (`iterConvW_bound` from `hInt`),
          peaked by `gaussDdim_le_diagonal` (kills `z` and `w`) and majorized by the width-antitone
          diagonal `gaussDdim_zero_antitone` + `(s·u)^{m−1} ≤ (t₂·u)^{m−1}` (kills `s`), give the
          `(s,z,w)`-uniform constant `M(u)`.
      The a.e.-`u` allowance only drops the null endpoint `u = 1` (where `s − s·u = 0` leaves positive
      time).  Genuine and satisfiable; NOT the conclusion.

    * (H1) `hnear_concrete` — the `hnear` slot produced from the honest per-`w∈K` GEOMETRIC bundle
      `Hgeo` (an open origin-ball-covering set `U`, the chart continuity `hWwcont` on `U`, an open
      active set `A` with `hEA`, the collar `hoff`).  This is exactly what
      `GapACoverGapB.heatOpWitness_fixedBase_originBall` consumes at each base `w`; wiring it into the
      `∀ w ∈ K` family is the frozen-active-bank uniformity.  ⚠ CHART-DOMAIN VERDICT (honest): the
      per-`w` chart continuity is required on an OPEN set `U ⊇ closedBall 0 R` (origin-centred), whereas
      the base-`w` `C²` region `FrozenBaseWChain.chartField_contDiffOn_ball_at` is `ball w ρc`
      (`w`-centred).  For `w` far from the origin these differ; the resolution is that the ACTIVE part of
      the origin ball sits inside `ball w ρc` (only there is `E(·,·,w)` non-zero), and OFF the active set
      `hoff` places every origin-slab point strictly chart-far so `E(·,·,w)` is locally the zero function
      there — hence `hWwcont` is genuinely needed only where it is available.  `Hgeo` carries this bundle
      honestly (it is satisfiable exactly on the reconciled active/collar geometry); it is NOT this file's
      conclusion.

    * (C1) `leviSlice_jointContinuousOn_DONE` — ★★ THE S-DOM-DISCHARGED CAPSTONE.  The full Levi `0`-slice
      joint continuity for the concrete witness with `hSdom` REMOVED (discharged by `hSdom_concrete`).
      Remaining inputs (the FINAL INPUT LIST): the banked `hEbound`/`hInt`/`hEmeas`, the base-0 slice
      `hbase`, the per-`w∈K` near-cover `hnear`, and the summable termwise envelope `env`/`hu`/`hbound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no vacuous /
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
     file edited.  **NOT `a₁ = R/6`** — this is a regularity / domination / coverage brick; it says
     NOTHING new about the curvature value.
-/
import Mathlib
import QIQTH.GapASdomInstantiation
import QIQTH.RDomEnvelope
import QIQTH.ParametrixHEboundWiring

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.RDomEnvelope QIQTH.RadialDistance
open QIQTH.GapASdomInstantiation QIQTH.GapACoverGapB
open scoped Topology ContDiff

namespace QIQTH.SdomHnearDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (S1) The S-dom discharge — the `p`-uniform integrable spatial dominator.
    ############################################################################### -/

/-- **★★★ (S1) `hSdom_concrete` — THE S-DOM DISCHARGE.**  For the concrete gated van-Vleck witness heat
    operator `E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)`, produces the EXACT `hSdom` slot
    consumed by `GapASdomInstantiation.iterE_jointContinuousOn_concrete_final` /
    `leviSlice_jointContinuousOn_concrete_final`:

      `∀ m, 1 ≤ m → ∀ t₁ t₂ R, 0<t₁ → t₁≤t₂ → 0<R →
        ∃ bnd : ℝ → Point n → ℝ,
          (∀ᵐ u ∂restrict(Ioc 0 1), Integrable (bnd u)) ∧
          (∀ᵐ u ∂restrict(Ioc 0 1), ∀ p ∈ Icc t₁ t₂ ×ˢ closedBall 0 R, ∀ᵐ w,
            ‖E (p.1−p.1·u) p.2 w · iterE E m (p.1·u) w 0‖ ≤ bnd u w)`,

    from ONLY the banked `hEbound` + `hInt` (`0 < κ`, `0 ≤ C`, `K` compact).  The dominator
    `bnd u w = M(u)·𝟙_K(w)` uses the hard `K`-gate zero (`heatOpWitness_baseNotMem_eq_zero`) to localize
    to the finite-measure compact `K`, and on `K` the peaked Gaussian majorants to reach the explicit
    `(s,z,w)`-free constant `M(u)`.  Genuine and satisfiable; NOT the conclusion.  NOT `a₁ = R/6`. -/
theorem hSdom_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (κ C : ℝ) (hκ : 0 < κ) (hC0 : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ →
      |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ 0 C) :
    ∀ (m : ℕ), 1 ≤ m → ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∃ bnd : ℝ → Point n → ℝ,
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume) ∧
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
            ∀ᵐ w ∂volume,
              ‖heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) (p.1 - p.1 * u) p.2 w
                * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) m (p.1 * u) w 0‖
                ≤ bnd u w) := by
  intro m hm t₁ t₂ R ht₁ ht₁₂ hR
  set E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) with hE
  -- the banked iterated bound `|iterE E m t x y| ≤ C^m · iterKernelW …`
  have hiter := iterConvW_bound E κ 0 C hEbound hInt
  -- measure facts for the compact base set `K`
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKfin : volume K < ⊤ := hK.measure_lt_top
  have hΓ : 0 < Real.Gamma (m : ℝ) :=
    Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < m by omega))
  have he : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hm)
  have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ ht₁₂
  refine ⟨fun u w =>
      (C * gaussDdim (κ * (t₁ * (1 - u))) (0 : Point n))
        * (C ^ m * (1 / Real.Gamma (m : ℝ) * (t₂ * u) ^ ((m : ℝ) - 1)
            * gaussDdim (κ * (t₁ * u)) (0 : Point n)))
        * Set.indicator K (fun _ => (1 : ℝ)) w, ?_, ?_⟩
  · -- (integrability) `bnd u` = constant · 𝟙_K, integrable since `K` has finite measure.
    refine ae_of_all _ (fun u => ?_)
    have hind : Integrable (Set.indicator K (fun _ => (1 : ℝ))) volume :=
      (integrable_indicator_iff hKmeas).mpr (integrableOn_const hKfin.ne)
    exact hind.const_mul _
  · -- (the pointwise bound) drop the null endpoint `u = 1`, then split `w ∈ K` / `w ∉ K`.
    have hlt1 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]; simp only [ne_eq, not_not]
      rw [show {a : ℝ | a = 1} = ({1} : Set ℝ) from by ext x; simp]
      exact measure_singleton 1
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hlt1] with u hu hune
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := lt_of_le_of_ne hu.2 hune
    have h1u : (0:ℝ) < 1 - u := by linarith
    intro p hp
    obtain ⟨hps, _hpz⟩ := hp
    have hs : p.1 ∈ Set.Icc t₁ t₂ := hps
    have hspos : 0 < p.1 := lt_of_lt_of_le ht₁ hs.1
    have hs1 : 0 < p.1 - p.1 * u := by nlinarith [mul_pos hspos h1u]
    have hs2 : 0 < p.1 * u := mul_pos hspos hu0
    refine ae_of_all _ (fun w => ?_)
    by_cases hwK : w ∈ K
    · -- NEAR: `w ∈ K`; the peaked Gaussian majorants give the constant `M u`.
      have hind1 : Set.indicator K (fun _ => (1:ℝ)) w = 1 := by
        simp [Set.indicator_of_mem hwK]
      rw [hind1, mul_one]
      -- factor majorants
      have hb1 : |E (p.1 - p.1 * u) p.2 w| ≤ C * baseKernelW κ 0 (p.1 - p.1 * u) p.2 w :=
        hEbound (p.1 - p.1 * u) p.2 w hs1
      have hb2 : |iterE E m (p.1 * u) w 0| ≤ C ^ m * iterKernelW κ 0 m (p.1 * u) w 0 :=
        hiter m hm (p.1 * u) hs2 w 0
      -- first factor ≤ `C · G_{κ·t₁·(1−u)}(0)`
      have hpos1 : 0 < κ * (t₁ * (1 - u)) := mul_pos hκ (mul_pos ht₁ h1u)
      have hle1 : κ * (t₁ * (1 - u)) ≤ κ * (p.1 - p.1 * u) := by
        have hinner : t₁ * (1 - u) ≤ p.1 - p.1 * u := by
          nlinarith [mul_le_mul_of_nonneg_right hs.1 h1u.le]
        exact mul_le_mul_of_nonneg_left hinner hκ.le
      have hgd1 : gaussDdim (κ * (p.1 - p.1 * u)) (0 : Point n)
          ≤ gaussDdim (κ * (t₁ * (1 - u))) (0 : Point n) :=
        gaussDdim_zero_antitone hpos1 hle1
      have hA : C * baseKernelW κ 0 (p.1 - p.1 * u) p.2 w
          ≤ C * gaussDdim (κ * (t₁ * (1 - u))) (0 : Point n) := by
        rw [baseKernelW_zero_apply]
        exact mul_le_mul_of_nonneg_left
          (le_trans (gaussDdim_le_diagonal (mul_pos hκ hs1) (p.2 - w)) hgd1) hC0
      -- second factor ≤ `C^m · Γ(m)⁻¹ · (t₂·u)^{m−1} · G_{κ·t₁·u}(0)`
      have hpos2 : 0 < κ * (t₁ * u) := mul_pos hκ (mul_pos ht₁ hu0)
      have hle2 : κ * (t₁ * u) ≤ κ * (p.1 * u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs.1 hu0.le) hκ.le
      have hgd2 : gaussDdim (κ * (p.1 * u)) (0 : Point n)
          ≤ gaussDdim (κ * (t₁ * u)) (0 : Point n) :=
        gaussDdim_zero_antitone hpos2 hle2
      have hrp : (p.1 * u) ^ ((m : ℝ) - 1) ≤ (t₂ * u) ^ ((m : ℝ) - 1) :=
        Real.rpow_le_rpow hs2.le (mul_le_mul_of_nonneg_right hs.2 hu0.le) he
      have hiterle : iterKernelW κ 0 m (p.1 * u) w 0
          ≤ 1 / Real.Gamma (m : ℝ) * (t₂ * u) ^ ((m : ℝ) - 1)
              * gaussDdim (κ * (t₁ * u)) (0 : Point n) := by
        rw [iterKernelW_zero_apply κ hκ hm hs2 w]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hrp (one_div_nonneg.mpr hΓ.le))
          (le_trans (gaussDdim_le_diagonal (mul_pos hκ hs2) (w - 0)) hgd2)
          (gaussDdim_nonneg _ _)
          (mul_nonneg (one_div_nonneg.mpr hΓ.le) (Real.rpow_nonneg (mul_nonneg ht₂.le hu0.le) _))
      have hB : C ^ m * iterKernelW κ 0 m (p.1 * u) w 0
          ≤ C ^ m * (1 / Real.Gamma (m : ℝ) * (t₂ * u) ^ ((m : ℝ) - 1)
              * gaussDdim (κ * (t₁ * u)) (0 : Point n)) :=
        mul_le_mul_of_nonneg_left hiterle (pow_nonneg hC0 m)
      -- combine
      rw [Real.norm_eq_abs, abs_mul]
      calc |E (p.1 - p.1 * u) p.2 w| * |iterE E m (p.1 * u) w 0|
          ≤ (C * baseKernelW κ 0 (p.1 - p.1 * u) p.2 w)
              * (C ^ m * iterKernelW κ 0 m (p.1 * u) w 0) :=
            mul_le_mul hb1 hb2 (abs_nonneg _) (le_trans (abs_nonneg _) hb1)
        _ ≤ _ :=
            mul_le_mul hA hB (le_trans (abs_nonneg _) hb2)
              (mul_nonneg hC0 (gaussDdim_nonneg _ _))
    · -- K-GATE ZERO: `w ∉ K` ⟹ `E (…,w) = 0`, so the product and the dominator both vanish.
      have hEz : E (p.1 - p.1 * u) p.2 w = 0 := by
        rw [hE]; exact heatOpWitness_baseNotMem_eq_zero g gi hC hK S a b _ _ hwK
      simp [hEz, Set.indicator_of_notMem hwK]

/-! ###############################################################################
    ## (H1) The `hnear` slot from the honest per-`w∈K` geometric bundle.
    ############################################################################### -/

/-- **★★ (H1) `hnear_concrete` — THE NEAR-COVER FROM THE GEOMETRIC BUNDLE.**  Produces the exact `hnear`
    slot (`∀ w ∈ K, ∀ s₁ s₂ R, 0<s₁ → s₁≤s₂ → ContinuousOn (E(·,·,w)) (Icc s₁ s₂ ×ˢ closedBall 0 R)`)
    from the honest per-`w∈K` GEOMETRIC bundle `Hgeo`: at each base `w ∈ K` and each origin ball an open
    covering set `U ⊇ closedBall 0 R`, the chart continuity `hWwcont` of `uniformInverseChart … w` on
    `U`, an open active set `A` with `hEA : ContinuousAt E`, and the collar `hoff` (off `A`, strictly
    chart-far).  This is exactly what `GapACoverGapB.heatOpWitness_fixedBase_originBall` consumes.
    `Hgeo` is genuine and satisfiable (the reconciled active/collar geometry, see the CHART-DOMAIN
    verdict in the header); it is NOT this file's conclusion.  NOT `a₁ = R/6`. -/
theorem hnear_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (Hgeo : ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ U : Set (Point n), IsOpen U ∧ Metric.closedBall (0 : Point n) R ⊆ U ∧
        ContinuousOn (uniformInverseChart g gi hC hK w) U ∧
        ∃ A : Set (ℝ × Point n),
          (∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
              heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p) ∧
          (∀ p ∈ Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
              b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2))) :
    ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro w hw s₁ s₂ R hs₁ hs
  obtain ⟨U, hUopen, hsubU, hWwcont, A, hEA, hoff⟩ := Hgeo w hw s₁ s₂ R hs₁ hs
  exact heatOpWitness_fixedBase_originBall g gi hC hK S a b ha hab s₁ s₂ R
    U hUopen hsubU hWwcont A hEA hoff

/-! ###############################################################################
    ## (C1) The S-dom-discharged Levi `0`-slice continuity capstone.
    ############################################################################### -/

/-- **★★ (C1) `leviSlice_jointContinuousOn_DONE` — THE S-DOM-DISCHARGED CAPSTONE.**  The joint
    `(s,z)`-continuity of the full Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on a positive-time
    compact, for the concrete gated van-Vleck witness, with BOTH the Gap-A carry (already discharged in
    `GapASdomInstantiation`) AND the S-dom carry (discharged here by `hSdom_concrete`) removed.  Remaining
    inputs (the FINAL INPUT LIST): the banked `hEbound`/`hInt`/`hEmeas`, the base-0 slice `hbase`, the
    per-`w∈K` near-cover `hnear`, and the summable termwise envelope `env`/`hu`/`hbound`.  NOT `a₁ = R/6`. -/
theorem leviSlice_jointContinuousOn_DONE (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (κ C : ℝ) (hκ : 0 < κ) (hC0 : 0 ≤ C)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (hR : 0 < R)
    (hEbound : ∀ τ p q, 0 < τ →
      |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hnear : ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k) :
    ContinuousOn (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  leviSlice_jointContinuousOn_concrete_final g gi hC hK S a b κ C hκ hC0 t₁ t₂ R ht₁ ht₁₂ hR
    hEbound hInt hEmeas hbase hnear
    (hSdom_concrete g gi hC hK S a b κ C hκ hC0 hEbound hInt) env hu hbound

#check @hSdom_concrete
#check @hnear_concrete
#check @leviSlice_jointContinuousOn_DONE

end QIQTH.SdomHnearDischarge

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SdomHnearDischarge
#print axioms hSdom_concrete
#print axioms hnear_concrete
#print axioms leviSlice_jointContinuousOn_DONE
end AxiomChecks
