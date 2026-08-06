/-
  GapASdomInstantiation — J4-296: the CONCRETE `hGapA` instantiation for the gated van-Vleck
  witness, via the near / K-gate-zero coverage split, plus the concrete Levi-continuity compose.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `HcontAssembly` (J4-295) closed the
  `iterE` termwise joint-continuity induction (`iterE_jointContinuousOn_strong`,
  `leviSlice_jointContinuousOn_of_strong`) down to TWO per-rung analytic carries on the abstract kernel
  `E`:
    • (Gap-A) `hGapA` — for a.e. `u ∈ (0,1)`, a.e. base `w`, the joint `(s,z)`-continuity of the
      time-reparametrized slice `(s,z) ↦ E (s − s·u) z w`, on `Icc t₁ t₂ ×ˢ closedBall 0 R`;
    • (S-dom) `hSdom` — for each rung a `p`-uniform integrable spatial dominator.
  This file DISCHARGES the Gap-A carry for the CONCRETE witness `E := heatOp g gi (vanVleckGatedWitness
  g gi hC hK S a b)`, replacing it by the honest per-base near-cover, and threads the result through the
  strong induction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE COVERAGE VERDICT (the load-bearing recon).  The Gap-A slice at a FIXED base `w` splits by the
  HARD `K`-GATE, NOT by a near/far norm annulus — so NO unbanked lower near-isometry bound is needed:

     • `w ∈ K` (NEAR).  The frozen-base cover `GapACoverGapB.heatOpWitness_fixedBase_originBall` gives
       the un-reparametrized origin-ball slice continuity `(s,z) ↦ E s z w` on `Icc s₁ s₂ ×ˢ closedBall
       0 R` (from the frozen active bank `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree` +
       the collar geometry `hoff` + the chart continuity `hWwcont`).  The time-reparametrization
       `GapACoverGapB.continuousOn_timeAffine_comp` (applied on the SHRUNK window
       `Icc (t₁·(1−u)) (t₂·(1−u))`, valid because `0 < u < 1`) then delivers the Gap-A slice
       `(s,z) ↦ E (s − s·u) z w`.  This per-`w∈K` cover is carried as `hnear` (satisfiable, not the
       conclusion — see the honest residual).

     • `w ∉ K` (K-GATE ZERO, FREE).  `vanVleckGatedWitness = gatedKernel K S H` VANISHES identically
       in `(τ, p)` at any base `w ∉ K` (the hard `K`-gate: `gatedKernel_apply_of_notMem`).  Hence the
       heat operator `E(·,·,w) ≡ 0` (`gatedKernel_heatOp_eq_zero_of_notMem`), so EVERY slice — including
       the time-reparametrized one — is `ContinuousOn` trivially.  NO annulus, NO far-region
       lower-isometry bound: the two cases `w ∈ K` / `w ∉ K` PARTITION all `w`.

     Because both cases hold for ALL `w` (given the `∀ w ∈ K` near-cover), the produced `hGapA` is in
     fact `∀ w` (`ae_of_all`), not merely a.e. `w`.  The single a.e.-`u` allowance is only to drop the
     endpoint `u = 1` (where `1 − u = 0` collapses the time window to `{0}`, outside the positive-time
     regularity of the parametrix); `{1}` is `volume`-null.

  ── WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `heatOpWitness_baseNotMem_eq_zero` — (K-gate zero, concrete) for `w ∉ K`,
        `heatOp g gi (vanVleckGatedWitness …) τ z w = 0`.  A one-line specialization of the banked
        `HeatResidualBound.gatedKernel_heatOp_eq_zero_of_notMem` through the definition of
        `vanVleckGatedWitness`.

    * `hGapA_concrete` — (I1) THE CONCRETE GAP-A.  For the gated van-Vleck witness, produces the EXACT
        `hGapA` slot shape of `HcontAssembly.iterE_jointContinuousOn_strong`
        (`∀ t₁ t₂ R, 0<t₁ → t₁≤t₂ → 0<R → ∀ᵐ u ∂restrict(Ioc 0 1), ∀ᵐ w, ContinuousOn (fun p ↦
        E (p.1 − p.1·u) p.2 w) (Icc t₁ t₂ ×ˢ closedBall 0 R)`), from ONLY the per-`w∈K` near-cover
        `hnear`.  The `w ∉ K` case is discharged internally by the K-gate zero.

    * `iterE_jointContinuousOn_concrete_final` — (I3) the strong-induction closure with the Gap-A carry
        REMOVED (discharged by `hGapA_concrete`), for the concrete witness.  Its remaining inputs are the
        banked outer bounds/measurability, the base-0 slice `hbase`, the per-`w∈K` near-cover `hnear`,
        and the S-dom carry `hSdom`.

    * `leviSlice_jointContinuousOn_concrete_final` — (I3) the full Levi `0`-slice joint continuity
        (`hf_cont` shape) for the concrete witness, Gap-A discharged; carries the same inputs plus the
        summable termwise envelope.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6).
     • `hnear` — the per-`w∈K` un-reparametrized origin-ball slice continuity.  This is EXACTLY what
       `GapACoverGapB.heatOpWitness_fixedBase_originBall` delivers at each base `w` (given its active
       bank `hEA`, collar `hoff`, chart continuity `hWwcont`); genuine and satisfiable, NOT this file's
       conclusion (the conclusion adds the K-gate case and the time-affine reparametrization).  Wiring
       the per-`w` covers into one `∀ w ∈ K` family is the frozen-active-bank uniformity — carried, not
       faked.
     • `hSdom` — the `p`-uniform integrable spatial dominator (S-dom).  NOT constructed here: the active
       region localizes `w` to `closedBall 0 (R + √(3/2)·b)` (`ZeroCollarLocalZero.heatOpGatedWitness_
       active_norm`) and the fixed-`u` Gaussian majorant is bounded by its diagonal
       (`gaussDdim_le_diagonal`), giving a constant · indicator dominator — the named S-dom residual.

  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no vacuous /
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
     file edited.  **NOT `a₁ = R/6`** — this is a regularity / coverage brick; it says NOTHING new about
     the curvature value.
-/
import Mathlib
import QIQTH.GapACoverGapB
import QIQTH.HcontAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.GaussianWidthTolerant
open scoped Topology ContDiff

namespace QIQTH.GapASdomInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (K-gate zero) The concrete base-not-in-`K` vanishing.
    ############################################################################### -/

/-- **★ `heatOpWitness_baseNotMem_eq_zero` — THE CONCRETE K-GATE ZERO.**  For the gated van-Vleck witness
    heat operator, at any base `w ∉ K` the operator vanishes identically:
    `heatOp g gi (vanVleckGatedWitness …) τ z w = 0`.  The witness is `gatedKernel K S H`, whose hard
    `K`-gate makes the kernel identically `0` in `(τ, p)` for `w ∉ K`; the banked
    `HeatResidualBound.gatedKernel_heatOp_eq_zero_of_notMem` (`Or.inl`) then vanishes the heat operator.
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_baseNotMem_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z : Point n) {w : Point n} (hw : w ∉ K) :
    heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ z w = 0 := by
  simp only [vanVleckGatedWitness]
  exact gatedKernel_heatOp_eq_zero_of_notMem g gi K S _ τ z w (Or.inl hw)

/-! ###############################################################################
    ## (I1) The concrete Gap-A — near / K-gate-zero coverage.
    ############################################################################### -/

/-- **★★★ (I1) `hGapA_concrete` — THE CONCRETE GAP-A.**  For the gated van-Vleck witness heat operator
    `E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)`, this produces the EXACT `hGapA` slot
    consumed by `HcontAssembly.iterE_jointContinuousOn_strong`:

      `∀ t₁ t₂ R, 0<t₁ → t₁≤t₂ → 0<R →
        ∀ᵐ u ∂(volume.restrict (Ioc 0 1)), ∀ᵐ w ∂volume,
          ContinuousOn (fun p ↦ E (p.1 − p.1·u) p.2 w) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,

    from ONLY the per-`w∈K` un-reparametrized origin-ball near-cover `hnear`.  Coverage split:
    `w ∈ K` uses `hnear` composed with `GapACoverGapB.continuousOn_timeAffine_comp` on the shrunk window;
    `w ∉ K` uses the K-gate zero (`heatOpWitness_baseNotMem_eq_zero`), so the slice is `const 0`.  The
    a.e.-`u` allowance drops only the null endpoint `u = 1`.  `hnear` is genuine and satisfiable (from
    `GapACoverGapB.heatOpWitness_fixedBase_originBall`) and is NOT the conclusion.  NOT `a₁ = R/6`. -/
theorem hGapA_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hnear : ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        ∀ᵐ w ∂volume, ContinuousOn
          (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) (p.1 - p.1 * u) p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro t₁ t₂ R ht₁ ht hR
  -- a.e.-`u`: `u ∈ Ioc 0 1` and `u ≠ 1`, hence `0 < u < 1`.
  have hlt1 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [show {a : ℝ | a = 1} = ({1} : Set ℝ) from by ext x; simp]
    exact measure_singleton 1
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hlt1] with u hu hune
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 hune
  have h1u : (0:ℝ) < 1 - u := by linarith
  -- inner `∀ w` (both `K`-cases cover ALL `w`).
  refine ae_of_all _ (fun w => ?_)
  by_cases hwK : w ∈ K
  · -- NEAR: `hnear` on the shrunk window, time-reparametrized.
    exact QIQTH.GapACoverGapB.continuousOn_timeAffine_comp
      (fun q : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) q.1 q.2 w)
      u t₁ t₂ R hu1 ht
      (hnear w hwK (t₁ * (1 - u)) (t₂ * (1 - u)) R (mul_pos ht₁ h1u)
        (mul_le_mul_of_nonneg_right ht h1u.le))
  · -- K-GATE ZERO: the slice is identically `0`.
    have hz : ContinuousOn (fun _ : ℝ × Point n => (0 : ℝ))
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := continuousOn_const
    refine hz.congr (fun p _ => ?_)
    exact heatOpWitness_baseNotMem_eq_zero g gi hC hK S a b (p.1 - p.1 * u) p.2 hwK

/-! ###############################################################################
    ## (I3) The concrete Levi-continuity closures — Gap-A discharged.
    ############################################################################### -/

/-- **★★ (I3) `iterE_jointContinuousOn_concrete_final`.**  The strong-induction closure
    (`HcontAssembly.iterE_jointContinuousOn_strong`) for the concrete gated van-Vleck witness, with the
    Gap-A carry DISCHARGED by `hGapA_concrete` (i.e. replaced by the per-`w∈K` near-cover `hnear`).
    Remaining inputs: the banked outer bounds `hEbound`/`hInt`/`hEmeas`, the base-0 slice `hbase`, the
    near-cover `hnear`, and the S-dom carry `hSdom`.  NOT `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_concrete_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (κ C : ℝ) (hκ : 0 < κ) (hC0 : 0 ≤ C)
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
    (hSdom : ∀ (m : ℕ), 1 ≤ m → ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∃ bnd : ℝ → Point n → ℝ,
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume) ∧
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
            ∀ᵐ w ∂volume,
              ‖heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) (p.1 - p.1 * u) p.2 w
                * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) m (p.1 * u) w 0‖
                ≤ bnd u w)) :
    ∀ k : ℕ, ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n =>
          iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  QIQTH.HcontAssembly.iterE_jointContinuousOn_strong
    (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ C hκ hC0 hEbound hInt hEmeas hbase
    (hGapA_concrete g gi hC hK S a b hnear) hSdom

/-- **★★ (I3) `leviSlice_jointContinuousOn_concrete_final` — the `hf_cont`-shaped capstone (concrete).**
    The joint `(s,z)`-continuity of the FULL Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on a
    positive-time compact, for the concrete gated van-Vleck witness, with the Gap-A carry DISCHARGED by
    `hGapA_concrete`.  Feeds `HcontAssembly.leviSlice_jointContinuousOn_of_strong`; carries the banked
    bounds, `hbase`, the near-cover `hnear`, the S-dom carry `hSdom`, and the summable termwise envelope
    (`env`/`hu`/`hbound`).  NOT `a₁ = R/6`. -/
theorem leviSlice_jointContinuousOn_concrete_final (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hSdom : ∀ (m : ℕ), 1 ≤ m → ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∃ bnd : ℝ → Point n → ℝ,
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume) ∧
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
            ∀ᵐ w ∂volume,
              ‖heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) (p.1 - p.1 * u) p.2 w
                * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) m (p.1 * u) w 0‖
                ≤ bnd u w))
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k) :
    ContinuousOn (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  QIQTH.HcontAssembly.leviSlice_jointContinuousOn_of_strong
    (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ C hκ hC0 t₁ t₂ R ht₁ ht₁₂ hR
    hEbound hInt hEmeas hbase (hGapA_concrete g gi hC hK S a b hnear) hSdom env hu hbound

#check @heatOpWitness_baseNotMem_eq_zero
#check @hGapA_concrete
#check @iterE_jointContinuousOn_concrete_final
#check @leviSlice_jointContinuousOn_concrete_final

end QIQTH.GapASdomInstantiation

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GapASdomInstantiation
#print axioms heatOpWitness_baseNotMem_eq_zero
#print axioms hGapA_concrete
#print axioms iterE_jointContinuousOn_concrete_final
#print axioms leviSlice_jointContinuousOn_concrete_final
end AxiomChecks
