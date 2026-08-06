/-
  GapACoverGapB — J4-294: the Gap-A cover (origin-centred, frozen-base) + the Gap-B time-affine
  bridge and the all-`k` reduction of the `iterE` engine.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  The frozen-base capstone
  `FrozenBaseWChain.heatOpWitness_fixedBase_continuousOn` (J4-293) proves, at every base `w`, the
  joint `(time, FIRST-spatial)` continuity of the gated van-Vleck witness heat operator
      `E p := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w`
  on the `w`-CENTRED slab `Icc t₁ t₂ ×ˢ closedBall w R`.  The inner/outer recursion engines
  (`InnerEngineRecursion` / `IterEEngineWiring`), by contrast, live on the ORIGIN-centred slab
  `Icc t₁ t₂ ×ˢ closedBall 0 R`.  This file bridges the two centres.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  regularity / geometry / wiring brick.  No `sorry` (this header prose aside), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * (G1-near) `heatOpWitness_fixedBase_originBall` — THE GAP-A COVER.  For a fixed base `w`, the
        slice `E(·,·,w)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)` — the ORIGIN-centred domain —
        given: an OPEN active set `A` with `hEA : ContinuousAt E` on `A` (the banked base-`w`
        active-region continuity, `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree`); the
        HONEST collar carry `hoff` (every origin-slab point off `A` is strictly chart-far,
        `b² < rncRadialSq (W w ·)`); and a chart-continuity carry `hWwcont` on an open `U ⊇ closedBall
        0 R`.  The local-zero half is DISCHARGED here (via the J4-292 `heatOpGatedWitness_eq_zero_of_far`
        at base `q = w`); the pasting is `ZeroCollarLocalZero.continuousOn_of_active_open_zero_off`.
        This is the exact analogue of `ZeroCollarLocalZero.E_slice_continuousOn_off_support`
        (which is base `w = 0`), generalized to any base `w` on the origin ball.

    * (G1-far) `heatOpWitness_fixedBase_originBall_far` — for a base `w` whose gate is chart-far from the
        ENTIRE origin ball (`hfar : ∀ z ∈ closedBall 0 R, b² < rncRadialSq (W w z)`), the slice
        `E(·,·,w)` is IDENTICALLY zero on the origin slab (`heatOpGatedWitness_eq_zero_of_far` at every
        point), hence trivially `ContinuousOn`.  Satisfiable: choose `‖w‖ > R + √(3/2)·b` so the whole
        origin ball sits outside the near ball of the `w`-gate (`heatOpGatedWitness_active_norm`).

    * (Bridge) `continuousOn_timeAffine_comp` — the Gap-B/Gap-A TIME-REPARAMETRIZATION bridge: from the
        continuity of `f` on the SHRUNK slab `Icc (t₁·(1−u)) (t₂·(1−u)) ×ˢ closedBall 0 R`, obtain the
        continuity of `(s,z) ↦ f (s − s·u, z)` on `Icc t₁ t₂ ×ˢ closedBall 0 R`, for a fixed
        `0 < u < 1`.  This is exactly the composition that feeds the engine's `hcontE` (Gap-A) slot
        `(s,z) ↦ E (s − s·u) z w` from the frozen-base cover `(s,z) ↦ E s z w` and, symmetrically, is
        the shape of the `hcontIter` (Gap-B) slot's time-argument `s·u`.

    * (G2-reduce) `iterE_jointContinuousOn_all` — the ALL-`k` termwise joint continuity on the origin
        ball, `∀ k, ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0)`, REDUCED to exactly three carries:
        the outer bounds (`hEbound`/`hInt`), the base joint measurability `hEmeas` (which DISCHARGES the
        engine's `hmeas` slot OUTRIGHT via `InnerEngineRecursion.convStepIntegral_u_aestronglyMeasurable
        _wired`), the base slice continuity `hbase` (= G1 at `w = 0`), and the a.e.-`u` inner joint
        continuity `hcont`.  A strictly tighter reduction than `IterEEngineWiring.iterE_jointContinuousOn
        _wired` (whose `hmeas` slot is here discharged from `hEmeas`).

    * (G2-concrete) `iterE_jointContinuousOn_all_concrete` — the same specialized to the concrete gated
        van-Vleck witness residual, with `hbase` the banked origin-ball base-0 slice
        (`ZeroCollarLocalZero.E_slice_continuousOn_off_support`).

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     • G1 carries the banked base-`w` ACTIVE continuity (`hEA`) — the F3+F2 active capstone — plus the
       collar geometry (`hoff`) and the chart `C²` continuity (`hWwcont`).  These are genuine and
       satisfiable (see `FrozenBaseWChain`); they are NOT discharged here.
     • G2's `hcont` carry is the a.e.-`u` inner joint continuity, whose per-fibre content
       (`InnerEngineRecursion.innerStep_cont_of_slots`) factors as Gap-A · Gap-B · S-dom.  Gap-A at a
       single base `w` is exactly what G1 + `continuousOn_timeAffine_comp` deliver; wiring the
       resulting per-`w` continuity into the a.e.-`w` engine slot needs the ∀`w` ACTIVE bank and the
       uniform Gaussian spatial dominator — the named residual, carried honestly, not faked.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrozenBaseWChain
import QIQTH.ZeroCollarLocalZero
import QIQTH.InnerEngineRecursion
import QIQTH.IterEEngineWiring

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.LeviSeries QIQTH.IterEEngineWiring QIQTH.InnerEngineRecursion
open QIQTH.ZeroCollarLocalZero QIQTH.FrozenBaseWChain
open scoped Topology

namespace QIQTH.GapACoverGapB

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (G1-near) THE GAP-A COVER — frozen base `w`, ORIGIN-centred slab.
    ############################################################################### -/

/-- **★★★ (G1-near) `heatOpWitness_fixedBase_originBall` — THE GAP-A COVER (origin-centred).**  For the
    fixed-base gated van-Vleck witness heat operator
        `E p := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w`,
    given:

    * `hWwcont` — `W w = uniformInverseChart g gi hC hK w` is `ContinuousOn U` for an OPEN `U` with
      `closedBall 0 R ⊆ U` (its `C²` region around the field centre, from F1);
    * an OPEN active set `A` with `hEA : ContinuousAt E` on `A` — the banked base-`w` active-region
      continuity (`FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree`);
    * `hoff` — the HONEST collar carry: every ORIGIN-slab point OFF `A` is strictly chart-far,
      `b² < rncRadialSq (W w ·)` (the cutoff support ⊆ `A`),

    the slice `E(·,·,w)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)`.  The local-zero half is
    DISCHARGED here (J4-292 B1/B2 at base `q = w`); the pasting is the J4-292 skeleton.  Exact
    origin-centred analogue of `ZeroCollarLocalZero.E_slice_continuousOn_off_support` (base `w = 0`).
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_originBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t₁ t₂ R : ℝ) {w : Point n}
    (U : Set (Point n)) (hUopen : IsOpen U) (hsubU : Metric.closedBall (0 : Point n) R ⊆ U)
    (hWwcont : ContinuousOn (uniformInverseChart g gi hC hK w) U)
    (A : Set (ℝ × Point n))
    (hEA : ∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p)
    (hoff : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine continuousOn_of_active_open_zero_off _ _ A hEA ?_
  intro p hp hpA
  have hfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2) := hoff p hp hpA
  have hz : p.2 ∈ U := hsubU hp.2
  have hUnhds : U ∈ nhds p.2 := hUopen.mem_nhds hz
  have hWc_z : ContinuousAt (uniformInverseChart g gi hC hK w) p.2 :=
    hWwcont.continuousAt hUnhds
  have hNnhds : (uniformInverseChart g gi hC hK w) ⁻¹' {v : Point n | b ^ 2 < rncRadialSq v}
      ∈ nhds p.2 :=
    hWc_z.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hfar)
  have hN'nhds :
      (uniformInverseChart g gi hC hK w) ⁻¹' {v : Point n | b ^ 2 < rncRadialSq v} ∩ U
        ∈ nhds p.2 :=
    Filter.inter_mem hNnhds hUnhds
  have hprodnhds : Set.univ ×ˢ ((uniformInverseChart g gi hC hK w) ⁻¹'
      {v : Point n | b ^ 2 < rncRadialSq v} ∩ U) ∈ nhds p := by
    have h := prod_mem_nhds (Filter.univ_mem : (Set.univ : Set ℝ) ∈ nhds p.1) hN'nhds
    rwa [Prod.mk.eta] at h
  filter_upwards [hprodnhds] with x hx
  have hx2 : x.2 ∈ (uniformInverseChart g gi hC hK w) ⁻¹'
      {v : Point n | b ^ 2 < rncRadialSq v} ∩ U := hx.2
  have hxfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w x.2) := hx2.1
  have hxU : x.2 ∈ U := hx2.2
  have hWc_x : ContinuousAt (uniformInverseChart g gi hC hK w) x.2 :=
    hWwcont.continuousAt (hUopen.mem_nhds hxU)
  show heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) x.1 x.2 w = 0
  simp only [vanVleckGatedWitness]
  exact heatOpGatedWitness_eq_zero_of_far g gi ha hab 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) K S (uniformInverseChart g gi hC hK)
    x.1 w hWc_x hxfar

/-! ###############################################################################
    ## (G1-far) The far-base slice — identically zero on the origin slab.
    ############################################################################### -/

/-- **★★ (G1-far) `heatOpWitness_fixedBase_originBall_far`.**  For a fixed base `w` whose gate is
    chart-far from the ENTIRE origin ball — `hfar : ∀ z ∈ closedBall 0 R, b² < rncRadialSq (W w z)` —
    the slice `E(·,·,w)` is IDENTICALLY zero on the origin slab, hence `ContinuousOn`.  Every point is
    off-support (`heatOpGatedWitness_eq_zero_of_far` at base `q = w`), so the slice equals `const 0`.
    Satisfiable: `‖w‖ > R + √(3/2)·b` forces the whole origin ball outside the near ball of the
    `w`-gate (`ZeroCollarLocalZero.heatOpGatedWitness_active_norm`).  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_originBall_far (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t₁ t₂ R : ℝ) {w : Point n}
    (U : Set (Point n)) (hUopen : IsOpen U) (hsubU : Metric.closedBall (0 : Point n) R ⊆ U)
    (hWwcont : ContinuousOn (uniformInverseChart g gi hC hK w) U)
    (hfar : ∀ z ∈ Metric.closedBall (0 : Point n) R,
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEqOn : Set.EqOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (fun _ => (0 : ℝ)) (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
    intro p hp
    have hz : p.2 ∈ U := hsubU hp.2
    have hWc_z : ContinuousAt (uniformInverseChart g gi hC hK w) p.2 :=
      hWwcont.continuousAt (hUopen.mem_nhds hz)
    show heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w = 0
    simp only [vanVleckGatedWitness]
    exact heatOpGatedWitness_eq_zero_of_far g gi ha hab 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) K S (uniformInverseChart g gi hC hK)
      p.1 w hWc_z (hfar p.2 hp.2)
  exact continuousOn_const.congr hEqOn

/-! ###############################################################################
    ## (Bridge) The Gap-A / Gap-B TIME-REPARAMETRIZATION composition.
    ############################################################################### -/

/-- **★ (Bridge) `continuousOn_timeAffine_comp` — the time-reparametrization bridge.**  For a fixed
    `0 < u < 1`, if `f` is `ContinuousOn` the SHRUNK slab `Icc (t₁·(1−u)) (t₂·(1−u)) ×ˢ closedBall 0 R`,
    then `(s,z) ↦ f (s − s·u, z)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)`.  The affine map
    `(s,z) ↦ (s − s·u, z) = (s·(1−u), z)` is continuous and, since `1−u > 0`, sends
    `[t₁,t₂]` into `[t₁·(1−u), t₂·(1−u)]` and fixes the spatial ball, so `ContinuousOn.comp` applies.
    This is EXACTLY the composition that produces the engine's `hcontE` (Gap-A) slot
    `(s,z) ↦ E (s − s·u) z w` from the frozen-base cover `(s,z) ↦ E s z w` (G1).  NOT `a₁ = R/6`. -/
theorem continuousOn_timeAffine_comp (f : ℝ × Point n → ℝ) (u t₁ t₂ R : ℝ)
    (hu1 : u < 1) (ht : t₁ ≤ t₂)
    (hf : ContinuousOn f
      (Set.Icc (t₁ * (1 - u)) (t₂ * (1 - u)) ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => f (p.1 - p.1 * u, p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hcont : Continuous (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2)) :=
    (continuous_fst.sub (continuous_fst.mul continuous_const)).prodMk continuous_snd
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => (p.1 - p.1 * u, p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
      (Set.Icc (t₁ * (1 - u)) (t₂ * (1 - u)) ×ˢ Metric.closedBall (0 : Point n) R) := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    obtain ⟨⟨h1, h2⟩, hpz⟩ := hp
    have hu0 : (0 : ℝ) ≤ 1 - u := by linarith
    refine ⟨⟨?_, ?_⟩, hpz⟩
    · nlinarith [mul_le_mul_of_nonneg_right h1 hu0]
    · nlinarith [mul_le_mul_of_nonneg_right h2 hu0]
  exact hf.comp hcont.continuousOn hmaps

/-! ###############################################################################
    ## (G2-reduce) The ALL-`k` termwise joint continuity — measurability discharged.
    ############################################################################### -/

/-- **★★★ (G2-reduce) `iterE_jointContinuousOn_all`.**  The ALL-`k` termwise joint continuity on the
    ORIGIN ball, `∀ k, ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`,
    reduced to exactly the outer bounds (`hEbound`/`hInt`), the base joint measurability `hEmeas`, the
    base slice continuity `hbase` (= G1 at `w = 0`), and the a.e.-`u` inner joint continuity `hcont`.
    The engine's `hmeas` slot is DISCHARGED OUTRIGHT from `hEmeas` via
    `InnerEngineRecursion.convStepIntegral_u_aestronglyMeasurable_wired` — a strictly tighter reduction
    than `IterEEngineWiring.iterE_jointContinuousOn_wired`.  NONE of the carries is the conclusion.
    NOT `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_all
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (hbase : ContinuousOn (fun p : ℝ × Point n => E p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  iterE_jointContinuousOn_wired E κ C hκ hC t₁ t₂ R ht₁ hEbound hInt hbase
    (convStepIntegral_u_aestronglyMeasurable_wired E t₁ t₂ R hEmeas) hcont

/-- **★★ (G2-concrete) `iterE_jointContinuousOn_all_concrete`.**  The G2 reduction specialized to the
    concrete gated van-Vleck witness residual `E := heatOp g gi (vanVleckGatedWitness …)`, with the base
    slice continuity `hbase` supplied by the banked origin-ball base-0 capstone
    `ZeroCollarLocalZero.E_slice_continuousOn_off_support` (= G1 at `w = 0`).  Reduced to the banked
    outer bounds/measurability + the a.e.-`u` inner joint continuity `hcont`.  NOT `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_all_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC0 : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (t₁ t₂ R ρc : ℝ) (ht₁ : 0 < t₁) (hRρc : R < ρc)
    (hW0cont : ContinuousOn (uniformInverseChart g gi hC0 hK 0) (Metric.ball (0 : Point n) ρc))
    (hEbound : ∀ τ p q, 0 < τ →
      |heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b) τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b)) κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b) q.1 q.2.1 q.2.2))
    (A : Set (ℝ × Point n))
    (hEA : ∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b) p.1 p.2 0) p)
    (hoff : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC0 hK 0 p.2))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w,
          heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b) (p.1 - p.1 * u) p.2 w
            * iterE (heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b)) (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × Point n =>
        iterE (heatOp g gi (vanVleckGatedWitness g gi hC0 hK S a b)) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  iterE_jointContinuousOn_all _ κ C hκ hC t₁ t₂ R ht₁ hEbound hInt hEmeas
    (E_slice_continuousOn_off_support g gi hC0 hK S a b ha hab t₁ t₂ R ρc hRρc hW0cont A hEA hoff)
    hcont

#check @heatOpWitness_fixedBase_originBall
#check @heatOpWitness_fixedBase_originBall_far
#check @continuousOn_timeAffine_comp
#check @iterE_jointContinuousOn_all
#check @iterE_jointContinuousOn_all_concrete

end QIQTH.GapACoverGapB

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GapACoverGapB
#print axioms heatOpWitness_fixedBase_originBall
#print axioms heatOpWitness_fixedBase_originBall_far
#print axioms continuousOn_timeAffine_comp
#print axioms iterE_jointContinuousOn_all
#print axioms iterE_jointContinuousOn_all_concrete
end AxiomChecks
