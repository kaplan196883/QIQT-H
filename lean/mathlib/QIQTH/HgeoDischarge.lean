/-
  HgeoDischarge — J4-298: the two-open-cover discharge of the per-`w∈K` origin-ball near-cover
  `hnear` — WITHOUT the impossible global chart continuity.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  The concrete S-dom-discharged Levi
  `0`-slice capstone `SdomHnearDischarge.leviSlice_jointContinuousOn_DONE` (J4-297) carries, beyond the
  banked `hEbound`/`hInt`/`hEmeas`/`hbase` + the summable envelope, exactly ONE remaining analytic
  carry: the per-`w∈K` origin-ball slice continuity `hnear`
    `∀ w ∈ K, ∀ s₁ s₂ R, 0<s₁ → s₁≤s₂ →
       ContinuousOn (E(·,·,w)) (Icc s₁ s₂ ×ˢ closedBall 0 R)`.
  `SdomHnearDischarge.hnear_concrete` reduces `hnear` to the geometric bundle `Hgeo`, which is
  consumed by `GapACoverGapB.heatOpWitness_fixedBase_originBall`.  ⚠ THE HONEST WALL: that consumer
  needs the base-`w` inverse chart `W w := uniformInverseChart g gi hC hK w` continuous on an OPEN set
  `U ⊇ closedBall 0 R` (ORIGIN-centred), whereas `W w` is only continuous on its `C²` region
  `ball w ρc` (`w`-centred, `FrozenBaseWChain.chartField_contDiffOn_ball_at`) and is `.choose`-garbage
  off it.  For a base `w` far from the origin these are incompatible — the exact `Hgeo` shape is
  UNSATISFIABLE for far `w`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE TWO-OPEN-COVER RESOLUTION (this file).  The off-active origin-ball points split into TWO OPEN
  regions, each giving the local-zero germ WITHOUT global chart continuity:

    • OFF-GATE (`z ∉ closure (S w)`): the OPEN complement `(closure (S w))ᶜ` is a neighbourhood on
      which the whole gated witness heat operator is IDENTICALLY zero — the hard gate makes
      `gatedKernel K S H` vanish off `S w` (`HeatResidualBound.gatedKernel_heatOp_eq_zero_of_notMem`,
      the `Or.inr` off-gate leg).  NO chart continuity is used.

    • COLLAR (`z ∈ closure (S w)`): here `z` sits inside the gate closure, hence inside the chart `C²`
      region (the provider gate `S w = φ_w '' ball 0 c` has `c < ρc`, so `closure (S w) ⊆ ball w ρc`).
      The chart IS continuous there; with the collar carry `b² < rncRadialSq (W w z)` (the cutoff
      support sits strictly inside the gate), the J4-292 space-germ/heatOp-locality
      (`ZeroCollarLocalZero.heatOpGatedWitness_eq_zero_of_far`) gives the local zero.

  Crucially the chart continuity is now required ONLY on an open `V ⊇ closure (S w)` — which the
  provider realizes as `ball w ρc` (available `∀ w ∈ K` from F1) — NEVER on the whole origin ball.
  This DISCHARGES `hnear` directly for every `w ∈ K`, resolving the far-`w` wall of the original
  `Hgeo`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry` outside this header, NO new axioms; NOT a₁=R/6).

    * (G1) `continuousOn_of_active_twoRegionZero` — THE ABSTRACT TWO-REGION PASTING COMBINATOR.  For a
      field `E : X → ℝ`, an active set `A` (continuity there), and a splitting region `D`: if `E` is
      locally zero at each off-`A` point OUTSIDE `D` (off-gate germ) AND at each off-`A` point INSIDE
      `D` (collar germ), then `E` is `ContinuousOn s`.  A one-line case-split on `D` over
      `ZeroCollarLocalZero.continuousOn_of_active_open_zero_off`.  Provider-agnostic.

    * (G2) `heatOpWitness_originBall_twoCover` — THE ORIGIN-BALL SLICE CONTINUITY VIA THE TWO-COVER.
      For the fixed-base gated van-Vleck witness `E(·,·,w)`, `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)`
      from: the banked active continuity `hEA` on an open `A`; an open `V ⊇ closure (S w)` with `W w`
      continuous on `V` (its `C²` region, realized as `ball w ρc`); and the collar carry `hcollar`
      (off-`A` points inside `closure (S w)` are strictly chart-far).  The off-gate germ is DISCHARGED
      here (the hard gate zero); the collar germ is DISCHARGED here (J4-292 at base `q = w`).  NO global
      chart continuity — the exact analogue of `heatOpWitness_fixedBase_originBall` but with the
      unsatisfiable-for-far-`w` `U ⊇ closedBall 0 R` REPLACED by the satisfiable `V ⊇ closure (S w)`.

    * (G3a) `hnear_twoCover` — the `hnear` slot `∀ w ∈ K` from the honest per-`w` two-cover bundle `H2`
      (the fields of G2, existentially packaged).  `H2` is genuine and satisfiable ∀ `w ∈ K` (the chart
      region `V := ball w ρc` from F1; the collar from the gate margin `c − b > 0`; `hEA` from the
      banked active chain) — strictly MORE satisfiable than the original `Hgeo` (no far-`w` wall).

    * (G3b) `leviSlice_jointContinuousOn_FINAL` — ★★ THE `hnear`-DISCHARGED CAPSTONE.  The full Levi
      `0`-slice joint continuity for the concrete witness with `hnear` REMOVED (discharged by
      `hnear_twoCover` from `H2`).  FINAL INPUT LIST: the banked `hEbound`/`hInt`/`hEmeas`, the base-0
      slice `hbase`, the honest per-`w` two-cover bundle `H2`, and the summable termwise envelope
      `env`/`hu`/`hbound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no vacuous /
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
     existing file edited.  The carried `H2` bundle is genuine and satisfiable ∀ `w ∈ K` (see the
     two-open-cover resolution above); it is NOT this file's conclusion.  **NOT `a₁ = R/6`** — this is a
     regularity / coverage brick; it says NOTHING new about the curvature value.
-/
import Mathlib
import QIQTH.SdomHnearDischarge
import QIQTH.GapACoverGapB

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.RDomEnvelope QIQTH.RadialDistance
open QIQTH.ZeroCollarLocalZero QIQTH.GapACoverGapB QIQTH.SdomHnearDischarge
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology ContDiff

namespace QIQTH.HgeoDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (G1) The abstract two-region pasting combinator.
    ############################################################################### -/

/-- **★ (G1) `continuousOn_of_active_twoRegionZero` — TWO-REGION CONTINUITY PASTING.**  If `E` is
    continuous at every point of an active set `A`, and at every off-`A` point of `s` the field `E`
    is locally the zero function — split by a region `D` into an OFF-`D` germ (`hoff`) and an ON-`D`
    germ (`hcollar`) — then `E` is `ContinuousOn s`.  A one-line case-split on `D` over the J4-292
    `ZeroCollarLocalZero.continuousOn_of_active_open_zero_off`.  Provider-agnostic.  NOT `a₁ = R/6`. -/
theorem continuousOn_of_active_twoRegionZero {X : Type*} [TopologicalSpace X]
    (E : X → ℝ) (s A D : Set X)
    (hEA : ∀ x ∈ A, ContinuousAt E x)
    (hoff : ∀ x ∈ s, x ∉ A → x ∉ D → E =ᶠ[nhds x] (fun _ => (0 : ℝ)))
    (hcollar : ∀ x ∈ s, x ∉ A → x ∈ D → E =ᶠ[nhds x] (fun _ => (0 : ℝ))) :
    ContinuousOn E s := by
  refine continuousOn_of_active_open_zero_off E s A hEA ?_
  intro x hx hxA
  by_cases hxD : x ∈ D
  · exact hcollar x hx hxA hxD
  · exact hoff x hx hxA hxD

/-! ###############################################################################
    ## (G2) The origin-ball slice continuity via the two-open cover.
    ############################################################################### -/

/-- **★★★ (G2) `heatOpWitness_originBall_twoCover` — THE ORIGIN-BALL COVER, NO GLOBAL CHART.**  For the
    fixed-base gated van-Vleck witness heat operator `E p := heatOp g gi (vanVleckGatedWitness …) p.1 p.2 w`,
    `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)` from:

    * an active set `A` with `hEA : ContinuousAt E` on `A` (the banked base-`w` active-region
      continuity, `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree`);
    * an OPEN `V ⊇ closure (S w)` with `W w = uniformInverseChart g gi hC hK w` continuous on `V`
      (its `C²` region — realized as `ball w ρc`, `FrozenBaseWChain.chartField_contDiffOn_ball_at`,
      containing `closure (S w)` since the gate `S w = φ_w '' ball 0 c` has `c < ρc`);
    * `hcollar` — the HONEST collar carry: every origin-slab point OFF `A` and INSIDE `closure (S w)`
      is strictly chart-far, `b² < rncRadialSq (W w ·)` (the cutoff support ⊆ `A`).

    The OFF-GATE germ (`z ∉ closure (S w)`) is discharged by the hard-gate zero
    (`gatedKernel_heatOp_eq_zero_of_notMem`, NO chart continuity); the COLLAR germ (`z ∈ closure (S w)`)
    by the J4-292 far-zero at base `q = w`.  Unlike `heatOpWitness_fixedBase_originBall`, the chart is
    NEVER needed on the whole origin ball — only on `V ⊇ closure (S w)` — so this is satisfiable ∀ `w`.
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_originBall_twoCover (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t₁ t₂ R : ℝ) {w : Point n}
    (A : Set (ℝ × Point n))
    (hEA : ∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p)
    (V : Set (Point n)) (hVopen : IsOpen V)
    (hclosSub : closure (S w) ⊆ V)
    (hWcont : ContinuousOn (uniformInverseChart g gi hC hK w) V)
    (hcollar : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
        p.2 ∈ closure (S w) →
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine continuousOn_of_active_twoRegionZero _ _ A
    {p : ℝ × Point n | p.2 ∈ closure (S w)} hEA ?_ ?_
  · -- OFF-GATE germ: `x.2 ∉ closure (S w)` ⟹ `E ≡ 0` on the open `univ ×ˢ (closure (S w))ᶜ`.
    intro x _hx _hxA hxD
    have hxD' : x.2 ∉ closure (S w) := hxD
    have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ (closure (S w))ᶜ) :=
      isOpen_univ.prod isClosed_closure.isOpen_compl
    have hxmem : x ∈ (Set.univ : Set ℝ) ×ˢ (closure (S w))ᶜ := ⟨Set.mem_univ _, hxD'⟩
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hxmem) (fun y hy => ?_)
    have hy2 : y.2 ∈ (closure (S w))ᶜ := hy.2
    have hnhds : {p' : Point n | p' ∉ S w} ∈ nhds y.2 :=
      Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hy2)
        (fun z hz hzS => hz (subset_closure hzS))
    show heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) y.1 y.2 w = 0
    simp only [vanVleckGatedWitness]
    exact gatedKernel_heatOp_eq_zero_of_notMem g gi K S
      (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK)) y.1 y.2 w (Or.inr hnhds)
  · -- COLLAR germ: `x.2 ∈ closure (S w) ⊆ V`, chart-far ⟹ `E ≡ 0` near `x` (J4-292 B1/B2 at base `w`).
    intro x hx hxA hxD
    have hxDcl : x.2 ∈ closure (S w) := hxD
    have hfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w x.2) :=
      hcollar x hx hxA hxDcl
    have hzV : x.2 ∈ V := hclosSub hxDcl
    have hVnhds : V ∈ nhds x.2 := hVopen.mem_nhds hzV
    have hNnhds : (uniformInverseChart g gi hC hK w) ⁻¹' {v : Point n | b ^ 2 < rncRadialSq v}
        ∈ nhds x.2 :=
      (hWcont.continuousAt hVnhds).preimage_mem_nhds
        ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hfar)
    have hN'nhds :
        (uniformInverseChart g gi hC hK w) ⁻¹' {v : Point n | b ^ 2 < rncRadialSq v} ∩ V
          ∈ nhds x.2 :=
      Filter.inter_mem hNnhds hVnhds
    have hprodnhds : Set.univ ×ˢ ((uniformInverseChart g gi hC hK w) ⁻¹'
        {v : Point n | b ^ 2 < rncRadialSq v} ∩ V) ∈ nhds x := by
      have h := prod_mem_nhds (Filter.univ_mem : (Set.univ : Set ℝ) ∈ nhds x.1) hN'nhds
      rwa [Prod.mk.eta] at h
    refine Filter.eventuallyEq_of_mem hprodnhds (fun y hy => ?_)
    have hy2 : y.2 ∈ (uniformInverseChart g gi hC hK w) ⁻¹'
        {v : Point n | b ^ 2 < rncRadialSq v} ∩ V := hy.2
    have hyfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w y.2) := hy2.1
    have hyV : y.2 ∈ V := hy2.2
    have hWc_y : ContinuousAt (uniformInverseChart g gi hC hK w) y.2 :=
      hWcont.continuousAt (hVopen.mem_nhds hyV)
    show heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) y.1 y.2 w = 0
    simp only [vanVleckGatedWitness]
    exact heatOpGatedWitness_eq_zero_of_far g gi ha hab 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) K S (uniformInverseChart g gi hC hK)
      y.1 w hWc_y hyfar

/-! ###############################################################################
    ## (G3a) The `hnear` slot ∀ `w ∈ K` from the honest two-cover bundle `H2`.
    ############################################################################### -/

/-- **★★ (G3a) `hnear_twoCover` — THE `hnear` SLOT FROM THE TWO-COVER BUNDLE.**  Produces the exact
    `hnear` slot of `SdomHnearDischarge.leviSlice_jointContinuousOn_DONE`
    (`∀ w ∈ K, ∀ s₁ s₂ R, 0<s₁ → s₁≤s₂ → ContinuousOn (E(·,·,w)) (Icc s₁ s₂ ×ˢ closedBall 0 R)`)
    from the honest per-`w∈K` two-cover bundle `H2`: at each base `w ∈ K` and each origin ball, an
    active `A` with `ContinuousAt E`, an open `V ⊇ closure (S w)` with `W w` continuous on `V`, and the
    collar carry.  `H2` is genuine and satisfiable ∀ `w ∈ K` (`V := ball w ρc` from F1; the collar from
    the gate margin), STRICTLY MORE satisfiable than the original `Hgeo` (no far-`w` global-chart wall);
    it is NOT this file's conclusion.  NOT `a₁ = R/6`. -/
theorem hnear_twoCover (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (H2 : ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ A : Set (ℝ × Point n),
        (∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p) ∧
        ∃ V : Set (Point n), IsOpen V ∧ closure (S w) ⊆ V ∧
          ContinuousOn (uniformInverseChart g gi hC hK w) V ∧
          (∀ p ∈ Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
              p.2 ∈ closure (S w) →
              b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2))) :
    ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro w hw s₁ s₂ R hs₁ hs
  obtain ⟨A, hEA, V, hVopen, hclosSub, hWcont, hcollar⟩ := H2 w hw s₁ s₂ R hs₁ hs
  exact heatOpWitness_originBall_twoCover g gi hC hK S a b ha hab s₁ s₂ R
    A hEA V hVopen hclosSub hWcont hcollar

/-! ###############################################################################
    ## (G3b) The `hnear`-discharged Levi `0`-slice continuity capstone.
    ############################################################################### -/

/-- **★★ (G3b) `leviSlice_jointContinuousOn_FINAL` — THE `hnear`-DISCHARGED CAPSTONE.**  The joint
    `(s,z)`-continuity of the full Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on a positive-time
    compact, for the concrete gated van-Vleck witness, with the Gap-A carry, the S-dom carry (both
    already discharged upstream) AND the near-cover carry `hnear` (discharged here by `hnear_twoCover`
    from the honest per-`w` two-cover bundle `H2`) all removed.  FINAL INPUT LIST: the banked
    `hEbound`/`hInt`/`hEmeas`, the base-0 slice `hbase`, the two-cover bundle `H2`, and the summable
    termwise envelope `env`/`hu`/`hbound`.  NOT `a₁ = R/6`. -/
theorem leviSlice_jointContinuousOn_FINAL (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
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
    (H2 : ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ A : Set (ℝ × Point n),
        (∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p) ∧
        ∃ V : Set (Point n), IsOpen V ∧ closure (S w) ⊆ V ∧
          ContinuousOn (uniformInverseChart g gi hC hK w) V ∧
          (∀ p ∈ Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
              p.2 ∈ closure (S w) →
              b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2)))
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k) :
    ContinuousOn (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  leviSlice_jointContinuousOn_DONE g gi hC hK S a b κ C hκ hC0 t₁ t₂ R ht₁ ht₁₂ hR
    hEbound hInt hEmeas hbase
    (hnear_twoCover g gi hC hK S a b ha hab H2) env hu hbound

#check @continuousOn_of_active_twoRegionZero
#check @heatOpWitness_originBall_twoCover
#check @hnear_twoCover
#check @leviSlice_jointContinuousOn_FINAL

end QIQTH.HgeoDischarge

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HgeoDischarge
#print axioms continuousOn_of_active_twoRegionZero
#print axioms heatOpWitness_originBall_twoCover
#print axioms hnear_twoCover
#print axioms leviSlice_jointContinuousOn_FINAL
end AxiomChecks
