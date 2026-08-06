/-
  HactiveWiring — J4-303: the `hactive` wiring (F5e / A6) for the two-cover Levi endgame.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `QIQTH.FastA5Fix`
  (J4-302) banked the FAST frozen-base full-gate capstone
      `heatOpWitness_fixedBase_fullGate(_chartFree)` :
        `ContinuousOn (fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
            (Icc t₁ t₂ ×ˢ closedBall w R)`
  — E(·,·,w)'s joint continuity on the WHOLE gate compact (plateau ∪ transition annulus), any base
  `w`, at any gate radius `R < ρc` (the chart `C²` radius) with the gate data.

  `QIQTH.H2Instantiation.leviSlice_jointContinuousOn_CONCRETE` (the LIVE consumer, superseding the
  `Hgeo` route) reduces the full Levi `0`-slice joint continuity to two precise residuals, `hgeo`
  (chart `C²` + containment) and `hactive`, where `hactive` is exactly

    ∀ w ∈ K, ∀ s₁ s₂ R, 0<s₁ → s₁≤s₂ →
      ∃ A, (∀ p ∈ A, ContinuousAt (E(·,·,w)) p) ∧
        (∀ p ∈ Icc s₁ s₂ ×ˢ closedBall 0 R, p ∉ A → p.2 ∈ closure (S w) →
            b² < rncRadialSq (W w p.2)),

  with `E(·,·,w) p := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w` and
  `W w := uniformInverseChart g gi hC hK w`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THIS FILE.  `hactive` mixes an ANALYTIC half (per-point `ContinuousAt E`) with a GEOMETRIC half (the
  collar).  We DISCHARGE the analytic half from the banked full-gate capstone and reduce `hactive` to a
  single PURE GEOMETRIC collar residual (no `heatOp`), exactly paralleling how `H2Instantiation`
  reduced the chart half.

    * (W1) `continuousAt_of_continuousOn_gateCompact` — the ContinuousOn → ContinuousAt extraction: the
      full-gate `ContinuousOn f (Icc t₁ t₂ ×ˢ closedBall w R)` yields `ContinuousAt f p` at every
      INTERIOR point `p ∈ Ioo t₁ t₂ ×ˢ ball w R` (the open interior is a neighbourhood contained in the
      compact; `ContinuousOn.continuousAt`).  Pure topology, provider-agnostic.

    * (W1c) `heatOpWitness_fixedBase_continuousAt_interior` — W1 specialized to the concrete gated
      van-Vleck witness `E(·,·,w)`, taking the banked full-gate `ContinuousOn` hypothesis.

    * (W2/W3) `hactive_of_fullGate` — THE `hactive` BUNDLE ∀ `w ∈ K`.  From a single per-`w` carry
      `hfg` bundling (i) the banked full-gate `ContinuousOn E(·,·,w) (Icc t₁ t₂ ×ˢ closedBall w Rg)` at
      a positive gate radius `Rg` on a time window strictly containing the slab, and (ii) the pure
      GEOMETRIC collar `∀ z ∈ closure (S w), z ∉ ball w Rg → b² < rncRadialSq (W w z)`, we produce the
      exact `hactive` shape consumed by `leviSlice_jointContinuousOn_CONCRETE`.  The active set is
      `A := Ioo t₁ t₂ ×ˢ ball w Rg`; the time window `t₁ := s₁/2`, `t₂ := s₂+1` strictly brackets
      `Icc s₁ s₂`, so every off-`A` slab point is off-`A` SPATIALLY (`p.2 ∉ ball w Rg`), whence the
      collar geometry yields the strict far bound.

    * (W3b) `hactive_concrete` — `hfg`'s `ContinuousOn` conjunct DISCHARGED from the banked
      `FastA5Fix.heatOpWitness_fixedBase_fullGate_chartFree`, leaving explicit the honest gate /
      geometry / collar carries.

    * (W4) `leviSlice_hf_cont` — the composition: the full Levi `0`-slice joint continuity
      (`H2Instantiation.leviSlice_jointContinuousOn_CONCRETE`) with `hactive` REPLACED by the full-gate
      bundle `hfg`.  FINAL INPUT LIST: the banked four (`hEbound`/`hInt`/`hEmeas`/`hbase`), the
      summable envelope (`env`/`hu`/`hbound`), the chart/containment residual `hgeo` (I1), and the
      full-gate + collar bundle `hfg`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no vacuous or
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
     existing file edited.  `hfg`'s `ContinuousOn` conjunct is EXACTLY the banked full-gate capstone
     (satisfiable — `FastA5Fix`); `hfg`'s collar conjunct is a pure geometric statement about the
     gate's chart-support (satisfiable — the cutoff support sits inside `ball w Rg`, so points of
     `closure (S w)` beyond it are chart-far).  Neither is this file's conclusion.  **NOT `a₁ = R/6`**
     — this is a regularity / coverage wiring brick; it says NOTHING new about the curvature value.
-/
import Mathlib
import QIQTH.FastA5Fix
import QIQTH.H2Instantiation

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.FastA5Fix QIQTH.FrozenBaseWChain QIQTH.H2Instantiation
open scoped Topology ContDiff

namespace QIQTH.HactiveWiring

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (W1) ContinuousOn on the gate compact ⟹ ContinuousAt on the open interior.
    ############################################################################### -/

/-- **★ (W1) `continuousAt_of_continuousOn_gateCompact`.**  If `f` is `ContinuousOn` the gate compact
    `Icc t₁ t₂ ×ˢ closedBall w R`, then `f` is `ContinuousAt` at every INTERIOR point
    `p ∈ Ioo t₁ t₂ ×ˢ ball w R`: the open interior is a neighbourhood of `p` contained in the compact,
    so `ContinuousOn.continuousAt` applies.  Pure topology, provider-agnostic.  NOT `a₁ = R/6`. -/
theorem continuousAt_of_continuousOn_gateCompact {f : ℝ × Point n → ℝ}
    {t₁ t₂ R : ℝ} {w : Point n}
    (hf : ContinuousOn f (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    {p : ℝ × Point n} (hp1 : p.1 ∈ Set.Ioo t₁ t₂) (hp2 : p.2 ∈ Metric.ball w R) :
    ContinuousAt f p := by
  have hopen : IsOpen (Set.Ioo t₁ t₂ ×ˢ Metric.ball w R) :=
    isOpen_Ioo.prod Metric.isOpen_ball
  have hmem : p ∈ Set.Ioo t₁ t₂ ×ˢ Metric.ball w R := Set.mem_prod.mpr ⟨hp1, hp2⟩
  have hsub : Set.Ioo t₁ t₂ ×ˢ Metric.ball w R ⊆
      Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R :=
    Set.prod_mono Set.Ioo_subset_Icc_self Metric.ball_subset_closedBall
  have hnhds : Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R ∈ nhds p :=
    Filter.mem_of_superset (hopen.mem_nhds hmem) hsub
  exact hf.continuousAt hnhds

/-- **★ (W1c) `heatOpWitness_fixedBase_continuousAt_interior`.**  W1 specialized to the concrete
    gated van-Vleck witness heat operator `E(·,·,w)`: given the banked full-gate `ContinuousOn`
    (`FastA5Fix.heatOpWitness_fixedBase_fullGate`) on `Icc t₁ t₂ ×ˢ closedBall w Rg`, `E(·,·,w)` is
    `ContinuousAt` at every interior point.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_continuousAt_interior (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ Rg : ℝ) (w : Point n)
    (hE : ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w Rg))
    {p : ℝ × Point n} (hp1 : p.1 ∈ Set.Ioo t₁ t₂) (hp2 : p.2 ∈ Metric.ball w Rg) :
    ContinuousAt (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p :=
  continuousAt_of_continuousOn_gateCompact hE hp1 hp2

/-! ###############################################################################
    ## (W2/W3) THE `hactive` BUNDLE ∀ `w ∈ K` from the full-gate + collar carry.
    ############################################################################### -/

/-- **★★★ (W2/W3) `hactive_of_fullGate` — THE `hactive` BUNDLE.**  Produces the exact `hactive` shape
    consumed by `H2Instantiation.leviSlice_jointContinuousOn_CONCRETE` from a single per-`w` carry `hfg`
    bundling, for a positive-time window, (i) the banked full-gate `ContinuousOn E(·,·,w)` on
    `Icc t₁ t₂ ×ˢ closedBall w Rg` at a positive gate radius `Rg` (= `FastA5Fix.…_fullGate`), and (ii)
    the pure GEOMETRIC collar `∀ z ∈ closure (S w), z ∉ ball w Rg → b² < rncRadialSq (W w z)`.

    Construction: at slab `Icc s₁ s₂` pick the strictly-bracketing window `t₁ := s₁/2`, `t₂ := s₂+1`
    and set `A := Ioo t₁ t₂ ×ˢ ball w Rg`.  The ANALYTIC half (`ContinuousAt E` on `A`) is W1 applied
    to `hfg`'s `ContinuousOn`; the collar half is pure geometry: every slab point has time in
    `Ioo t₁ t₂`, so off-`A` ⟹ off-`A` SPATIALLY (`p.2 ∉ ball w Rg`), whence `hfg`'s collar delivers the
    strict far bound.  `hfg`'s `ContinuousOn` conjunct is the banked capstone (satisfiable); its collar
    conjunct is the honest geometric residual.  Neither is this conclusion.  NOT `a₁ = R/6`. -/
theorem hactive_of_fullGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hfg : ∀ w ∈ K, ∀ t₁ t₂ : ℝ, 0 < t₁ →
      ∃ Rg : ℝ, 0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w Rg) ∧
        (∀ z ∈ closure (S w), z ∉ Metric.ball w Rg →
            b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z))) :
    ∀ w ∈ K, ∀ s₁ s₂ R : ℝ, 0 < s₁ → s₁ ≤ s₂ →
      ∃ A : Set (ℝ × Point n),
        (∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p) ∧
        (∀ p ∈ Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
            p.2 ∈ closure (S w) →
            b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2)) := by
  intro w hw s₁ s₂ R hs₁ hs
  obtain ⟨Rg, hRg, hcont, hcollar⟩ := hfg w hw (s₁ / 2) (s₂ + 1) (half_pos hs₁)
  refine ⟨Set.Ioo (s₁ / 2) (s₂ + 1) ×ˢ Metric.ball w Rg, ?_, ?_⟩
  · intro p hpA
    exact continuousAt_of_continuousOn_gateCompact hcont
      (Set.mem_prod.mp hpA).1 (Set.mem_prod.mp hpA).2
  · intro p hp hpA hpS
    have hp1 : p.1 ∈ Set.Icc s₁ s₂ := (Set.mem_prod.mp hp).1
    obtain ⟨hl, hr⟩ := hp1
    have hp1' : p.1 ∈ Set.Ioo (s₁ / 2) (s₂ + 1) :=
      ⟨lt_of_lt_of_le (half_lt_self hs₁) hl, lt_of_le_of_lt hr (by linarith)⟩
    have hp2notball : p.2 ∉ Metric.ball w Rg :=
      fun hb => hpA (Set.mem_prod.mpr ⟨hp1', hb⟩)
    exact hcollar p.2 hpS hp2notball

/-! ###############################################################################
    ## (W4) The full Levi `0`-slice continuity with `hactive` replaced by `hfg`.
    ############################################################################### -/

/-- **★★ (W4) `leviSlice_hf_cont` — THE `hactive`-DISCHARGED LEVI `0`-SLICE CONTINUITY.**  The joint
    `(s,z)`-continuity of the full Levi `0`-slice `p ↦ leviSeries E p.1 p.2 0` on a positive-time
    compact, for the concrete gated van-Vleck witness, with `H2Instantiation`'s `hactive` REPLACED by
    the full-gate + collar bundle `hfg` (discharged via W2).  FINAL INPUT LIST: the banked
    `hEbound`/`hInt`/`hEmeas`, the base-0 slice `hbase`, the chart/containment residual `hgeo` (I1), the
    full-gate + collar bundle `hfg`, and the summable termwise envelope `env`/`hu`/`hbound`.  Neither
    `hgeo` nor `hfg` is the conclusion; both are genuine and satisfiable (see header).  NOT `a₁ = R/6`. -/
theorem leviSlice_hf_cont (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hgeo : ∀ w ∈ K, ∃ ρc : ℝ, 0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc) ∧
      closure (S w) ⊆ Metric.ball w ρc)
    (hfg : ∀ w ∈ K, ∀ t₁ t₂ : ℝ, 0 < t₁ →
      ∃ Rg : ℝ, 0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w Rg) ∧
        (∀ z ∈ closure (S w), z ∉ Metric.ball w Rg →
            b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z)))
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k) :
    ContinuousOn (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  leviSlice_jointContinuousOn_CONCRETE g gi hC hK S a b ha hab κ C hκ hC0 t₁ t₂ R ht₁ ht₁₂ hR
    hEbound hInt hEmeas hbase hgeo
    (hactive_of_fullGate g gi hC hK S a b hfg) env hu hbound

/-! ###############################################################################
    ## (W3b) The full-gate + collar bundle `hfg` with `ContinuousOn` DISCHARGED.
    ############################################################################### -/

/-- **★★ (W3b) `hactive_concrete` — `hfg`'s `ContinuousOn` DISCHARGED from the banked capstone.**
    Produces the full-gate + collar bundle `hfg` (the input of W2/W4) with the `ContinuousOn` conjunct
    no longer carried but DERIVED from `FastA5Fix.heatOpWitness_fixedBase_fullGate_chartFree`: given the
    global coefficient regularity (`hw`/`hΘc`/`hΘne`/`huc`) and, per `w ∈ K` and time window, an honest
    gate/geometry/collar bundle `hgate` supplying a gate radius `Rg < ρc` (the internal chart `C²`
    radius) with the gate data (openness, `closedBall w Rg ⊆ S w`), the geometry continuities, the
    metric symmetry, and the pure geometric collar, the full-gate `ContinuousOn` is produced by the
    banked chart-free capstone.  The only residuals left are the genuine gate/geometry/collar carries;
    none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hactive_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w', vanVleck g w' ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgate : ∀ w ∈ K, ∀ t₁ t₂ : ℝ, 0 < t₁ → ∀ ρc : ℝ, 0 < ρc →
      ∃ Rg : ℝ, 0 < Rg ∧ Rg < ρc ∧
        IsOpen (S w) ∧ Metric.closedBall w Rg ⊆ S w ∧
        (∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w Rg)) ∧
        (∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w Rg)) ∧
        (∀ z i j, gi z i j = gi z j i) ∧
        (∀ z ∈ closure (S w), z ∉ Metric.ball w Rg →
            b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z))) :
    ∀ w ∈ K, ∀ t₁ t₂ : ℝ, 0 < t₁ →
      ∃ Rg : ℝ, 0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w Rg) ∧
        (∀ z ∈ closure (S w), z ∉ Metric.ball w Rg →
            b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z)) := by
  intro w hwK t₁ t₂ ht₁
  obtain ⟨ρc, hρc, hbig⟩ :=
    heatOpWitness_fixedBase_fullGate_chartFree g gi hC hK S a b t₁ t₂ ht₁ hwK hw hΘc hΘne huc
  obtain ⟨Rg, hRg, hRgρc, hSopen, hsub, hgiC, hChrC, hsymm, hcollar⟩ :=
    hgate w hwK t₁ t₂ ht₁ ρc hρc
  exact ⟨Rg, hRg, hbig Rg hRg hRgρc hSopen hsub hgiC hChrC hsymm, hcollar⟩

#check @continuousAt_of_continuousOn_gateCompact
#check @heatOpWitness_fixedBase_continuousAt_interior
#check @hactive_of_fullGate
#check @hactive_concrete
#check @leviSlice_hf_cont

end QIQTH.HactiveWiring

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HactiveWiring
#print axioms continuousAt_of_continuousOn_gateCompact
#print axioms heatOpWitness_fixedBase_continuousAt_interior
#print axioms hactive_of_fullGate
#print axioms hactive_concrete
#print axioms leviSlice_hf_cont
end AxiomChecks
