/-
  ChartCoherentDerivativeFieldRepresentative — J4-1130: dispatch 8 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, target-facing
  value/`fderiv`/carrier consumer triple J4-1126, literal coordinate-line `HasDerivAt` transfer
  J4-1127, first-order coefficient-field agreement J4-1128, second-order (`Qfield`) agreement
  J4-1129, per `gpt-5.6-sol` high consult 2026-08-24 x8).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1123–J4-1129 all reasoned about ARBITRARY candidate coefficient fields `Pfield`/`Qfield`
  (universally quantified inputs), establishing well-definedness ("IF two candidates witness the
  respective charts' derivatives THEN they agree on the overlap") without ever CONSTRUCTING a
  concrete candidate. Per Sol's J4-1129 scoped plan, this dispatch supplies the first genuinely
  CONCRETE, `fderiv`-built representative — for a SINGLE seed `(z₀,v₀)`, fixed coordinate `k` — of
  the exact `Pfield` shape `ChartJointBorel.lean`'s `hcarField` existential asks for:

    `∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ jj, Measurable (fun w : ℝ×Point n×Point n => Pfield w.2.2 w.2.1 jj)) ∧
        (∀ w, w.2.2 ∈ K → 0 < w.1 → … ∧ (∀ jj, HasDerivAt (fun s => uniformInverseChart …
          (Function.update w.2.1 k s) jj) (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧ …)`

  restricted to a genuine OPEN neighbourhood `U` of the seed's image point, exactly mirroring how
  `hChartRep` in `ChartJointBorel.chartJoint_measurable_of_rep` reduces the GLOBAL chart wall to a
  single representative obligation — this dispatch discharges the analogous obligation for the
  DERIVATIVE coefficient field, at the single-seed / single-open-piece level (the piecewise/global
  gluing across many such seeds, covering all of `K`, is the NEXT dispatch, per Sol).

  ## The construction (per `gpt-5.6-sol` high consult, 2026-08-24, eighth consult).

  Sol flagged one load-bearing correction to the naive plan: a per-fixed-`q` "`ContinuousOn` on the
  `p`-slice" fact is NOT enough for global measurability — one needs JOINT continuity of the
  representative in `(q,p)` on an OPEN set. The fix: build the representative as the JOINT `fderiv`
  of `chartCoherent`'s `jj`-component evaluated at the FIXED direction `(0, Pi.single k 1)` (varying
  only the second/field slot, coordinate `k`) — `ContDiffOn.fderiv_of_isOpen` gives this joint
  `fderiv` map itself `ContinuousOn` an open set, and `ContinuousOn.clm_apply` (evaluating at a
  CONSTANT direction) preserves joint continuity. Concretely:

    1. `pd_hasDerivAt` — a new, generic, reusable bridge lemma: `DifferentiableAt ℝ f x` gives the
       literal coordinate-line `HasDerivAt (fun s ↦ f (Function.update x i s)) (pd f i x) (x i)`
       (the converse direction of the existing `pd_eq_fderiv`'s internal chain-rule step, exposed
       as standalone API — `hasDerivAt_update` + `HasFDerivAt.comp_hasDerivAt`).
    2. From `generalCenter_coherent_joint_chart`'s seed `ContDiffAt ℝ 2 (joint chartCoherent) ξ₀`,
       extract (`ContDiffAt.contDiffOn` + `mem_nhds_iff`) a genuine OPEN set `U0 ∋ ξ₀` on which
       `chartCoherent` is jointly `ContDiffOn ℝ 2` (not merely `ContDiffAt` at the one point).
    3. From `uniformInverseChart_agree_chartCoherent_uniform`'s germ fact, extract (`mem_nhds_iff`)
       a second OPEN set `V0 ∋ ξ₀` on which `uniformInverseChart = chartCoherent` POINTWISE.
    4. `W := U0 ∩ V0` is open, `ξ₀ ∈ W`, and carries BOTH facts. Define, for the fixed coordinate
       `k`, the CONCRETE representative `PfieldRep ξ jj := fderiv ℝ (fun η ↦ chartCoherent η.1 η.2
       jj) ξ (0, Pi.single k 1)` — literally `fderiv`-built from `chartCoherent`, no
       `Classical.choose`. `ContDiffOn.fderiv_of_isOpen` + `ContinuousOn.clm_apply` give JOINT
       `ContinuousOn (fun ξ ↦ PfieldRep ξ jj) W`.
    5. The coordinate-line `HasDerivAt` fact for `chartCoherent` at `PfieldRep ξ jj` follows by
       composing `chartCoherent`'s `HasFDerivAt` at `ξ` (from step 2's `ContDiffOn`) with the
       coordinate-line map's own `HasDerivAt (0, Pi.single k 1)` (`HasDerivAt.prodMk` of a constant
       first slot and `hasDerivAt_update` on the second) via `HasFDerivAt.comp_hasDerivAt`.
    6. Transfer that fact to `uniformInverseChart` via the pointwise equality on `W` (step 3),
       upgraded to a coordinate-line curve-level `EventuallyEq` (continuity of the coordinate-line
       map landing back in the open `W`) and closed with `HasDerivAt.congr_of_eventuallyEq` — the
       SAME technique J4-1127's (private, file-local) `hasDerivAt_coordLine_iff_of_germ` uses,
       re-derived here (that helper is `private` to its own file, so not reusable directly).
    7. GLOBAL measurability: `W` open ⟹ `MeasurableSet W` ⟹ `MeasurableEmbedding.subtype_coe` gives
       a measurable embedding `W ↪ Point n × Point n`; step 4's joint `ContinuousOn` restricts to a
       genuine `Continuous` map on the subtype `W` (`ContinuousOn.restrict`), hence `Measurable`
       (`Continuous.measurable`); `MeasurableEmbedding.measurable_extend` (Sol's flagged exact API)
       extends this to a GLOBAL `Measurable` function on all of `Point n × Point n` (junk value `0`
       off `W`), agreeing with `PfieldRep` on `W` by `Function.Injective.extend_apply`. Composing
       with the measurable swap `w ↦ (w.2.2, w.2.1)` gives the exact `hcarField` measurability
       shape.

  Sol confirmed (eighth consult): raw `PfieldRep`, as a totally junk-valued `fderiv`, is NOT
  provably globally measurable from these hypotheses alone (no control of `chartCoherent` off `W`)
  — the honest, standard fix is exactly the zero-extension-via-`MeasurableEmbedding` route above,
  NOT a `Set.piecewise` on the raw total function (which would circularly require global
  measurability of the un-extended piece). No sympy check triggered: pure differentiation /
  measurable-embedding composition from already-established `ContDiffAt`/germ facts, matching all
  eight prior dispatches in this sub-campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. No `sorry`, no new axioms, no vacuous/unsatisfiable
  hypotheses, no existing file edited. This is a SINGLE-SEED, SINGLE-open-piece representative —
  it does NOT cover all of `K` (the piecewise/global gluing across many seeds — the next dispatch,
  per Sol — is required before this can literally instantiate `hcarField`'s `∀ w, w.2.2 ∈ K → …`
  universal quantifier over all of `K`). It also does NOT yet address the `Qfield` (second-order)
  shape, nor the `IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2`/`PdiffAt` conjuncts (which concern the
  AMPLITUDE `chartFieldAmp`, a wholly separate obligation outside the chart-overlap machinery this
  sub-campaign targets). `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.
-/
import Mathlib
import QIQTH.ChartOverlapUniquenessGeneralCenter

open MeasureTheory Filter

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-! ###############################################################################
    ## Step 1 — the generic `pd_hasDerivAt` bridge (new, reusable).
    ############################################################################### -/

/-- **★ `pd_hasDerivAt` — the converse direction of `pd_eq_fderiv`, exposed as standalone API.**
    If a scalar field `f : Point n → ℝ` is `DifferentiableAt ℝ f x`, the coordinate-line curve
    `s ↦ f (Function.update x i s)` literally `HasDerivAt` value `pd f i x` at `s = x i`. Built
    from `hasDerivAt_update` (Mathlib) chained through `HasFDerivAt.comp_hasDerivAt`, exactly
    mirroring `pd_eq_fderiv`'s own internal chain-rule step (there discarded via `.deriv`; here
    exposed as the full `HasDerivAt` proposition itself). -/
theorem pd_hasDerivAt (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun s : ℝ => f (Function.update x i s)) (pd f i x) (x i) := by
  have hu : HasDerivAt (Function.update x i) (Pi.single i (1 : ℝ)) (x i) := hasDerivAt_update x i (x i)
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]; exact hf.hasFDerivAt
  have hcomp := hf'.comp_hasDerivAt (x i) hu
  rw [pd_eq_fderiv f i x hf]
  simpa only [Function.comp] using hcomp

/-! ###############################################################################
    ## Step 2 — pointwise `EqOn` on an open set transfers coordinate-line `HasDerivAt`.
    ############################################################################### -/

/-- **Private helper — pointwise `EqOn` on an OPEN set congrs a coordinate-line `HasDerivAt`.**
    If `F G : Point n → Point n → Point n` agree pointwise (jointly) throughout an OPEN set `W`,
    then at any `ξ ∈ W`, any coordinate `k`, any output component `jj`, a coordinate-line
    `HasDerivAt` fact for `F`'s curve transfers to the SAME fact for `G`'s curve. The coordinate
    line `s ↦ (ξ.1, Function.update ξ.2 k s)` is continuous and lands at `ξ ∈ W` when `s = ξ.2 k`
    (`Function.update_eq_self`), so it stays in `W` for `s` near `ξ.2 k`
    (`ContinuousAt.eventually_mem`), giving a curve-level `EventuallyEq` that
    `HasDerivAt.congr_of_eventuallyEq` closes. -/
private lemma coordLine_hasDerivAt_congr_of_eqOn_open {F G : Point n → Point n → Point n}
    {W : Set (Point n × Point n)} (hWopen : IsOpen W)
    (hEq : Set.EqOn (fun ζ : Point n × Point n => F ζ.1 ζ.2) (fun ζ => G ζ.1 ζ.2) W)
    {ξ : Point n × Point n} (hξ : ξ ∈ W) (k jj : Fin n) {d : ℝ}
    (hFd : HasDerivAt (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k)) :
    HasDerivAt (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k) := by
  have hcontLine : ContinuousAt
      (fun s : ℝ => ((ξ.1, Function.update ξ.2 k s) : Point n × Point n)) (ξ.2 k) :=
    (continuous_const.prodMk (continuous_const.update k continuous_id)).continuousAt
  have hmem0 : ((ξ.1, Function.update ξ.2 k (ξ.2 k)) : Point n × Point n) = ξ := by
    rw [Function.update_eq_self]
  have heventually : ∀ᶠ s in nhds (ξ.2 k),
      ((ξ.1, Function.update ξ.2 k s) : Point n × Point n) ∈ W := by
    have hWnhds : W ∈ nhds ((ξ.1, Function.update ξ.2 k (ξ.2 k)) : Point n × Point n) := by
      rw [hmem0]; exact hWopen.mem_nhds hξ
    exact hcontLine.eventually_mem hWnhds
  have hcurveEq : (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s) jj)
      =ᶠ[nhds (ξ.2 k)] (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) := by
    filter_upwards [heventually] with s hs
    exact congrFun (hEq hs) jj
  exact hFd.congr_of_eventuallyEq hcurveEq.symm

/-! ###############################################################################
    ## The main capstone — the concrete, `fderiv`-built, measurable representative.
    ############################################################################### -/

/-- **★★ J4-1130 — `chartCoherent_pfield_representative_single_seed`: a CONCRETE, `fderiv`-built,
    globally-`Measurable` derivative-coefficient representative, at a single seed and a single
    coordinate `k`.** For every interior base `z₀`, every velocity `v₀` below the derived
    invertibility radius `r₀`, and every coordinate `k`, there is a GLOBALLY `Measurable` field
    `Pfield : Point n → Point n → Fin n → ℝ` and a genuine OPEN neighbourhood `U` of the seed's
    image point `(z₀, exp z₀ v₀)` such that `Pfield` literally witnesses `uniformInverseChart`'s
    `k`-coordinate-line derivative throughout `U` — the exact shape `ChartJointBorel.lean`'s
    `hcarField` existential (at coordinate `k`) asks for, restricted to this single open piece.
    `Pfield` is built by zero-extending, off a genuine open set `W` where the construction is
    live, the joint `fderiv` of a coherently-built inverse chart `chartCoherent` (from
    `uniformInverseChart_agree_chartCoherent_uniform`) evaluated at the fixed direction
    `(0, Pi.single k 1)` — no `Classical.choose` beyond `chartCoherent`'s own IFT construction. -/
theorem chartCoherent_pfield_representative_single_seed
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∀ z₀ : Point n, z₀ ∈ interior K → ∀ v₀ : Point n, ‖v₀‖ < r₀ → ∀ k : Fin n,
      ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ jj : Fin n, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj)) ∧
        ∃ U : Set (Point n × Point n), IsOpen U ∧
          ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U ∧
          (∀ ξ ∈ U, ∀ jj : Fin n,
            HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
              (Pfield ξ.1 ξ.2 jj) (ξ.2 k)) := by
  classical
  obtain ⟨r₀, hr₀pos, hall⟩ := uniformInverseChart_agree_chartCoherent_uniform g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ k
  obtain ⟨chartCoherent, hcd, _hval, hgerm⟩ := hall z₀ hz₀ v₀ hv₀
  set ξ₀ : Point n × Point n := (z₀, uniformFlowExp g gi hC hK z₀ v₀) with hξ₀def
  -- (2) an OPEN set `U0 ∋ ξ₀` on which `chartCoherent` is jointly `ContDiffOn ℝ 2`.
  obtain ⟨u, hunhds, hucd⟩ := hcd.contDiffOn (le_refl (2 : WithTop ℕ∞)) (by simp)
  obtain ⟨U0, hU0sub, hU0open, hU0mem⟩ := mem_nhds_iff.mp hunhds
  have hU0cd : ContDiffOn ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) U0 :=
    hucd.mono hU0sub
  -- (3) an OPEN set `V0 ∋ ξ₀` on which `uniformInverseChart = chartCoherent` pointwise.
  obtain ⟨V0, hV0sub, hV0open, hV0mem⟩ := mem_nhds_iff.mp (Filter.eventually_iff.mp hgerm)
  -- (4) `W := U0 ∩ V0` carries both facts.
  set W : Set (Point n × Point n) := U0 ∩ V0 with hWdef
  have hWopen : IsOpen W := hU0open.inter hV0open
  have hWmem : ξ₀ ∈ W := ⟨hU0mem, hV0mem⟩
  have hWcd : ContDiffOn ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2) W :=
    hU0cd.mono Set.inter_subset_left
  have hWeq : Set.EqOn (fun ζ : Point n × Point n => chartCoherent ζ.1 ζ.2)
      (fun ζ : Point n × Point n => uniformInverseChart g gi hC hK ζ.1 ζ.2) W := by
    intro ζ hζ
    exact (hV0sub (Set.inter_subset_right hζ)).symm
  -- the concrete representative and its joint continuity, per component `jj`.
  have hFjjCD : ∀ jj : Fin n,
      ContDiffOn ℝ 2 (fun ξ : Point n × Point n => chartCoherent ξ.1 ξ.2 jj) W :=
    fun jj => (contDiff_apply ℝ ℝ jj).comp_contDiffOn hWcd
  set PfieldRep : Point n × Point n → Fin n → ℝ := fun ξ jj =>
      fderiv ℝ (fun η : Point n × Point n => chartCoherent η.1 η.2 jj) ξ
        ((0, Pi.single k (1 : ℝ)) : Point n × Point n) with hPfieldRepDef
  have hcontOn : ∀ jj : Fin n, ContinuousOn (fun ξ : Point n × Point n => PfieldRep ξ jj) W := by
    intro jj
    have hfd : ContDiffOn ℝ 1
        (fun ξ : Point n × Point n => fderiv ℝ (fun η => chartCoherent η.1 η.2 jj) ξ) W :=
      (hFjjCD jj).fderiv_of_isOpen hWopen (by norm_num)
    exact hfd.continuousOn.clm_apply continuousOn_const
  -- the coordinate-line `HasDerivAt` fact for `chartCoherent` throughout `W`.
  have hDerivChart : ∀ ξ ∈ W, ∀ jj : Fin n,
      HasDerivAt (fun s : ℝ => chartCoherent ξ.1 (Function.update ξ.2 k s) jj)
        (PfieldRep ξ jj) (ξ.2 k) := by
    intro ξ hξ jj
    have hdiffAt : DifferentiableAt ℝ (fun η : Point n × Point n => chartCoherent η.1 η.2 jj) ξ :=
      ((hFjjCD jj).differentiableOn (by norm_num)).differentiableAt (hWopen.mem_nhds hξ)
    have hFfd : HasFDerivAt (fun η : Point n × Point n => chartCoherent η.1 η.2 jj)
        (fderiv ℝ (fun η => chartCoherent η.1 η.2 jj) ξ) ξ := hdiffAt.hasFDerivAt
    have hFfd' : HasFDerivAt (fun η : Point n × Point n => chartCoherent η.1 η.2 jj)
        (fderiv ℝ (fun η => chartCoherent η.1 η.2 jj) ξ)
        ((ξ.1, Function.update ξ.2 k (ξ.2 k)) : Point n × Point n) := by
      rw [Function.update_eq_self]; exact hFfd
    have hLine : HasDerivAt (fun s : ℝ => ((ξ.1, Function.update ξ.2 k s) : Point n × Point n))
        ((0, Pi.single k (1 : ℝ)) : Point n × Point n) (ξ.2 k) :=
      (hasDerivAt_const (ξ.2 k) ξ.1).prodMk (hasDerivAt_update ξ.2 k (ξ.2 k))
    have hcomp := hFfd'.comp_hasDerivAt (ξ.2 k) hLine
    simpa only [Function.comp, hPfieldRepDef] using hcomp
  -- transfer to `uniformInverseChart` throughout `W`.
  have hDerivUniform : ∀ ξ ∈ W, ∀ jj : Fin n,
      HasDerivAt
        (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
        (PfieldRep ξ jj) (ξ.2 k) :=
    fun ξ hξ jj =>
      coordLine_hasDerivAt_congr_of_eqOn_open hWopen hWeq hξ k jj (hDerivChart ξ hξ jj)
  -- (7) global measurability, via the zero-extension along the open measurable embedding `W ↪ …`.
  have hWmeasSet : MeasurableSet W := hWopen.measurableSet
  have hEmb : MeasurableEmbedding (Subtype.val : W → Point n × Point n) :=
    MeasurableEmbedding.subtype_coe hWmeasSet
  have hgMeas : ∀ jj : Fin n, Measurable (fun ζ : W => PfieldRep ζ.1 jj) := by
    intro jj
    exact ((hcontOn jj).restrict).measurable
  set PfieldGlobal : Fin n → Point n × Point n → ℝ := fun jj =>
      Function.extend (Subtype.val : W → Point n × Point n)
        (fun ζ : W => PfieldRep ζ.1 jj) (fun _ => 0) with hPfieldGlobalDef
  have hPfieldGlobalMeas : ∀ jj : Fin n, Measurable (PfieldGlobal jj) :=
    fun jj => hEmb.measurable_extend (hgMeas jj) measurable_const
  have hPfieldGlobalAgree : ∀ ξ ∈ W, ∀ jj : Fin n, PfieldGlobal jj ξ = PfieldRep ξ jj := by
    intro ξ hξ jj
    exact Subtype.coe_injective.extend_apply (fun ζ : W => PfieldRep ζ.1 jj) (fun _ => 0)
      (⟨ξ, hξ⟩ : W)
  -- assemble the final `Pfield`, `U := W`.
  refine ⟨fun q p jj => PfieldGlobal jj (q, p), ?_, W, hWopen, hWmem, ?_⟩
  · intro jj
    have hswap : Measurable (fun w : ℝ × Point n × Point n =>
        ((w.2.2, w.2.1) : Point n × Point n)) :=
      Measurable.prodMk measurable_snd.snd measurable_snd.fst
    exact (hPfieldGlobalMeas jj).comp hswap
  · intro ξ hξ jj
    have hval : PfieldGlobal jj (ξ.1, ξ.2) = PfieldRep ξ jj := by
      have := hPfieldGlobalAgree ξ hξ jj
      simpa using this
    show HasDerivAt
        (fun s : ℝ => uniformInverseChart g gi hC hK ξ.1 (Function.update ξ.2 k s) jj)
        (PfieldGlobal jj (ξ.1, ξ.2)) (ξ.2 k)
    rw [hval]
    exact hDerivUniform ξ hξ jj

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms pd_hasDerivAt
#print axioms chartCoherent_pfield_representative_single_seed
end AxiomChecks
