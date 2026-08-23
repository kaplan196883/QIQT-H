/-
  ChartOverlapQfieldAgreementTwoSeeds — J4-1129: dispatch 7 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, target-facing
  value/`fderiv`/carrier consumer triple J4-1126, literal coordinate-line `HasDerivAt` transfer
  J4-1127, first-order coefficient-field agreement J4-1128, per `gpt-5.6-sol` high consult
  2026-08-24 x7).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1128 built `chartCoherent_field_agree_at_overlap_two_seeds`: IF candidate coefficient fields
  `P1`/`P2` respectively witness `chartCoherent1`'s/`chartCoherent2`'s `k`-coordinate-line
  derivatives throughout `U1`/`U2`, THEN `P1` and `P2` agree POINTWISE on the overlap `U1 ∩ U2`.
  J4-1128 explicitly left `ChartJointBorel.lean`'s `hcarField2` `Qfield` conjunct open: `Qfield` is
  the SECOND derivative — the `i`-coordinate-line derivative of `Pjfield` ITSELF (`Pjfield` already
  being the `j`-coordinate-line derivative of the chart map), and the J4-1128 pointwise fact alone
  is not enough to differentiate again.

  This dispatch closes that gap by the "one level up" route Sol confirmed in the pre-Lean consult
  (2026-08-24, seventh consult): (1) upgrade J4-1128's pointwise overlap agreement to a genuine
  filter-GERM equality at each overlap point, via the SAME open-set argument J4-1125 already used
  (`filter_upwards` off `(hU1open.inter hU2open).mem_nhds hξ`); (2) push that germ equality along
  the `i`-coordinate-line map exactly as J4-1127's `hasDerivAt_coordLine_iff_of_germ` does, giving
  a coordinate-line `HasDerivAt ↔ HasDerivAt` transfer for `Pjfield1`/`Pjfield2` themselves (not
  just for `chartCoherent1`/`chartCoherent2`); (3) combine with `HasDerivAt.unique` exactly as
  J4-1128 did, now one derivative order higher, to conclude `Qfield1 = Qfield2` on the overlap.

  Sol confirmed (pre-Lean, load-bearing question (A)): **no genuine new second-order obstruction**.
  The construction is mechanically parallel to J4-1127/J4-1128 — no independent differentiability
  or continuity of `Pjfield1`/`Pjfield2` needs to be established from scratch; the `HasDerivAt`
  witnesses for `Qfield1`/`Qfield2` supply all needed differentiability data as hypotheses (exactly
  mirroring how J4-1128 took `hP1`/`hP2` as hypothesis-supplied witnesses rather than deriving
  existence). Germ congruence only TRANSPORTS a witness across an already-established local
  equality; it does not need to prove differentiability independently. No circularity: step (1)'s
  pointwise agreement comes from the (separately supplied) FIRST-order witnessing hypotheses via
  J4-1128; step (1)'s germ upgrade needs only openness of `U1 ∩ U2` (already banked); step (3)'s
  `Qfield` conclusion comes from the SEPARATELY supplied second-order witnessing hypotheses. Sol
  also confirmed no sympy/quantitative check is relevant here (pure filter/calculus congruence,
  matching all six prior dispatches).

  ## Packaging (per Sol's recommendation).

  Two layers, as Sol suggested: (i) a GENERIC private helper `scalar_coordLine_hasDerivAt_iff_of_pointwise_eq_open`,
  chart-agnostic — given ANY `F G : Point n → Point n → Fin n → ℝ` pointwise-agreeing on an OPEN
  set `U`, transfers coordinate-line `HasDerivAt` statements for `F`/`G` at any `ξ ∈ U`; this is
  exactly J4-1127's coordinate-line congruence technique, specialized to already-scalar-valued
  fields (no output-component extraction step needed, since `F ξ.1 ξ.2 jj : ℝ` already); (ii) the
  chart-specific theorem `chartCoherent_Qfield_agree_at_overlap_two_seeds`, which internally invokes
  J4-1128 (at coordinate `j`) to get the `Pjfield1 = Pjfield2` pointwise premise the generic helper
  needs, then applies the generic helper once to the `Qfield1`/`Qfield2` witnesses.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure logical/filter/calculus-congruence upgrade built on the
  already-banked `ChartOverlapCoefficientAgreementTwoSeeds.lean` first-order fact — no new
  analytic estimate, no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses (the candidate
  fields `Pjfield1`/`Pjfield2`/`Qfield1`/`Qfield2` are universally quantified inputs, not asserted
  to exist; the conclusion is the correct conditional "IF both witness their respective chart's
  first- and second-order derivatives on `U1`/`U2` THEN the second derivatives agree on the
  overlap" shape), no existing file edited. Does NOT yet supply a concrete
  `Pfield`/`Pifield`/`Pjfield`/`Qfield`/measurability representative for `hcarField`/`hcarField2`
  (Sol's flagged next dispatch, J4-1130: an explicit `fderiv`-built concrete representative with
  measurability, PRIOR to the piecewise/global gluing of the two charts — Sol's estimate: roughly
  5-9 further dispatches remain in the original 10-20 budget, i.e. ~12-16 total).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartOverlapCoefficientAgreementTwoSeeds

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Shared helper — pointwise agreement on an open set forces a coordinate-line `HasDerivAt`
    transfer (one level up from J4-1127's chart-level version).** If two SCALAR-valued coefficient
    fields `F G : Point n → Point n → Fin n → ℝ` agree pointwise (at every output component `jj`)
    throughout an OPEN set `U`, then for any `ξ ∈ U`, any coordinate `i`, any output component `jj`,
    and any candidate derivative value `d`, the `i`-coordinate-line derivative statement (base
    point `ξ.1` frozen, second argument varying only in coordinate `i`, evaluated at component
    `jj`) transfers between `F` and `G`. Proof: openness + pointwise agreement gives a filter germ
    at `ξ` (mirroring J4-1125's technique); the germ is sliced to the `ξ.1`-fixed fiber and pushed
    along the coordinate-line map exactly as J4-1127's `hasDerivAt_coordLine_iff_of_germ`, closing
    via `Filter.EventuallyEq.hasDerivAt_iff` (no output-component extraction needed here, since `F`
    and `G` are already scalar-valued once `jj` is fixed). -/
private lemma scalar_coordLine_hasDerivAt_iff_of_pointwise_eq_open
    {F G : Point n → Point n → Fin n → ℝ} {U : Set (Point n × Point n)} (hUopen : IsOpen U)
    (heq : ∀ ξ ∈ U, ∀ jj : Fin n, F ξ.1 ξ.2 jj = G ξ.1 ξ.2 jj)
    {ξ : Point n × Point n} (hξ : ξ ∈ U) (i jj : Fin n) (d : ℝ) :
    HasDerivAt (fun s : ℝ => F ξ.1 (Function.update ξ.2 i s) jj) d (ξ.2 i) ↔
    HasDerivAt (fun s : ℝ => G ξ.1 (Function.update ξ.2 i s) jj) d (ξ.2 i) := by
  have hgerm : (fun η : Point n × Point n => F η.1 η.2 jj)
      =ᶠ[nhds ξ] (fun η : Point n × Point n => G η.1 η.2 jj) := by
    filter_upwards [hUopen.mem_nhds hξ] with η hη using heq η hη jj
  -- Slice the joint germ down to the `ξ.1`-fixed fiber via the continuous inclusion `p ↦ (ξ.1,p)`.
  have hcont : Filter.Tendsto (fun p : Point n => ((ξ.1, p) : Point n × Point n))
      (nhds ξ.2) (nhds ξ) := by
    have h1 : Filter.Tendsto (fun _ : Point n => ξ.1) (nhds ξ.2) (nhds ξ.1) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (id : Point n → Point n) (nhds ξ.2) (nhds ξ.2) := Filter.tendsto_id
    have hprod := h1.prodMk h2
    rw [← nhds_prod_eq] at hprod
    simpa [Prod.mk.eta] using hprod
  have hsliced : (fun p : Point n => F ξ.1 p jj) =ᶠ[nhds ξ.2] (fun p : Point n => G ξ.1 p jj) :=
    hgerm.comp_tendsto hcont
  -- Push the sliced fiber germ along the coordinate-line map `s ↦ Function.update ξ.2 i s`.
  have hupdateTendsto : Filter.Tendsto (fun s : ℝ => Function.update ξ.2 i s)
      (nhds (ξ.2 i)) (nhds ξ.2) := by
    have hf : Filter.Tendsto (fun _ : ℝ => ξ.2) (nhds (ξ.2 i)) (nhds ξ.2) := tendsto_const_nhds
    have hg : Filter.Tendsto (id : ℝ → ℝ) (nhds (ξ.2 i)) (nhds (ξ.2 i)) := Filter.tendsto_id
    have h := hf.update i hg
    simpa [Function.update_eq_self] using h
  have hline : (fun s : ℝ => F ξ.1 (Function.update ξ.2 i s) jj)
      =ᶠ[nhds (ξ.2 i)] (fun s : ℝ => G ξ.1 (Function.update ξ.2 i s) jj) :=
    hsliced.comp_tendsto hupdateTendsto
  exact hline.hasDerivAt_iff

/-- **★ J4-1129 — `chartCoherent_Qfield_agree_at_overlap_two_seeds`: second-order (`Qfield`)
    derivative-coefficient agreement on the overlap, matching `ChartJointBorel.lean`'s `hcarField2`
    `Qfield` well-definedness need.** At the SAME uniform radius `r₀` from the hub lemma, for any
    TWO seeds `(z₀,v₀)`, `(z₀',v₀')`, there are coherently-built charts `chartCoherent1`,
    `chartCoherent2` and OPEN neighbourhoods `U1`, `U2` such that: for every coordinate `j` and
    every pair of candidate FIRST-order coefficient fields `Pjfield1 Pjfield2` witnessing
    `chartCoherent1`'s/`chartCoherent2`'s `j`-coordinate-line derivatives throughout `U1`/`U2`, and
    for every coordinate `i`, every pair of candidate SECOND-order coefficient fields
    `Qfield1 Qfield2` witnessing `Pjfield1`'s/`Pjfield2`'s `i`-coordinate-line derivatives AT a
    given overlap point `ξ ∈ U1 ∩ U2` (component `k`), `Qfield1` and `Qfield2` necessarily AGREE at
    that point. This is the well-definedness fact a future piecewise/glued `Qfield` representative
    needs, one derivative order above J4-1128's `Pfield`/`Pifield`/`Pjfield` fact. -/
theorem chartCoherent_Qfield_agree_at_overlap_two_seeds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ),
      ∀ z₀ : Point n, z₀ ∈ interior K → ∀ v₀ : Point n, ‖v₀‖ < r₀ →
      ∀ z₀' : Point n, z₀' ∈ interior K → ∀ v₀' : Point n, ‖v₀'‖ < r₀ →
      ∃ chartCoherent1 chartCoherent2 : Point n → Point n → Point n,
      ∃ U1 : Set (Point n × Point n), IsOpen U1 ∧
        ((z₀, uniformFlowExp g gi hC hK z₀ v₀) : Point n × Point n) ∈ U1 ∧
      ∃ U2 : Set (Point n × Point n), IsOpen U2 ∧
        ((z₀', uniformFlowExp g gi hC hK z₀' v₀') : Point n × Point n) ∈ U2 ∧
        (∀ j : Fin n, ∀ Pjfield1 Pjfield2 : Point n → Point n → Fin n → ℝ,
          (∀ ξ ∈ U1, ∀ jj : Fin n,
            HasDerivAt (fun s : ℝ => chartCoherent1 ξ.1 (Function.update ξ.2 j s) jj)
              (Pjfield1 ξ.1 ξ.2 jj) (ξ.2 j)) →
          (∀ ξ ∈ U2, ∀ jj : Fin n,
            HasDerivAt (fun s : ℝ => chartCoherent2 ξ.1 (Function.update ξ.2 j s) jj)
              (Pjfield2 ξ.1 ξ.2 jj) (ξ.2 j)) →
          ∀ i : Fin n, ∀ Qfield1 Qfield2 : Point n → Point n → Fin n → ℝ,
          ∀ ξ ∈ U1 ∩ U2, ∀ k : Fin n,
            HasDerivAt (fun s : ℝ => Pjfield1 ξ.1 (Function.update ξ.2 i s) k)
              (Qfield1 ξ.1 ξ.2 k) (ξ.2 i) →
            HasDerivAt (fun s : ℝ => Pjfield2 ξ.1 (Function.update ξ.2 i s) k)
              (Qfield2 ξ.1 ξ.2 k) (ξ.2 i) →
            Qfield1 ξ.1 ξ.2 k = Qfield2 ξ.1 ξ.2 k) := by
  obtain ⟨r₀, hr₀pos, hall⟩ := chartCoherent_field_agree_at_overlap_two_seeds g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  obtain ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem, hFieldAgree⟩ :=
    hall z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  refine ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem, ?_⟩
  intro j Pjfield1 Pjfield2 hPj1 hPj2 i Qfield1 Qfield2 ξ hξ k hQ1 hQ2
  have hEqOn : ∀ ζ ∈ U1 ∩ U2, ∀ jj : Fin n, Pjfield1 ζ.1 ζ.2 jj = Pjfield2 ζ.1 ζ.2 jj :=
    hFieldAgree j Pjfield1 Pjfield2 hPj1 hPj2
  have hIff := scalar_coordLine_hasDerivAt_iff_of_pointwise_eq_open
    (hU1open.inter hU2open) hEqOn hξ i k (Qfield1 ξ.1 ξ.2 k)
  exact (hIff.mp hQ1).unique hQ2

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_Qfield_agree_at_overlap_two_seeds
end AxiomChecks
