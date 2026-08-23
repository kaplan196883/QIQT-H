/-
  ChartOverlapCoefficientAgreementTwoSeeds — J4-1128: dispatch 6 of the "inverse-branch
  overlap-uniqueness bridge" sub-campaign (greenlit J4-1122, hub lemma J4-1123, two-seed
  `Set.EqOn` corollary J4-1124, open-overlap germ compatibility J4-1125, target-facing
  value/`fderiv`/carrier consumer triple J4-1126, literal coordinate-line `HasDerivAt` transfer
  J4-1127, per `gpt-5.6-sol` high consult 2026-08-24 x6).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file does.

  J4-1127 built the literal `HasDerivAt ↔ HasDerivAt` transfer, at the exact syntactic shape
  `ChartJointBorel.lean`'s `hcarField`/`hcarField2` hypotheses consume, for an ARBITRARY candidate
  derivative value `d`. This dispatch upgrades that `iff` to the actual "coefficient-agreement"
  fact those hypotheses' eventual `Pfield`/`Pifield`/`Pjfield` suppliers will need for
  well-definedness: IF two candidate derivative-coefficient FIELDS `P1`, `P2` respectively
  witness `chartCoherent1`'s and `chartCoherent2`'s coordinate-line derivatives throughout `U1`,
  resp. `U2`, THEN `P1` and `P2` necessarily AGREE on the overlap `U1 ∩ U2` — via
  `HasDerivAt.unique` composed with J4-1127's overlap transfer.

  Per `gpt-5.6-sol` (high, sixth consult, 2026-08-24): the bare pointwise "`d1 = d2` given two
  witnessing `HasDerivAt` facts at a single point" corollary is correct but too thin standing
  alone; the useful exported shape is the FIELD-level agreement statement above (candidate fields
  `P1 P2 : Point n → Point n → Fin n → ℝ`, agreement concluded pointwise for every `ξ ∈ U1 ∩ U2`
  and every output component `jj`) — closer to the actual gluing/well-definedness use a future
  concrete `Pfield` construction will need. Sol confirmed this is PURE LOGIC (no new
  quantitative/analytic claim, no sympy check needed): the proof is exactly "instantiate the
  overlap iff at `d1`, transport `h1` across it, then `HasDerivAt.unique` against `h2`". Sol also
  confirmed the SAME generic helper (parameterized by an arbitrary coordinate `k`, arbitrary
  domain `U`, arbitrary compared functions `F G`) discharges not only the `Pfield` shape (single
  fixed differentiated coordinate) but ALSO the `Pifield`/`Pjfield` shapes from `hcarField2` (each
  is a first-order coordinate-line derivative field over an open set, differing only in WHICH
  coordinate `i`/`j` is differentiated and evaluated at an ARBITRARY point `y`, not just the
  "current" `w.2.1` — already covered since the helper quantifies over every `ξ ∈ U`).

  ## Explicitly OUT of scope (per Sol, confirmed).

  `hcarField2`'s `Qfield` is the SECOND derivative — the derivative, in coordinate `i`, of
  `Pjfield` ITSELF (`HasDerivAt (fun s => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield …) …`).
  This dispatch's field-level agreement gives `Pjfield1 = Pjfield2` only POINTWISE, for every
  `ξ ∈ U1 ∩ U2` individually — NOT yet as a germ/eventual equality on a neighbourhood of any single
  point, which is what would be needed to differentiate the agreement itself and transfer `Qfield`.
  Sol confirmed this second-order upgrade (turning the pointwise field agreement into a germ
  equality along the coordinate-line map, then re-applying the same congruence machinery one
  derivative up) is the correct NEXT dispatch (J4-1129), not something to fold in here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL. NOT `a₁ = R/6`. Pure logical corollary of the already-banked
  `ChartOverlapCoordinateLineHasDerivAtTransfer.lean` transfer + `HasDerivAt.unique` — no new
  analytic estimate, no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses (the candidate
  fields `P1`/`P2` are universally quantified inputs, not asserted to exist; the conclusion is the
  correct conditional "IF both witness their respective chart's derivatives on `U1`/`U2` THEN they
  agree on the overlap" shape), no existing file edited. Does NOT yet supply a concrete
  `Pfield`/`Pifield`/`Pjfield`/`Qfield`/measurability representative for `hcarField`/`hcarField2`,
  and does NOT reach `Qfield` agreement — both remain open (J4-1129+).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ChartOverlapCoordinateLineHasDerivAtTransfer

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.HeatResidualBound
open scoped Topology NNReal

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Shared helper — a coordinate-line `HasDerivAt` transfer forces derivative-FIELD agreement.**
    If two functions `F G : Point n → Point n → Point n` have their `k`-coordinate-line
    `HasDerivAt` statements related by an `iff` throughout a set `U` (for ANY candidate value `d`),
    and candidate coefficient fields `P1`, `P2` respectively witness `F`'s and `G`'s actual
    coordinate-line derivatives throughout `U`, then `P1` and `P2` agree pointwise on `U` (at every
    output component `jj`). Pure logic: instantiate the `iff` at `P1 ξ.1 ξ.2 jj`, transport `hP1`
    across it to get a `chartCoherent2`-shape witness at that SAME value, then `HasDerivAt.unique`
    against `hP2`. -/
private lemma coordLine_field_eq_of_iff_of_witnesses {F G : Point n → Point n → Point n}
    {U U1 U2 : Set (Point n × Point n)} (hUU1 : U ⊆ U1) (hUU2 : U ⊆ U2)
    (hIff : ∀ ξ ∈ U, ∀ k jj : Fin n, ∀ d : ℝ,
      HasDerivAt (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k) ↔
      HasDerivAt (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) d (ξ.2 k))
    {P1 P2 : Point n → Point n → Fin n → ℝ} {k : Fin n}
    (hP1 : ∀ ξ ∈ U1, ∀ jj : Fin n,
      HasDerivAt (fun s : ℝ => F ξ.1 (Function.update ξ.2 k s) jj) (P1 ξ.1 ξ.2 jj) (ξ.2 k))
    (hP2 : ∀ ξ ∈ U2, ∀ jj : Fin n,
      HasDerivAt (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) (P2 ξ.1 ξ.2 jj) (ξ.2 k)) :
    ∀ ξ ∈ U, ∀ jj : Fin n, P1 ξ.1 ξ.2 jj = P2 ξ.1 ξ.2 jj := by
  intro ξ hξ jj
  have h1 := hP1 ξ (hUU1 hξ) jj
  have h2 := hP2 ξ (hUU2 hξ) jj
  have h1' : HasDerivAt (fun s : ℝ => G ξ.1 (Function.update ξ.2 k s) jj) (P1 ξ.1 ξ.2 jj) (ξ.2 k) :=
    (hIff ξ hξ k jj (P1 ξ.1 ξ.2 jj)).mp h1
  exact h1'.unique h2

/-- **★ J4-1128 — `chartCoherent_field_agree_at_overlap_two_seeds`: derivative-coefficient-field
    agreement on the overlap, matching the `Pfield`/`Pifield`/`Pjfield` well-definedness need.**
    At the SAME uniform radius `r₀` from the hub lemma, for any TWO seeds `(z₀,v₀)`, `(z₀',v₀')`,
    there are coherently-built charts `chartCoherent1`, `chartCoherent2` and OPEN neighbourhoods
    `U1`, `U2` such that: for every coordinate `k` and every pair of candidate coefficient fields
    `P1 P2 : Point n → Point n → Fin n → ℝ`, IF `P1` witnesses `chartCoherent1`'s `k`-coordinate-line
    derivative throughout `U1` and `P2` witnesses `chartCoherent2`'s throughout `U2`, THEN `P1` and
    `P2` agree (at every output component `jj`) on the overlap `U1 ∩ U2`. This is the
    well-definedness fact a future piecewise/glued `Pfield`/`Pifield`/`Pjfield` representative
    needs: switching which chart supplies the coefficient on the overlap does not change the
    value. -/
theorem chartCoherent_field_agree_at_overlap_two_seeds (g gi : Point n → Fin n → Fin n → ℝ)
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
        (∀ k : Fin n, ∀ P1 P2 : Point n → Point n → Fin n → ℝ,
          (∀ ξ ∈ U1, ∀ jj : Fin n,
            HasDerivAt (fun s : ℝ => chartCoherent1 ξ.1 (Function.update ξ.2 k s) jj)
              (P1 ξ.1 ξ.2 jj) (ξ.2 k)) →
          (∀ ξ ∈ U2, ∀ jj : Fin n,
            HasDerivAt (fun s : ℝ => chartCoherent2 ξ.1 (Function.update ξ.2 k s) jj)
              (P2 ξ.1 ξ.2 jj) (ξ.2 k)) →
          ∀ ξ ∈ U1 ∩ U2, ∀ jj : Fin n, P1 ξ.1 ξ.2 jj = P2 ξ.1 ξ.2 jj) := by
  obtain ⟨r₀, hr₀pos, hall⟩ := chartCoherent_hasDerivAt_transfer_at_overlap_two_seeds g gi hC hK
  refine ⟨r₀, hr₀pos, ?_⟩
  intro z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  obtain ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem,
    _hTr1, _hTr2, hTrOv⟩ := hall z₀ hz₀ v₀ hv₀ z₀' hz₀' v₀' hv₀'
  refine ⟨chartCoherent1, chartCoherent2, U1, hU1open, hU1mem, U2, hU2open, hU2mem, ?_⟩
  intro k P1 P2 hP1 hP2
  exact coordLine_field_eq_of_iff_of_witnesses
    (U1 := U1) (U2 := U2) Set.inter_subset_left Set.inter_subset_right hTrOv hP1 hP2

end QIQTH.ExpMap

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ExpMap
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms chartCoherent_field_agree_at_overlap_two_seeds
end AxiomChecks
