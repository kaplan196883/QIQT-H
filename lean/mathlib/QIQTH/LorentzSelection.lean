/-
  LorentzSelection — the discrete skeleton of the Lorentz-covariance of the
  QIQT-H single-outcome selection map (Open Problem 3b, foundations paper §11.4).

  GPT-5.5-pro sharpening (Lorentz-covariance consultation):

      The full target is a "Poincaré-equivariant holographic recorded-history
      sheaf theorem": a record-sector presheaf X over the causal-diamond poset,
      with λ a GLOBAL SECTION, a decoherence-functional measure μ, capacity
      bounds log #Atoms ≤ Q_D, boundary reconstruction, and Poincaré
      equivariance — under which the selector is mere evaluation
      A_D[Φ,λ] = λ_D and the covariance identity
      A_{gD}[U_gΦ, g·λ] = g · A_D[Φ,λ] follows immediately.

      The ANALYTIC core (Type III₁ / Tomita–Takesaki / Haagerup-L^p: existence
      of the finite record algebras, the holographic bound, boundary
      reconstruction, the decoherence-functional measure and its σ-additive
      extension, the no-signaling marginal lemma) is beyond current Mathlib and
      is named here as explicit interface axioms — exactly the strategy of
      AxiomAudit.lean / the Born pipeline.

      The DISCRETE / order-theoretic SKELETON is provable now and is what this
      module delivers:

        * the causal-diamond poset and a record-sector presheaf X over it,
          with restriction maps respecting the order (functoriality);
        * a global section λ ∈ Γ(X) (the foliation-free global-consistency
          condition, Correction A: gluing over BULK OVERLAPS via restriction,
          not screen intersections);
        * a Poincaré action on diamonds and an equivariant family of
          presheaf isomorphisms γ_g : X(D) → X(gD) (Correction B lives in the
          *existence* of γ_g, deferred to an axiom; here we assume it and use
          it);
        * the selector A_D[Φ,λ] := λ_D (evaluation), and the
          EVALUATION-GIVES-COVARIANCE theorem proved unconditionally from the
          equivariant-naturality hypotheses.

  Strategic content (mirrors MarginalLocality's split): the substantive
  covariance content — "equivariant naturality + a global section ⟹ a
  covariant single-outcome selection map" — is a *theorem* here, depending on
  NO project axioms; the AQFT existence inputs are named, explicit interface
  axioms, not eliminated. This is the Lorentz analogue of
  `pushforward_marginal_local`: the conclusion is not baked into the
  hypotheses (nothing about holography, decoherence, or Born is assumed in the
  proved part — only naturality of restriction and the cocycle action of g).
-/

import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace QIQTH
namespace LorentzSelection

/- ── 1. The causal-diamond poset ──────────────────────────────────────

    Abstract the geometry: `Diam` is the type of causal diamonds, ordered
    by inclusion `≤` (`K ≤ D` means `K ⊆ D`).  We only need a `Preorder`;
    reflexivity + transitivity of inclusion are all the skeleton uses. -/

variable {Diam : Type*} [Preorder Diam]

/- ── 2. The record-sector presheaf X over the diamond poset ───────────

    `X D` is the (Stone space of the) finite Boolean record algebra on the
    diamond `D` — the set of admissible λ-selected record sectors there.
    `restrict h : X D → X K` for `h : K ≤ D` is the record-restriction map
    `ρ_{D,K}` (a larger-diamond sector induces a smaller-diamond sector).

    `RecordPresheaf` packages the functoriality of restriction: identity
    restriction is the identity, and nested restriction composes.  This is
    exactly "X is a presheaf on the poset". -/

structure RecordPresheaf (Diam : Type*) [Preorder Diam] where
  /-- record-sector space over each diamond -/
  X : Diam → Type*
  /-- restriction map `ρ_{D,K} : X D → X K` for `K ≤ D` -/
  restrict : ∀ {K D : Diam}, K ≤ D → X D → X K
  /-- functoriality: restricting along reflexivity is the identity -/
  restrict_id : ∀ {D : Diam} (x : X D), restrict (le_refl D) x = x
  /-- functoriality: nested restriction composes
      (`L ≤ K ≤ D`: restrict to L = restrict to K then to L) -/
  restrict_comp : ∀ {L K D : Diam} (hLK : L ≤ K) (hKD : K ≤ D) (x : X D),
    restrict hLK (restrict hKD x) = restrict (le_trans hLK hKD) x

/- ── 3. Global sections: λ ∈ Γ(X) ─────────────────────────────────────

    A **global section** assigns to every diamond `D` a record sector
    `val D : X D` such that the assignments are *consistent under
    restriction*: for `K ≤ D`, restricting the `D`-sector gives the
    `K`-sector.

    This is the precise, foliation-free, order-theoretic statement of
    Requirement 4 (Correction A): consistency is gluing along the poset's
    restriction maps — equivalently bulk-overlap agreement, since for any
    two diamonds `D, E` and any common sub-diamond `L ≤ D`, `L ≤ E`, both
    `restrict _ (val D)` and `restrict _ (val E)` equal `val L`.  No global
    time function appears. -/

structure GlobalSection (P : RecordPresheaf Diam) where
  /-- the selected record sector on each diamond -/
  val : ∀ D : Diam, P.X D
  /-- restriction-consistency (the gluing / global-section condition) -/
  consistent : ∀ {K D : Diam} (h : K ≤ D), P.restrict h (val D) = val K

/-- **Bulk-overlap agreement (Correction A), as a derived fact.**

    For any two diamonds `D E` and any common sub-diamond `L` (i.e. `L ≤ D`
    and `L ≤ E`), the two records restricted from `D` and from `E` agree on
    `L`.  This is the content GPT-5.5-pro insisted on — consistency is gluing
    over bulk sub-diamonds of the overlap, *not* agreement on the screen
    intersection `∂D ∩ ∂E` (which is too weak because `∂K ⊄ ∂D`).  Here it is
    an immediate consequence of the global-section condition. -/
theorem bulk_overlap_agreement
    {P : RecordPresheaf Diam} (lam : GlobalSection P)
    {L D E : Diam} (hLD : L ≤ D) (hLE : L ≤ E) :
    P.restrict hLD (lam.val D) = P.restrict hLE (lam.val E) := by
  rw [lam.consistent hLD, lam.consistent hLE]

/- ── 4. The selector A_D[Φ,λ] := evaluation ───────────────────────────

    Given a global section `λ`, the QIQT-H regional beable on diamond `D`
    is just the value of the section there.  `C_D = A_D[Φ,λ] = λ_D`.  All
    the physics (decoherence, capacity, Born) is in the *construction* of
    `P` and `λ` (the deferred axioms below); the selector itself is mere
    evaluation, which is what makes covariance a one-liner. -/

def selector {P : RecordPresheaf Diam} (lam : GlobalSection P) (D : Diam) : P.X D :=
  lam.val D

/- ── 5. Poincaré action and equivariant naturality ────────────────────

    `g : Diam ≃ Diam` is the action of a Poincaré element on diamonds
    (a poset automorphism — boosts/translations send causal diamonds to
    causal diamonds, preserving inclusion).  We package the action of a
    *single* `g` together with the natural isomorphism `γ_g : X D → X (g D)`
    on record sectors that commutes with restriction.

    The EXISTENCE of such a `γ_g` (covariant from U_g via the spinor rep, and
    natural — the content GPT flagged as needing Bisognano–Wichmann /
    a Poincaré-natural split, and as carrying the Roberts-net-cohomology
    obstruction) is the analytic input; it is an `axiom` below.  Given it,
    the covariance identity is proved here. -/

/-- A Poincaré element acting covariantly on the record presheaf:
    an **order isomorphism** `act` of diamonds (a poset automorphism whose
    inverse is also monotone — this is what `≃o` provides, and what makes the
    pushed-forward section provably consistent, with no transport axiom)
    together with a natural family of sector isomorphisms `γ` commuting with
    restriction.

    Using `≃o` rather than a bare `≃` + a one-directional `mono` field is the
    fix flagged by the GPT-5.5-pro review: a monotone *bijection* need not have
    a monotone inverse, which is exactly why the earlier formulation had to
    leave `actSection`'s consistency as an axiom.  An `OrderIso` carries
    inverse-monotonicity for free, so the consistency is now *proved*. -/
structure PoincareAction (P : RecordPresheaf Diam) where
  /-- action on diamonds: a poset automorphism (order isomorphism).  Using
      `≃o` (not a bare `≃` + one-directional `mono`) gives inverse-monotonicity
      for free, which is what makes the pushed-forward section's consistency
      *provable* rather than axiomatic (GPT-5.5-pro review fix). -/
  act : Diam ≃o Diam
  /-- the natural record-sector isomorphism `γ_g : X D → X (act D)` -/
  γ : ∀ D : Diam, P.X D ≃ P.X (act D)
  /-- **naturality**: `γ` commutes with restriction
      (`ρ ∘ γ = γ ∘ ρ`) — the equivariant-naturality square. -/
  natural : ∀ {K D : Diam} (h : K ≤ D) (x : P.X D),
    P.restrict (act.monotone h) (γ D x) = γ K (P.restrict h x)

/-- Cast a record sector along an equality of diamonds (transport in the
    presheaf fibre).  Isolated so the transport reasoning is contained. -/
def castSector {P : RecordPresheaf Diam} {D D' : Diam} (h : D = D')
    (x : P.X D) : P.X D' := h ▸ x

/-- `castSector` is heterogeneously equal to its argument. -/
theorem castSector_heq {P : RecordPresheaf Diam} {D D' : Diam} (h : D = D')
    (x : P.X D) : HEq (castSector (P := P) h x) x := by
  subst h; rfl

/-- **Restriction commutes with the diamond-cast (transport naturality of
    `restrict`).**  Restricting a cast equals casting a restrict.  Proved by
    `subst`-ing the two diamond equalities, after which both casts are the
    identity and the two `restrict` proofs coincide by proof irrelevance. -/
theorem restrict_cast {P : RecordPresheaf Diam} {K₀ D₀ K D : Diam}
    (hD : D₀ = D) (hK : K₀ = K) (h : K ≤ D) (h₀ : K₀ ≤ D₀) (x : P.X D₀) :
    P.restrict h (castSector hD x) = castSector hK (P.restrict h₀ x) := by
  subst hD; subst hK; rfl

/-- The pushed-forward section value at `D'`, before casting:
    `γ_g (λ_{act.symm D'})`, living in `X (act (act.symm D'))`. -/
private noncomputable def actVal
    {P : RecordPresheaf Diam} (g : PoincareAction P) (lam : GlobalSection P)
    (D' : Diam) : P.X (g.act (g.act.symm D')) :=
  g.γ (g.act.symm D') (lam.val (g.act.symm D'))

/-- **Consistency of the pushed-forward section — PROVED (no axiom).**

    `restrict h ((g·λ).val D) = (g·λ).val K` for `K ≤ D`.  This is the fix
    flagged by the GPT-5.5-pro review: with `act : ≃o`, `act.symm` is monotone
    (`hKD`), so γ-naturality applies at the pulled-back diamonds and
    λ-consistency closes it; the transport casts are handled cleanly by
    `restrict_cast` (no HEq gymnastics, no axiom). -/
theorem actSection_consistent
    {P : RecordPresheaf Diam} (g : PoincareAction P) (lam : GlobalSection P)
    {K D : Diam} (h : K ≤ D) :
    P.restrict h
        (castSector (g.act.apply_symm_apply D) (actVal g lam D))
      = castSector (g.act.apply_symm_apply K) (actVal g lam K) := by
  -- act.symm is monotone (the ≃o inverse): pull `h` back to the source frame.
  have hKD : g.act.symm K ≤ g.act.symm D := g.act.symm.monotone h
  -- γ-naturality at `hKD`, then collapse the inner restrict by λ-consistency.
  have hnat := g.natural hKD (lam.val (g.act.symm D))
  rw [lam.consistent hKD] at hnat
  -- hnat : P.restrict (g.act.monotone hKD) (γ (act.symm D) (λ (act.symm D)))
  --        = γ (act.symm K) (λ (act.symm K))
  -- Unfold actVal so the casts' arguments match, push `restrict h` through the
  -- LHS cast via transport-naturality, then rewrite by hnat.
  unfold actVal
  rw [restrict_cast (g.act.apply_symm_apply D) (g.act.apply_symm_apply K)
        h (g.act.monotone hKD) (g.γ (g.act.symm D) (lam.val (g.act.symm D))), hnat]

/-- **Push a global section forward by a Poincaré action: `g · λ`** — now a
    well-defined element of `Γ(X)`, with `actSection_consistent` as its
    consistency field (PROVED, no axiom). -/
noncomputable def actSection
    {P : RecordPresheaf Diam} (g : PoincareAction P) (lam : GlobalSection P) :
    GlobalSection P where
  val := fun D' =>
    castSector (g.act.apply_symm_apply D') (actVal g lam D')
  consistent := fun h => actSection_consistent g lam h

/-- **Public evaluation of `actSection`** (the `actVal` field is private; this
    is the public spec).  Exposed so downstream modules can reason about the
    pushed-forward section's values — e.g. to prove `actSection` is a group
    action on `Γ(X)` (`LorentzSelectionStrong`). -/
@[simp] theorem actSection_val {P : RecordPresheaf Diam} (g : PoincareAction P)
    (lam : GlobalSection P) (D' : Diam) :
    (actSection g lam).val D'
      = castSector (g.act.apply_symm_apply D')
          (g.γ (g.act.symm D') (lam.val (g.act.symm D'))) := rfl

/-- **Extensionality for global sections**: equal on every diamond ⟹ equal.
    (The `consistent` field is a `Prop`, hence proof-irrelevant.) -/
theorem GlobalSection.ext {P : RecordPresheaf Diam} {s t : GlobalSection P}
    (h : ∀ D : Diam, s.val D = t.val D) : s = t := by
  obtain ⟨v, _⟩ := s; obtain ⟨w, _⟩ := t
  have hvw : v = w := funext h
  subst hvw; rfl

/-- **Transport a section value along a diamond equality** — `castSector` of a
    section value at `D₀` is the section value at `D₁`.  Removes transport noise
    when reasoning about `actSection` across propositionally-equal diamonds
    (GPT-5.5-pro-recommended helper for the section-object group-action law). -/
theorem GlobalSection.val_cast {P : RecordPresheaf Diam} (s : GlobalSection P)
    {D₀ D₁ : Diam} (h : D₀ = D₁) : castSector h (s.val D₀) = s.val D₁ := by
  cases h; rfl

/- ── 6. THE COVARIANCE IDENTITY (the proved one-liner) ─────────────────

    Requirement 3:  A_{gD}[U_gΦ, g·λ] = g · A_D[Φ,λ].

    With the selector as evaluation and `g · λ` the pushed-forward section,
    the identity says: the record selected on the boosted diamond `g D` by
    the boosted section equals `γ_g` applied to the record selected on `D` by
    the original section.  This is the precise sense of "every frame agrees
    on the physical facts," and it is now a one-line consequence of the
    definitions + naturality — exactly as the §11.4 sketch claims. -/

/-- **Evaluation-gives-covariance.**

    `selector (g · λ) (act D) = γ_g (selector λ D)`, i.e.

        A_{gD}[U_gΦ, g·λ]  =  g · A_D[Φ,λ].

    Proved directly from the definition of the pushed-forward section: its
    value at `act D` is, after cancelling the transport `act (act.symm (act D))
    = act D`, exactly `γ_g (λ_D)`.  Depends on NO project axioms beyond the
    `actSection` definition (whose only deferred piece is the order-theoretic
    transport lemma); in particular nothing about holography, decoherence, or
    Born is used — the covariance is purely structural, from equivariant
    naturality. -/
theorem evaluation_covariance
    {P : RecordPresheaf Diam} (g : PoincareAction P) (lam : GlobalSection P)
    (D : Diam) :
    selector (actSection g lam) (g.act D) = g.γ D (selector lam D) := by
  -- selector (actSection g lam) (act D) = (g·λ).val (act D)
  --   = castSector _ (γ (act.symm (act D)) (λ (act.symm (act D)))).
  -- Cancel the cast heterogeneously, then collapse `act.symm (act D) = D`.
  show castSector (g.act.apply_symm_apply (g.act D)) (actVal g lam (g.act D))
      = g.γ D (lam.val D)
  apply eq_of_heq
  refine (castSector_heq _ _).trans ?_
  -- goal: HEq (actVal g lam (act D)) (γ D (λ D)), i.e.
  --       HEq (γ (act.symm (act D)) (λ (act.symm (act D)))) (γ D (λ D));
  -- collapses to rfl once `act.symm (act D) = D`.
  show HEq (g.γ (g.act.symm (g.act D)) (lam.val (g.act.symm (g.act D))))
           (g.γ D (lam.val D))
  rw [g.act.symm_apply_apply D]

/- ── 7. Equivariant family over all of Γ(X) (req-5 hook) ───────────────

    Requirement 5 (equivariance, NOT invariance): `g_* μ_Φ = μ_{U_gΦ}`.  The
    measure `μ` lives on `Γ(X)`; the action of `g` on `Γ(X)` is `actSection g`.
    The measure itself (the decoherence functional) is analytic and deferred;
    but the *carrier* of req-5 — that `g` acts on global sections — is exactly
    `actSection`, and `evaluation_covariance` is the compatibility of that
    action with the selector.  The equivariance statement `g_* μ_Φ = μ_{U_gΦ}`
    is recorded as an interface axiom on the deferred measure. -/

/- ── 8. THE DEFERRED ANALYTIC INPUTS — now EXPLICIT PROPOSITIONS ────────

    Previously these were four *opaque* placeholder axioms (`axiom name : Prop`,
    asserting nothing, used by nothing — pure budget markers).  The
    GPT-5.5-pro-style discharge pass replaces them with an explicit `structure`
    that actually WRITES DOWN the intended Type III₁ / Tomita–Takesaki /
    Haagerup-L^p content as type-checked data + propositions, and makes the
    covariance result a *conditional theorem* over it.

    This is more honest than the old axioms for *formal hygiene*: the deferred
    assumptions are now precisely-stated hypotheses (the "interface-as-hypothesis,
    not axiom" pattern this corpus prefers — cf. `pushforward_marginal_local` and
    the discharged Gleason module), and the module adds ZERO project axioms.

    HONEST CAVEAT (GPT-5.5-pro adversarial review — do not overstate this):
    * The covariance theorem below (`covariant_selection_of_net`) consumes only
      the presheaf field `net.P`; its proof is the structural identity
      `evaluation_covariance`, and the analytic fields (`N`, `recon`, `ω`,
      `ω_marg`) are NOT used.  So it is evaluation-equivariance, not covariance
      of the decoherence measure or of a fixed selection rule.
    * Several fields are NON-RIGID as written (chosen inside the same structure):
      `card_le` is satisfiable by `N D := Fintype.card (P.X D)`; boundary
      reconstruction by `Pb := P`, `recon := Equiv.refl`; `ω` by any finite PMF.
      The one-point net (`P.X D := Unit`) satisfies every field, so the BARE
      existence statement "a `RecordedHistoryNet` exists" is TRIVIALLY TRUE and
      is NOT the open problem.
    * `net_no_signaling` is a two-line rewrite of the ASSUMED `ω_marg`, not a
      derivation from microcausality.
    The genuine Open Problem 3b is the REALIZATION problem: a net whose data are
    extracted from a fixed relativistic QFT + geometry (area-law `N` and boundary
    algebra fixed externally; weights pinned to Born values `ω_Φ(P_i^D)` of an
    actual state `Φ`) under a true Poincaré GROUP action with equivariant
    measure.  This module retires the four opaque axioms and machine-checks the
    finite combinatorial skeleton; it does NOT discharge that realization. -/

universe uD uX

/-- **A recorded-history net** — the finite/holographic data the §11.4 linchpin
    theorem assumes to exist (linchpin hypotheses 1–3, 2, 6, 9), here written
    out explicitly instead of being four opaque axioms.

    Fields, mapped to the retired axioms:

    * `P`, `fin`, `N`, `card_le` — *(was `record_presheaf_exists`, Hyp 1–3)*:
      a record-sector presheaf whose fibres are **finite** with a **holographic
      cardinality bound** `#Atoms(B_Φ(D)) ≤ N D` (the discrete form of
      `log #Atoms ≤ Q_D = A(∂D)/4ℓ_P²`).
    * `Pb`, `recon`, `recon_nat` — *(was `boundary_reconstruction`, Hyp 2)*:
      a **boundary (screen) presheaf** `Pb` with a **natural isomorphism**
      `recon D : P.X D ≃ Pb.X D` commuting with restriction — the holographic
      bulk≅boundary content of P2.
    * `ω`, `ω_nonneg`, `ω_norm` — *(was `decoherence_functional_measure`,
      Hyp 6)*: a **probability weight** on each (finite) fibre — the cylinder
      values of the decoherence-functional measure `μ_Φ(λ_D = i) = ω_Φ(P_i^D)`.
    * `ω_marg` — *(was `decoherence_functional_measure`'s Kolmogorov consistency
      AND `screen_local_marginal`, Hyp 6 & 9)*: the **projective / no-signaling
      marginal** — marginalizing the `D`-measure onto a sub-diamond `K ≤ D`
      yields `ω K`, *the same answer for every larger diamond `D ⊇ K`*.  This is
      simultaneously σ-additive (Kolmogorov) consistency and the relativistic
      no-signaling statement (the marginal on `K` is independent of the
      spacelike-extended context `D`). -/
structure RecordedHistoryNet (Diam : Type uD) [Preorder Diam] where
  /-- bulk record-sector presheaf -/
  P : RecordPresheaf.{uD, uX} Diam
  /-- holographic finiteness of each fibre -/
  fin : ∀ D : Diam, Fintype (P.X D)
  /-- decidable equality on fibres (for the marginal sum) -/
  deceq : ∀ D : Diam, DecidableEq (P.X D)
  /-- holographic atom budget `N D ≈ ⌊exp Q_D⌋` -/
  N : Diam → ℕ
  /-- the holographic bound `#Atoms(B_Φ(D)) ≤ N D` -/
  card_le : ∀ D : Diam, @Fintype.card (P.X D) (fin D) ≤ N D
  /-- boundary (screen) record-sector presheaf -/
  Pb : RecordPresheaf.{uD, uX} Diam
  /-- boundary reconstruction iso `B_{Φ,∂}(D) ≅ B_Φ(D)` -/
  recon : ∀ D : Diam, P.X D ≃ Pb.X D
  /-- naturality of boundary reconstruction (commutes with restriction) -/
  recon_nat : ∀ {K D : Diam} (h : K ≤ D) (x : P.X D),
    Pb.restrict h (recon D x) = recon K (P.restrict h x)
  /-- decoherence-functional cylinder weights `ω_Φ(P_i^D)` -/
  ω : ∀ D : Diam, P.X D → ℝ
  /-- nonnegativity of the measure -/
  ω_nonneg : ∀ (D : Diam) (x : P.X D), 0 ≤ ω D x
  /-- normalization (probability measure on each fibre) -/
  ω_norm : ∀ D : Diam,
    @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (fin D)) (ω D) = 1
  /-- projective / no-signaling marginal: the marginal onto `K` is `ω K`,
      independent of the larger diamond `D ⊇ K` -/
  ω_marg : ∀ {K D : Diam} (h : K ≤ D) (y : P.X K),
    @Finset.sum (P.X D) ℝ _
      (@Finset.filter (P.X D) (fun x => P.restrict h x = y)
        (fun x => deceq K (P.restrict h x) y) (@Finset.univ (P.X D) (fin D)))
      (ω D) = ω K y

/-- **No-signaling, derived from the net (not assumed).**  The marginal of the
    history measure onto a sub-diamond `K` is the same whether computed by
    restricting from `D` or from `E` (any two larger diamonds), because both
    equal `ω K y`.  This is `bulk_overlap_agreement` lifted to the measure —
    the relativistic no-signaling statement, now a *theorem* about any
    `RecordedHistoryNet`. -/
theorem net_no_signaling {Diam : Type*} [Preorder Diam]
    (net : RecordedHistoryNet Diam) {K D E : Diam} (hKD : K ≤ D) (hKE : K ≤ E)
    (y : net.P.X K) :
    @Finset.sum (net.P.X D) ℝ _
      (@Finset.filter (net.P.X D) (fun x => net.P.restrict hKD x = y)
        (fun x => net.deceq K (net.P.restrict hKD x) y)
        (@Finset.univ (net.P.X D) (net.fin D))) (net.ω D)
    = @Finset.sum (net.P.X E) ℝ _
      (@Finset.filter (net.P.X E) (fun x => net.P.restrict hKE x = y)
        (fun x => net.deceq K (net.P.restrict hKE x) y)
        (@Finset.univ (net.P.X E) (net.fin E))) (net.ω E) := by
  rw [net.ω_marg hKD y, net.ω_marg hKE y]

/- ── 9. THE CONDITIONAL CAPSTONE + audit conclusion ────────────────────-/

/-- **Conditional Lorentz-covariant selection — from the net, no axioms.**
    Given a recorded-history net (the explicit replacement for the four AQFT
    axioms), a global section `λ`, and a Poincaré action `g`, the selector is
    covariant: `A_{gD}[U_gΦ, g·λ] = g · A_D[Φ,λ]`.  The covariance is the
    already-proved structural fact `evaluation_covariance`; this theorem records
    that it holds *over the full analytic apparatus*, depending on NO project
    axioms (the net is a hypothesis, not an axiom). -/
theorem covariant_selection_of_net {Diam : Type*} [Preorder Diam]
    (net : RecordedHistoryNet Diam) (lam : GlobalSection net.P)
    (g : PoincareAction net.P) (D : Diam) :
    selector (actSection g lam) (g.act D) = g.γ D (selector lam D) :=
  evaluation_covariance g lam D

/-- **Existence form.** IF a recorded-history net with a global section and a
    Poincaré action exists (the precise, written-down statement of what was
    four opaque axioms), THEN a Poincaré-covariant single-outcome selector
    provably exists.  Zero project axioms; the open content is exactly the
    antecedent's truth for realistic QFT. -/
theorem covariant_selection_exists {Diam : Type uD} [Preorder Diam]
    (h : ∃ (net : RecordedHistoryNet.{uD, uX} Diam) (_lam : GlobalSection net.P)
           (_g : PoincareAction net.P), True) :
    ∃ (P : RecordPresheaf.{uD, uX} Diam) (lam : GlobalSection P) (g : PoincareAction P),
      ∀ D : Diam, selector (actSection g lam) (g.act D) = g.γ D (selector lam D) := by
  obtain ⟨net, lam, g, _⟩ := h
  exact ⟨net.P, lam, g, fun D => evaluation_covariance g lam D⟩

/-- **Audit conclusion (carefully stated), mirroring MarginalLocality.**

    The Lorentz-covariance of the QIQT-H selection map splits, exactly as the
    Born pipeline does, into:

      (1) **The structural covariance step — PROVED here, no project axioms.**
          `evaluation_covariance`: given a record presheaf `P` (functorial
          restriction), a global section `λ` (the foliation-free consistency
          condition, with `bulk_overlap_agreement` derived), and a
          Poincaré action with *equivariant-natural* sector isomorphisms
          `γ_g`, the selector `A_D := λ_D` satisfies the covariance identity
          `A_{gD}[U_gΦ, g·λ] = g · A_D[Φ,λ]`.  This is the relativistic
          analogue of `pushforward_marginal_local`: the covariance is forced
          by naturality alone — nothing about holography, decoherence, or
          Born enters the proved part.

      (2) **The AQFT existence inputs — now an EXPLICIT structure, no longer
          axioms.**  `RecordedHistoryNet` writes out, as type-checked data +
          propositions, what were the four opaque axioms `record_presheaf_exists`,
          `boundary_reconstruction`, `decoherence_functional_measure`,
          `screen_local_marginal` (= linchpin hypotheses 1–3, 2, 6, 9): the
          holographic finiteness bound, the boundary-reconstruction natural iso,
          the decoherence-functional probability weights, and the projective /
          no-signaling marginal (the last gives the convenience lemma
          `net_no_signaling` — a two-line rewrite of the assumed `ω_marg`, NOT a
          derivation from microcausality).  The covariance result is the
          conditional theorems `covariant_selection_of_net` /
          `covariant_selection_exists` over this structure.  The module adds ZERO
          project axioms.

    Net effect, stated honestly (with the adversarial-review caveat above):
    "equivariant naturality + a global section ⟹ a covariant single-outcome
    selection map" is a machine-checked, axiom-free theorem, and the four AQFT
    inputs are no longer assumed axioms but an explicit hypothesis structure.
    But this is FORMAL HYGIENE, not a discharge of the physics: the covariance
    theorem uses only `net.P`, the structure's analytic fields are non-rigid
    (the one-point net satisfies them all), so the BARE existence of a
    `RecordedHistoryNet` is trivially true and is NOT the open problem.  The
    genuine Open Problem 3b is the REALIZATION problem — a net extracted from a
    fixed QFT + geometry (externally-rigid area-law `N` and boundary algebra,
    Born-pinned weights `ω_Φ(P_i^D)`) under a true Poincaré GROUP action with
    equivariant measure — i.e. the Type III₁ / Tomita–Takesaki / Haagerup-L^p
    existence problem (carrying the Roberts-net-cohomology gluing obstruction and
    the equivariant-γ split).  That remains open; only the finite combinatorial
    skeleton is machine-checked here. -/
theorem audit_conclusion : True := trivial

end LorentzSelection
end QIQTH
