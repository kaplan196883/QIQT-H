/-
  LorentzSelectionStrong — the GPT-5.5-pro "make it genuinely stronger" pass on
  Open Problem 3b (Lorentz covariance).

  The base module `LorentzSelection.lean` retired four opaque AQFT axioms in
  favour of an explicit `RecordedHistoryNet` structure.  An adversarial review
  (GPT-5.5-pro) correctly judged that pass to be *formal hygiene*, not a
  discharge of the physics, because:
    (i)   the covariance theorem used only the presheaf field;
    (ii)  the structure's fields were NON-RIGID (N, boundary, ω chosen inside
          the same structure ⇒ the one-point net satisfies everything), so bare
          existence is trivially true;
    (iii) `net_no_signaling` was a rewrite of an assumed marginal.

  This module addresses (i)–(ii) with genuine, non-faking content along the four
  axes the review named (its items A–G):

    A. EXTERNALIZE the geometry.  `GeometrySpec` fixes the area-law budget `N`
       and the boundary presheaf BEFORE a net is chosen; `NetOn S` must match
       them.  This makes the holographic bound and boundary reconstruction
       rigid (no longer `N := card`, `Pb := P`).  Consuming theorems:
       `card_le_of_le` (uses holographic monotonicity) and `reconSection`
       (the screen-encoded selected history is itself a consistent boundary
       section — uses `recon_nat`).

    B. A real Poincaré GROUP action (`GroupAction G P`) with identity and
       composition laws, replacing the single order-automorphism.  Consuming
       theorems: `group_evaluation_covariance` (covariance for ALL g),
       `act_one_diam`, `act_mul_diam` (use the group laws).

    C. EQUIVARIANT measure.  `measure_pushforward_total`: a g-covariant weight
       has g-invariant total mass — a theorem that genuinely CONSUMES the
       covariance hypothesis (reindexing by the sector equivalence).

    G. The BORN LINK (the anti-vacuity lock).  `BornData` pins the weights to
       Born values `ω_Φ(P_i^D) = ⟨ψ_D|E_x^D|ψ_D⟩` of an actual unit state, with
       the events a resolution of identity.  Then NORMALIZATION is no longer an
       assumed field but a THEOREM (`bornω_sum_one`), derived from the already-
       discharged Born functional (`GleasonSelector.born_add/born_one`).  This
       ties the Lorentz strand to the axiom-free Gleason strand.

  Everything here is axiom-free (standard Lean axioms only); what remains open
  is unchanged — the *realization* of such data from a genuine relativistic QFT
  (Type III₁ / Tomita–Takesaki existence).  This module makes the conditional
  interface RIGID and CONNECTED, not the existence proved.
-/

import QIQTH.LorentzSelection
import QIQTH.GleasonSelector
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace QIQTH
namespace LorentzSelectionStrong

open LorentzSelection
open GleasonSelector
open Matrix
open scoped BigOperators
open scoped ComplexOrder

variable {Diam : Type*} [Preorder Diam]

universe uD uX

/- ── A. Externalized geometry: rigid holographic bound + boundary ──────── -/

/-- **External geometric data**, fixed before any net is chosen.  This is the
    fix for review point (ii): because `N` and `Boundary` live OUTSIDE the net,
    the holographic bound `card ≤ N D` and the reconstruction `P.X D ≃ Boundary`
    can no longer be satisfied by the cheap choices `N := card` / `Pb := P`. -/
structure GeometrySpec (Diam : Type uD) [Preorder Diam] where
  /-- the holographic atom budget `N D ≈ ⌊exp Q_D⌋`, externally fixed -/
  N : Diam → ℕ
  /-- holographic monotonicity: a sub-diamond has no more capacity -/
  N_mono : ∀ {K D : Diam}, K ≤ D → N K ≤ N D
  /-- the boundary / screen record presheaf, externally fixed -/
  Boundary : RecordPresheaf.{uD, uX} Diam

/-- **A recorded-history net realizing a fixed geometry spec `S`.**  The
    holographic bound is now measured against the EXTERNAL `S.N`, and
    reconstruction lands in the EXTERNAL `S.Boundary` — both rigid. -/
structure NetOn {Diam : Type uD} [Preorder Diam] (S : GeometrySpec.{uD, uX} Diam) where
  P : RecordPresheaf.{uD, uX} Diam
  fin : ∀ D : Diam, Fintype (P.X D)
  /-- holographic bound against the externally-fixed budget -/
  card_le : ∀ D : Diam, @Fintype.card (P.X D) (fin D) ≤ S.N D
  /-- reconstruction onto the externally-fixed boundary presheaf -/
  recon : ∀ D : Diam, P.X D ≃ S.Boundary.X D
  /-- naturality of reconstruction (commutes with restriction) -/
  recon_nat : ∀ {K D : Diam} (h : K ≤ D) (x : P.X D),
    S.Boundary.restrict h (recon D x) = recon K (P.restrict h x)

/-- **Holographic bound propagates along inclusions** — uses BOTH `card_le` and
    the external monotonicity `N_mono` (so the field `N_mono` is load-bearing). -/
theorem card_le_of_le {S : GeometrySpec Diam} (net : NetOn S) {K D : Diam}
    (h : K ≤ D) : @Fintype.card (net.P.X K) (net.fin K) ≤ S.N D :=
  le_trans (net.card_le K) (S.N_mono h)

/-- **The screen-encoded selected history is a consistent boundary section.**
    Reconstructing a global section `λ` onto the boundary yields a global section
    of `S.Boundary` — the holographic statement "the selected bulk record is
    encoded consistently on the screen."  Genuinely USES `recon_nat`. -/
def reconSection {S : GeometrySpec Diam} (net : NetOn S)
    (lam : GlobalSection net.P) : GlobalSection S.Boundary where
  val := fun D => net.recon D (lam.val D)
  consistent := fun {K D} h => by
    rw [net.recon_nat h, lam.consistent h]

/- ── B. A real Poincaré GROUP action (representation) ──────────────────── -/

/-- **A group action on the record presheaf** — the fix for review point on
    "single automorphism, not a representation."  Carries identity and
    composition laws (a left action: `act (g₁*g₂) = (act g₁).trans (act g₂)`,
    i.e. `act (g₁*g₂) D = act g₂ (act g₁ D)`). -/
structure GroupAction (G : Type*) [Group G] (P : RecordPresheaf Diam) where
  /-- each group element acts as an order automorphism of diamonds -/
  act : G → (Diam ≃o Diam)
  /-- the natural sector isomorphism for each `g` -/
  γ : ∀ (g : G) (D : Diam), P.X D ≃ P.X (act g D)
  /-- naturality of `γ g` (commutes with restriction) -/
  natural : ∀ (g : G) {K D : Diam} (h : K ≤ D) (x : P.X D),
    P.restrict ((act g).monotone h) (γ g D x) = γ g K (P.restrict h x)
  /-- identity law -/
  act_one : act 1 = OrderIso.refl Diam
  /-- composition law -/
  act_mul : ∀ g₁ g₂ : G, act (g₁ * g₂) = (act g₁).trans (act g₂)

/-- Extract the single-element `PoincareAction` for a fixed `g`. -/
def GroupAction.toPoincare {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (g : G) : PoincareAction P where
  act := A.act g
  γ := A.γ g
  natural := A.natural g

/-- **Covariance for EVERY group element** (not one possibly-identity action). -/
theorem group_evaluation_covariance {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (lam : GlobalSection P) (g : G) (D : Diam) :
    selector (actSection (A.toPoincare g) lam) ((A.act g) D)
      = (A.γ g D) (selector lam D) :=
  evaluation_covariance (A.toPoincare g) lam D

/-- The identity element acts trivially on diamonds — USES `act_one`. -/
theorem act_one_diam {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (D : Diam) : (A.act 1) D = D := by
  rw [A.act_one]; rfl

/-- Composition law on diamonds — USES `act_mul` (left action convention). -/
theorem act_mul_diam {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (g₁ g₂ : G) (D : Diam) :
    (A.act (g₁ * g₂)) D = (A.act g₂) ((A.act g₁) D) := by
  rw [A.act_mul]; rfl

/- ── B′. The γ-cocycle: a genuine representation on the fibres ──────────── -/

/-- Transport a record sector along an equality of diamonds (fibre cast).  This
    is the cast the cocycle laws need to compare `γ` over equal-but-not-syntactic
    diamonds (`act (g₁*g₂) D` vs `act g₂ (act g₁ D)`). -/
def fibCast {P : RecordPresheaf Diam} {D D' : Diam} (h : D = D') :
    P.X D ≃ P.X D' := Equiv.cast (congrArg P.X h)

/-- **Identity cocycle law** (`γ 1 = id`, modulo the diamond cast).  This is the
    γ-component of "being a representation," absent from the bare `GroupAction`
    (where the group laws only acted on the base poset). -/
def IsRepOne {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) : Prop :=
  ∀ D : Diam, A.γ 1 D = fibCast (act_one_diam A D).symm

/-- **Composition cocycle law** (`γ (g₁*g₂) = γ g₂ ∘ γ g₁`, modulo the diamond
    cast).  Together with `IsRepOne` this upgrades the family `{γ g}` from "a
    natural equivalence per element" to a genuine action on the record-sector
    fibres — the gap the review flagged. -/
def IsRepMul {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) : Prop :=
  ∀ (g₁ g₂ : G) (D : Diam),
    A.γ (g₁ * g₂) D
      = ((A.γ g₁ D).trans (A.γ g₂ ((A.act g₁) D))).trans
          (fibCast (act_mul_diam A g₁ g₂ D).symm)

/-- **Identity cocycle, pointwise** — CONSUMES `IsRepOne`. -/
theorem γ_rep_one_apply {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (hone : IsRepOne A) (D : Diam) (x : P.X D) :
    A.γ 1 D x = fibCast (act_one_diam A D).symm x := by
  rw [hone D]

/-- **Composition cocycle, pointwise** — CONSUMES `IsRepMul`: applying `g₁` then
    `g₂` to a sector equals applying `g₁*g₂` (up to the diamond cast).  This is
    the representation property at the level of records. -/
theorem γ_cocycle_apply {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (hmul : IsRepMul A) (g₁ g₂ : G) (D : Diam) (x : P.X D) :
    A.γ (g₁ * g₂) D x
      = fibCast (act_mul_diam A g₁ g₂ D).symm
          ((A.γ g₂ ((A.act g₁) D)) (A.γ g₁ D x)) := by
  rw [hmul g₁ g₂ D]; rfl

/- ── C. Equivariant measure: covariance is consumed, not ignored ───────── -/

/-- **A g-covariant weight has g-invariant total mass.**  This theorem
    genuinely CONSUMES the covariance hypothesis `hcov` (by reindexing the sum
    along the sector equivalence `γ g D`) — unlike `covariant_selection_of_net`,
    which ignored the measure.  This is the measure-level content review point
    (i) found missing. -/
theorem measure_pushforward_total {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (ω : ∀ D : Diam, P.X D → ℝ)
    (hcov : ∀ (g : G) (D : Diam) (x : P.X D), ω (A.act g D) (A.γ g D x) = ω D x)
    (g : G) (D : Diam) [Fintype (P.X D)] [Fintype (P.X (A.act g D))] :
    ∑ y : P.X (A.act g D), ω (A.act g D) y = ∑ x : P.X D, ω D x := by
  rw [← Equiv.sum_comp (A.γ g D) (ω (A.act g D))]
  exact Finset.sum_congr rfl (fun x _ => hcov g D x)

/-- **Per-cell measure covariance** (the stronger, non-coarse statement the
    review asked for).  The weight on a sector `y` over the boosted diamond
    equals the weight on its pre-image sector over the original diamond — not
    merely equal total mass.  CONSUMES `hcov` (at the pulled-back point). -/
theorem measure_pushforward_cell {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (ω : ∀ D : Diam, P.X D → ℝ)
    (hcov : ∀ (g : G) (D : Diam) (x : P.X D), ω (A.act g D) (A.γ g D x) = ω D x)
    (g : G) (D : Diam) (y : P.X (A.act g D)) :
    ω (A.act g D) y = ω D ((A.γ g D).symm y) := by
  have h := hcov g D ((A.γ g D).symm y)
  rwa [Equiv.apply_symm_apply] at h

/- ── G. The Born link: normalization is DERIVED, not assumed ───────────── -/

/-- The Born functional is additive over a finite sum of effects (folds
    `born_add`). -/
theorem born_sum {n : Type*} [Fintype n] [DecidableEq n] (ψ : n → ℂ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → Matrix n n ℂ) :
    born ψ (∑ i ∈ s, E i) = ∑ i ∈ s, born ψ (E i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [born]
  · intro a t ha ih
    rw [Finset.sum_insert ha, born_add, ih, Finset.sum_insert ha]

/-- **Born data realizing the weights of a net.**  Each diamond carries a finite
    Hilbert space `Fin (dim D)`, a unit state `ψ_D`, and a resolution of identity
    `{E_x^D}` indexed by the record sectors `P.X D`.  This is the anti-vacuity
    lock: the weights are pinned to Born values, not free PMF data. -/
structure BornData (P : RecordPresheaf Diam) where
  fin : ∀ D : Diam, Fintype (P.X D)
  ddeq : ∀ D : Diam, DecidableEq (P.X D)
  /-- local Hilbert-space dimension on each diamond -/
  dim : Diam → ℕ
  /-- the (restricted) global state on each diamond -/
  ψ : ∀ D : Diam, Fin (dim D) → ℂ
  /-- the state is a unit vector `⟨ψ|ψ⟩ = 1` -/
  ψ_unit : ∀ D : Diam, star (ψ D) ⬝ᵥ (ψ D) = 1
  /-- the record effect (projector) for each sector -/
  E : ∀ D : Diam, P.X D → Matrix (Fin (dim D)) (Fin (dim D)) ℂ
  /-- the effects are a resolution of identity (PVM completeness) -/
  complete : ∀ D : Diam,
    @Finset.sum (P.X D) _ _ (@Finset.univ (P.X D) (fin D)) (E D) = 1

/-- The Born weight of sector `x` on diamond `D`: `⟨ψ_D|E_x^D|ψ_D⟩`. -/
noncomputable def bornω {P : RecordPresheaf Diam} (B : BornData P)
    (D : Diam) (x : P.X D) : ℂ := born (B.ψ D) (B.E D x)

/-- **Normalization is a THEOREM, not an assumption.**  When the weights are
    Born values of a unit state on a resolution of identity, they sum to `1`.
    Proof: `∑ born = born (∑ E) = born 1 = ⟨ψ|ψ⟩ = 1`, via the already-discharged
    `born_sum` / `born_one`.  This is the field `ω_norm` of `RecordedHistoryNet`
    DERIVED — the link between the Lorentz strand and the axiom-free Gleason
    strand. -/
theorem bornω_sum_one {P : RecordPresheaf Diam} (B : BornData P) (D : Diam) :
    @Finset.sum (P.X D) ℂ _ (@Finset.univ (P.X D) (B.fin D)) (bornω B D) = 1 := by
  haveI := B.ddeq D
  have h1 : @Finset.sum (P.X D) ℂ _ (@Finset.univ (P.X D) (B.fin D)) (bornω B D)
      = born (B.ψ D)
          (@Finset.sum (P.X D) _ _ (@Finset.univ (P.X D) (B.fin D)) (B.E D)) :=
    (born_sum (B.ψ D) (@Finset.univ (P.X D) (B.fin D)) (B.E D)).symm
  rw [h1, B.complete D]
  exact born_one (B.ψ D) (B.ψ_unit D)

/-- The real (probability) Born weight. -/
noncomputable def bornωRe {P : RecordPresheaf Diam} (B : BornData P)
    (D : Diam) (x : P.X D) : ℝ := (bornω B D x).re

/-- **Real normalization** — the probabilities sum to `1`. -/
theorem bornωRe_sum_one {P : RecordPresheaf Diam} (B : BornData P) (D : Diam) :
    @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (bornωRe B D) = 1 := by
  have hc := bornω_sum_one B D
  have hre : @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (bornωRe B D)
      = (@Finset.sum (P.X D) ℂ _ (@Finset.univ (P.X D) (B.fin D)) (bornω B D)).re :=
    (Complex.re_sum (@Finset.univ (P.X D) (B.fin D)) (fun x => bornω B D x)).symm
  rw [hre, hc, Complex.one_re]

/- ── G′. PVM positivity: weights are genuine PROBABILITIES ─────────────── -/

/-- A Hermitian idempotent (orthogonal projection) is positive semidefinite:
    `P = Pᴴ P`, so `P = Eᴴ*E`-form. -/
theorem proj_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {E : Matrix n n ℂ} (hh : Eᴴ = E) (hi : E * E = E) : E.PosSemidef := by
  have he : Eᴴ * E = E := by rw [hh]; exact hi
  have hp := posSemidef_conjTranspose_mul_self E
  rwa [he] at hp

/-- **Born value of a PSD effect is nonnegative** (and real): `0 ≤ ⟨ψ|E|ψ⟩` in
    `ℂ`.  This is the matrix-adjoint positivity the review asked to mechanize,
    obtained from `PosSemidef.dotProduct_mulVec_nonneg`. -/
theorem born_posSemidef_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : n → ℂ) {E : Matrix n n ℂ} (hE : E.PosSemidef) :
    0 ≤ born ψ E := by
  unfold born
  exact hE.dotProduct_mulVec_nonneg ψ

/-- **A projection-valued measure realizing the net's weights.**  Strengthens
    `BornData` with the requirement that every effect is a Hermitian projection
    (an orthogonal PVM element), the constraint the review flagged as missing —
    without it, `complete : ∑ E = 1` permits signed/complex "weights." -/
structure PVMData (P : RecordPresheaf Diam) extends BornData P where
  /-- each effect is self-adjoint -/
  proj_herm : ∀ (D : Diam) (x : P.X D), (E D x)ᴴ = E D x
  /-- each effect is idempotent (a projection) -/
  proj_idem : ∀ (D : Diam) (x : P.X D), (E D x) * (E D x) = E D x

/-- **Born weights of a PVM are nonnegative** — the missing half of "these are
    probabilities."  `0 ≤ bornωRe`, from projection ⇒ PSD ⇒ `⟨ψ|E|ψ⟩ ≥ 0`. -/
theorem pvm_bornωRe_nonneg {P : RecordPresheaf Diam} (B : PVMData P)
    (D : Diam) (x : P.X D) : 0 ≤ bornωRe B.toBornData D x := by
  have hps : (B.E D x).PosSemidef := proj_posSemidef (B.proj_herm D x) (B.proj_idem D x)
  have hnn : (0 : ℂ) ≤ born (B.ψ D) (B.E D x) := born_posSemidef_nonneg (B.ψ D) hps
  unfold bornωRe bornω
  simpa using (Complex.nonneg_iff.mp hnn).1

/-- **Born weights of a PVM are real** (zero imaginary part) — so `bornωRe`
    loses no information. -/
theorem pvm_bornω_im_zero {P : RecordPresheaf Diam} (B : PVMData P)
    (D : Diam) (x : P.X D) : (bornω B.toBornData D x).im = 0 := by
  have hps : (B.E D x).PosSemidef := proj_posSemidef (B.proj_herm D x) (B.proj_idem D x)
  have hnn : (0 : ℂ) ≤ born (B.ψ D) (B.E D x) := born_posSemidef_nonneg (B.ψ D) hps
  unfold bornω
  exact ((Complex.nonneg_iff.mp hnn).2).symm

/-- **PVM weights form a finite probability distribution.**  Combining
    `pvm_bornωRe_nonneg` (nonneg) with `bornωRe_sum_one` (sums to 1): the Born
    lock now yields genuine PROBABILITY normalization, not merely an affine
    functional summing to 1 — the review's single highest-value gap, closed.  (A
    `PMF` term is then immediate from these two facts.) -/
theorem pvm_isProbability {P : RecordPresheaf Diam} (B : PVMData P) (D : Diam) :
    (∀ x : P.X D, 0 ≤ bornωRe B.toBornData D x) ∧
      @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (bornωRe B.toBornData D) = 1 :=
  ⟨fun x => pvm_bornωRe_nonneg B D x, bornωRe_sum_one B.toBornData D⟩

/- ── H. Measure covariance DERIVED from unitarity (hcov is now a theorem) ── -/

/-  HONEST-SCOPE CAVEAT (2026-06-08, post GPT-5.5-pro review).  What is "derived
    from unitarity" below is the COVARIANCE OF THE BORN KERNEL `(ψ,E) ↦ ⟨ψ,Eψ⟩`
    under unitary transport of the state and effects (`born_unitary_invariant`,
    consumed by `ubornω_covariant` GIVEN the `UnitaryCovariance` transport laws
    `ψ_cov`/`E_cov`).  This is the *automatic* equivariance of the Born functional
    — it is NOT, and must not be read as, a derivation that the actuality-selector
    measure μ over λ MUST be Born, nor does it discharge the Layer-B measure-
    EQUIVARIANCE premise.  That premise (the Born distribution is dynamically
    preserved / is the typicality measure) remains an INDEPENDENT, provably-
    necessary postulate: see `EquivarianceGap` (support-preservation ≠ measure-
    preservation) and `BornMinimalityTable`.  In short: "covariance of the Born
    candidate" (here, free) ≠ "the selector law is forced to be Born" (open). -/

/-- **The Born functional is unitary-invariant** — the unconditional core fact:
    `⟨Uψ| U E Uᴴ |Uψ⟩ = ⟨ψ|E|ψ⟩` for `Uᴴ U = 1`.  This is a genuine theorem
    (no hypotheses beyond unitarity).  It lets us derive covariance of the Born
    KERNEL given unitary transport (see the honest-scope caveat above — this does
    NOT discharge the Layer-B equivariance premise). -/
theorem born_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (ψ : n → ℂ) (E : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    born (U *ᵥ ψ) (U * E * Uᴴ) = born ψ E := by
  have hUU : Uᴴ *ᵥ (U *ᵥ ψ) = ψ := by rw [mulVec_mulVec, hU, one_mulVec]
  have e1 : (U * E * Uᴴ) *ᵥ (U *ᵥ ψ) = U *ᵥ (E *ᵥ ψ) := by
    rw [mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hUU]
  unfold born
  rw [e1, star_mulVec, dotProduct_mulVec, vecMul_vecMul, hU, vecMul_one]

/-- **Uniform-dimension Born data**: the local Hilbert space has a single
    dimension `d` across all diamonds (the boosted region carries an isomorphic
    Hilbert space — the natural setting for a *unitary* Poincaré transport, with
    no fibre-dimension casts).  Otherwise identical to `BornData`. -/
structure UniformBornData (P : RecordPresheaf Diam) where
  fin : ∀ D : Diam, Fintype (P.X D)
  ddeq : ∀ D : Diam, DecidableEq (P.X D)
  d : ℕ
  ψ : Diam → Fin d → ℂ
  ψ_unit : ∀ D : Diam, star (ψ D) ⬝ᵥ (ψ D) = 1
  E : ∀ D : Diam, P.X D → Matrix (Fin d) (Fin d) ℂ
  complete : ∀ D : Diam,
    @Finset.sum (P.X D) _ _ (@Finset.univ (P.X D) (fin D)) (E D) = 1

/-- The (real) Born weight for uniform-dimension data. -/
noncomputable def ubornω {P : RecordPresheaf Diam} (B : UniformBornData P)
    (D : Diam) (x : P.X D) : ℝ := (born (B.ψ D) (B.E D x)).re

/-- **Unitary Poincaré transport**: the LOWER-LEVEL covariance the review asked
    us to assume *instead of* `hcov`.  For each `g` and `D` a unitary `U g D`
    implements the action — the state transforms `ψ_{gD} = U_{g,D} ψ_D` and the
    effects conjugate `E_{gD}(γ_g x) = U_{g,D} (E_D x) U_{g,D}ᴴ`.  From THIS,
    measure covariance is a theorem (`ubornω_covariant`), not a premise. -/
structure UnitaryCovariance {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (B : UniformBornData P) where
  /-- the unitary implementing `g` on the local Hilbert space of `D` -/
  U : G → Diam → Matrix (Fin B.d) (Fin B.d) ℂ
  /-- unitarity -/
  U_unit : ∀ (g : G) (D : Diam), (U g D)ᴴ * (U g D) = 1
  /-- the state transforms unitarily -/
  ψ_cov : ∀ (g : G) (D : Diam), B.ψ (A.act g D) = (U g D) *ᵥ (B.ψ D)
  /-- the effects conjugate unitarily, intertwined with the sector map `γ` -/
  E_cov : ∀ (g : G) (D : Diam) (x : P.X D),
    B.E (A.act g D) (A.γ g D x) = (U g D) * (B.E D x) * (U g D)ᴴ

/-- **Measure covariance is now a THEOREM** (`hcov` derived).  Given unitary
    transport of the state and effects, the Born weights are covariant:
    `ω_{gD}(γ_g x) = ω_D(x)`.  Proof: substitute the transport laws and apply
    `born_unitary_invariant`.  This converts the previously-assumed `hcov` into a
    consequence of lower-level unitary equivariance — the review's top ask. -/
theorem ubornω_covariant {G : Type*} [Group G] {P : RecordPresheaf Diam}
    {A : GroupAction G P} {B : UniformBornData P} (C : UnitaryCovariance A B)
    (g : G) (D : Diam) (x : P.X D) :
    ubornω B (A.act g D) (A.γ g D x) = ubornω B D x := by
  unfold ubornω
  rw [C.ψ_cov g D, C.E_cov g D x,
    born_unitary_invariant (C.U g D) (B.ψ D) (B.E D x) (C.U_unit g D)]

/-- **Per-cell pushforward covariance, now UNCONDITIONAL** (given unitary
    transport): `ω_{gD}(y) = ω_D(γ_g⁻¹ y)`, with the measure-covariance input
    discharged by `ubornω_covariant` rather than assumed. -/
theorem ubornω_pushforward_cell {G : Type*} [Group G] {P : RecordPresheaf Diam}
    {A : GroupAction G P} {B : UniformBornData P} (C : UnitaryCovariance A B)
    (g : G) (D : Diam) (y : P.X (A.act g D)) :
    ubornω B (A.act g D) y = ubornω B D ((A.γ g D).symm y) :=
  measure_pushforward_cell A (ubornω B) (fun g D x => ubornω_covariant C g D x) g D y

/-- **Total-mass invariance, now UNCONDITIONAL** (given unitary transport). -/
theorem ubornω_total_invariant {G : Type*} [Group G] {P : RecordPresheaf Diam}
    {A : GroupAction G P} {B : UniformBornData P} (C : UnitaryCovariance A B)
    (g : G) (D : Diam) :
    @Finset.sum (P.X (A.act g D)) ℝ _ (@Finset.univ (P.X (A.act g D)) (B.fin (A.act g D)))
        (ubornω B (A.act g D))
      = @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (ubornω B D) :=
  @measure_pushforward_total Diam _ G _ P A (ubornω B)
    (fun g D x => ubornω_covariant C g D x) g D (B.fin D) (B.fin (A.act g D))

/- ── I. The γ-cocycle threaded onto the SELECTION (item 1) ─────────────── -/

/-- **The selection transports as a cocycle.**  The record selected at `D`,
    transported by the composite `g₁*g₂`, equals `g₂` applied to the *actual
    selection on the `g₁`-pushed section* — i.e. multi-step transformed
    selections agree with the one-step transform.  CONSUMES the γ-cocycle
    `IsRepMul` (via `γ_cocycle_apply`) and the structural `group_evaluation_
    covariance`, threading `act_mul` through `actSection`.  This is the
    representation property at the level of the selector, not just of `γ`. -/
theorem selection_cocycle {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (hmul : IsRepMul A) (lam : GlobalSection P)
    (g₁ g₂ : G) (D : Diam) :
    A.γ (g₁ * g₂) D (selector lam D)
      = fibCast (act_mul_diam A g₁ g₂ D).symm
          (A.γ g₂ ((A.act g₁) D)
            (selector (actSection (A.toPoincare g₁) lam) ((A.act g₁) D))) := by
  rw [γ_cocycle_apply A hmul g₁ g₂ D (selector lam D),
      ← group_evaluation_covariance A lam g₁ D]

/- ── J. Unified COVARIANT PROBABILITY data (item 4) ────────────────────── -/

/-- Normalization for uniform Born data (the `UniformBornData` analogue of
    `bornωRe_sum_one`): `∑_x ω = 1`. -/
theorem ubornω_sum_one {P : RecordPresheaf Diam} (B : UniformBornData P) (D : Diam) :
    @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (ubornω B D) = 1 := by
  haveI := B.ddeq D
  have h1 : @Finset.sum (P.X D) ℂ _ (@Finset.univ (P.X D) (B.fin D))
        (fun x => born (B.ψ D) (B.E D x))
      = born (B.ψ D)
          (@Finset.sum (P.X D) _ _ (@Finset.univ (P.X D) (B.fin D)) (B.E D)) :=
    (born_sum (B.ψ D) (@Finset.univ (P.X D) (B.fin D)) (B.E D)).symm
  have hcomplex : @Finset.sum (P.X D) ℂ _ (@Finset.univ (P.X D) (B.fin D))
        (fun x => born (B.ψ D) (B.E D x)) = 1 := by
    rw [h1, B.complete D]; exact born_one (B.ψ D) (B.ψ_unit D)
  have hre : @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (ubornω B D)
      = (@Finset.sum (P.X D) ℂ _ (@Finset.univ (P.X D) (B.fin D))
          (fun x => born (B.ψ D) (B.E D x))).re :=
    (Complex.re_sum (@Finset.univ (P.X D) (B.fin D))
      (fun x => born (B.ψ D) (B.E D x))).symm
  rw [hre, hcomplex, Complex.one_re]

/-- **Uniform Born data that is also a PVM** — both the unitary-covariance layer
    (`UniformBornData` + `UnitaryCovariance`) and the probability layer (PVM
    positivity) in ONE object, closing the review's "two structures" gap. -/
structure UniformPVMData (P : RecordPresheaf Diam) extends UniformBornData P where
  proj_herm : ∀ (D : Diam) (x : P.X D), (E D x)ᴴ = E D x
  proj_idem : ∀ (D : Diam) (x : P.X D), (E D x) * (E D x) = E D x

/-- PVM uniform Born weights are nonnegative. -/
theorem upvm_ubornω_nonneg {P : RecordPresheaf Diam} (B : UniformPVMData P)
    (D : Diam) (x : P.X D) : 0 ≤ ubornω B.toUniformBornData D x := by
  have hps : (B.E D x).PosSemidef := proj_posSemidef (B.proj_herm D x) (B.proj_idem D x)
  have hnn : (0 : ℂ) ≤ born (B.ψ D) (B.E D x) := born_posSemidef_nonneg (B.ψ D) hps
  unfold ubornω
  simpa using (Complex.nonneg_iff.mp hnn).1

/-- **A covariant probability distribution — the unified capstone.**  For uniform
    PVM data with a unitary Poincaré transport, the Born weights on each diamond
    are simultaneously (i) nonnegative, (ii) summing to `1`, and (iii) Poincaré-
    covariant `ω_{gD}(γ_g x) = ω_D(x)` — a genuine probability distribution whose
    covariance is *derived* (not assumed).  This fuses the PVM-positivity strand
    and the unitary-covariance strand into one object, the last in-interface gap
    the review named. -/
theorem upvm_covariant_probability {G : Type*} [Group G] {P : RecordPresheaf Diam}
    {A : GroupAction G P} {B : UniformPVMData P}
    (C : UnitaryCovariance A B.toUniformBornData) (g : G) (D : Diam) :
    (∀ x : P.X D, 0 ≤ ubornω B.toUniformBornData D x) ∧
    (@Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D))
        (ubornω B.toUniformBornData D) = 1) ∧
    (∀ x : P.X D, ubornω B.toUniformBornData (A.act g D) (A.γ g D x)
        = ubornω B.toUniformBornData D x) :=
  ⟨fun x => upvm_ubornω_nonneg B D x,
   ubornω_sum_one B.toUniformBornData D,
   fun x => ubornω_covariant C g D x⟩

/- ── K. Coherence: unitary transport preserves the PVM (item 4 coherence) ─ -/

/-- **Unitary conjugation preserves a projection.**  If `E` is a Hermitian
    idempotent and `Uᴴ U = 1`, then `U E Uᴴ` is again a Hermitian idempotent.
    This is the coherence fact behind `E_cov`: the boosted effects are guaranteed
    to remain PVM elements (answering the review's "is the structure secretly
    over-determined / contradictory?" — no, it is automatically consistent). -/
theorem proj_conj_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {U E : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hh : Eᴴ = E) (hi : E * E = E) :
    (U * E * Uᴴ)ᴴ = U * E * Uᴴ ∧ (U * E * Uᴴ) * (U * E * Uᴴ) = U * E * Uᴴ := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_mul, hh, ← mul_assoc]
  · have h1 : (U * E * Uᴴ) * (U * E * Uᴴ) = U * E * (Uᴴ * U) * E * Uᴴ := by noncomm_ring
    rw [h1, hU, mul_one, mul_assoc U E E, hi]

/-- **The boosted effects remain a PVM** (coherence as a THEOREM).  Given the
    unitary transport `E_cov` and unitarity, the effect on the boosted diamond
    `E_{gD}(γ_g x)` is a Hermitian idempotent — so `UnitaryCovariance` over a
    `UniformPVMData` is internally consistent, not over-determined. -/
theorem E_cov_preserves_proj {G : Type*} [Group G] {P : RecordPresheaf Diam}
    {A : GroupAction G P} {B : UniformPVMData P}
    (C : UnitaryCovariance A B.toUniformBornData) (g : G) (D : Diam) (x : P.X D) :
    (B.E (A.act g D) (A.γ g D x))ᴴ = B.E (A.act g D) (A.γ g D x) ∧
      (B.E (A.act g D) (A.γ g D x)) * (B.E (A.act g D) (A.γ g D x))
        = B.E (A.act g D) (A.γ g D x) := by
  rw [C.E_cov g D x]
  exact proj_conj_unitary (C.U_unit g D) (B.proj_herm D x) (B.proj_idem D x)

/-- **Covariant probability distribution, packaged** (API polish, review item).
    The three facts of `upvm_covariant_probability` as a single `Prop`-bundle. -/
structure CovariantProbability {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (B : UniformBornData P) : Prop where
  nonneg : ∀ (D : Diam) (x : P.X D), 0 ≤ ubornω B D x
  sum_one : ∀ D : Diam,
    @Finset.sum (P.X D) ℝ _ (@Finset.univ (P.X D) (B.fin D)) (ubornω B D) = 1
  covariant : ∀ (g : G) (D : Diam) (x : P.X D),
    ubornω B (A.act g D) (A.γ g D x) = ubornω B D x

/-- A uniform PVM with unitary transport IS a covariant probability. -/
theorem covariantProbability_of_unitaryPVM {G : Type*} [Group G]
    {P : RecordPresheaf Diam} {A : GroupAction G P} {B : UniformPVMData P}
    (C : UnitaryCovariance A B.toUniformBornData) :
    CovariantProbability A B.toUniformBornData where
  nonneg := fun D x => upvm_ubornω_nonneg B D x
  sum_one := fun D => ubornω_sum_one B.toUniformBornData D
  covariant := fun g D x => ubornω_covariant C g D x

/-- **Unitary transport preserves the resolution of identity** — completeness,
    not just individual projections, is preserved.  Conjugating the source PVM's
    resolution of identity `∑_x E_x = 1` by `U` gives `U·1·Uᴴ = U Uᴴ = 1` (the
    last step uses `U Uᴴ = 1`, derived from the finite-square `Uᴴ U = 1` via
    `mul_eq_one_comm`).  Together with `E_cov` (`E_{gD}(γ x) = U E_x Uᴴ`) and
    `E_cov_preserves_proj`, this says the boosted effects form a FULL PVM —
    closing the preservation gap the review left (only projections were
    preserved before). -/
theorem unitary_preserves_resolution {G : Type*} [Group G] {P : RecordPresheaf Diam}
    {A : GroupAction G P} {B : UniformPVMData P}
    (C : UnitaryCovariance A B.toUniformBornData) (g : G) (D : Diam) :
    (C.U g D)
        * (@Finset.sum (P.X D) _ _ (@Finset.univ (P.X D) (B.fin D)) (B.E D))
        * (C.U g D)ᴴ = 1 := by
  rw [B.complete D, mul_one]
  exact mul_eq_one_comm.mpr (C.U_unit g D)

/- ── L. The section-object group-action law (item a — section-level) ────── -/

/-- `fibCast` along `h.symm` undoes `castSector` along `h`. -/
theorem fibCast_symm_castSector {P : RecordPresheaf Diam} {D₀ D₁ : Diam}
    (h : D₀ = D₁) (z : P.X D₀) : fibCast h.symm (castSector h z) = z := by
  cases h; rfl

/-- **Cast-free evaluation of the pushed-forward section at the acted diamond**:
    `(g·λ)(gD) = γ_g(λ_D)` (this is `evaluation_covariance` in `A.act`/`A.γ`
    form — the key fact that makes the section-object law avoid `HEq`). -/
theorem actSection_val_act' {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (g : G) (lam : GlobalSection P) (D : Diam) :
    (actSection (A.toPoincare g) lam).val ((A.act g) D) = A.γ g D (lam.val D) :=
  evaluation_covariance (A.toPoincare g) lam D

/-- **Identity law for the section action**: `1 · λ = λ`.  Uses `IsRepOne` and
    the public eval API; the diamond cast `act 1 D = D` is handled by
    `val_cast` + `fibCast_symm_castSector` (no `HEq`). -/
theorem actSection_one {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (hone : IsRepOne A) (lam : GlobalSection P) :
    actSection (A.toPoincare 1) lam = lam := by
  apply GlobalSection.ext; intro D'
  obtain ⟨D, rfl⟩ : ∃ D, (A.act 1) D = D' :=
    ⟨(A.act 1).symm D', (A.act 1).apply_symm_apply D'⟩
  rw [actSection_val_act' A 1 lam D, γ_rep_one_apply A hone D (lam.val D),
      ← GlobalSection.val_cast lam (act_one_diam A D)]
  exact fibCast_symm_castSector (act_one_diam A D) (lam.val ((A.act 1) D))

/-- **Composition law for the section action**: `(g₁*g₂) · λ = g₂ · (g₁ · λ)` —
    `actSection` is a genuine group action on `Γ(X)`, the section-object–level
    statement of which `selection_cocycle` was the evaluation shadow.  Uses
    `IsRepMul` (the γ-cocycle) and the public eval API; all transports are
    handled by `val_cast` + `fibCast_symm_castSector`, no raw `HEq` (the strategy
    GPT-5.5-pro outlined). -/
theorem actSection_mul {G : Type*} [Group G] {P : RecordPresheaf Diam}
    (A : GroupAction G P) (hmul : IsRepMul A) (lam : GlobalSection P) (g₁ g₂ : G) :
    actSection (A.toPoincare (g₁ * g₂)) lam
      = actSection (A.toPoincare g₂) (actSection (A.toPoincare g₁) lam) := by
  apply GlobalSection.ext; intro D'
  obtain ⟨D, rfl⟩ : ∃ D, (A.act (g₁ * g₂)) D = D' :=
    ⟨(A.act (g₁ * g₂)).symm D', (A.act (g₁ * g₂)).apply_symm_apply D'⟩
  rw [actSection_val_act' A (g₁ * g₂) lam D,
      γ_cocycle_apply A hmul g₁ g₂ D (lam.val D),
      ← actSection_val_act' A g₁ lam D,
      ← actSection_val_act' A g₂ (actSection (A.toPoincare g₁) lam) ((A.act g₁) D),
      ← GlobalSection.val_cast
          (actSection (A.toPoincare g₂) (actSection (A.toPoincare g₁) lam))
          (act_mul_diam A g₁ g₂ D)]
  exact fibCast_symm_castSector (act_mul_diam A g₁ g₂ D)
    ((actSection (A.toPoincare g₂) (actSection (A.toPoincare g₁) lam)).val
      ((A.act (g₁ * g₂)) D))

end LorentzSelectionStrong
end QIQTH
