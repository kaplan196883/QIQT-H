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

end LorentzSelectionStrong
end QIQTH
