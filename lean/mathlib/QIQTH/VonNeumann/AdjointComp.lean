/-
  THE VON NEUMANN CAMPAIGN — VN3 (THE_VON_NEUMANN_PLAN.md) — von Neumann's theorem.

  **VON NEUMANN'S THEOREM (`T†T` is self-adjoint)**: for a CLOSED densely defined partial
  linear map `T` on a Hilbert space over any `RCLike` field `𝕜`, the composite `T†T` —
  built by hand on the two-layer domain `{x ∈ dom T | Tx ∈ dom T†}` — is genuinely
  SELF-ADJOINT in the Mathlib `LinearPMap.adjoint` sense (`IsSelfAdjoint` through
  `LinearPMap.instStar`). ABSENT from Mathlib at this pin: no `T†T`/`T*T` result of any
  kind exists there (verified in the campaign consult, file-by-file).

  Route (von Neumann 1932, assembled from VN1 + VN2):
  * `adjointCompDom T` / `adjointComp T`: the two-layer ∃-domain and the hand-rolled
    composite `x ↦ T†(Tx)` (the `towerModularDom`/`towerModularOp` pattern, abstractly —
    `LinearPMap.comp` is deliberately avoided: it demands the whole image in the domain).
  * SYMMETRY: `⟪T†(Tx), y⟫ = ⟪Tx, Ty⟫ = ⟪x, T†(Ty)⟫` — `adjoint_isFormalAdjoint` twice,
    the second through `inner_conj_symm`.
  * SURJECTIVITY of `1 + T†T`: VN2's graph decomposition hands, for every `h`, an
    `x ∈ dom T` with `⟪a, h − x⟫ = ⟪Ta, Tx⟫` for all `a`; conjugating, `h − x` is a Riesz
    witness certifying `Tx ∈ dom T†` (`mem_adjoint_domain_of_exists`) with value
    `T†(Tx) = h − x` (`adjoint_apply_eq`), so `x + T†(Tx) = h`.
  * DENSITY of the two-layer domain (the classical trick — no closedness of `T†T` used):
    any `u ⊥ dom(T†T)` is hit by surjectivity, `u = x + T†(Tx)` with `x ∈ dom(T†T)`, so
    `0 = ⟪x, u⟫ = ‖x‖² + ‖Tx‖²`, forcing `x = 0` and then `u = 0`; `(dom)ᗮ = ⊥` upgrades
    to density through `topologicalClosure_eq_top_iff` (completeness).
  * ★★ the headline `vonNeumann_isSelfAdjoint`: VN1's kernel criterion closes
    `(T†T)† = T†T` from symmetry + surjectivity + density.

  This file is ABSTRACT and REUSABLE: Mathlib-only imports beyond VN1 + VN2, no QIQTH
  dependency (a Mathlib-gap contribution; hypotheses are threaded as arguments, never
  axioms). NOT here (deliberately): the tower/modular application (VN4/VN5 route through
  VN1 directly), positivity or spectral statements for `T†T`, the polar decomposition.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import QIQTH.VonNeumann.SelfAdjointCriterion
import QIQTH.VonNeumann.GraphDecomposition

namespace QIQTH.VonNeumann

open LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### The two-layer domain `{x ∈ dom T | Tx ∈ dom T†}` -/

/-- **The domain of `T†T`**: the two-layer ∃-domain `{x | ∃ hx : x ∈ dom T, Tx ∈ dom T†}`,
a `Submodule 𝕜 E` — closure under `+`/`•`/`0` transports through the linearity of `T`
into the submodule `dom T†` (membership proofs move by proof irrelevance; never rw under
a subtype). -/
noncomputable def adjointCompDom (T : E →ₗ.[𝕜] E) : Submodule 𝕜 E where
  carrier := {x : E | ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T.adjoint.domain}
  zero_mem' := by
    refine ⟨T.domain.zero_mem, ?_⟩
    have hsub : (⟨(0 : E), T.domain.zero_mem⟩ : T.domain) = 0 := Subtype.ext rfl
    rw [hsub, LinearPMap.map_zero]
    exact T.adjoint.domain.zero_mem
  add_mem' := by
    rintro x y ⟨hx, hTx⟩ ⟨hy, hTy⟩
    have hxy : x + y ∈ T.domain := Submodule.add_mem _ hx hy
    have hsub : (⟨x + y, hxy⟩ : T.domain) = ⟨x, hx⟩ + ⟨y, hy⟩ := Subtype.ext rfl
    have hval : T ⟨x + y, hxy⟩ = T ⟨x, hx⟩ + T ⟨y, hy⟩ := by
      rw [hsub]
      exact T.map_add _ _
    refine ⟨hxy, ?_⟩
    rw [hval]
    exact Submodule.add_mem _ hTx hTy
  smul_mem' := by
    rintro c x ⟨hx, hTx⟩
    have hcx : c • x ∈ T.domain := Submodule.smul_mem _ _ hx
    have hsub : (⟨c • x, hcx⟩ : T.domain) = c • ⟨x, hx⟩ := Subtype.ext rfl
    have hval : T ⟨c • x, hcx⟩ = c • T ⟨x, hx⟩ := by
      rw [hsub]
      exact T.map_smul _ _
    refine ⟨hcx, ?_⟩
    rw [hval]
    exact Submodule.smul_mem _ _ hTx

variable {T : E →ₗ.[𝕜] E}

/-- Membership unfolding for the two-layer ∃-domain (definitional). -/
theorem mem_adjointCompDom_iff {x : E} :
    x ∈ adjointCompDom T ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T.adjoint.domain :=
  Iff.rfl

/-- **The membership intro lemma** — memberships in the two-layer domain route through
THIS. -/
theorem mem_adjointCompDom {x : E} (hx : x ∈ T.domain)
    (hTx : T ⟨x, hx⟩ ∈ T.adjoint.domain) : x ∈ adjointCompDom T :=
  ⟨hx, hTx⟩

/-- The subtype-presented membership intro: for `x : dom T` with `Tx ∈ dom T†`, the
underlying vector lies in the two-layer domain (structure eta collapses `⟨↑x, x.2⟩` to
`x`). -/
theorem coe_mem_adjointCompDom (x : T.domain) (hTx : T x ∈ T.adjoint.domain) :
    (x : E) ∈ adjointCompDom T :=
  ⟨x.2, hTx⟩

/-- First-layer extraction: the two-layer domain sits inside `dom T`. -/
theorem mem_domain_of_mem_adjointCompDom {x : E} (h : x ∈ adjointCompDom T) :
    x ∈ T.domain :=
  h.choose

/-- Second-layer extraction: on the two-layer domain, the `T`-image lies in `dom T†` —
stated for an ARBITRARY first-layer membership proof (transport by proof irrelevance,
never rw under a subtype). -/
theorem apply_mem_adjoint_domain_of_mem_adjointCompDom {x : E}
    (h : x ∈ adjointCompDom T) (hx : x ∈ T.domain) :
    T ⟨x, hx⟩ ∈ T.adjoint.domain :=
  h.choose_spec

/-! ### The composite `T†T` as a partial linear map -/

/-- **`T†T` — the von Neumann composite**: the hand-rolled composition `x ↦ T†(Tx)` on
the two-layer ∃-domain (the `towerModularOp` pattern; `LinearPMap.comp` deliberately
avoided). Well-defined by proof irrelevance; additivity/homogeneity transport through
`LinearPMap.map_add`/`map_smul` of `T` and `T†` with `Subtype.ext` moving the identities
under the subtype mk. -/
noncomputable def adjointComp (T : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E where
  domain := adjointCompDom T
  toFun :=
    { toFun := fun x => T.adjoint
        ⟨T ⟨(x : E), mem_domain_of_mem_adjointCompDom x.2⟩,
          apply_mem_adjoint_domain_of_mem_adjointCompDom x.2
            (mem_domain_of_mem_adjointCompDom x.2)⟩
      map_add' := fun x y => by
        have hx := mem_domain_of_mem_adjointCompDom x.2
        have hTx := apply_mem_adjoint_domain_of_mem_adjointCompDom x.2 hx
        have hy := mem_domain_of_mem_adjointCompDom y.2
        have hTy := apply_mem_adjoint_domain_of_mem_adjointCompDom y.2 hy
        have hxy : (x : E) + (y : E) ∈ T.domain := Submodule.add_mem _ hx hy
        have hsub : (⟨(x : E) + (y : E), hxy⟩ : T.domain)
            = ⟨(x : E), hx⟩ + ⟨(y : E), hy⟩ := Subtype.ext rfl
        have hval : T ⟨(x : E) + (y : E), hxy⟩
            = T ⟨(x : E), hx⟩ + T ⟨(y : E), hy⟩ := by
          rw [hsub]
          exact T.map_add _ _
        have hTxy : T ⟨(x : E) + (y : E), hxy⟩ ∈ T.adjoint.domain := by
          rw [hval]
          exact Submodule.add_mem _ hTx hTy
        show T.adjoint ⟨T ⟨(x : E) + (y : E), hxy⟩, hTxy⟩
            = T.adjoint ⟨T ⟨(x : E), hx⟩, hTx⟩ + T.adjoint ⟨T ⟨(y : E), hy⟩, hTy⟩
        have hkey : (⟨T ⟨(x : E) + (y : E), hxy⟩, hTxy⟩ : T.adjoint.domain)
            = ⟨T ⟨(x : E), hx⟩, hTx⟩ + ⟨T ⟨(y : E), hy⟩, hTy⟩ := Subtype.ext hval
        rw [hkey]
        exact T.adjoint.map_add _ _
      map_smul' := fun c x => by
        have hx := mem_domain_of_mem_adjointCompDom x.2
        have hTx := apply_mem_adjoint_domain_of_mem_adjointCompDom x.2 hx
        have hcx : c • (x : E) ∈ T.domain := Submodule.smul_mem _ _ hx
        have hsub : (⟨c • (x : E), hcx⟩ : T.domain) = c • ⟨(x : E), hx⟩ :=
          Subtype.ext rfl
        have hval : T ⟨c • (x : E), hcx⟩ = c • T ⟨(x : E), hx⟩ := by
          rw [hsub]
          exact T.map_smul _ _
        have hTcx : T ⟨c • (x : E), hcx⟩ ∈ T.adjoint.domain := by
          rw [hval]
          exact Submodule.smul_mem _ _ hTx
        show T.adjoint ⟨T ⟨c • (x : E), hcx⟩, hTcx⟩
            = c • T.adjoint ⟨T ⟨(x : E), hx⟩, hTx⟩
        have hkey : (⟨T ⟨c • (x : E), hcx⟩, hTcx⟩ : T.adjoint.domain)
            = c • ⟨T ⟨(x : E), hx⟩, hTx⟩ := Subtype.ext hval
        rw [hkey]
        exact T.adjoint.map_smul _ _ }

/-- The domain of `T†T` is the two-layer ∃-domain (definitional). -/
@[simp]
theorem adjointComp_domain : (adjointComp T).domain = adjointCompDom T :=
  rfl

/-- **THE ONE SPEC LEMMA for `T†T`** (general form): on ANY presentation of the two-layer
membership, `(T†T) x = T† ⟨T ⟨x, hx⟩, hTx⟩` — pure proof irrelevance, `rfl`. -/
theorem adjointComp_apply' (x : (adjointComp T).domain)
    (hx : (x : E) ∈ T.domain) (hTx : T ⟨(x : E), hx⟩ ∈ T.adjoint.domain) :
    adjointComp T x = T.adjoint ⟨T ⟨(x : E), hx⟩, hTx⟩ :=
  rfl

/-- **THE ONE SPEC LEMMA for `T†T`** (mk form):
`(T†T) ⟨x, ⟨hx, hTx⟩⟩ = T† ⟨T ⟨x, hx⟩, hTx⟩`. -/
theorem adjointComp_apply {x : E} (hx : x ∈ T.domain)
    (hTx : T ⟨x, hx⟩ ∈ T.adjoint.domain) :
    adjointComp T ⟨x, mem_adjointCompDom hx hTx⟩ = T.adjoint ⟨T ⟨x, hx⟩, hTx⟩ :=
  rfl

/-- The spec lemma in subtype presentation: for `x : dom T` with `Tx ∈ dom T†`,
`(T†T) ↑x = T† ⟨Tx, hTx⟩` (structure eta, `rfl`). -/
theorem adjointComp_apply_coe (x : T.domain) (hTx : T x ∈ T.adjoint.domain) :
    adjointComp T ⟨(x : E), coe_mem_adjointCompDom x hTx⟩ = T.adjoint ⟨T x, hTx⟩ :=
  rfl

/-- The value of `T†T` depends only on the domain VECTOR (the membership-proof-transport
adapter — never rw under a subtype). -/
theorem adjointComp_congr {x y : E} (hx : x ∈ adjointCompDom T)
    (hy : y ∈ adjointCompDom T) (h : x = y) :
    adjointComp T ⟨x, hx⟩ = adjointComp T ⟨y, hy⟩ := by
  cases h
  rfl

/-! ### Symmetry: `T†T` is formally self-adjoint -/

/-- **SYMMETRY of `T†T`**: `⟪(T†T) x, y⟫ = ⟪x, (T†T) y⟫` on the two-layer domain —
`⟪T†(Tx), y⟫ = ⟪Tx, Ty⟫ = conj ⟪Ty, Tx⟫ = conj ⟪T†(Ty), x⟫ = ⟪x, T†(Ty)⟫`, two
applications of Mathlib's `adjoint_isFormalAdjoint` glued by `inner_conj_symm`. -/
theorem adjointComp_isFormalAdjoint (hd : Dense (T.domain : Set E)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  have hx := mem_domain_of_mem_adjointCompDom x.2
  have hTx := apply_mem_adjoint_domain_of_mem_adjointCompDom x.2 hx
  have hy := mem_domain_of_mem_adjointCompDom y.2
  have hTy := apply_mem_adjoint_domain_of_mem_adjointCompDom y.2 hy
  have h1 : ⟪adjointComp T x, (y : E)⟫
      = ⟪(T ⟨(x : E), hx⟩ : E), (T ⟨(y : E), hy⟩ : E)⟫ := by
    rw [adjointComp_apply' x hx hTx]
    exact adjoint_isFormalAdjoint hd ⟨T ⟨(x : E), hx⟩, hTx⟩ ⟨(y : E), hy⟩
  have h2 : ⟪adjointComp T y, (x : E)⟫
      = ⟪(T ⟨(y : E), hy⟩ : E), (T ⟨(x : E), hx⟩ : E)⟫ := by
    rw [adjointComp_apply' y hy hTy]
    exact adjoint_isFormalAdjoint hd ⟨T ⟨(y : E), hy⟩, hTy⟩ ⟨(x : E), hx⟩
  have h3 : ⟪(x : E), adjointComp T y⟫
      = starRingEnd 𝕜 ⟪adjointComp T y, (x : E)⟫ :=
    (inner_conj_symm _ _).symm
  rw [h1, h3, h2]
  exact (inner_conj_symm _ _).symm

/-! ### Surjectivity: `ran (1 + T†T) = ⊤` (the VN2 graph decomposition, consumed) -/

/-- **SURJECTIVITY of `1 + T†T`** for closed densely defined `T`: every `h : E` is
`x + T†(Tx)` for some `x` in the two-layer domain. VN2's graph decomposition provides
`x ∈ dom T` with `⟪a, h − x⟫ = ⟪Ta, Tx⟫` for all `a ∈ dom T`; conjugating both sides,
`h − x` is a Riesz witness in Mathlib's expected orientation
(`⟪h − x, a⟫ = ⟪Tx, Ta⟫`), so `Tx ∈ dom T†` with `T†(Tx) = h − x`. -/
theorem adjointComp_one_add_surjective (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    ∀ h : E, ∃ x : (adjointComp T).domain, (x : E) + adjointComp T x = h := by
  intro h
  obtain ⟨x, hpair⟩ := exists_pairing_of_isClosed hT h
  -- conjugate VN2's pairing into the adjoint's Riesz orientation
  have hw : ∀ a : T.domain, ⟪h - (x : E), (a : E)⟫ = ⟪(T x : E), T a⟫ := by
    intro a
    rw [← inner_conj_symm, hpair a, inner_conj_symm]
  -- `Tx ∈ dom T†`, with value `h − x`
  have hTx : T x ∈ T.adjoint.domain :=
    mem_adjoint_domain_of_exists _ ⟨h - (x : E), hw⟩
  have hval : T.adjoint ⟨T x, hTx⟩ = h - (x : E) :=
    adjoint_apply_eq hd ⟨T x, hTx⟩ hw
  refine ⟨⟨(x : E), coe_mem_adjointCompDom x hTx⟩, ?_⟩
  rw [adjointComp_apply_coe x hTx, hval]
  abel

/-! ### Density of the two-layer domain (the classical von Neumann trick) -/

/-- **DENSITY of `dom (T†T)`**: for closed densely defined `T`, the two-layer domain is
dense. The classical trick: any `u ⊥ dom(T†T)` is, by surjectivity of `1 + T†T`, of the
form `u = x + T†(Tx)` with `x ∈ dom(T†T)`; then
`0 = ⟪x, u⟫ = ⟪x, x⟫ + ⟪Tx, Tx⟫ = ‖x‖² + ‖Tx‖²`, forcing `x = 0` and hence `u = 0`;
`(dom)ᗮ = ⊥` upgrades to density through `topologicalClosure_eq_top_iff`. -/
theorem vonNeumann_dense_domain (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    Dense ((adjointComp T).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  obtain ⟨x, hxu⟩ := adjointComp_one_add_surjective hT hd u
  have hx := mem_domain_of_mem_adjointCompDom x.2
  have hTx := apply_mem_adjoint_domain_of_mem_adjointCompDom x.2 hx
  -- `u ⊥` the domain element `x`
  have horth : ⟪(x : E), u⟫ = 0 :=
    (Submodule.mem_orthogonal _ u).mp hu (x : E) x.2
  -- `⟪x, T†(Tx)⟫ = ⟪Tx, Tx⟫` (the adjoint pairing, conjugated)
  have hval : ⟪(x : E), adjointComp T x⟫
      = ⟪(T ⟨(x : E), hx⟩ : E), (T ⟨(x : E), hx⟩ : E)⟫ := by
    have h2 : ⟪adjointComp T x, (x : E)⟫
        = ⟪(T ⟨(x : E), hx⟩ : E), (T ⟨(x : E), hx⟩ : E)⟫ := by
      rw [adjointComp_apply' x hx hTx]
      exact adjoint_isFormalAdjoint hd ⟨T ⟨(x : E), hx⟩, hTx⟩ ⟨(x : E), hx⟩
    rw [← inner_conj_symm, h2, inner_conj_symm]
  -- `0 = ⟪x, x⟫ + ⟪Tx, Tx⟫`
  have hzero : ⟪(x : E), (x : E)⟫
      + ⟪(T ⟨(x : E), hx⟩ : E), (T ⟨(x : E), hx⟩ : E)⟫ = 0 := by
    rw [← hval, ← inner_add_right, hxu]
    exact horth
  -- descend to `ℝ`: `‖x‖² + ‖Tx‖² = 0`, so `x = 0`
  have hcast : ((‖(x : E)‖ : 𝕜)) ^ 2 + ((‖(T ⟨(x : E), hx⟩ : E)‖ : 𝕜)) ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K]
    exact hzero
  have hreal : ‖(x : E)‖ ^ 2 + ‖(T ⟨(x : E), hx⟩ : E)‖ ^ 2 = 0 := by
    exact_mod_cast hcast
  have h1 : ‖(x : E)‖ ^ 2 = 0 :=
    ((add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hreal).1
  have hx0 : (x : E) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h1)
  -- hence `u = 0 + T†(T 0) = 0`
  have hxz : x = 0 := by
    ext
    simpa using hx0
  rw [← hxu, hxz, LinearPMap.map_zero]
  simp

/-! ### ★★ THE VON NEUMANN THEOREM ★★ -/

/-- **★★ VON NEUMANN'S THEOREM (VN3)**: for a CLOSED densely defined partial linear map
`T` on a Hilbert space over any `RCLike` field, the composite `T†T` (on the two-layer
domain `{x ∈ dom T | Tx ∈ dom T†}`) is SELF-ADJOINT — `(T†T)† = T†T` in the Mathlib
`LinearPMap.adjoint` sense. Assembled entirely from this campaign: VN1's kernel
criterion, fed by the symmetry of `T†T`, the surjectivity of `1 + T†T` (VN2's graph
decomposition), and the density of the two-layer domain. ABSENT from Mathlib at this
pin. -/
theorem vonNeumann_isSelfAdjoint (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    IsSelfAdjoint (adjointComp T) :=
  isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective
    (vonNeumann_dense_domain hT hd)
    (adjointComp_isFormalAdjoint hd)
    (adjointComp_one_add_surjective hT hd)

/-- Von Neumann's theorem restated as the raw adjoint equation `(T†T)† = T†T` (adapter
corollary, unfolded from the `Star` instance — the VN1 pattern). -/
theorem vonNeumann_adjoint_eq (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    (adjointComp T).adjoint = adjointComp T :=
  LinearPMap.isSelfAdjoint_def.mp (vonNeumann_isSelfAdjoint hT hd)

end QIQTH.VonNeumann
