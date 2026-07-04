/-
  THE MODULAR OPERATOR M3 (THE_MODULAR_OPERATOR_PLAN.md) — Tomita's F at TowerGNS.

  F on the ∃-Riesz domain; the boundedness equivalence not formalized/not needed; Δ next;
  Δ†=Δ/J/Δ^{it}/KMS/type NOT constructed or claimed.

  The instantiation of the abstract M1–M2 theory (`QIQTH/TowerGNS/ConjAdjoint.lean`) at
  the tower, exactly once:

  * `towerTomitaF := conjAdjoint (towerTomitaBar) (dense_towerTomitaBar_domain)` — Tomita's
    F, the conjugate-linear adjoint of S̄ through the sesquilinear pairing ⟪Fy, x⟫ = ⟪S̄x, y⟫,
    packaged as a (starRingEnd ℂ)-semilinear partial map on the ∃-Riesz domain (verdict A2:
    no toDual, no CLM extension, no boundedness predicate — the classical equivalence of the
    ∃-Riesz domain with the boundedness domain is NOT formalized and NOT needed).
  * THE KEY MEMBERSHIP + VALUE (verdict A4(v)): every pure component lies in dom F and
    **F ↑(of C b) = ↑(of C ((rightConj² b)ᴴ))** — the pairing is established FIRST on the
    orbit core (towerTomitaR's domain, where elements ARE TΩ's and `tomita_adjoint_pairing`
    applies VERBATIM), THEN extended to all of dom S̄ = dom (towerTomitaR.closure) by the M2
    equalizer lemma `pairing_extends_of_closure`.
  * FΩ = Ω (at C = ∅, b = 1, through the modAut bridge: (rightConj² 1)ᴴ = modAut ρ 1 = 1);
    dom F is DENSE (it contains every pure component and is a ℂ-submodule); the i-sensitive
    TWIST GUARD F(c•Ω) = conj c • Ω (from `map_smulₛₗ` alone — the twist is never guessed).

  Choice hygiene (binding): all memberships route through the intro lemma
  `mem_towerTomitaF_dom`; values route through `conjAdjoint_eq` (the choice-discharge) and
  the membership-proof-transport adapter `towerTomitaF_congr`; `towerTomitaF` is never
  unfolded downstream.
-/
import Mathlib
import QIQTH.TowerGNS.ConjAdjoint
import QIQTH.TowerGNS.TomitaBar

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.ConjAdjoint
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### M3.1 — Tomita's F at the tower

    F on the ∃-Riesz domain; the boundedness equivalence not formalized/not needed; Δ next;
    Δ†=Δ/J/Δ^{it}/KMS/type NOT constructed or claimed. -/

/-- **TOMITA'S F AT THE TOWER**: the conjugate-linear adjoint of S̄ through the sesquilinear
pairing `⟪F y, x⟫ = ⟪S̄ x, y⟫`, on the ∃-Riesz domain (M1's `conjAdjoint`, fed by the density
of dom S̄).

F on the ∃-Riesz domain; the boundedness equivalence not formalized/not needed; Δ next;
Δ†=Δ/J/Δ^{it}/KMS/type NOT constructed or claimed. -/
noncomputable def towerTomitaF :
    TowerGNS L ω β →ₛₗ.[starRingEnd ℂ] TowerGNS L ω β :=
  conjAdjoint (towerTomitaBar L ω β) (dense_towerTomitaBar_domain L ω β)

/-- Membership in dom F IS the ∃-Riesz condition against S̄ (from
`mem_conjAdjointDom_iff`). -/
theorem mem_towerTomitaF_dom_iff {y : TowerGNS L ω β} :
    y ∈ (towerTomitaF L ω β).domain ↔
      ∃ w : TowerGNS L ω β, ∀ x : (towerTomitaBar L ω β).domain,
        ⟪(towerTomitaBar L ω β x : TowerGNS L ω β), y⟫_ℂ
          = ⟪w, (x : TowerGNS L ω β)⟫_ℂ :=
  mem_conjAdjointDom_iff

/-- **The membership intro lemma** — ALL later memberships route through THIS: any Riesz
witness `w` for `y` against S̄ certifies `y ∈ dom F`. -/
theorem mem_towerTomitaF_dom {y w : TowerGNS L ω β}
    (h : ∀ x : (towerTomitaBar L ω β).domain,
      ⟪(towerTomitaBar L ω β x : TowerGNS L ω β), y⟫_ℂ
        = ⟪w, (x : TowerGNS L ω β)⟫_ℂ) :
    y ∈ (towerTomitaF L ω β).domain :=
  mem_conjAdjointDom h

/-- The value of F depends only on the domain VECTOR (the membership-proof-transport
adapter — the `towerTomitaBar_congr` pattern; never rw under a subtype). -/
theorem towerTomitaF_congr {x y : TowerGNS L ω β}
    (hx : x ∈ (towerTomitaF L ω β).domain) (hy : y ∈ (towerTomitaF L ω β).domain)
    (h : x = y) :
    towerTomitaF L ω β ⟨x, hx⟩ = towerTomitaF L ω β ⟨y, hy⟩ := by
  cases h
  rfl

/-! ### M3.2 — THE KEY MEMBERSHIP: pure components lie in dom F

    Route (verdict A4(v)): the CORE identity first — on the orbit domain the elements ARE
    `TΩ`'s and T0_5's `tomita_adjoint_pairing` applies VERBATIM — then the M2 equalizer
    extension to all of dom S̄ = dom (towerTomitaR.closure). -/

/-- **The core pairing** on the orbit domain: for every `x` in dom S₀ (presented as `TΩ`),
`⟪S₀ x, ↑(of C b)⟫ = ⟪↑(of C ((rightConj² b)ᴴ)), x⟫` — unpack the orbit presentation, route
the value through `towerTomitaR_apply`/`towerTomita₀_apply`, and apply T0_5's
`tomita_adjoint_pairing` verbatim. -/
theorem towerTomitaR_adjoint_pairing (C : Finset M) (b : DiamondAlg L C)
    (x : (towerTomitaR L ω β).domain) :
    ⟪(towerTomitaR L ω β x : TowerGNS L ω β),
        ((towerOf L ω β C b : TowerPre L ω β) : TowerGNS L ω β)⟫_ℂ
      = ⟪((towerOf L ω β C ((rightConj L ω β C (rightConj L ω β C b))ᴴ)
            : TowerPre L ω β) : TowerGNS L ω β), (x : TowerGNS L ω β)⟫_ℂ := by
  have hx : (x : TowerGNS L ω β) ∈ towerTomitaDom L ω β := x.2
  obtain ⟨T, hT, hxT⟩ := (mem_tomitaDom_iff L ω β).mp hx
  have h1 : towerTomitaR L ω β x
      = towerTomita₀ L ω β ⟨(x : TowerGNS L ω β), hx⟩ :=
    towerTomitaR_apply L ω β hx x.2
  have h2 : towerTomita₀ L ω β ⟨(x : TowerGNS L ω β), hx⟩
      = towerTomita₀ L ω β
          ⟨T (towerCyclicVec L ω β), apply_mem_tomitaDom L ω β hT⟩ :=
    towerTomita₀_congr L ω β hx (apply_mem_tomitaDom L ω β hT) hxT
  have hval : towerTomitaR L ω β x = (star T) (towerCyclicVec L ω β) := by
    rw [h1, h2]
    exact towerTomita₀_apply L ω β hT
  rw [hval, hxT]
  exact tomita_adjoint_pairing L ω β hT C b

/-- **The pairing on ALL of dom S̄** — the M2 equalizer extension
(`pairing_extends_of_closure` at `towerTomitaR`, whose closure IS `towerTomitaBar`
definitionally): `⟪S̄ x, ↑(of C b)⟫ = ⟪↑(of C ((rightConj² b)ᴴ)), x⟫` for every
`x` in dom S̄. -/
theorem towerTomitaBar_adjoint_pairing (C : Finset M) (b : DiamondAlg L C)
    (x : (towerTomitaBar L ω β).domain) :
    ⟪(towerTomitaBar L ω β x : TowerGNS L ω β),
        ((towerOf L ω β C b : TowerPre L ω β) : TowerGNS L ω β)⟫_ℂ
      = ⟪((towerOf L ω β C ((rightConj L ω β C (rightConj L ω β C b))ᴴ)
            : TowerPre L ω β) : TowerGNS L ω β), (x : TowerGNS L ω β)⟫_ℂ :=
  pairing_extends_of_closure (towerTomitaR_isClosable L ω β)
    (towerTomitaR_adjoint_pairing L ω β C b) x

/-- **M3 KEY MEMBERSHIP — every pure component lies in dom F**: the Riesz witness for
`↑(of C b)` is `↑(of C ((rightConj² b)ᴴ))`, certified by the extended pairing. -/
theorem of_mem_towerTomitaF_dom (C : Finset M) (b : DiamondAlg L C) :
    ((towerOf L ω β C b : TowerPre L ω β) : TowerGNS L ω β)
      ∈ (towerTomitaF L ω β).domain :=
  mem_towerTomitaF_dom L ω β (towerTomitaBar_adjoint_pairing L ω β C b)

/-! ### M3.3 — THE VALUE ON THE CORE: F ↑(of C b) = ↑(of C ((rightConj² b)ᴴ)) -/

/-- **M3 VALUE ON THE PURE-COMPONENT CORE**: `F ↑(of C b) = ↑(of C ((rightConj² b)ᴴ))` —
the witness IS the value (M1's choice-discharge `conjAdjoint_eq` against the established
pairing; `= ↑(of C (modAut ρ_C bᴴ))` by the modAut bridge — the Δ headline routes through
THIS in M5). -/
theorem towerTomitaF_of (C : Finset M) (b : DiamondAlg L C) :
    towerTomitaF L ω β
        ⟨((towerOf L ω β C b : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerTomitaF_dom L ω β C b⟩
      = ((towerOf L ω β C ((rightConj L ω β C (rightConj L ω β C b))ᴴ)
          : TowerPre L ω β) : TowerGNS L ω β) :=
  conjAdjoint_eq (towerTomitaBar L ω β) (dense_towerTomitaBar_domain L ω β)
    (towerTomitaBar_adjoint_pairing L ω β C b)

/-! ### M3.4 — FΩ = Ω -/

/-- Ω lies in dom F (Ω = ↑(of ∅ 1) definitionally; the key membership at `C = ∅`,
`b = 1`). -/
theorem cyclicVec_mem_towerTomitaF_dom :
    towerCyclicVec L ω β ∈ (towerTomitaF L ω β).domain :=
  of_mem_towerTomitaF_dom L ω β ∅ 1

/-- **F Ω = Ω** — the cyclic vector is a fixed point of Tomita's F: compute at `C = ∅`,
`b = 1` and collapse the parameter through the modAut bridge —
`(rightConj² 1)ᴴ = modAut ρ_∅ 1ᴴ = 1`. -/
theorem towerTomitaF_cyclicVec :
    towerTomitaF L ω β
        ⟨towerCyclicVec L ω β, cyclicVec_mem_towerTomitaF_dom L ω β⟩
      = towerCyclicVec L ω β := by
  have h1 : towerTomitaF L ω β
        ⟨towerCyclicVec L ω β, cyclicVec_mem_towerTomitaF_dom L ω β⟩
      = towerTomitaF L ω β
          ⟨((towerOf L ω β ∅ 1 : TowerPre L ω β) : TowerGNS L ω β),
            of_mem_towerTomitaF_dom L ω β ∅ 1⟩ :=
    towerTomitaF_congr L ω β _ _ rfl
  have h2 : (rightConj L ω β ∅ (rightConj L ω β ∅ (1 : DiamondAlg L ∅)))ᴴ = 1 := by
    rw [rightConj_sq_conjTranspose_eq_modAut, Matrix.conjTranspose_one, modAut_one]
  rw [h1, towerTomitaF_of L ω β ∅ 1, h2]
  rfl

/-! ### M3.5 — the domain of F is dense -/

/-- **THE DOMAIN OF F IS DENSE** — it contains every pure component (M3.2) and is a
ℂ-submodule, so it swallows the span of the dense orbit (the `dense_tomitaDom` pattern
through R8's `dense_span_towerRep_cyclicVec` and the orbit identity). -/
theorem dense_towerTomitaF_dom :
    Dense (((towerTomitaF L ω β).domain : Set (TowerGNS L ω β))) := by
  refine (dense_span_towerRep_cyclicVec L ω β).mono ?_
  refine SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr ?_)
  rintro v ⟨C, a, rfl⟩
  rw [towerRep_cyclicVec_of L ω β C a]
  exact of_mem_towerTomitaF_dom L ω β C a

/-! ### M3.6 — THE TWIST GUARD (i-sensitive, binding failure mode 2) -/

/-- **THE TWIST GUARD**: `F (c • Ω) = conj c • Ω` — the concrete `c = i`-sensitive check
that F is CONJUGATE-linear and the twist was not silently swapped; derived from
`map_smulₛₗ` (the single source of truth for the twist) and `F Ω = Ω` alone. -/
theorem towerTomitaF_smul_cyclicVec (c : ℂ) :
    ∃ h : c • towerCyclicVec L ω β ∈ (towerTomitaF L ω β).domain,
      towerTomitaF L ω β ⟨c • towerCyclicVec L ω β, h⟩
        = starRingEnd ℂ c • towerCyclicVec L ω β := by
  refine ⟨Submodule.smul_mem _ c (cyclicVec_mem_towerTomitaF_dom L ω β), ?_⟩
  have hz : (⟨c • towerCyclicVec L ω β,
        Submodule.smul_mem _ c (cyclicVec_mem_towerTomitaF_dom L ω β)⟩
        : (towerTomitaF L ω β).domain)
      = c • ⟨towerCyclicVec L ω β, cyclicVec_mem_towerTomitaF_dom L ω β⟩ :=
    Subtype.ext rfl
  rw [hz, LinearPMap.map_smulₛₗ, towerTomitaF_cyclicVec L ω β]

/-! ### M4.1 — THE TWO-LAYER ∃-DOMAIN of Δ (verdict A3; failure mode 4)

    dom Δ = {x | ∃ hx : x ∈ dom S̄, S̄⟨x, hx⟩ ∈ dom F} — a `Submodule ℂ`: dom S̄ is only an
    ℝ-submodule, but conjugate-homogeneity of S̄ (`towerTomitaBar_conjHomogeneous`) supplies
    the ℂ-smul membership, and the conjugated value `conj c • S̄x` stays in the ℂ-submodule
    dom F. All membership transport is by proof irrelevance — never rw under a subtype. -/

/-- **THE DOMAIN OF Δ** (verdict A3): the two-layer ∃-domain
`{x | ∃ hx : x ∈ dom S̄, S̄⟨x, hx⟩ ∈ dom F}`, a `Submodule ℂ` — the ℂ-smul membership comes
from the conjugate-homogeneity of S̄, whose `conj c`-twisted value lands back in the
ℂ-submodule dom F. -/
noncomputable def towerModularDom : Submodule ℂ (TowerGNS L ω β) where
  carrier := {x : TowerGNS L ω β | ∃ hx : x ∈ (towerTomitaBar L ω β).domain,
    towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain}
  zero_mem' := by
    refine ⟨(towerTomitaBar L ω β).domain.zero_mem, ?_⟩
    have hsub : (⟨(0 : TowerGNS L ω β), (towerTomitaBar L ω β).domain.zero_mem⟩
        : (towerTomitaBar L ω β).domain) = 0 := Subtype.ext rfl
    rw [hsub, LinearPMap.map_zero]
    exact (towerTomitaF L ω β).domain.zero_mem
  add_mem' := by
    rintro x y ⟨hx, hFx⟩ ⟨hy, hFy⟩
    have hxy : x + y ∈ (towerTomitaBar L ω β).domain := Submodule.add_mem _ hx hy
    have hsub : (⟨x + y, hxy⟩ : (towerTomitaBar L ω β).domain)
        = ⟨x, hx⟩ + ⟨y, hy⟩ := Subtype.ext rfl
    have hbar : towerTomitaBar L ω β ⟨x + y, hxy⟩
        = towerTomitaBar L ω β ⟨x, hx⟩ + towerTomitaBar L ω β ⟨y, hy⟩ := by
      rw [hsub]
      exact (towerTomitaBar L ω β).map_add _ _
    refine ⟨hxy, ?_⟩
    rw [hbar]
    exact Submodule.add_mem _ hFx hFy
  smul_mem' := by
    rintro c x ⟨hx, hFx⟩
    obtain ⟨hcx0, hcval0⟩ := towerTomitaBar_conjHomogeneous L ω β c ⟨x, hx⟩
    have hcx : c • x ∈ (towerTomitaBar L ω β).domain := hcx0
    have hcval : towerTomitaBar L ω β ⟨c • x, hcx⟩
        = starRingEnd ℂ c • towerTomitaBar L ω β ⟨x, hx⟩ := hcval0
    refine ⟨hcx, ?_⟩
    rw [hcval]
    exact Submodule.smul_mem _ _ hFx

/-- Membership unfolding for the two-layer ∃-domain (definitional). -/
theorem mem_towerModularDom_iff {x : TowerGNS L ω β} :
    x ∈ towerModularDom L ω β ↔
      ∃ hx : x ∈ (towerTomitaBar L ω β).domain,
        towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain :=
  Iff.rfl

/-- **The membership intro lemma** — ALL later dom-Δ memberships route through THIS. -/
theorem mem_towerModularDom {x : TowerGNS L ω β}
    (hx : x ∈ (towerTomitaBar L ω β).domain)
    (hF : towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain) :
    x ∈ towerModularDom L ω β :=
  ⟨hx, hF⟩

/-- First-layer extraction: dom Δ ⊆ dom S̄. -/
theorem mem_bar_of_mem_towerModularDom {x : TowerGNS L ω β}
    (h : x ∈ towerModularDom L ω β) : x ∈ (towerTomitaBar L ω β).domain :=
  ((mem_towerModularDom_iff L ω β).mp h).choose

/-- Second-layer extraction: on dom Δ, the S̄-image lies in dom F — stated for an ARBITRARY
first-layer membership proof (transport by proof irrelevance, never rw under a subtype). -/
theorem barF_of_mem_towerModularDom {x : TowerGNS L ω β}
    (h : x ∈ towerModularDom L ω β) (hx : x ∈ (towerTomitaBar L ω β).domain) :
    towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain :=
  ((mem_towerModularDom_iff L ω β).mp h).choose_spec

/-! ### M4.2 — the spec pairing at the tower F

    The single source for all M5 inner-product computations (failure mode 3: ONE pairing
    orientation, `⟪S̄ x, y⟫ = ⟪F y, x⟫`, from M1's `conjAdjoint_apply_spec`). -/

/-- **The F spec pairing at the tower** (from `conjAdjoint_apply_spec`, the one lemma
downstream uses): `⟪S̄ x, y⟫ = ⟪F y, x⟫` for `y` in dom F and `x` in dom S̄. -/
theorem towerTomitaF_pairing (y : (towerTomitaF L ω β).domain)
    (x : (towerTomitaBar L ω β).domain) :
    ⟪(towerTomitaBar L ω β x : TowerGNS L ω β), (y : TowerGNS L ω β)⟫_ℂ
      = ⟪towerTomitaF L ω β y, (x : TowerGNS L ω β)⟫_ℂ :=
  conjAdjoint_apply_spec (towerTomitaBar L ω β) (dense_towerTomitaBar_domain L ω β) y x

/-! ### M4.3 — Δ := F ∘ S̄, THE MODULAR OPERATOR (verdict A3)

    ℂ-linear (the conjugations cancel: Δ(c•x) = F(S̄(c•x)) = F(conj c • S̄x) =
    conj(conj c) • F(S̄x) = c • Δx), packaged as `→ₗ.[ℂ]` so Mathlib's entire id-adjoint
    theory applies (M6). Δ†=Δ/J/Δ^{1/2}/Δ^{it}/KMS/type NOT constructed or claimed. -/

/-- **Δ — THE MODULAR OPERATOR OF THE TOWER LIMIT STATE**: the bespoke composition
`Δ := F ∘ S̄` on the two-layer ∃-domain, a ℂ-LINEAR partial map (the two conjugate-linear
twists cancel). Symmetric, positive, fixes Ω, and acts as the finite modular automorphism
on the pure-component core (M5); Δ†=Δ/J/Δ^{it}/KMS/type NOT constructed or claimed. -/
noncomputable def towerModularOp : TowerGNS L ω β →ₗ.[ℂ] TowerGNS L ω β where
  domain := towerModularDom L ω β
  toFun :=
    { toFun := fun x => towerTomitaF L ω β
        ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β),
            mem_bar_of_mem_towerModularDom L ω β x.2⟩,
          barF_of_mem_towerModularDom L ω β x.2
            (mem_bar_of_mem_towerModularDom L ω β x.2)⟩
      map_add' := fun x y => by
        have hx := mem_bar_of_mem_towerModularDom L ω β x.2
        have hFx := barF_of_mem_towerModularDom L ω β x.2 hx
        have hy := mem_bar_of_mem_towerModularDom L ω β y.2
        have hFy := barF_of_mem_towerModularDom L ω β y.2 hy
        have hxy : (x : TowerGNS L ω β) + (y : TowerGNS L ω β)
            ∈ (towerTomitaBar L ω β).domain := Submodule.add_mem _ hx hy
        have hsub : (⟨(x : TowerGNS L ω β) + (y : TowerGNS L ω β), hxy⟩
            : (towerTomitaBar L ω β).domain)
            = ⟨(x : TowerGNS L ω β), hx⟩ + ⟨(y : TowerGNS L ω β), hy⟩ :=
          Subtype.ext rfl
        have hbar : towerTomitaBar L ω β
              ⟨(x : TowerGNS L ω β) + (y : TowerGNS L ω β), hxy⟩
            = towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩
              + towerTomitaBar L ω β ⟨(y : TowerGNS L ω β), hy⟩ := by
          rw [hsub]
          exact (towerTomitaBar L ω β).map_add _ _
        have hFxy : towerTomitaBar L ω β
              ⟨(x : TowerGNS L ω β) + (y : TowerGNS L ω β), hxy⟩
            ∈ (towerTomitaF L ω β).domain := by
          rw [hbar]
          exact Submodule.add_mem _ hFx hFy
        show towerTomitaF L ω β
              ⟨towerTomitaBar L ω β
                ⟨(x : TowerGNS L ω β) + (y : TowerGNS L ω β), hxy⟩, hFxy⟩
            = towerTomitaF L ω β
                ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩, hFx⟩
              + towerTomitaF L ω β
                  ⟨towerTomitaBar L ω β ⟨(y : TowerGNS L ω β), hy⟩, hFy⟩
        have hkey : (⟨towerTomitaBar L ω β
              ⟨(x : TowerGNS L ω β) + (y : TowerGNS L ω β), hxy⟩, hFxy⟩
            : (towerTomitaF L ω β).domain)
            = ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩, hFx⟩
              + ⟨towerTomitaBar L ω β ⟨(y : TowerGNS L ω β), hy⟩, hFy⟩ :=
          Subtype.ext hbar
        rw [hkey]
        exact (towerTomitaF L ω β).map_add _ _
      map_smul' := fun c x => by
        have hx := mem_bar_of_mem_towerModularDom L ω β x.2
        have hFx := barF_of_mem_towerModularDom L ω β x.2 hx
        obtain ⟨hcx0, hcval0⟩ :=
          towerTomitaBar_conjHomogeneous L ω β c ⟨(x : TowerGNS L ω β), hx⟩
        have hcx : c • (x : TowerGNS L ω β) ∈ (towerTomitaBar L ω β).domain := hcx0
        have hcval : towerTomitaBar L ω β ⟨c • (x : TowerGNS L ω β), hcx⟩
            = starRingEnd ℂ c
              • towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩ := hcval0
        have hFcx : towerTomitaBar L ω β ⟨c • (x : TowerGNS L ω β), hcx⟩
            ∈ (towerTomitaF L ω β).domain := by
          rw [hcval]
          exact Submodule.smul_mem _ _ hFx
        show towerTomitaF L ω β
              ⟨towerTomitaBar L ω β ⟨c • (x : TowerGNS L ω β), hcx⟩, hFcx⟩
            = c • towerTomitaF L ω β
                ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩, hFx⟩
        have hkey : (⟨towerTomitaBar L ω β ⟨c • (x : TowerGNS L ω β), hcx⟩, hFcx⟩
            : (towerTomitaF L ω β).domain)
            = starRingEnd ℂ c
              • ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩, hFx⟩ :=
          Subtype.ext hcval
        rw [hkey, LinearPMap.map_smulₛₗ, starRingEnd_self_apply] }

/-- The domain of Δ is the two-layer ∃-domain (definitional). -/
@[simp]
theorem towerModularOp_domain :
    (towerModularOp L ω β).domain = towerModularDom L ω β :=
  rfl

/-- **THE ONE SPEC LEMMA for Δ** (general form): on ANY presentation of the two-layer
membership, `Δ x = F ⟨S̄ ⟨x, hx⟩, hF⟩` — pure proof irrelevance, `rfl`. -/
theorem towerModularOp_apply' (x : (towerModularOp L ω β).domain)
    (hx : (x : TowerGNS L ω β) ∈ (towerTomitaBar L ω β).domain)
    (hF : towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩
      ∈ (towerTomitaF L ω β).domain) :
    towerModularOp L ω β x
      = towerTomitaF L ω β ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩, hF⟩ :=
  rfl

/-- **THE ONE SPEC LEMMA for Δ** (mk form): `Δ ⟨x, ⟨hx, hF⟩⟩ = F ⟨S̄ ⟨x, hx⟩, hF⟩`. -/
theorem towerModularOp_apply {x : TowerGNS L ω β}
    (hx : x ∈ (towerTomitaBar L ω β).domain)
    (hF : towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain) :
    towerModularOp L ω β ⟨x, mem_towerModularDom L ω β hx hF⟩
      = towerTomitaF L ω β ⟨towerTomitaBar L ω β ⟨x, hx⟩, hF⟩ :=
  rfl

/-- The value of Δ depends only on the domain VECTOR (the membership-proof-transport
adapter — the `towerTomitaBar_congr` pattern; never rw under a subtype). -/
theorem towerModularOp_congr {x y : TowerGNS L ω β}
    (hx : x ∈ towerModularDom L ω β) (hy : y ∈ towerModularDom L ω β) (h : x = y) :
    towerModularOp L ω β ⟨x, hx⟩ = towerModularOp L ω β ⟨y, hy⟩ := by
  cases h
  rfl

/-! ### M5.1 — POSITIVITY: ⟪Δx, x⟫ = ‖S̄x‖² ≥ 0 (verdict A4(ii))

    ONE application of the spec pairing at `y := S̄x`. -/

/-- **POSITIVITY, exact form**: `⟪Δ x, x⟫ = ‖S̄ x‖²` — the spec pairing at `y := S̄x`
turns `⟪F (S̄x), x⟫` into `⟪S̄x, S̄x⟫`, which is the norm squared. -/
theorem towerModularOp_inner_self {x : TowerGNS L ω β}
    (hx : x ∈ (towerTomitaBar L ω β).domain)
    (hF : towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain) :
    ⟪towerModularOp L ω β ⟨x, mem_towerModularDom L ω β hx hF⟩, x⟫_ℂ
      = (‖towerTomitaBar L ω β ⟨x, hx⟩‖ : ℂ) ^ 2 := by
  have h1 : ⟪towerModularOp L ω β ⟨x, mem_towerModularDom L ω β hx hF⟩, x⟫_ℂ
      = ⟪(towerTomitaBar L ω β ⟨x, hx⟩ : TowerGNS L ω β),
          (towerTomitaBar L ω β ⟨x, hx⟩ : TowerGNS L ω β)⟫_ℂ := by
    rw [towerModularOp_apply L ω β hx hF]
    exact (towerTomitaF_pairing L ω β
      ⟨towerTomitaBar L ω β ⟨x, hx⟩, hF⟩ ⟨x, hx⟩).symm
  rw [h1]
  exact inner_self_eq_norm_sq_to_K _

/-- **POSITIVITY, order form**: `0 ≤ ⟪Δ x, x⟫` in the complex order (real and
nonnegative). -/
theorem towerModularOp_inner_self_nonneg {x : TowerGNS L ω β}
    (hx : x ∈ (towerTomitaBar L ω β).domain)
    (hF : towerTomitaBar L ω β ⟨x, hx⟩ ∈ (towerTomitaF L ω β).domain) :
    0 ≤ ⟪towerModularOp L ω β ⟨x, mem_towerModularDom L ω β hx hF⟩, x⟫_ℂ := by
  rw [towerModularOp_inner_self L ω β hx hF, ← Complex.ofReal_pow]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

/-! ### M5.2 — SYMMETRY: IsFormalAdjoint Δ Δ (verdict A4(iii))

    Two applications of the spec pairing + `inner_conj_symm` — at the marked steps ONLY
    (failure mode 3). -/

/-- **SYMMETRY**: `Δ` is a formal adjoint of itself — `⟪Δ x, y⟫ = ⟪x, Δ y⟫` on dom Δ:
`⟪F(S̄x), y⟫ = ⟪S̄y, S̄x⟫ = conj ⟪S̄x, S̄y⟫ = conj ⟪F(S̄y), x⟫ = ⟪x, F(S̄y)⟫`. This is the
statement Mathlib's id-adjoint theory consumes in M6 (`IsFormalAdjoint.le_adjoint`). -/
theorem towerModularOp_isFormalAdjoint :
    (towerModularOp L ω β).IsFormalAdjoint (towerModularOp L ω β) := by
  intro x y
  have hx := mem_bar_of_mem_towerModularDom L ω β x.2
  have hFx := barF_of_mem_towerModularDom L ω β x.2 hx
  have hy := mem_bar_of_mem_towerModularDom L ω β y.2
  have hFy := barF_of_mem_towerModularDom L ω β y.2 hy
  have h1 : ⟪towerModularOp L ω β x, (y : TowerGNS L ω β)⟫_ℂ
      = ⟪(towerTomitaBar L ω β ⟨(y : TowerGNS L ω β), hy⟩ : TowerGNS L ω β),
          (towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩ : TowerGNS L ω β)⟫_ℂ := by
    rw [towerModularOp_apply' L ω β x hx hFx]
    exact (towerTomitaF_pairing L ω β
      ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩, hFx⟩
      ⟨(y : TowerGNS L ω β), hy⟩).symm
  have h2 : ⟪towerModularOp L ω β y, (x : TowerGNS L ω β)⟫_ℂ
      = ⟪(towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hx⟩ : TowerGNS L ω β),
          (towerTomitaBar L ω β ⟨(y : TowerGNS L ω β), hy⟩ : TowerGNS L ω β)⟫_ℂ := by
    rw [towerModularOp_apply' L ω β y hy hFy]
    exact (towerTomitaF_pairing L ω β
      ⟨towerTomitaBar L ω β ⟨(y : TowerGNS L ω β), hy⟩, hFy⟩
      ⟨(x : TowerGNS L ω β), hx⟩).symm
  have h3 : ⟪(x : TowerGNS L ω β), towerModularOp L ω β y⟫_ℂ
      = starRingEnd ℂ ⟪towerModularOp L ω β y, (x : TowerGNS L ω β)⟫_ℂ :=
    (inner_conj_symm _ _).symm
  rw [h1, h3, h2]
  exact (inner_conj_symm _ _).symm

/-! ### M5.3 — ΔΩ = Ω (verdict A4(iv)) -/

/-- Ω lies in dom Δ: `Ω ∈ dom S̄` and `S̄Ω = Ω ∈ dom F` (both from M3/CC5). -/
theorem cyclicVec_mem_towerModularDom :
    towerCyclicVec L ω β ∈ towerModularDom L ω β := by
  obtain ⟨hΩ, hΩval⟩ := towerTomitaBar_cyclicVec L ω β
  refine mem_towerModularDom L ω β hΩ ?_
  rw [hΩval]
  exact cyclicVec_mem_towerTomitaF_dom L ω β

/-- **Δ Ω = Ω** — the cyclic vector is a fixed point of the modular operator:
`Δ Ω = F (S̄ Ω) = F Ω = Ω`, all routed through the congr adapters. -/
theorem towerModularOp_cyclicVec :
    towerModularOp L ω β
        ⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩
      = towerCyclicVec L ω β := by
  obtain ⟨hΩ, hΩval⟩ := towerTomitaBar_cyclicVec L ω β
  have hF : towerTomitaBar L ω β ⟨towerCyclicVec L ω β, hΩ⟩
      ∈ (towerTomitaF L ω β).domain := by
    rw [hΩval]
    exact cyclicVec_mem_towerTomitaF_dom L ω β
  have h1 : towerModularOp L ω β
        ⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩
      = towerTomitaF L ω β
          ⟨towerTomitaBar L ω β ⟨towerCyclicVec L ω β, hΩ⟩, hF⟩ :=
    towerModularOp_apply' L ω β
      ⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩ hΩ hF
  have h2 : towerTomitaF L ω β ⟨towerTomitaBar L ω β ⟨towerCyclicVec L ω β, hΩ⟩, hF⟩
      = towerTomitaF L ω β
          ⟨towerCyclicVec L ω β, cyclicVec_mem_towerTomitaF_dom L ω β⟩ :=
    towerTomitaF_congr L ω β _ _ hΩval
  rw [h1, h2, towerTomitaF_cyclicVec L ω β]

/-! ### M5.4 — ★★★ THE HEADLINE ★★★ Δ↑(of C a) = ↑(of C (modAut ρ_C a)) (verdict A4(v))

    Δ↑(of C a) = F(S̄↑(of C a)) = F↑(of C aᴴ) [M3/CC5] = ↑(of C ((rightConj² (aᴴ))ᴴ)) [M3]
    = ↑(of C (modAut ρ ((aᴴ)ᴴ))) [the modAut bridge] = ↑(of C (modAut ρ a)) — THE MODULAR
    OPERATOR ACTS AS THE FINITE MODULAR AUTOMORPHISM ON THE PURE-COMPONENT CORE. -/

/-- Every pure component lies in dom Δ: `↑(of C a) ∈ dom S̄` with
`S̄↑(of C a) = ↑(of C aᴴ) ∈ dom F` (the M3 key membership). -/
theorem of_mem_towerModularDom (C : Finset M) (a : DiamondAlg L C) :
    ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
      ∈ towerModularDom L ω β := by
  obtain ⟨h, hval⟩ := towerTomitaBar_of L ω β C a
  refine mem_towerModularDom L ω β h ?_
  rw [hval]
  exact of_mem_towerTomitaF_dom L ω β C aᴴ

/-- **★★★ THE HEADLINE ★★★ — Δ↑(of C a) = ↑(of C (modAut ρ_C a))**: the modular operator
of the tower limit state acts as the FINITE MODULAR AUTOMORPHISM `modAut (gibbsDensity)`
on the dense pure-component core — the modular operator of the physics, computed.
Route: `Δ↑(of C a) = F↑(of C aᴴ) = ↑(of C ((rightConj² (aᴴ))ᴴ)) = ↑(of C (modAut ρ a))`
via the M3 value on the core and the modAut bridge
`rightConj_sq_conjTranspose_eq_modAut`. -/
theorem towerModularOp_of (C : Finset M) (a : DiamondAlg L C) :
    towerModularOp L ω β
        ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerModularDom L ω β C a⟩
      = ((towerOf L ω β C
            (QIQTH.FiniteModularTheory.modAut (gibbsDensity L C ω β) a)
          : TowerPre L ω β) : TowerGNS L ω β) := by
  obtain ⟨h, hval⟩ := towerTomitaBar_of L ω β C a
  have hF : towerTomitaBar L ω β
      ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), h⟩
      ∈ (towerTomitaF L ω β).domain := by
    rw [hval]
    exact of_mem_towerTomitaF_dom L ω β C aᴴ
  have h1 : towerModularOp L ω β
        ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerModularDom L ω β C a⟩
      = towerTomitaF L ω β
          ⟨towerTomitaBar L ω β
            ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), h⟩, hF⟩ :=
    towerModularOp_apply' L ω β
      ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
        of_mem_towerModularDom L ω β C a⟩ h hF
  have h2 : towerTomitaF L ω β
        ⟨towerTomitaBar L ω β
          ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), h⟩, hF⟩
      = towerTomitaF L ω β
          ⟨((towerOf L ω β C aᴴ : TowerPre L ω β) : TowerGNS L ω β),
            of_mem_towerTomitaF_dom L ω β C aᴴ⟩ :=
    towerTomitaF_congr L ω β _ _ hval
  have h3 : (rightConj L ω β C (rightConj L ω β C aᴴ))ᴴ
      = QIQTH.FiniteModularTheory.modAut (gibbsDensity L C ω β) a := by
    rw [rightConj_sq_conjTranspose_eq_modAut, Matrix.conjTranspose_conjTranspose]
  rw [h1, h2, towerTomitaF_of L ω β C aᴴ, h3]

/-! ### M5.5 — the domain of Δ is dense (verdict A4(vi)) -/

/-- **THE DOMAIN OF Δ IS DENSE** — it contains every pure component (M5.4) and is a
ℂ-submodule, so it swallows the span of the dense orbit (the M3.5 pattern). -/
theorem dense_towerModularDom :
    Dense ((towerModularDom L ω β : Set (TowerGNS L ω β))) := by
  refine (dense_span_towerRep_cyclicVec L ω β).mono ?_
  refine SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr ?_)
  rintro v ⟨C, a, rfl⟩
  rw [towerRep_cyclicVec_of L ω β C a]
  exact of_mem_towerModularDom L ω β C a

/-! ### M5.6 — THE Δ TWIST GUARD (i-sensitive, binding failure mode 2) -/

/-- **THE Δ TWIST GUARD**: `Δ (c • Ω) = c • Ω` — ℂ-LINEAR, NO conjugation (the two
conjugate-linear twists of F and S̄ cancel); the concrete `c = i`-sensitive check, derived
from `map_smul` (the single source of truth) and `Δ Ω = Ω` alone. -/
theorem towerModularOp_smul_cyclicVec (c : ℂ) :
    ∃ h : c • towerCyclicVec L ω β ∈ towerModularDom L ω β,
      towerModularOp L ω β ⟨c • towerCyclicVec L ω β, h⟩
        = c • towerCyclicVec L ω β := by
  refine ⟨Submodule.smul_mem _ c (cyclicVec_mem_towerModularDom L ω β), ?_⟩
  have hz : (⟨c • towerCyclicVec L ω β,
        Submodule.smul_mem _ c (cyclicVec_mem_towerModularDom L ω β)⟩
        : (towerModularOp L ω β).domain)
      = c • ⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩ :=
    Subtype.ext rfl
  rw [hz, LinearPMap.map_smul, towerModularOp_cyclicVec L ω β]

/-! ### M6 — the Mathlib hookup: Δ ≤ Δ†, Δ† closed, Δ CLOSABLE

    Near-instantiations of Mathlib's id-ℂ `LinearPMap.adjoint` theory (the Garding
    precedent): symmetry (M5.2) + dense domain (M5.5) feed `IsFormalAdjoint.le_adjoint`;
    `adjoint_isClosed` needs `[CompleteSpace]` (automatic — `TowerGNS` is a
    `UniformSpace.Completion`); closability = closed extension exists.
    Δ†=Δ (self-adjointness of the closure)/J/Δ^{it}/KMS/type NOT constructed or claimed. -/

/-- The density of dom Δ, repackaged on `(towerModularOp L ω β).domain` — the exact form
Mathlib's adjoint theory consumes (`hT` of `le_adjoint`/`adjoint_isClosed`); definitionally
`dense_towerModularDom`. -/
theorem dense_towerModularOp_domain :
    Dense (((towerModularOp L ω β).domain : Set (TowerGNS L ω β))) :=
  dense_towerModularDom L ω β

/-- **Δ ≤ Δ†** — the modular operator is contained in its Mathlib adjoint: symmetry
(`towerModularOp_isFormalAdjoint`, M5.2) + the dense domain (M5.5) through
`LinearPMap.IsFormalAdjoint.le_adjoint`. The adjoint here is Mathlib's genuine unbounded
id-ℂ adjoint on the completion (well-defined because dom Δ is dense). -/
theorem towerModularOp_le_adjoint :
    towerModularOp L ω β ≤ (towerModularOp L ω β).adjoint :=
  (towerModularOp_isFormalAdjoint L ω β).le_adjoint
    (hT := dense_towerModularOp_domain L ω β)

/-- **Δ† is CLOSED** — `LinearPMap.adjoint_isClosed` at the dense domain (the adjoint of any
densely-defined operator is closed; `CompleteSpace (TowerGNS L ω β)` is automatic from the
completion). -/
theorem towerModularOp_adjoint_isClosed :
    (towerModularOp L ω β).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (T := towerModularOp L ω β)
    (dense_towerModularOp_domain L ω β)

/-- **★ Δ IS CLOSABLE** — the closure `Δ̄` exists: Δ has a closed extension, namely its own
adjoint (`towerModularOp_le_adjoint` + `towerModularOp_adjoint_isClosed`), so
`IsClosed.isClosable` + `IsClosable.leIsClosable` give closability. This is the prerequisite
for forming `Δ̄ = (towerModularOp L ω β).closure` and asking `Δ̄† = Δ̄` (von Neumann —
NOT claimed here). -/
theorem towerModularOp_isClosable :
    (towerModularOp L ω β).IsClosable :=
  (towerModularOp_adjoint_isClosed L ω β).isClosable.leIsClosable
    (towerModularOp_le_adjoint L ω β)

/- M6 optional item (closure symmetry/positivity via the equalizer trick) SKIPPED per plan:
   the three required theorems above are the M6 content; closure-level statements belong to
   the von Neumann Δ†=Δ increment (M7+ consult). -/

end QIQTH.TowerGNS
