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

end QIQTH.TowerGNS
