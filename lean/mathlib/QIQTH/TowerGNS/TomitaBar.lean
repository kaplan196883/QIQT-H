/-
  THE CONJUGATE CLOSURE CC5 (THE_CONJUGATE_CLOSURE_PLAN.md) — S̄, the closure of the Tomita
  operator, AS AN OBJECT.

  S̄ constructed via the ℝ-reduction; the Δ contract: Tomita's F as the conjugate-linear
  adjoint through the sesquilinear pairing ⟪Fy,x⟫ = ⟪S̄x,y⟫, then Δ := F∘S̄ ℂ-linear — the
  named next campaign; Δ/J/polar/KMS/type NOT constructed or claimed.

  The instantiation of the abstract CC1–CC4 theory (`QIQTH/TowerGNS/ConjClosure.lean`) at
  TowerGNS, exactly once (binding verdict A1):

  * `towerTomitaR`   := the ℝ-linear view `realRestrict (towerTomita₀)` — same domain (the
    orbit domain, scalars restricted), same values.
  * `towerTomitaR_isClosable` — the CC2 bridge fed by `towerTomita₀_closable'` (the verbatim
    sequence interface, verdict A3).
  * **`towerTomitaBar` := (towerTomitaR).closure** — S̄, Mathlib's id-linear closure at ℝ.
  * The theorem pack: S̄ is CLOSED; extends S₀ (`le_closure`); agrees with S₀ on the whole
    orbit domain (S̄⟨TΩ⟩ = T*Ω, S̄Ω = Ω, S̄↑(of C a) = ↑(of C aᴴ)); has DENSE domain; is
    conjugate-homogeneous with the concrete c = i-sensitive TWIST GUARD S̄(c•Ω) = conj c • Ω
    (verdict A5); is FULLY INVOLUTIVE on its domain with trivial kernel and range = domain
    (the adjoint-free swap-graph transfer, CC4); and the orbit domain is a CORE
    (`closureHasCore`, for free).

  Choice hygiene (binding): every object behind a named def + spec lemmas; towerTomitaBar is
  NEVER simp-unfolded; domain memberships route through `le_closure` and the
  membership-proof-transport adapter `towerTomitaBar_congr`.
-/
import Mathlib
import QIQTH.TowerGNS.ConjClosure
import QIQTH.TowerGNS.Tomita

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.ConjClosure
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### CC5.0 — the instance smoke test (failure mode 1: the Module ℝ diamond)

    The global priority-900 `complexToReal` instances must resolve on TowerGNS with NO letI
    — checked here before anything is built. -/

noncomputable example : Module ℝ (TowerGNS L ω β) := inferInstance
example : ContinuousSMul ℝ (TowerGNS L ω β) := inferInstance
noncomputable example : NormedSpace ℂ (TowerGNS L ω β) := inferInstance
example : IsScalarTower ℝ ℂ (TowerGNS L ω β) := inferInstance

/-! ### CC5.1 — the ℝ-linear view of S₀ -/

/-- **The ℝ-linear view of the Tomita operator**: `realRestrict towerTomita₀` — same orbit
domain (scalars restricted to ℝ), same values. The vehicle (binding verdict A1) that carries
S₀ into Mathlib's id-linear closure theory. -/
noncomputable def towerTomitaR : TowerGNS L ω β →ₗ.[ℝ] TowerGNS L ω β :=
  realRestrict (towerTomita₀ L ω β)

/-- The domain of the ℝ-view is the orbit domain with scalars restricted (definitional). -/
theorem towerTomitaR_domain :
    (towerTomitaR L ω β).domain = (towerTomitaDom L ω β).restrictScalars ℝ :=
  rfl

/-- Membership in the ℝ-view domain IS membership in the orbit domain (definitional). -/
theorem mem_towerTomitaR_domain_iff {v : TowerGNS L ω β} :
    v ∈ (towerTomitaR L ω β).domain ↔ v ∈ towerTomitaDom L ω β :=
  Iff.rfl

/-- The ℝ-view agrees with S₀ on the orbit domain (the `realRestrict_apply` rfl-spec,
memberships transported by definitional equality of the carriers). -/
theorem towerTomitaR_apply {x : TowerGNS L ω β} (hx : x ∈ towerTomitaDom L ω β)
    (hx' : x ∈ (towerTomitaR L ω β).domain) :
    towerTomitaR L ω β ⟨x, hx'⟩ = towerTomita₀ L ω β ⟨x, hx⟩ :=
  rfl

/-! ### CC5.2 — closability of the ℝ-view -/

/-- **The ℝ-view is closable** — the CC2 sequence bridge `isClosable_of_seq` fed by T0_3's
`towerTomita₀_closable'` (the interfaces match verbatim, binding verdict A3; the domain
memberships are transported by definitional equality). -/
theorem towerTomitaR_isClosable : (towerTomitaR L ω β).IsClosable := by
  refine isClosable_of_seq (towerTomitaR L ω β) ?_
  intro x v hx0 hxv
  exact towerTomita₀_closable' L ω β
    (fun n => ⟨((x n : TowerGNS L ω β)), (x n).2⟩) hx0 hxv

/-! ### CC5.3 — THE CLOSURE S̄ -/

/-- **S̄ — THE CLOSURE OF THE TOMITA OPERATOR**, as an object: the Mathlib closure of the
ℝ-linear view of `towerTomita₀`.

S̄ constructed via the ℝ-reduction; the Δ contract: Tomita's F as the conjugate-linear
adjoint through the sesquilinear pairing ⟪Fy,x⟫ = ⟪S̄x,y⟫, then Δ := F∘S̄ ℂ-linear — the
named next campaign; Δ/J/polar/KMS/type NOT constructed or claimed. -/
noncomputable def towerTomitaBar : TowerGNS L ω β →ₗ.[ℝ] TowerGNS L ω β :=
  (towerTomitaR L ω β).closure

/-- The value of S̄ depends only on the domain VECTOR (the membership-proof-transport
adapter — proofs are irrelevant, so this is `rfl` after substitution). -/
theorem towerTomitaBar_congr {x y : TowerGNS L ω β}
    (hx : x ∈ (towerTomitaBar L ω β).domain) (hy : y ∈ (towerTomitaBar L ω β).domain)
    (h : x = y) :
    towerTomitaBar L ω β ⟨x, hx⟩ = towerTomitaBar L ω β ⟨y, hy⟩ := by
  cases h
  rfl

/-! ### CC5.4 — the theorem pack -/

/-- **(a) S̄ IS CLOSED** — its graph is closed (`IsClosable.closure_isClosed`). -/
theorem towerTomitaBar_isClosed : (towerTomitaBar L ω β).IsClosed :=
  (towerTomitaR_isClosable L ω β).closure_isClosed

/-- **(b) S̄ EXTENDS the ℝ-view of S₀** (`le_closure` — unconditional in Mathlib). -/
theorem towerTomitaR_le_towerTomitaBar :
    towerTomitaR L ω β ≤ towerTomitaBar L ω β :=
  (towerTomitaR L ω β).le_closure

/-- The agreement workhorse: on ANY element of the orbit domain, S̄ is defined and computes
to S₀'s value (domain membership through `le_closure`, agreement through the `≤` of
`LinearPMap`). Everything in (c)–(e) routes through THIS. -/
theorem towerTomitaBar_agrees {x : TowerGNS L ω β} (hx : x ∈ towerTomitaDom L ω β) :
    ∃ h : x ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β ⟨x, h⟩ = towerTomita₀ L ω β ⟨x, hx⟩ := by
  have hx0 : x ∈ (towerTomitaR L ω β).domain := hx
  have hle : towerTomitaR L ω β ≤ towerTomitaBar L ω β :=
    towerTomitaR_le_towerTomitaBar L ω β
  refine ⟨hle.1 hx0, ?_⟩
  have h1 : towerTomitaR L ω β ⟨x, hx0⟩
      = towerTomitaBar L ω β ⟨x, hle.1 hx0⟩ :=
    hle.2 (x := ⟨x, hx0⟩) (y := ⟨x, hle.1 hx0⟩) rfl
  rw [← h1]
  exact towerTomitaR_apply L ω β hx hx0

/-- **(c) S̄ AGREES WITH S₀ ON THE ORBIT DOMAIN**: `S̄ ⟨TΩ⟩ = T*Ω` for every
`T ∈ towerLimitVN`. -/
theorem towerTomitaBar_apply_orbit {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    ∃ hmem : T (towerCyclicVec L ω β) ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β ⟨T (towerCyclicVec L ω β), hmem⟩
        = (star T) (towerCyclicVec L ω β) := by
  obtain ⟨h, hval⟩ := towerTomitaBar_agrees L ω β (apply_mem_tomitaDom L ω β hT)
  exact ⟨h, hval.trans (towerTomita₀_apply L ω β hT)⟩

/-- **(d) S̄ Ω = Ω** — the cyclic vector is a fixed point of the closure. -/
theorem towerTomitaBar_cyclicVec :
    ∃ h : towerCyclicVec L ω β ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β ⟨towerCyclicVec L ω β, h⟩ = towerCyclicVec L ω β := by
  obtain ⟨h, hval⟩ := towerTomitaBar_agrees L ω β (cyclicVec_mem_tomitaDom L ω β)
  exact ⟨h, hval.trans (towerTomita₀_cyclicVec L ω β)⟩

/-- **(e) S̄ ↑(of C a) = ↑(of C aᴴ)** — the closure acts as the conjugate-transpose on the
pure-component core. -/
theorem towerTomitaBar_of (C : Finset M) (a : DiamondAlg L C) :
    ∃ h : ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
        ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β
          ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), h⟩
        = ((towerOf L ω β C aᴴ : TowerPre L ω β) : TowerGNS L ω β) := by
  obtain ⟨h, hval⟩ := towerTomitaBar_agrees L ω β (of_mem_tomitaDom L ω β C a)
  exact ⟨h, hval.trans (towerTomita₀_of L ω β C a)⟩

/-- **(f) THE DOMAIN OF S̄ IS DENSE** — it contains the dense orbit domain. -/
theorem dense_towerTomitaBar_domain :
    Dense ((towerTomitaBar L ω β).domain : Set (TowerGNS L ω β)) := by
  have hd : Dense ((towerTomitaR L ω β).domain : Set (TowerGNS L ω β)) :=
    realRestrict_dense (towerTomita₀ L ω β) (dense_tomitaDom L ω β)
  exact hd.mono fun x hx => (towerTomitaR_le_towerTomitaBar L ω β).1 hx

/-- **(g) S̄ IS CONJUGATE-HOMOGENEOUS** — `realRestrict_conjHomogeneous` (from
`map_smulₛₗ`, the single source of truth for the twist, verdict A5) survives closure
(CC3's `ConjHomogeneous.closure`). -/
theorem towerTomitaBar_conjHomogeneous :
    ConjHomogeneous (towerTomitaBar L ω β) :=
  (realRestrict_conjHomogeneous (towerTomita₀ L ω β)).closure

/-- **(h) THE TWIST GUARD** (binding verdict A5): `S̄ (c • Ω) = conj c • Ω` — the concrete
`c = i`-sensitive check that the twist was not silently swapped. -/
theorem towerTomitaBar_smul_cyclicVec (c : ℂ) :
    ∃ h : c • towerCyclicVec L ω β ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β ⟨c • towerCyclicVec L ω β, h⟩
        = starRingEnd ℂ c • towerCyclicVec L ω β := by
  obtain ⟨hΩ, hΩval⟩ := towerTomitaBar_cyclicVec L ω β
  obtain ⟨hc, hcval⟩ :=
    towerTomitaBar_conjHomogeneous L ω β c ⟨towerCyclicVec L ω β, hΩ⟩
  refine ⟨hc, ?_⟩
  rw [hcval, hΩval]

/-- **(i) the graph of the ℝ-view is swap-invariant** — the graph elements are
`(TΩ, T*Ω)`, and the swap `(T*Ω, TΩ)` is the graph element of `star T` (T0_2's
involution, adjoint-free). -/
theorem towerTomitaR_graphSymm : GraphSymm (towerTomitaR L ω β) := by
  intro p hp
  rw [LinearPMap.mem_graph_iff] at hp
  obtain ⟨y, hy1, hy2⟩ := hp
  have hy : (y : TowerGNS L ω β) ∈ towerTomitaDom L ω β := y.2
  have hSy : towerTomitaR L ω β y
      = towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩ :=
    towerTomitaR_apply L ω β hy y.2
  have hmem : towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩ ∈ towerTomitaDom L ω β :=
    towerTomita₀_mem_tomitaDom L ω β ⟨(y : TowerGNS L ω β), hy⟩
  rw [LinearPMap.mem_graph_iff]
  refine ⟨⟨towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩, hmem⟩, ?_, ?_⟩
  · show towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩ = (Prod.swap p).1
    rw [Prod.fst_swap, ← hy2, hSy]
  · show towerTomitaR L ω β
        ⟨towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩, hmem⟩ = (Prod.swap p).2
    have h2 : towerTomitaR L ω β
          ⟨towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩, hmem⟩
        = towerTomita₀ L ω β ⟨towerTomita₀ L ω β ⟨(y : TowerGNS L ω β), hy⟩, hmem⟩ :=
      towerTomitaR_apply L ω β hmem hmem
    rw [Prod.snd_swap, ← hy1, h2]
    exact towerTomita₀_involutive L ω β ⟨(y : TowerGNS L ω β), hy⟩

/-- **(i) S̄ HAS A SWAP-INVARIANT GRAPH** — graph symmetry survives closure (CC4's
`GraphSymm.closure`, swap is a homeomorphism; no adjoint anywhere). -/
theorem towerTomitaBar_graphSymm : GraphSymm (towerTomitaBar L ω β) :=
  (towerTomitaR_graphSymm L ω β).closure

/-- **(i) S̄ IS FULLY INVOLUTIVE ON ITS DOMAIN**: `S̄ (S̄ x) = x` for EVERY `x` in the
domain of the closure — not just on the orbit core (the adjoint-free swap-graph
argument). -/
theorem towerTomitaBar_involutive (x : (towerTomitaBar L ω β).domain) :
    ∃ h1 : towerTomitaBar L ω β x ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β ⟨towerTomitaBar L ω β x, h1⟩ = (x : TowerGNS L ω β) :=
  (towerTomitaBar_graphSymm L ω β).involutive x

/-- **(i) S̄ HAS TRIVIAL KERNEL**: `S̄ x = 0 → x = 0`. -/
theorem towerTomitaBar_eq_zero (x : (towerTomitaBar L ω β).domain)
    (hx : towerTomitaBar L ω β x = 0) : (x : TowerGNS L ω β) = 0 :=
  (towerTomitaBar_graphSymm L ω β).eq_zero_of_apply_eq_zero x hx

/-- **(i) THE RANGE OF S̄ EQUALS ITS DOMAIN** (both inclusions from involutivity). -/
theorem towerTomitaBar_range_eq_domain :
    Set.range (fun x : (towerTomitaBar L ω β).domain => towerTomitaBar L ω β x)
      = ((towerTomitaBar L ω β).domain : Set (TowerGNS L ω β)) :=
  (towerTomitaBar_graphSymm L ω β).range_eq_domain

/-- **(j) THE ORBIT DOMAIN IS A CORE OF S̄** (`closureHasCore`, for free: restricting S̄
back to the orbit domain and closing again reproduces S̄). -/
theorem towerTomitaBar_hasCore :
    (towerTomitaBar L ω β).HasCore (towerTomitaR L ω β).domain :=
  (towerTomitaR L ω β).closureHasCore

end QIQTH.TowerGNS
