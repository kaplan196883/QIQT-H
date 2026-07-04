/-
  THE TOMITA OPERATOR T0_1–T0_3 (THE_TOMITA_PLAN.md) — S₀ on the orbit domain.

  constructed on the orbit domain; conjugate-linear partial operator; closable in the
  sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
  claimed.

  T0_1 — the domain `towerTomitaDom`: the ℂ-submodule with carrier
  `{v | ∃ T ∈ towerLimitVN, v = T Ω}` — a submodule OUTRIGHT (towerLimitVN is closed under
  +/•/0), containing Ω and every pure component ↑(of C a), and DENSE (S8's cyclicity of Ω
  for the limit algebra: the span of the same carrier is dense and the carrier is already a
  submodule).

  T0_2 — the operator `towerTomita₀ : TowerGNS →ₛₗ.[starRingEnd ℂ] TowerGNS` (the
  conjugate-linear partial map, binding verdict A1): toFun by Classical.choose,
  well-defined because T ↦ TΩ is INJECTIVE on towerLimitVN (S8's
  `towerLimitVN_eq_of_apply_cyclicVec` — Ω is separating). CHOICE HYGIENE (binding):
  exactly ONE spec lemma `towerTomita₀_apply : S₀ ⟨TΩ, _⟩ = (star T) Ω`; everything
  downstream routes through it; towerTomita₀ is never unfolded. Computed on the core:
  S₀ Ω = Ω and S₀ ↑(of C a) = ↑(of C aᴴ); the image stays in the domain and S₀ is an
  INVOLUTION there.

  T0_3 — CLOSABILITY in the sequence/graph-limit sense (binding verdict A3, banked early,
  independent of the right-multiplication adjoint): TₙΩ → 0 and Tₙ*Ω → v force v = 0 —
  ⟪R_aΩ, Tₙ*Ω⟫ = ⟪Tₙ(R_aΩ), Ω⟫ = ⟪R_a(TₙΩ), Ω⟫ = ⟪TₙΩ, R_a†Ω⟫ → 0 (only the ABSTRACT
  adjoint of R_a is used), so ⟪↑(of C a), v⟫ = 0 on the dense orbit and v = 0.
-/
import Mathlib
import QIQTH.TowerGNS.Separation

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### T0_1 — the orbit domain

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/

/-- **T0_1 — THE ORBIT DOMAIN**: the classical Tomita domain `{TΩ : T ∈ towerLimitVN}` — a
    ℂ-submodule OUTRIGHT, because the limit von Neumann algebra is closed under addition,
    scalar multiplication, and contains 0 (no span is needed).

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/
noncomputable def towerTomitaDom : Submodule ℂ (TowerGNS L ω β) where
  carrier := {v : TowerGNS L ω β | ∃ T ∈ towerLimitVN L ω β,
    v = T (towerCyclicVec L ω β)}
  add_mem' := by
    rintro v w ⟨T, hT, rfl⟩ ⟨S, hS, rfl⟩
    exact ⟨T + S, add_mem hT hS, (ContinuousLinearMap.add_apply T S _).symm⟩
  zero_mem' :=
    ⟨0, zero_mem (towerLimitVN L ω β), (ContinuousLinearMap.zero_apply _).symm⟩
  smul_mem' := by
    rintro c v ⟨T, hT, rfl⟩
    exact ⟨c • T, (towerLimitVN L ω β).toStarSubalgebra.smul_mem hT c,
      (ContinuousLinearMap.smul_apply c T _).symm⟩

/-- Membership in the orbit domain IS the orbit condition (definitional). -/
theorem mem_tomitaDom_iff {v : TowerGNS L ω β} :
    v ∈ towerTomitaDom L ω β
      ↔ ∃ T ∈ towerLimitVN L ω β, v = T (towerCyclicVec L ω β) :=
  Iff.rfl

/-- Ω itself lies in the orbit domain (`T := 1`). -/
theorem cyclicVec_mem_tomitaDom :
    towerCyclicVec L ω β ∈ towerTomitaDom L ω β :=
  ⟨1, one_mem (towerLimitVN L ω β), (ContinuousLinearMap.one_apply _).symm⟩

/-- Every pure tower component `↑(of C a)` lies in the orbit domain (`T := π_C(a)`). -/
theorem of_mem_tomitaDom (C : Finset M) (a : DiamondAlg L C) :
    ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β) ∈ towerTomitaDom L ω β :=
  ⟨towerRep L ω β C a, towerRep_mem_towerLimitVN L ω β C a,
    (towerRep_cyclicVec_of L ω β C a).symm⟩

/-- The orbit of Ω under the limit algebra lies in the orbit domain (tautologically). -/
theorem apply_mem_tomitaDom {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    T (towerCyclicVec L ω β) ∈ towerTomitaDom L ω β :=
  ⟨T, hT, rfl⟩

/-- **T0_1 — THE DOMAIN IS DENSE**: S8's cyclicity of Ω for the limit algebra gives density
    of the SPAN of the orbit; the orbit is already a submodule, so the span collapses into
    it and density transfers. -/
theorem dense_tomitaDom :
    Dense (towerTomitaDom L ω β : Set (TowerGNS L ω β)) := by
  refine (dense_span_limitVN_orbit_cyclicVec L ω β).mono ?_
  exact SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr fun v hv => hv)

/-! ### T0_2 — the operator (choice hygiene: ONE spec lemma; towerTomita₀ never unfolded) -/

/-- **The injectivity of the orbit map** `T ↦ TΩ` on the limit algebra — Ω is separating
    (S8's `towerLimitVN_eq_of_apply_cyclicVec`), so the Tomita assignment `TΩ ↦ T*Ω` is
    well-defined. -/
theorem orbit_injective {T S : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) (hS : S ∈ towerLimitVN L ω β)
    (h : T (towerCyclicVec L ω β) = S (towerCyclicVec L ω β)) : T = S :=
  towerLimitVN_eq_of_apply_cyclicVec L ω β hT hS h

/-- The chosen orbit witness of a domain element (`Classical.choose` — contained HERE, with
    the two witness lemmas below; everything else routes through `tomitaFun_eq` /
    `towerTomita₀_apply`). -/
noncomputable def tomitaWitness (v : towerTomitaDom L ω β) :
    TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  Classical.choose ((mem_tomitaDom_iff L ω β).mp v.2)

/-- The chosen witness lies in the limit algebra. -/
theorem tomitaWitness_mem (v : towerTomitaDom L ω β) :
    tomitaWitness L ω β v ∈ towerLimitVN L ω β :=
  (Classical.choose_spec ((mem_tomitaDom_iff L ω β).mp v.2)).1

/-- The chosen witness reproduces the domain element on Ω. -/
theorem tomitaWitness_apply (v : towerTomitaDom L ω β) :
    (v : TowerGNS L ω β) = tomitaWitness L ω β v (towerCyclicVec L ω β) :=
  (Classical.choose_spec ((mem_tomitaDom_iff L ω β).mp v.2)).2

/-- **The Tomita assignment** `TΩ ↦ (star T) Ω` as a bare function on the orbit domain
    (via the chosen witness — well-defined by `orbit_injective`).

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/
noncomputable def tomitaFun (v : towerTomitaDom L ω β) : TowerGNS L ω β :=
  (star (tomitaWitness L ω β v)) (towerCyclicVec L ω β)

/-- **The choice-discharge lemma**: on ANY orbit presentation `↑v = TΩ` with
    `T ∈ towerLimitVN`, the Tomita assignment computes to `(star T) Ω` — the chosen witness
    EQUALS `T` by injectivity of the orbit map (Ω is separating). -/
theorem tomitaFun_eq {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) (v : towerTomitaDom L ω β)
    (hv : (v : TowerGNS L ω β) = T (towerCyclicVec L ω β)) :
    tomitaFun L ω β v = (star T) (towerCyclicVec L ω β) := by
  have hW : tomitaWitness L ω β v = T :=
    orbit_injective L ω β (tomitaWitness_mem L ω β v) hT
      ((tomitaWitness_apply L ω β v).symm.trans hv)
  show (star (tomitaWitness L ω β v)) (towerCyclicVec L ω β)
    = (star T) (towerCyclicVec L ω β)
  rw [hW]

/-- Conjugate-additivity of the Tomita assignment (additivity, in fact — via injectivity and
    `star_add`). -/
theorem tomitaFun_add (u v : towerTomitaDom L ω β) :
    tomitaFun L ω β (u + v) = tomitaFun L ω β u + tomitaFun L ω β v := by
  obtain ⟨T, hT, hu⟩ := (mem_tomitaDom_iff L ω β).mp u.2
  obtain ⟨S, hS, hv⟩ := (mem_tomitaDom_iff L ω β).mp v.2
  have huv : ((u + v : towerTomitaDom L ω β) : TowerGNS L ω β)
      = (T + S) (towerCyclicVec L ω β) := by
    rw [Submodule.coe_add, hu, hv, ContinuousLinearMap.add_apply]
  rw [tomitaFun_eq L ω β (add_mem hT hS) (u + v) huv, tomitaFun_eq L ω β hT u hu,
    tomitaFun_eq L ω β hS v hv, star_add, ContinuousLinearMap.add_apply]

/-- Conjugate-homogeneity of the Tomita assignment — via injectivity and `star_smul`. -/
theorem tomitaFun_smul (c : ℂ) (v : towerTomitaDom L ω β) :
    tomitaFun L ω β (c • v) = (starRingEnd ℂ) c • tomitaFun L ω β v := by
  obtain ⟨T, hT, hv⟩ := (mem_tomitaDom_iff L ω β).mp v.2
  have hcv : ((c • v : towerTomitaDom L ω β) : TowerGNS L ω β)
      = (c • T) (towerCyclicVec L ω β) := by
    rw [Submodule.coe_smul, hv, ContinuousLinearMap.smul_apply]
  rw [tomitaFun_eq L ω β ((towerLimitVN L ω β).toStarSubalgebra.smul_mem hT c) (c • v) hcv,
    tomitaFun_eq L ω β hT v hv, star_smul, ContinuousLinearMap.smul_apply,
    starRingEnd_apply]

/-- **T0_2 — THE TOMITA OPERATOR** `S₀ : TΩ ↦ T*Ω`, packaged as a CONJUGATE-LINEAR partial
    map (`→ₛₗ.[starRingEnd ℂ]`) on the orbit domain — binding verdict A1.

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/
noncomputable def towerTomita₀ :
    (TowerGNS L ω β) →ₛₗ.[starRingEnd ℂ] (TowerGNS L ω β) where
  domain := towerTomitaDom L ω β
  toFun :=
    { toFun := tomitaFun L ω β
      map_add' := tomitaFun_add L ω β
      map_smul' := tomitaFun_smul L ω β }

/-- **THE ONE SPEC LEMMA** (choice hygiene, binding): `S₀ ⟨TΩ, _⟩ = (star T) Ω` for every
    `T ∈ towerLimitVN` — everything downstream routes through THIS; `towerTomita₀` is never
    unfolded. -/
theorem towerTomita₀_apply {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    towerTomita₀ L ω β ⟨T (towerCyclicVec L ω β), apply_mem_tomitaDom L ω β hT⟩
      = (star T) (towerCyclicVec L ω β) :=
  tomitaFun_eq L ω β hT ⟨T (towerCyclicVec L ω β), apply_mem_tomitaDom L ω β hT⟩ rfl

/-- The value of `S₀` depends only on the domain VECTOR (the membership-proof-transport
    adapter — proofs are irrelevant, so this is `rfl` after substitution). -/
theorem towerTomita₀_congr {x y : TowerGNS L ω β} (hx : x ∈ towerTomitaDom L ω β)
    (hy : y ∈ towerTomitaDom L ω β) (h : x = y) :
    towerTomita₀ L ω β ⟨x, hx⟩ = towerTomita₀ L ω β ⟨y, hy⟩ := by
  cases h
  rfl

/-- **S₀ Ω = Ω** — the cyclic vector is a fixed point (`T := 1`, `star_one`). -/
theorem towerTomita₀_cyclicVec :
    towerTomita₀ L ω β ⟨towerCyclicVec L ω β, cyclicVec_mem_tomitaDom L ω β⟩
      = towerCyclicVec L ω β := by
  calc towerTomita₀ L ω β ⟨towerCyclicVec L ω β, cyclicVec_mem_tomitaDom L ω β⟩
      = towerTomita₀ L ω β
          ⟨(1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) (towerCyclicVec L ω β),
            apply_mem_tomitaDom L ω β (one_mem (towerLimitVN L ω β))⟩ :=
        towerTomita₀_congr L ω β _ _ (ContinuousLinearMap.one_apply _).symm
    _ = (star (1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) (towerCyclicVec L ω β) :=
        towerTomita₀_apply L ω β (one_mem (towerLimitVN L ω β))
    _ = towerCyclicVec L ω β := by rw [star_one, ContinuousLinearMap.one_apply]

/-- **T0_2 — THE EXACT ACTION ON THE PURE-COMPONENT CORE**: `S₀ ↑(of C a) = ↑(of C aᴴ)` —
    the Tomita operator is the ⋆-operation of the tower, computed exactly on the dense core
    (`T := π_C(a)`, the ⋆-law of the representation, and R8's orbit identity twice). -/
theorem towerTomita₀_of (C : Finset M) (a : DiamondAlg L C) :
    towerTomita₀ L ω β ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
        of_mem_tomitaDom L ω β C a⟩
      = ((towerOf L ω β C aᴴ : TowerPre L ω β) : TowerGNS L ω β) := by
  calc towerTomita₀ L ω β ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_tomitaDom L ω β C a⟩
      = towerTomita₀ L ω β ⟨towerRep L ω β C a (towerCyclicVec L ω β),
          apply_mem_tomitaDom L ω β (towerRep_mem_towerLimitVN L ω β C a)⟩ :=
        towerTomita₀_congr L ω β _ _ (towerRep_cyclicVec_of L ω β C a).symm
    _ = (star (towerRep L ω β C a)) (towerCyclicVec L ω β) :=
        towerTomita₀_apply L ω β (towerRep_mem_towerLimitVN L ω β C a)
    _ = towerRep L ω β C (star a) (towerCyclicVec L ω β) := by
        rw [← map_star (towerRep L ω β C) a]
    _ = ((towerOf L ω β C aᴴ : TowerPre L ω β) : TowerGNS L ω β) := by
        rw [Matrix.star_eq_conjTranspose]
        exact towerRep_cyclicVec_of L ω β C aᴴ

/-- The image of `S₀` stays in the orbit domain (`star T ∈ towerLimitVN`). -/
theorem towerTomita₀_mem_tomitaDom (v : towerTomitaDom L ω β) :
    towerTomita₀ L ω β v ∈ towerTomitaDom L ω β := by
  obtain ⟨T, hT, hv⟩ := (mem_tomitaDom_iff L ω β).mp v.2
  have hveq : v = ⟨T (towerCyclicVec L ω β), apply_mem_tomitaDom L ω β hT⟩ :=
    Subtype.ext hv
  have h1 : towerTomita₀ L ω β v = (star T) (towerCyclicVec L ω β) := by
    rw [hveq]; exact towerTomita₀_apply L ω β hT
  rw [h1]
  exact apply_mem_tomitaDom L ω β (star_mem hT)

/-- **The involution, T-parametrized form**: `S₀ ⟨T*Ω, _⟩ = TΩ` — the spec lemma at `star T`
    plus `star_star`. -/
theorem towerTomita₀_star_apply {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    towerTomita₀ L ω β ⟨(star T) (towerCyclicVec L ω β),
        apply_mem_tomitaDom L ω β (star_mem hT)⟩
      = T (towerCyclicVec L ω β) := by
  rw [towerTomita₀_apply L ω β (star_mem hT), star_star]

/-- **T0_2 — S₀ IS AN INVOLUTION on its domain**: `S₀ (S₀ v) = v`. -/
theorem towerTomita₀_involutive (v : towerTomitaDom L ω β) :
    towerTomita₀ L ω β ⟨towerTomita₀ L ω β v, towerTomita₀_mem_tomitaDom L ω β v⟩
      = (v : TowerGNS L ω β) := by
  obtain ⟨T, hT, hv⟩ := (mem_tomitaDom_iff L ω β).mp v.2
  have h1 : towerTomita₀ L ω β v = (star T) (towerCyclicVec L ω β) := by
    have hveq : v = ⟨T (towerCyclicVec L ω β), apply_mem_tomitaDom L ω β hT⟩ :=
      Subtype.ext hv
    rw [hveq]; exact towerTomita₀_apply L ω β hT
  calc towerTomita₀ L ω β ⟨towerTomita₀ L ω β v, towerTomita₀_mem_tomitaDom L ω β v⟩
      = towerTomita₀ L ω β ⟨(star T) (towerCyclicVec L ω β),
          apply_mem_tomitaDom L ω β (star_mem hT)⟩ :=
        towerTomita₀_congr L ω β _ _ h1
    _ = T (towerCyclicVec L ω β) := towerTomita₀_star_apply L ω β hT
    _ = (v : TowerGNS L ω β) := hv.symm

/-! ### T0_3 — CLOSABILITY (the sequence/graph-limit form — binding verdict A3)

    Only the ABSTRACT Hilbert-space adjoint of the right multiplication `R_a` is used; no
    closure object is constructed. -/

/-- **T0_3 — CLOSABILITY, the sequence form**: if `TₙΩ → 0` and `Tₙ*Ω → v` with every
    `Tₙ ∈ towerLimitVN`, then `v = 0` — the graph-limit closability of the Tomita
    assignment. Chain: `⟪R_aΩ, Tₙ*Ω⟫ = ⟪Tₙ(R_aΩ), Ω⟫ = ⟪R_a(TₙΩ), Ω⟫ = ⟪TₙΩ, R_a†Ω⟫ → 0`,
    so `⟪↑(of C a), v⟫ = 0` on R8's dense orbit and `v = 0`.

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/
theorem towerTomita₀_closable (T : ℕ → (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))
    (hT : ∀ n, T n ∈ towerLimitVN L ω β) {v : TowerGNS L ω β}
    (h0 : Filter.Tendsto (fun n => T n (towerCyclicVec L ω β)) Filter.atTop (nhds 0))
    (hv : Filter.Tendsto (fun n => (star (T n)) (towerCyclicVec L ω β)) Filter.atTop
      (nhds v)) : v = 0 := by
  -- the pure-component pairings with v all vanish
  have key : ∀ (C : Finset M) (a : DiamondAlg L C),
      ⟪((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), v⟫_ℂ = 0 := by
    intro C a
    -- the pointwise exchange: ⟪R_aΩ, Tₙ*Ω⟫ = ⟪TₙΩ, R_a†Ω⟫
    have hpt : ∀ n, ⟪towerRightMulCLM L ω β C a (towerCyclicVec L ω β),
          (star (T n)) (towerCyclicVec L ω β)⟫_ℂ
        = ⟪T n (towerCyclicVec L ω β),
            (ContinuousLinearMap.adjoint (towerRightMulCLM L ω β C a))
              (towerCyclicVec L ω β)⟫_ℂ := by
      intro n
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        ← ContinuousLinearMap.mul_apply, ← towerRightMul_comm_limitVN L ω β C a (hT n),
        ContinuousLinearMap.mul_apply]
      exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    -- limit 1: the pairing tends to ⟪R_aΩ, v⟫
    have lim1 : Filter.Tendsto
        (fun n => ⟪towerRightMulCLM L ω β C a (towerCyclicVec L ω β),
          (star (T n)) (towerCyclicVec L ω β)⟫_ℂ) Filter.atTop
        (nhds ⟪towerRightMulCLM L ω β C a (towerCyclicVec L ω β), v⟫_ℂ) :=
      Filter.Tendsto.inner tendsto_const_nhds hv
    -- limit 2: through the exchange, the pairing tends to 0
    have lim2 : Filter.Tendsto
        (fun n => ⟪towerRightMulCLM L ω β C a (towerCyclicVec L ω β),
          (star (T n)) (towerCyclicVec L ω β)⟫_ℂ) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto
          (fun n => ⟪T n (towerCyclicVec L ω β),
            (ContinuousLinearMap.adjoint (towerRightMulCLM L ω β C a))
              (towerCyclicVec L ω β)⟫_ℂ) Filter.atTop
          (nhds ⟪(0 : TowerGNS L ω β),
            (ContinuousLinearMap.adjoint (towerRightMulCLM L ω β C a))
              (towerCyclicVec L ω β)⟫_ℂ) :=
        Filter.Tendsto.inner h0 tendsto_const_nhds
      rw [inner_zero_left] at h2
      exact h2.congr fun n => (hpt n).symm
    have hR0 : ⟪towerRightMulCLM L ω β C a (towerCyclicVec L ω β), v⟫_ℂ = 0 :=
      tendsto_nhds_unique lim1 lim2
    rw [← towerRightMul_cyclicVec L ω β C a]
    exact hR0
  -- span induction over R8's dense orbit, then density kills v
  have hspan : ∀ w, w ∈ Submodule.span ℂ
      {u : TowerGNS L ω β | ∃ (C : Finset M) (a : DiamondAlg L C),
        u = towerRep L ω β C a (towerCyclicVec L ω β)} → ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨C, a, rfl⟩ := hu
      rw [towerRep_cyclicVec_of L ω β C a]
      exact key C a
    | zero => exact inner_zero_left v
    | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
    | smul c x hx ihx => rw [inner_smul_left, ihx, mul_zero]
  exact (dense_span_towerRep_cyclicVec L ω β).eq_zero_of_inner_right ℂ
    fun w hw => hspan w hw

/-- **T0_3 — CLOSABILITY, phrased through S₀**: a domain sequence `xₙ → 0` with
    `S₀ xₙ → v` forces `v = 0` — each `xₙ` is unpacked to an orbit presentation and the
    sequence theorem applies (the ONE contained appearance of choice beyond the spec
    lemma). -/
theorem towerTomita₀_closable' (x : ℕ → towerTomitaDom L ω β)
    (hx0 : Filter.Tendsto (fun n => ((x n : TowerGNS L ω β))) Filter.atTop (nhds 0))
    {v : TowerGNS L ω β}
    (hv : Filter.Tendsto (fun n => towerTomita₀ L ω β (x n)) Filter.atTop (nhds v)) :
    v = 0 := by
  choose T hT hx using fun n => (mem_tomitaDom_iff L ω β).mp (x n).2
  have h0 : Filter.Tendsto (fun n => T n (towerCyclicVec L ω β)) Filter.atTop (nhds 0) :=
    hx0.congr fun n => hx n
  have hS : ∀ n, towerTomita₀ L ω β (x n) = (star (T n)) (towerCyclicVec L ω β) := by
    intro n
    have hxe : x n = ⟨T n (towerCyclicVec L ω β), apply_mem_tomitaDom L ω β (hT n)⟩ :=
      Subtype.ext (hx n)
    rw [hxe]; exact towerTomita₀_apply L ω β (hT n)
  have hv' : Filter.Tendsto (fun n => (star (T n)) (towerCyclicVec L ω β)) Filter.atTop
      (nhds v) := hv.congr fun n => hS n
  exact towerTomita₀_closable L ω β T hT h0 hv'

end QIQTH.TowerGNS
