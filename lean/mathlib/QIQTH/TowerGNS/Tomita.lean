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

/-! ### T0_4 — the right-multiplication adjoint (binding verdict A2)

    THE FINITE σ₋ᵢ, COMPUTED — not analytically continued: the commutant-side right
    multiplication `R_a` has the EXACT Hilbert-space adjoint `R_{(rightConj² a)ᴴ}`
    (= `R_{ρ aᴴ ρ⁻¹}` by the modAut bridge below). The engine squared slides the embedded
    corner element past the WHOLE Gibbs density (two E1 applications — no `S_K⁻¹` at stage
    `K`); the stage pairing is `trace_mul_cycle` bookkeeping; the raw layer mirrors
    `rawInner_leftMulRaw_conjTranspose`; the capstone mirrors `towerRepCLM_star`.

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/

/-- **THE ENGINE SQUARED**: `ι(a)·ρ_K = ρ_K·ι(rightConj² a)` — the embedded corner element
    slides past the FULL Gibbs density at the price of TWO √ρ-conjugations: factor
    `ρ_K = S_K·S_K` and apply E1 (`cornerEmbed_mul_sqrtGibbs`) once per square root. -/
theorem cornerEmbed_mul_gibbsDensity {C₀ K : Finset M} (h : C₀ ⊆ K) (a : DiamondAlg L C₀) :
    cornerEmbed L C₀ K h a * gibbsDensity L K ω β
      = gibbsDensity L K ω β
          * cornerEmbed L C₀ K h (rightConj L ω β C₀ (rightConj L ω β C₀ a)) := by
  calc cornerEmbed L C₀ K h a * gibbsDensity L K ω β
      = cornerEmbed L C₀ K h a * (sqrtGibbs L ω β K * sqrtGibbs L ω β K) := by
        rw [sqrtGibbs_mul_self]
    _ = (cornerEmbed L C₀ K h a * sqrtGibbs L ω β K) * sqrtGibbs L ω β K :=
        (Matrix.mul_assoc _ _ _).symm
    _ = (sqrtGibbs L ω β K * cornerEmbed L C₀ K h (rightConj L ω β C₀ a))
          * sqrtGibbs L ω β K := by rw [cornerEmbed_mul_sqrtGibbs]
    _ = sqrtGibbs L ω β K
          * (cornerEmbed L C₀ K h (rightConj L ω β C₀ a) * sqrtGibbs L ω β K) :=
        Matrix.mul_assoc _ _ _
    _ = sqrtGibbs L ω β K * (sqrtGibbs L ω β K
          * cornerEmbed L C₀ K h (rightConj L ω β C₀ (rightConj L ω β C₀ a))) := by
        rw [cornerEmbed_mul_sqrtGibbs]
    _ = (sqrtGibbs L ω β K * sqrtGibbs L ω β K)
          * cornerEmbed L C₀ K h (rightConj L ω β C₀ (rightConj L ω β C₀ a)) :=
        (Matrix.mul_assoc _ _ _).symm
    _ = gibbsDensity L K ω β
          * cornerEmbed L C₀ K h (rightConj L ω β C₀ (rightConj L ω β C₀ a)) := by
        rw [sqrtGibbs_mul_self]

/-- **The stage adjoint pairing**: `⟪x·ι((rightConj² a)ᴴ), y⟫_K = ⟪x, y·ι(a)⟫_K` — unfold the
    GNS form, push ⋆ through the embedding (`cornerEmbed_star`), slide the density by the
    engine squared, and cycle the trace. -/
theorem gnsInner_rightMul_adjoint {C₀ K : Finset M} (h : C₀ ⊆ K) (a : DiamondAlg L C₀)
    (x y : DiamondAlg L K) :
    gnsInner L ω β K
        (x * cornerEmbed L C₀ K h ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ)) y
      = gnsInner L ω β K x (y * cornerEmbed L C₀ K h a) := by
  rw [gnsInner_def, gnsInner_def, Matrix.conjTranspose_mul, cornerEmbed_star,
    Matrix.conjTranspose_conjTranspose]
  calc Matrix.trace (gibbsDensity L K ω β
        * (cornerEmbed L C₀ K h (rightConj L ω β C₀ (rightConj L ω β C₀ a)) * xᴴ * y))
      = Matrix.trace (cornerEmbed L C₀ K h a * (gibbsDensity L K ω β * (xᴴ * y))) := by
        simp only [← Matrix.mul_assoc]
        rw [← cornerEmbed_mul_gibbsDensity L ω β h a]
    _ = Matrix.trace (gibbsDensity L K ω β * (xᴴ * (y * cornerEmbed L C₀ K h a))) := by
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]

/-- **The raw adjoint relation for the right action**: `⟪R₀_{(rightConj² a)ᴴ} x, y⟫ =
    ⟪x, R₀_a y⟫` at the raw direct sum — the exact mirror of
    `rawInner_leftMulRaw_conjTranspose`: double DirectSum induction, both sides embedded at
    the common deep stage `C₀ ⊔ (C ⊔ C')`, where the identity is the stage adjoint pairing. -/
theorem rawInner_rightMulRaw_adjoint (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x y : ⨁ C : Finset M, DiamondAlg L C) :
    rawInner L ω β
        (rightMulRaw L C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ) x) y
      = rawInner L ω β x (rightMulRaw L C₀ a y) := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (rightMulRaw L C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ)),
      map_zero (rawInner L ω β), AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
  | of C v =>
    induction y using DirectSum.induction_on with
    | zero =>
      rw [map_zero (rightMulRaw L C₀ a),
        map_zero (rawInner L ω β
          (rightMulRaw L C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ)
            (DirectSum.of _ C v))),
        map_zero (rawInner L ω β (DirectSum.of _ C v))]
    | of C' w =>
      rw [rightMulRaw_of, rightMulRaw_of, rawInner_of_of, rawInner_of_of]
      have hC₀K : C₀ ⊆ C₀ ⊔ (C ⊔ C') := Finset.subset_union_left
      have hCK : C ⊆ C₀ ⊔ (C ⊔ C') :=
        Finset.subset_union_left.trans Finset.subset_union_right
      have hC'K : C' ⊆ C₀ ⊔ (C ⊔ C') :=
        Finset.subset_union_right.trans Finset.subset_union_right
      rw [pairInner_embed L ω β (C₀ ⊔ C) C' (C₀ ⊔ (C ⊔ C'))
          (Finset.union_subset hC₀K hCK) hC'K,
        pairInner_embed L ω β C (C₀ ⊔ C') (C₀ ⊔ (C ⊔ C'))
          hCK (Finset.union_subset hC₀K hC'K)]
      simp only [cornerEmbed_mul, cornerEmbed_trans]
      exact gnsInner_rightMul_adjoint L ω β hC₀K a _ _
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (rightMulRaw L C₀ a),
        map_add (rawInner L ω β
          (rightMulRaw L C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ)
            (DirectSum.of _ C v))),
        map_add (rawInner L ω β (DirectSum.of _ C v)), h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (rightMulRaw L C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ)),
      map_add (rawInner L ω β), AddMonoidHom.add_apply,
      map_add (rawInner L ω β), AddMonoidHom.add_apply, h₁, h₂]

/-- **T0_4 CAPSTONE — THE RIGHT-MULTIPLICATION ADJOINT** (binding verdict A2):
    `(R_a)† = R_{(rightConj² a)ᴴ}` — the commutant-side right multiplication has an EXACT
    adjoint, again a right multiplication, by the finite-stage `σ₋ᵢ`-image of `aᴴ`
    (COMPUTED, not analytically continued). Proved with the explicit candidate through
    `eq_adjoint_iff` + double completion induction — the `towerRepCLM_star` shape.

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/
theorem towerRightMulCLM_adjoint (C₀ : Finset M) (a : DiamondAlg L C₀) :
    ContinuousLinearMap.adjoint (towerRightMulCLM L ω β C₀ a)
      = towerRightMulCLM L ω β C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ) := by
  refine Eq.symm ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun ξ η => ?_)
  induction ξ, η using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [towerRightMulCLM_coe, towerRightMulCLM_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, towerInner_def, towerInner_def]
    exact rawInner_rightMulRaw_adjoint L ω β C₀ a x y

/-- **The modAut bridge**: `(rightConj² a)ᴴ = modAut ρ_{C₀} aᴴ = ρ·aᴴ·ρ⁻¹` — the adjoint
    parameter of T0_4 IS the finite modular automorphism (the held finite `σ₋ᵢ` of
    `towerState_kms_boundary`'s calculus) applied to `aᴴ`. Entrywise: two half-power
    conjugations compose into the full weight ratio, and the ⋆ flips it. -/
theorem rightConj_sq_conjTranspose_eq_modAut (C₀ : Finset M) (a : DiamondAlg L C₀) :
    (rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ
      = modAut (gibbsDensity L C₀ ω β) aᴴ := by
  have hmul : gibbsDensity L C₀ ω β * gibbsInv L C₀ ω β = 1 := by
    rw [gibbsInv, gibbsDensity, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (gibbsWeight_pos L C₀ ω β i).ne',
      Complex.ofReal_one]
  have hrhs : modAut (gibbsDensity L C₀ ω β) aᴴ
      = gibbsDensity L C₀ ω β * aᴴ * gibbsInv L C₀ ω β := by
    rw [modAut, invOf_eq_right_inv hmul]
  rw [hrhs, gibbsDensity, gibbsInv]
  ext m n
  rw [Matrix.conjTranspose_apply, rightConj_apply, rightConj_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  have h1 : ((Real.sqrt (gibbsWeight L C₀ ω β m) : ℝ) : ℂ)
        * ((Real.sqrt (gibbsWeight L C₀ ω β m) : ℝ) : ℂ)
      = ((gibbsWeight L C₀ ω β m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (gibbsWeight_pos L C₀ ω β m).le]
  have h2 : ((Real.sqrt (gibbsWeight L C₀ ω β n) : ℝ) : ℂ)
        * ((Real.sqrt (gibbsWeight L C₀ ω β n) : ℝ) : ℂ)
      = ((gibbsWeight L C₀ ω β n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (gibbsWeight_pos L C₀ ω β n).le]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  rw [← h1, ← h2]
  ring

/-! ### T0_5 — the adjoint-domain pairing capstone (binding verdict A4)

    The classical `⟪T*Ω, T′Ω⟫ = ⟪T′*Ω, TΩ⟫` with `T′ = R_a` on the dense pure-component
    family — the pairing family carries the full adjoint-domain content (no second
    choice-based operator is packaged).

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/

/-- **T0_5 CAPSTONE — THE ADJOINT-DOMAIN PAIRING**: for every `T ∈ towerLimitVN` and every
    pure component, `⟪T*Ω, ↑(of C₀ a)⟫ = ⟪↑(of C₀ (rightConj² a)ᴴ), TΩ⟫` — the Tomita
    assignment `S₀ : TΩ ↦ T*Ω` is paired against the computed right-multiplication adjoint
    of T0_4 on the dense orbit family. Chain: `⟪T*Ω, R_aΩ⟫ = ⟪Ω, T(R_aΩ)⟫ = ⟪Ω, R_a(TΩ)⟫
    = ⟪R_a†Ω, TΩ⟫ = ⟪R_{(rightConj² a)ᴴ}Ω, TΩ⟫`.

    constructed on the orbit domain; conjugate-linear partial operator; closable in the
    sequence sense; the closure, Δ, J, KMS-at-the-limit, and type are NOT constructed or
    claimed. -/
theorem tomita_adjoint_pairing {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) (C₀ : Finset M) (a : DiamondAlg L C₀) :
    ⟪(star T) (towerCyclicVec L ω β),
        ((towerOf L ω β C₀ a : TowerPre L ω β) : TowerGNS L ω β)⟫_ℂ
      = ⟪((towerOf L ω β C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ)
            : TowerPre L ω β) : TowerGNS L ω β), T (towerCyclicVec L ω β)⟫_ℂ := by
  rw [← towerRightMul_cyclicVec L ω β C₀ a,
    ← towerRightMul_cyclicVec L ω β C₀ ((rightConj L ω β C₀ (rightConj L ω β C₀ a))ᴴ),
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.mul_apply, ← towerRightMul_comm_limitVN L ω β C₀ a hT,
    ContinuousLinearMap.mul_apply, ← towerRightMulCLM_adjoint L ω β C₀ a,
    ContinuousLinearMap.adjoint_inner_left]

end QIQTH.TowerGNS
