/-
  ID5 (THE_IDENTIFICATION_PLAN.md) — ★ TOMITA'S THEOREM, FIRST HALF ★ — the campaign
  capstone: Δ^{it} IMPLEMENTS THE MODULAR AUTOMORPHISMS AND PRESERVES towerLimitVN.

  ID4 identified the transported physical flow with the spectral modular flow of Δ
  (`towerModUnitary_eq_towerFlow`: U_t = towerFlow t as bounded operators).  This file
  harvests the identification: every Track-B covariance/invariance theorem of the
  transported flow (FlowCovariance.lean) is now a theorem about the GENUINE modular
  unitary group of Δ — each proof is a rewrite under ID4 followed by the flow-side lemma.

  • `towerModUnitary_towerRep`       — Δ^{it} π_C(a) = π_C(σ_t a) Δ^{it} (composition form);
  • `towerModUnitary_conj_towerRep`  — Δ^{it} π_C(a) Δ^{−it} = π_C(σ_t a): the modular
    group of Δ implements the per-corner Gibbs modular flows in the tower representation;
  • ★ `towerLimitVN_modUnitary_invariant` — T ∈ towerLimitVN → Δ^{it} T Δ^{−it} ∈
    towerLimitVN: **Tomita's theorem, first half (Δ^{it} M Δ^{−it} = M), for the tower
    limit state** — the strongly continuous unitary group of the modular operator of the
    state preserves the limit von Neumann algebra;
  • `towerLimitVN_modUnitary_conj_mem_iff` — the iff (bijection) form.

  HONEST SCOPE (binding): ONLY the first half of Tomita's theorem for the finite-stage
  Gibbs inductive-limit state.  No J, no polar decomposition S̄ = JΔ^{1/2}, no second half
  JMJ = M′, no analytic strip-KMS of the limit state (only the finite-stage boundary
  identity elsewhere), no von Neumann type classification, and no continuum/free-field
  object is touched.  Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.Identification
import QIQTH.TowerGNS.FlowCovariance

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped Matrix DirectSum

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The implementation theorem for the modular group of Δ -/

/-- **The composition form of the implementation theorem, for Δ^{it}**:
    `Δ^{it} ∘ π_C(a) = π_C(σ_t a) ∘ Δ^{it}` — `towerFlow_towerRep` rewritten under ID4's
    identification `towerModUnitary t = towerFlow t`. -/
theorem towerModUnitary_towerRep (t : ℝ) (C₀ : Finset M) (a : DiamondAlg L C₀) :
    towerModUnitary L ω β t ∘L towerRep L ω β C₀ a
      = towerRep L ω β C₀ (cornerFlow L ω β C₀ t a) ∘L towerModUnitary L ω β t := by
  rw [towerModUnitary_eq_towerFlow]
  exact towerFlow_towerRep L ω β t C₀ a

/-- **THE MODULAR GROUP OF Δ IMPLEMENTS THE MODULAR AUTOMORPHISMS (conjugation form)**:
    `Δ^{it} π_C(a) Δ^{−it} = π_C(σ_t a)` — the genuine spectral modular group of the tower
    limit state implements the per-corner Gibbs modular flows in the tower representation:
    `towerFlow_conj_towerRep` rewritten under ID4. -/
theorem towerModUnitary_conj_towerRep (t : ℝ) (C₀ : Finset M) (a : DiamondAlg L C₀) :
    towerModUnitary L ω β t ∘L towerRep L ω β C₀ a ∘L towerModUnitary L ω β (-t)
      = towerRep L ω β C₀ (cornerFlow L ω β C₀ t a) := by
  rw [towerModUnitary_eq_towerFlow L ω β t, towerModUnitary_eq_towerFlow L ω β (-t)]
  exact towerFlow_conj_towerRep L ω β t C₀ a

/-! ### ★ Tomita's theorem, first half: Δ^{it} towerLimitVN Δ^{−it} = towerLimitVN -/

/-- **★ TOMITA'S THEOREM, FIRST HALF, FOR THE TOWER LIMIT STATE**:
    `T ∈ towerLimitVN → Δ^{it} T Δ^{−it} ∈ towerLimitVN` — conjugation by the modular
    unitary group of Δ maps the limit von Neumann algebra into itself (with the iff form
    below: ONTO itself — `Δ^{it} M Δ^{−it} = M`).  This is `towerLimitVN_flow_invariant`
    rewritten under ID4's identification: the strongly continuous unitary group of the
    modular operator OF THE STATE preserves the algebra OF THE PHYSICS. -/
theorem towerLimitVN_modUnitary_invariant (t : ℝ)
    {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β} (hT : T ∈ towerLimitVN L ω β) :
    towerModUnitary L ω β t ∘L T ∘L towerModUnitary L ω β (-t) ∈ towerLimitVN L ω β := by
  rw [towerModUnitary_eq_towerFlow L ω β t, towerModUnitary_eq_towerFlow L ω β (-t)]
  exact towerLimitVN_flow_invariant L ω β t hT

/-- **The iff form of Tomita's first half**: conjugation by `Δ^{it}` is a BIJECTION of the
    limit von Neumann algebra — `towerLimitVN_flow_conj_mem_iff` rewritten under ID4. -/
theorem towerLimitVN_modUnitary_conj_mem_iff (t : ℝ)
    (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    towerModUnitary L ω β t ∘L T ∘L towerModUnitary L ω β (-t) ∈ towerLimitVN L ω β
      ↔ T ∈ towerLimitVN L ω β := by
  rw [towerModUnitary_eq_towerFlow L ω β t, towerModUnitary_eq_towerFlow L ω β (-t)]
  exact towerLimitVN_flow_conj_mem_iff L ω β t T

end QIQTH.TowerGNS
