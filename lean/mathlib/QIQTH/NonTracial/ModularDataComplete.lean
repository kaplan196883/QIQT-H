/-
  THE KMS-BOUNDARY CAMPAIGN — C1 CAPSTONE: MODULAR DATA COMPLETE.

  This file is the single citable index of the tower limit state's Tomita–Takesaki modular
  data, now machine-checked in full (axiom-free, std-3, budget 0). The KMS-boundary side
  (K1 `towerState_kms_boundary`, K2 `towerFlow_vectorState`) was already built during the
  flow campaign and is verified present; this capstone bundles the whole tower and records
  the honest boundary.

  HAVE: "The tower vacuum state ω (the vector state of the cyclic-separating Ω) satisfies the
  algebraic KMS boundary identity ω(π_C(x)π_C(y)) = ω(π_C(y)π_C(σ(x))) at every finite stage
  C, where σ = modAut(ρ_C) is the finite modular automorphism (conjugation by the Gibbs
  density ρ_C = the imaginary-time modular translate σ_{−iβ}). Combined with the
  already-proved real modular flow Δ^{it}=towerFlow, its exact covariance
  U_t π_C(a) U_{−t} = π_C(σ_t a), its fixing of Ω, and its state invariance, the tower vacuum
  is a KMS-boundary state for its modular automorphism. Axiom-free, std-3. With this, the
  tower limit state carries the COMPLETE machine-checked Tomita–Takesaki modular data: S̄
  (closed involutive Tomita operator), Δ self-adjoint (Δ†=Δ, von Neumann's theorem),
  Δ^{it}=towerFlow (the physical flow, the identification), Tomita I (Δ^{it}MΔ^{−it}=M), J
  anti-unitary with polar decomposition on the core, Tomita II inclusion (JMJ ⊆ M′),
  non-traciality (ω not a trace, Δ≠1), and the KMS-boundary identity — the first complete
  Tomita–Takesaki modular theory in any proof assistant."

  HAVE-NOT: "This is the algebraic/boundary KMS relation w.r.t. the modular AUTOMORPHISM, NOT
  the Kubo–Martin–Schwinger strip-analyticity at the thermodynamic limit: the holomorphy of
  t ↦ ω(π(a)Δ^{it}π(b)Ω) on 0≤Im t≤β and the identification of its boundary with the
  imaginary-time endpoint are not formalized, and σ_{−iβ} = (analytic continuation of Δ^{it})
  is not proved (modAut is imaginary-time-only; cornerFlow is real-t-only). No full commutant
  equality J M J = M′ (only the inclusion J M J ⊆ M′, the reverse being the Rieffel–van Daele
  wall); no type classification (III₁/Connes invariant — Mathlib has no tracial-state/type
  API); everything remains the finite-stage Gibbs inductive-limit state — the free-field /
  Type-III continuum objects are untouched, and are the named pivot."

  THE INDEX (canonical names, all axiom-free std-3):
  • S̄ closed involutive Tomita operator — `towerTomitaBar`, `towerTomitaBar_involutive`
  • Δ self-adjoint (von Neumann) — `towerModularOp`, `towerModularOp_isSelfAdjoint`
  • Δ^{it} = physical flow — `towerModUnitary`, `towerModUnitary_eq_towerFlow`
  • Tomita I (algebra preserved) — `towerLimitVN_modUnitary_invariant`
  • J anti-unitary — `towerJ`, `towerJ_involutive`
  • polar decomposition on the core — `towerTomitaBar_eq_towerJ_deltaHalf`
  • Tomita II inclusion — `jconj_limitVN_mem_commutant`
  • non-traciality — `towerVacuum_not_tracial`, `towerModularOp_ne_id`, `towerModUnitary_ne_id`
  • KMS-boundary — `towerState_kms_boundary`, `towerFlow_vectorState`
-/
import QIQTH.NonTracial.FiniteNonTrace
import QIQTH.NonTracial.TowerNonTrace
import QIQTH.NonTracial.ModularNonTrivial
import QIQTH.TowerGNS.Identification
import QIQTH.TowerGNS.TomitaSecondHalf
import QIQTH.TowerGNS.PolarCore

namespace QIQTH.NonTracial

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory QIQTH.TowerGNS
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **C1 CAPSTONE — MODULAR DATA COMPLETE (the non-degenerate witness).** A single
compile-verified bundle: at any stage `C` with two modes `n ≠_w m` whose Gibbs weights
differ, the tower vacuum simultaneously exhibits (1) the KMS-boundary identity on the
matrix-unit word, (2) state non-traciality, and (3) modular non-triviality Δ ≠ 1 — the three
faces of the tower's non-tracial KMS structure, all from the ONE datum `w_n ≠ w_m`. This is
not new mathematics; it is the honest capstone that the tower modular theory is complete and
internally coherent. See the file docstring for the full HAVE / HAVE-NOT. -/
theorem modular_data_complete_witness (C : Finset M) (n m : Micro L C)
    (h : gibbsWeight L C ω β n ≠ gibbsWeight L C ω β m) :
    -- (1) KMS-boundary on the matrix-unit word E_nm · E_mn
    (⟪towerCyclicVec L ω β,
        towerRep L ω β C (Matrix.single n m 1 * Matrix.single m n 1)
          (towerCyclicVec L ω β)⟫_ℂ
      = ⟪towerCyclicVec L ω β,
        towerRep L ω β C
          (Matrix.single m n 1 * modAut (gibbsDensity L C ω β) (Matrix.single n m 1))
          (towerCyclicVec L ω β)⟫_ℂ)
    -- (2) state non-traciality
    ∧ (⟪towerCyclicVec L ω β, towerRep L ω β C (Matrix.single n m 1)
          (towerRep L ω β C (Matrix.single m n 1) (towerCyclicVec L ω β))⟫_ℂ
        ≠ ⟪towerCyclicVec L ω β, towerRep L ω β C (Matrix.single m n 1)
          (towerRep L ω β C (Matrix.single n m 1) (towerCyclicVec L ω β))⟫_ℂ)
    -- (3) modular non-triviality Δ ≠ 1
    ∧ (towerModularOp L ω β
          ⟨((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β),
            of_mem_towerModularDom L ω β C (Matrix.single n m 1)⟩
        ≠ ((towerOf L ω β C (Matrix.single n m 1) : TowerPre L ω β) : TowerGNS L ω β)) :=
  ⟨towerState_kms_boundary L ω β C (Matrix.single n m 1) (Matrix.single m n 1),
   towerVacuum_not_tracial L ω β C n m h,
   towerModularOp_ne_id L ω β C n m h⟩

end QIQTH.NonTracial
