/-
  THE MODULAR CONJUGATION J5 (THE_MODULAR_CONJUGATION_PLAN.md) — THE POLAR DECOMPOSITION
  ON THE DENSE PURE-COMPONENT CORE: S̄ = J∘Δ^{1/2}, F = Δ^{1/2}∘J, (Δ^{1/2})² = Δ — all at
  core level, harvested from J1–J4 + CC5/M3/M5 by short rewrite chains.

  Deliverables:
  • `towerTomitaBar_eq_towerJ_deltaHalf` ★ — THE POLAR DECOMPOSITION ON THE CORE:
    `S̄ ↑(of C a) = J ↑(of C (Δ^{1/2}_C a))` — the closed Tomita operator factors through
    the global anti-unitary and the stage half-power on every pure component
    (`towerTomitaBar_of` + `towerJ_of` + `jStage_deltaHalfStage`);
  • `towerJ_towerTomitaBar` — the mirror: `J (S̄ ↑(of C a)) = ↑(of C (Δ^{1/2}_C a))` —
    the core Δ^{1/2}-action is recovered as J∘S̄ (J² = 1 at stage level);
  • `jStage_conjTranspose_eq_deltaHalf` — the tiny stage bridge `J_C (aᴴ) = Δ^{1/2}_C a`
    feeding the mirror (`ᴴᴴ` collapse);
  • `towerTomitaF_eq_deltaHalf_jStage` — THE OTHER ORDER IS F:
    `F ↑(of C b) = ↑(of C (Δ^{1/2}_C (J_C b)))` — Tomita's F factors as Δ^{1/2}∘J on the
    core (`towerTomitaF_of` + `deltaHalfStage_jStage` + the modAut bridge);
  • `deltaHalf_sq_eq_modularOp_core` — `Δ ↑(of C a) = ↑(of C (Δ^{1/2}_C (Δ^{1/2}_C a)))` —
    the half-power squares to the modular operator's core action
    (`towerModularOp_of` + `deltaHalfStage_sq`);
  • `towerOf_deltaHalfStage_single` — the Δ^{1/2}-eigenbasis action on the GNS space:
    `↑(of C (Δ^{1/2} E_{nm}c)) = √(w_n/w_m) • ↑(of C (E_{nm}c))`.

  THE ORDER GUARD (documented, per plan): S̄ = J∘Δ^{1/2} = Δ^{−1/2}∘J on the core; the
  REVERSED composition Δ^{1/2}∘J is NOT S̄ — it is Tomita's F (item
  `towerTomitaF_eq_deltaHalf_jStage`): Δ^{1/2}(J_C a) = ρ·aᴴ·ρ⁻¹ = modAut ρ (aᴴ), the ⋆
  twisted by the FULL modular automorphism, which differs from aᴴ whenever ρ is not
  central. No negation is stated as a theorem; the guard lives in the two POSITIVE
  identities (S̄-core vs F-core) having different right-hand sides.

  HONEST SCOPE: core-level identities ONLY. This is NOT an operator factorization
  S̄ = J·Δ^{1/2} on the full domain of S̄ — no unbounded operator Δ^{1/2} is constructed,
  no closure of the half-power, no polar decomposition of the closed operator in the
  functional-analytic sense; everything holds on the dense pure-component core, where the
  half-power acts through the finite matrix closed form √ρ·a·√ρ⁻¹. Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ModularConj
import QIQTH.TowerGNS.ModularOp

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The tiny stage bridge — `J_C (aᴴ) = Δ^{1/2}_C a` -/

/-- **The stage bridge**: `J_C (aᴴ) = Δ^{1/2}_C a` — conjugating the conjugate-transpose
    collapses the ᴴᴴ and leaves the bare √ρ-sandwich (feeds the J∘S̄ mirror below). -/
theorem jStage_conjTranspose_eq_deltaHalf (C : Finset M) (a : DiamondAlg L C) :
    jStage L ω β C aᴴ = deltaHalfStage L ω β C a := by
  rw [jStage, Matrix.conjTranspose_conjTranspose, deltaHalfStage]

/-! ### ★ THE POLAR DECOMPOSITION ON THE CORE — S̄ = J∘Δ^{1/2} -/

/-- **★ THE POLAR DECOMPOSITION ON THE DENSE PURE-COMPONENT CORE**:
    `S̄ ↑(of C a) = J ↑(of C (Δ^{1/2}_C a))` — the closed Tomita operator factors as the
    global anti-unitary applied to the stage half-power, on every pure component.
    Route: `RHS = ↑(of C (J_C (Δ^{1/2}_C a)))` (`towerJ_of`) `= ↑(of C aᴴ)`
    (`jStage_deltaHalfStage`) `= LHS` (`towerTomitaBar_of`).

    ORDER GUARD: this is S̄ = J∘Δ^{1/2} (J OUTSIDE); the reversed composition Δ^{1/2}∘J is
    NOT S̄ but Tomita's F — see `towerTomitaF_eq_deltaHalf_jStage`. NOT an operator
    factorization on the full domain of S̄ — core level only, no unbounded Δ^{1/2}. -/
theorem towerTomitaBar_eq_towerJ_deltaHalf (C : Finset M) (a : DiamondAlg L C) :
    ∃ h : ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
        ∈ (towerTomitaBar L ω β).domain,
      towerTomitaBar L ω β
          ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), h⟩
        = towerJ L ω β
            ((towerOf L ω β C (deltaHalfStage L ω β C a) : TowerPre L ω β) :
              TowerGNS L ω β) := by
  obtain ⟨h, hval⟩ := towerTomitaBar_of L ω β C a
  refine ⟨h, ?_⟩
  rw [hval, towerJ_of, jStage_deltaHalfStage]

/-! ### The mirror — Δ^{1/2}-core = J∘S̄ -/

/-- **The mirror**: `J (S̄ ↑(of C a)) = ↑(of C (Δ^{1/2}_C a))` — applying the anti-unitary
    to the closed Tomita operator recovers the core half-power action (J² = 1 undoes the
    J of the polar decomposition). Route: `S̄ ↑(of C a) = ↑(of C aᴴ)` (`towerTomitaBar_of`),
    then `J ↑(of C aᴴ) = ↑(of C (J_C aᴴ)) = ↑(of C (Δ^{1/2}_C a))` (`towerJ_of` + the
    stage bridge). -/
theorem towerJ_towerTomitaBar (C : Finset M) (a : DiamondAlg L C) :
    ∃ h : ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
        ∈ (towerTomitaBar L ω β).domain,
      towerJ L ω β
          (towerTomitaBar L ω β
            ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β), h⟩)
        = ((towerOf L ω β C (deltaHalfStage L ω β C a) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  obtain ⟨h, hval⟩ := towerTomitaBar_of L ω β C a
  refine ⟨h, ?_⟩
  rw [hval, towerJ_of, jStage_conjTranspose_eq_deltaHalf]

/-! ### THE OTHER ORDER IS F — Tomita's F = Δ^{1/2}∘J on the core (the order guard) -/

/-- **THE OTHER ORDER IS F (the order guard made positive)**:
    `F ↑(of C b) = ↑(of C (Δ^{1/2}_C (J_C b)))` — composing the half-power AFTER the
    conjugation gives Tomita's F on the core, NOT S̄: the value is
    `Δ^{1/2}(J_C b) = modAut ρ (bᴴ)` (`deltaHalfStage_jStage`), the ⋆ twisted by the full
    modular automorphism, matching `towerTomitaF_of` through the modAut bridge
    `rightConj_sq_conjTranspose_eq_modAut`. -/
theorem towerTomitaF_eq_deltaHalf_jStage (C : Finset M) (b : DiamondAlg L C) :
    towerTomitaF L ω β
        ⟨((towerOf L ω β C b : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerTomitaF_dom L ω β C b⟩
      = ((towerOf L ω β C (deltaHalfStage L ω β C (jStage L ω β C b))
          : TowerPre L ω β) : TowerGNS L ω β) := by
  rw [towerTomitaF_of, deltaHalfStage_jStage, rightConj_sq_conjTranspose_eq_modAut]

/-! ### (Δ^{1/2})² = Δ on the core -/

/-- **`(Δ^{1/2})² = Δ` on the core**: `Δ ↑(of C a) = ↑(of C (Δ^{1/2}_C (Δ^{1/2}_C a)))` —
    the modular operator's core action (`towerModularOp_of`, the M5 headline) IS the
    square of the stage half-power (`deltaHalfStage_sq`: the two √ρ-conjugations compose
    into the full ρ-conjugation `modAut ρ`). -/
theorem deltaHalf_sq_eq_modularOp_core (C : Finset M) (a : DiamondAlg L C) :
    towerModularOp L ω β
        ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerModularDom L ω β C a⟩
      = ((towerOf L ω β C (deltaHalfStage L ω β C (deltaHalfStage L ω β C a))
          : TowerPre L ω β) : TowerGNS L ω β) := by
  rw [towerModularOp_of, deltaHalfStage_sq]

/-! ### The Δ^{1/2}-eigenbasis action on the GNS space -/

/-- **The Δ^{1/2}-eigenbasis action on the GNS space**:
    `↑(of C (Δ^{1/2} E_{nm}c)) = √(w_n/w_m) • ↑(of C (E_{nm}c))` — indices NOT flipped,
    scalar NOT conjugated: the coerced matrix units carry the square root of the
    Δ-eigenvalue `w_n/w_m` (`deltaHalfStage_single` + the scalar push
    `towerOf_smul_coe`); feeds any later Δ^{1/2}-eigenbasis computation. -/
theorem towerOf_deltaHalfStage_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    ((towerOf L ω β C (deltaHalfStage L ω β C (Matrix.single n m c))
        : TowerPre L ω β) : TowerGNS L ω β)
      = ((Real.sqrt (gibbsWeight L C ω β n / gibbsWeight L C ω β m) : ℝ) : ℂ)
        • ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  rw [deltaHalfStage_single]
  exact towerOf_smul_coe L ω β C _ _

end QIQTH.TowerGNS
