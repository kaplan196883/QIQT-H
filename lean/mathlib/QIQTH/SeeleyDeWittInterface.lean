/-
  SEELEY–DEWITT INTERFACE — the deferred heat-kernel coefficient `a₁ = R/6 + tr E`, carried as a
  NAMED INTERFACE (option (b), the `DonaldSystem` typeclass-interface pattern).

  The conjecture input #3 (the curved-space Seeley–DeWitt coefficient `a₁ = R/6`) is gated on
  Mathlib's absent Riemannian heat-kernel theory (`docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`).  Rather
  than leave it as an ad-hoc `PhysicalInputs` hypothesis (G3 `CorrespondenceAssembly.lean`), this file
  NAMES it once as a reusable interface `SeeleyDeWittData`: the short-time coefficients `a₀ = 1`,
  `a₁ = R/6 + tr E` the heat-kernel theory WOULD supply, carried as structure fields (NEVER a Lean
  `axiom`).  The conditional correspondence theorem is restated sourcing its `a₁` input from this
  interface, so the eventual discharge (`HEAT_KERNEL_GAP_PLAN.md`, Phase 5) is a SINGLE instance, not
  a refactor.

  What is PROVED here (all axiom-free):
  • `SeeleyDeWittData` — the interface carrying `a₀ = 1`, `a₁ = R/6 + tr E`;
  • `SeeleyDeWittData.a1_eq_scalarA1_of_minimal` — for a minimal scalar (`tr E = 0`) the interface
    delivers `a₁ = R/6 = scalarA1 0 R`, exactly the form G3's `PhysicalInputs` consumes;
  • `physicalInputs_of_seeleyDeWitt` — G3's `PhysicalInputs` with input #3 sourced FROM the interface
    (inputs #4/#5 carried as before);
  • `flatSpaceCorrespondence_of_seeleyDeWitt` — ★ the conditional correspondence, its `a₁` input now
    an interface field.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (honest scope, binding).  This is OPTION (b): `a₁ = R/6` is CARRIED as an
  explicit named interface, NOT derived and NOT an axiom.  The `SeeleyDeWittData` interface is the
  DEFERRED heat-kernel data; its analytic discharge (proving `a₁ = R/6` from the Riemannian heat
  kernel) is the entire `HEAT_KERNEL_GAP_PLAN.md` and stays CITED / unbuilt.  The correspondence
  remains CONDITIONAL (on this interface + inputs #4/#5); it is NOT a proof of the conjecture, NOT the
  strong holographic principle, NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.CorrespondenceAssembly

namespace QIQTH.SeeleyDeWittInterface

open QIQTH.CorrespondenceAssembly QIQTH.ConicalSakharov QIQTH.Conjectures

/-- **The Seeley–DeWitt heat-kernel data, as a deferred INTERFACE** (the `DonaldSystem` pattern).
    It names the short-time coefficients `a₀ = 1`, `a₁ = R/6 + tr E` that the Riemannian heat-kernel
    theory WOULD supply — to be discharged by a single instance once Mathlib has that theory
    (`HEAT_KERNEL_GAP_PLAN.md`, Phase 5).  Until then it is CARRIED (option (b)), never a Lean
    `axiom`. -/
structure SeeleyDeWittData where
  /-- scalar curvature `R` -/
  R : ℝ
  /-- endomorphism trace `tr E` -/
  trE : ℝ
  /-- the zeroth heat-kernel coefficient -/
  a0 : ℝ
  /-- the first heat-kernel coefficient -/
  a1 : ℝ
  /-- `a₀ = 1` (the leading Seeley–DeWitt coefficient). -/
  a0_eq : a0 = 1
  /-- `a₁ = R/6 + tr E` (the Seeley–DeWitt identity, CARRIED — the deferred heat-kernel fact). -/
  a1_eq : a1 = a1Laplace R trE

namespace SeeleyDeWittData

/-- For a MINIMAL scalar (`E = 0`) the interface delivers `a₁ = R/6 = scalarA1 0 R` — exactly the
    form G3's `PhysicalInputs.a1_eq_R_div_six` consumes. -/
theorem a1_eq_scalarA1_of_minimal (S : SeeleyDeWittData) (hE : S.trE = 0) :
    S.a1 = scalarA1 0 S.R := by
  simp only [S.a1_eq, a1Laplace, scalarA1, hE]; ring

end SeeleyDeWittData

/-- **G3's `PhysicalInputs` with input #3 sourced FROM the Seeley–DeWitt interface** (minimal scalar,
    matched to the region's curvature); the cutoff/regulator inputs (#4/#5) are carried as before.
    This is option (b) made an interface: #3 is a discharged interface field, not an ad-hoc
    hypothesis. -/
theorem physicalInputs_of_seeleyDeWitt (D : ConstructiveCLD) (S : SeeleyDeWittData)
    (hR : S.R = D.curvR) (hE : S.trE = 0) (ha1 : S.a1 = D.a1coeff)
    (h5 : ∀ R, D.recEnt R = Sent D.N (D.areaOf R) D.entReg)
    (h4 : D.newtonReg = D.entReg)
    (hnm : D.sakInvG = dInvG D.N D.entReg)
    (hne : dInvG D.N D.entReg ≠ 0) :
    PhysicalInputs D := by
  refine
    { a1_eq_R_div_six := ?_, cutoff_identifies := h5, same_regulator := h4,
      newton_matches := hnm, dInvG_ne := hne }
  rw [← ha1, ← hR]
  exact S.a1_eq_scalarA1_of_minimal hE

/-- **★ THE CONDITIONAL CORRESPONDENCE, with the `a₁` input sourced from the Seeley–DeWitt
    interface.**  Given a `SeeleyDeWittData` (minimal scalar, matched to the region's curvature) and
    the carried cutoff/regulator inputs (#4/#5), the constructed continuum data satisfies the
    conjecture.  Discharging the interface (Phase 5 of the heat-kernel plan) would remove the last
    curvature-side assumption; it stays CITED. -/
theorem flatSpaceCorrespondence_of_seeleyDeWitt (D : ConstructiveCLD) (S : SeeleyDeWittData)
    (hR : S.R = D.curvR) (hE : S.trE = 0) (ha1 : S.a1 = D.a1coeff)
    (h5 : ∀ R, D.recEnt R = Sent D.N (D.areaOf R) D.entReg)
    (h4 : D.newtonReg = D.entReg)
    (hnm : D.sakInvG = dInvG D.N D.entReg)
    (hne : dInvG D.N D.entReg ≠ 0) :
    FlatSpaceRecordGravityCorrespondence D.toOpaque :=
  flatSpaceCorrespondence_of_constructive D
    (physicalInputs_of_seeleyDeWitt D S hR hE ha1 h5 h4 hnm hne)

end QIQTH.SeeleyDeWittInterface
