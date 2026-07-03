/-
  THE DYNAMICS DY6 (THE_DYNAMICS_PLAN.md) — the saturated induced cross-check.

  ★ CALIBRATION-FREE MODULE (the binding verdict): the proofs below reference NONE of the keystone
  calibration identifiers — no `wEntTau`, no `cutTau`, no `inducedScreenAreaTau`, no `tauMonomial`,
  no `hJoin` (grep-checkable). The type-level import of `Micro`/`DiamondAlg`/`LinkDims` is
  unavoidable (the objects live in the keystone file); the ban is on the CALIBRATION — using it
  would be the shared-calibration trap that voids the check. ★

  THE CHECK (the QIQT-H analogue of Brown–Henneaux = Cardy, in its honest finite form): the
  MICROSCOPIC side is the code dynamics' region entropy `S_micro(R,β)` (DY1–DY5 — an independent
  computation from the Hamiltonian and its Gibbs states). The MACROSCOPIC side is supplied by
  `InducedCrossCheckData` — Sakharov/species/cell data (`A_ind`, `N_eff`, `Λ_s`, `G_ind`) with its
  two identities carried as STRUCTURE FIELDS (honest data, never Lean axioms). The theorems:
  `S_micro(R,β) ≤ A_ind/4G_ind` for ALL β, and EQUALITY at β = 0 (saturation) ONLY — the
  arbitrary-β equality is FALSE (as β → ∞ the entropy dies while the area does not) and is never
  claimed. The genuinely one-loop continuum heat-kernel equality remains the named
  frontier/conjecture (DY7).
-/
import Mathlib
import QIQTH.Dynamics
import QIQTH.InducedNewtonConstant
import QIQTH.SakharovRatio

namespace QIQTH.CrossCheck

open QIQTH.Keystone QIQTH.Dynamics

variable {M : Type*} [DecidableEq M]

/-- **The macro side of the cross-check** — independent Sakharov/species/cell data: an induced
    area, an effective species count, the granularity scale, and an induced Newton constant, with
    the two identities they must satisfy (carried as named structure fields — honest data, never
    axioms): the quarter-G primitives identity and the species/cell matching. -/
structure InducedCrossCheckData (M : Type*) [DecidableEq M] (L : LinkDims M) where
  /-- the induced area of a mode region -/
  Aind : Finset M → ℝ
  /-- the effective species count of a mode region -/
  Neff : Finset M → ℝ
  /-- the granularity scale (the ONE carried scale) -/
  Λs : ℝ
  /-- the induced Newton constant of a mode region -/
  Gind : Finset M → ℝ
  /-- the quarter-G identity in primitives: `A/4G = (A/4)·N_eff·Λs²` -/
  quarterG_eq_primitives :
    ∀ R : Finset M, Aind R / (4 * Gind R) = Aind R * Neff R * Λs ^ 2 / 4
  /-- the species/cell matching: the primitives capacity equals the total log-cutoff -/
  speciesCellMatch :
    ∀ R : Finset M, Aind R * Neff R * Λs ^ 2 / 4 = ∑ k ∈ R, Real.log (L.D k)

variable (L : LinkDims M) (ω : M → ℝ)

/-- **The canonical constructor**: with the DERIVED `G_ind = 1/(N_eff·Λs²)` (the granularity
    reframing), the quarter-G identity is the held `capacity_exponent_in_primitives` THEOREM —
    only the species/cell matching remains genuine input data. -/
noncomputable def InducedCrossCheckData.ofSpecies (Aind Neff : Finset M → ℝ) (Λs : ℝ)
    (hN : ∀ R, Neff R ≠ 0) (hΛ : Λs ≠ 0)
    (hmatch : ∀ R : Finset M, Aind R * Neff R * Λs ^ 2 / 4 = ∑ k ∈ R, Real.log (L.D k)) :
    InducedCrossCheckData M L where
  Aind := Aind
  Neff := Neff
  Λs := Λs
  Gind := fun R => QIQTH.InducedG.inducedG (Neff R) Λs
  quarterG_eq_primitives := fun R =>
    QIQTH.InducedG.capacity_exponent_in_primitives (Neff R) Λs (Aind R) (hN R) hΛ
  speciesCellMatch := hmatch

/-- **DY6 — the all-β bound**: the code's thermal region entropy never exceeds the induced
    area over `4G_ind` — for EVERY inverse temperature (the macro side supplied independently;
    the proof uses NO keystone calibration). -/
theorem S_micro_le_inducedQuarterG (X : InducedCrossCheckData M L) (Rg : Finset M) (β : ℝ) :
    Smicro L ω Rg β ≤ X.Aind Rg / (4 * X.Gind Rg) := by
  rw [X.quarterG_eq_primitives Rg, X.speciesCellMatch Rg]
  exact Smicro_le_count L ω Rg β

/-- **DY6 CAPSTONE — the SATURATED conditional Sakharov cross-check**: at `β = 0` the code
    dynamics' region entropy EQUALS the induced area over `4G_ind` —
    `S_micro(R,0) = A_ind(R)/4G_ind(R)` — with the microscopic side computed from the Hamiltonian
    (DY1–DY5) and the macroscopic side from the independent Sakharov/species/cell data. Equality
    holds at SATURATION ONLY (the arbitrary-β equality is FALSE and never claimed); the genuinely
    one-loop continuum version is the named frontier (the DY7 conjecture). -/
theorem S_micro_zero_eq_inducedQuarterG (X : InducedCrossCheckData M L) (Rg : Finset M) :
    Smicro L ω Rg 0 = X.Aind Rg / (4 * X.Gind Rg) := by
  rw [X.quarterG_eq_primitives Rg, X.speciesCellMatch Rg]
  exact Smicro_zero L ω Rg

end QIQTH.CrossCheck
