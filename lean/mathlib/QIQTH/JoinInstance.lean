/-
  THE JOIN INSTANCE (JOIN_INSTANCE_PLAN.md) — delete `hJoin` by construction: the bridge at the
  finite level.

  The code tower (keystone THE COUNT) and the graviton tower (Q1–Q5) merged into ONE object: the
  dictionary instance links ↔ screen elements, with the code weights defined FROM the geometry, so
  the Q5 carried hypothesis `hJoin` becomes a THEOREM for the constructed instance.

  JI1 — the local area decomposition:
  • `localAreaVar` — the per-element linearized area share `δA_a = ½ w_a (h(e₁ᵃ,e₁ᵃ)+h(e₂ᵃ,e₂ᵃ))`,
    with `sum_localAreaVar` (the shares sum to the held `areaVar`);
  • `A0Split` — the NAMED apportionment of the global background area across the elements (honest
    DATA, per the binding verdict: there is no canonical per-link split of a global constant);
    `A0Split.uniform` as an optional constructor, never pretended-derived;
  • CAPSTONE `sum_localArea` — the algebraic core `∑_a (β_a + δA_a) = A₀ + areaVar S h`.
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.OperatorEmergence
import QIQTH.CalibratedAreaLaw
import QIQTH.InducedNewtonConstant

namespace QIQTH.JoinInstance

open QIQTH.AreaMap QIQTH.GravDyn

variable {ι : Type*}

/-- **The per-element linearized area share** `δA_a := ½ w_a (h(e₁ᵃ,e₁ᵃ) + h(e₂ᵃ,e₂ᵃ))` — the
    single element's contribution to the held discretized area response. -/
noncomputable def localAreaVar (S : ScreenSurface ι) (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  (1 / 2) * (S.w a * (quadForm h (S.e1 a) + quadForm h (S.e2 a)))

/-- The per-element shares sum to the held total area response. -/
theorem sum_localAreaVar (S : ScreenSurface ι) (h : Matrix (Fin 4) (Fin 4) ℝ) :
    ∑ a ∈ S.elems, localAreaVar S h a = areaVar S h := by
  rw [areaVar, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- **The named apportionment of the background area** across the screen elements — honest DATA
    (per the binding verdict: a global constant has no canonical per-link decomposition; any split
    is a CHOICE, carried as a structure field, never pretended-derived). -/
structure A0Split (S : ScreenSurface ι) (A0 : ℝ) where
  /-- the per-element background share -/
  share : ι → ℝ
  /-- the shares reassemble the background -/
  sum_share : ∑ a ∈ S.elems, share a = A0

/-- The uniform split — an optional CONSTRUCTOR (a policy, not a derivation). -/
noncomputable def A0Split.uniform (S : ScreenSurface ι) (A0 : ℝ) (hne : S.elems.Nonempty) :
    A0Split S A0 where
  share := fun _ => A0 / S.elems.card
  sum_share := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [Finset.card_ne_zero_of_mem hne.choose_spec]

/-- **The local area of an element**: background share plus linearized response. -/
noncomputable def localArea (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  β.share a + localAreaVar S h a

/-- **JI1 CAPSTONE — the algebraic core of the join:** the local areas reassemble the total,
    `∑_a (β_a + δA_a) = A₀ + areaVar S h` — exactly the right-hand side of the carried `hJoin`,
    now decomposed per link. -/
theorem sum_localArea (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    (h : Matrix (Fin 4) (Fin 4) ℝ) :
    ∑ a ∈ S.elems, localArea S β h a = A0 + areaVar S h := by
  simp only [localArea, Finset.sum_add_distrib, β.sum_share, sum_localAreaVar]

/-! ## JI2 — the generic τ join dictionary

The geometry-defined code: weights `wEnt a := A^loc_a/(4G)` and REAL trace-dimensions
`Dτ_a := exp(wEnt a)` (per the binding verdict: generic-exact at the τ level, NO integrality — the
calibration is `Real.log_exp`). CAPSTONE `hJoin_tau`: the Q5 carried `hJoin` equality is a THEOREM
for the constructed dictionary (direction geometry → code; links = the screen elements). -/

section TauDictionary

open QIQTH.EarnGravity QIQTH.OperatorEmergence

variable [Fintype ι] [DecidableEq ι]

/-- **The geometry-defined code weight**: the element's local area over `4G`. -/
noncomputable def tauWEnt (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  localArea S β h a / (4 * G)

/-- **The REAL trace-dimension of a link**: `Dτ_a := exp(wEnt a)` — a positive real, no
    integrality (the Type II lesson: trace-dimensions need not be natural numbers). -/
noncomputable def tauDim (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  Real.exp (tauWEnt S β G h a)

theorem tauDim_pos (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : 0 < tauDim S β G h a :=
  Real.exp_pos _

/-- **The calibration is a THEOREM at the τ level** — `log Dτ_a = wEnt a`, by `Real.log_exp`;
    nothing is calibrated, no integrality is needed. -/
theorem hcal_tau (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) :
    Real.log (tauDim S β G h a) = tauWEnt S β G h a :=
  Real.log_exp _

/-- **JI2 CAPSTONE — the carried `hJoin` is a THEOREM for the constructed dictionary:** with the
    code weights defined FROM the geometry (links = the screen elements, `wEnt = A^loc/(4G)`), the
    code's induced screen area equals the background plus the linearized area response —
    `inducedScreenArea G S.elems wEnt = A₀ + areaVar S (classicalH pol α)`. This is exactly the Q5
    hypothesis shape, now supplied by construction (geometry → code; no smuggling: the theorem is
    about the instance BUILT from this geometric data). -/
theorem hJoin_tau (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) {G : ℝ} (hG : 0 < G)
    (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) :
    inducedScreenArea G S.elems (tauWEnt S β G (classicalH pol α))
      = A0 + areaVar S (classicalH pol α) := by
  rw [inducedScreenArea, screen_cut_eq,
    show ∑ a ∈ S.elems, tauWEnt S β G (classicalH pol α) a
        = (∑ a ∈ S.elems, localArea S β (classicalH pol α) a) / (4 * G) from by
      rw [Finset.sum_div]
      rfl,
    sum_localArea]
  field_simp

end TauDictionary

end QIQTH.JoinInstance
