/-
  E4 (MICROTHEORY_EARNS_GRAVITY_PLAN.md) — dynamics rung one: code equilibrium ⟹ first law ⟹ Einstein.

  The dynamical statement of the bridge, from parts we hold: a CODE AT EQUILIBRIUM — a per-ray family of state
  paths, each through its own reference, each a relative-entropy stationary point — satisfies the entanglement
  first law at EVERY ray probe (`finiteCorner_firstLaw_boostEnergy`, B4′: stationarity of `D(ρ_t‖ρ_0)` forces
  `δS = 2π·δ⟨K_boost⟩`), and therefore, through the assembled skeleton (`bridge_firstLaw_iff_einstein`), the
  emergent perturbation satisfies LINEARIZED VACUUM EINSTEIN. Jacobson's "Einstein = equation of state," with the
  state being the code's equilibrium.

  Verifier-binding structure: ONE equilibrium path is NOT enough — `RayPathFamilyRealizes` carries a path PER RAY,
  each realizing that ray's first-law datum (`δS v` = the entropy rate, `δK v = 2π·B'(v)` = the modular-energy
  rate under the per-ray BW identification). The SIGN ADAPTER between the first-law orientation `δS = δ⟨K_σ⟩`
  and the Clausius orientation `δ⟨K⟩ = −δS` (the `K ↦ −K` generator reversal) is EXPLICIT
  (`clausius_sign_adapter`), never implicit.

  ⚠ Honest labels: finite/model level; the per-ray BW identification, the analytic derivative data, and the
  Iyer–Wald identity are carried hypotheses (structure fields, never axioms); linearized, free. NOT QG.
-/
import Mathlib
import QIQTH.ModularEnergyBound
import QIQTH.BridgeAssembly

namespace QIQTH.EarnGravity

open QIQTH.QuantumEntropy QIQTH.ModularEnergyBound QIQTH.BridgeASM QIQTH.AreaMap QIQTH.GravDyn QIQTH.LinEinstein
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The entanglement first law at every ray probe** — exactly the LHS of the assembled skeleton. -/
def FirstLawAtEveryRay (δS δK : (Fin 4 → ℝ) → ℝ) : Prop := ∀ v : Fin 4 → ℝ, δS v = δK v

/-- **The per-ray equilibrium family** (one path per ray — one path is NOT enough): for every ray `v`, a
    differentiable state path `ρ_t(v)` through its own reference `ρ_0(v)`, with the per-ray BW identification
    `K_σ(v) = 2π·K_boost(v) + c(v)·1` and the analytic derivative data, REALIZING the ray's first-law datum:
    `δS v` is the path's entropy rate and `δK v = 2π·B'(v)` its modular-energy rate. All fields are carried
    hypotheses (never axioms). -/
structure RayPathFamilyRealizes (n : Type*) [Fintype n] [DecidableEq n]
    (δS δK : (Fin 4 → ℝ) → ℝ) where
  /-- the state path of ray `v` -/
  ρt : (Fin 4 → ℝ) → ℝ → Matrix n n ℂ
  /-- the boost generator of ray `v` -/
  Kboost : (Fin 4 → ℝ) → Matrix n n ℂ
  /-- the BW additive constant of ray `v` -/
  cshift : (Fin 4 → ℝ) → ℝ
  /-- the boost-energy rate of ray `v` -/
  Brate : (Fin 4 → ℝ) → ℝ
  hpos : ∀ v t, (ρt v t).PosDef
  hdens : ∀ v t, IsDensity (ρt v t)
  /-- the per-ray BW identification (carried) -/
  hBW : ∀ v, modHam (hpos v 0).1 = (2 * Real.pi) • Kboost v + cshift v • (1 : Matrix n n ℂ)
  /-- the ray's `δS` IS the path's entropy rate (analytic input, carried) -/
  hS : ∀ v, HasDerivAt (fun t => vonNeumannEntropy (hdens v t)) (δS v) 0
  /-- the path's boost-energy rate (analytic input, carried) -/
  hB : ∀ v, HasDerivAt (fun t => boostEnergy (ρt v t) (Kboost v)) (Brate v) 0
  /-- the ray's `δK` IS the modular-energy rate `2π·B'` -/
  hK : ∀ v, δK v = 2 * Real.pi * Brate v

/-- **Equilibrium ⟹ the first law at every ray**: each ray's path is a relative-entropy stationary point
    (`D(ρ_t‖ρ_0) ≥ 0 = D(ρ_0‖ρ_0)`), so B4′ forces `δS v = 2π·B'(v) = δK v` — at EVERY probe. -/
theorem rayFamily_firstLaw (δS δK : (Fin 4 → ℝ) → ℝ) (F : RayPathFamilyRealizes n δS δK) :
    FirstLawAtEveryRay δS δK := by
  intro v
  rw [F.hK v]
  exact finiteCorner_firstLaw_boostEnergy (F.Kboost v) (F.hpos v) (F.hdens v) (F.hBW v)
    (F.hS v) (F.hB v)

/-- **The explicit sign adapter** (verifier-required, never implicit): the first-law orientation
    `δS = δ⟨K_σ⟩ = 2π·B'` converts to the Clausius orientation `δ⟨K⟩ = −δS` under the generator reversal
    `K_boost ↦ −K_boost` (whose rate is `−B'`): `2π·(−B'(v)) = −δS v`. -/
theorem clausius_sign_adapter (δS δK : (Fin 4 → ℝ) → ℝ) (F : RayPathFamilyRealizes n δS δK)
    (v : Fin 4 → ℝ) : 2 * Real.pi * (-(F.Brate v)) = -(δS v) := by
  have h := rayFamily_firstLaw δS δK F v
  rw [F.hK v] at h
  linarith

/-- **E4 CAPSTONE — code equilibrium ⟹ linearized Einstein.** A code whose per-ray state paths are at
    relative-entropy equilibrium (the `RayPathFamilyRealizes` family), with the carried Iyer–Wald identity tying
    the first-law deficit to the area pairing of the Einstein residual, has an emergent perturbation satisfying
    **linearized vacuum Einstein**: Jacobson's equation-of-state, with the state the code's equilibrium.
    ⚠ CONDITIONAL on the carried per-ray BW/analytic data + Iyer–Wald; linearized, free, finite/model. NOT QG. -/
theorem code_equilibrium_einstein (k : Fin 4 → ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hSym : h.IsSymm) (δS δK : (Fin 4 → ℝ) → ℝ) (F : RayPathFamilyRealizes n δS δK)
    (hIW : ∀ v : Fin 4 → ℝ, δK v - δS v = areaVar (raySurf v) (einsteinSymbol k h)) :
    einsteinSymbol k h = 0 :=
  (bridge_firstLaw_iff_einstein k h hSym δS δK hIW).mp (rayFamily_firstLaw δS δK F)

end QIQTH.EarnGravity
