/-
  Route 1 (reframed) — the free-field modular-energy bound (Casini / first law).

  GOAL (GPT-5.5-pro expert reframing, 2026-07-01). "Deriving holography" via the JLMS identity
  `K_{∂R} = A/4ℓ_P² + K_bulk` — for a fixed-background FREE scalar the `A/4ℓ_P²` term is **NOT
  derivable** (the free theory has no Newton constant `G`, no geometric area operator; the wedge
  entropy's cutoff coefficient is matter/scheme-dependent, not universally `1/4G`; and the
  `δA/4G = 2π∫δT_kk` step USES the Einstein equations, not pure Bisognano–Wichmann kinematics).
  So BW supplies the Unruh `2π`, but NOT the `1/4G`.

  What IS derivable — and is the honest content of Route 1 — is the **modular-energy bound**:
      ΔS  ≤  Δ⟨K_σ⟩     (Casini),      δS = δ⟨K_σ⟩  (first law),
  from relative-entropy positivity (Klein) and `K_σ = −log σ` the modular Hamiltonian. Combined with
  the (elsewhere machine-checked) one-particle Bisognano–Wichmann `K_wedge = 2π B_boost`, this reads
  `ΔS ≤ 2π Δ⟨B_boost⟩` — the Unruh-temperature modular bound.

  ⚠ HONEST SCOPE. This is **formalized modular QFT**, NOT a derivation of the holographic `A/4G` bound.
  It NEVER claims to derive `A/4G`, holography, quantum gravity, or the value of `G`; the `A/4G`/area
  identification stays a *gravitational input*, and the continuum Type III₁→II crossed-product
  dual-weight trace (where `A/4G` would live) is a multi-year cited frontier. It upgrades the *modular*
  pieces of the carried `Phase5Master` hypothesis from an assumption to theorems (finite-dim Type-I
  corner; the Fock lift is a labelled follow-on). See `ROUTE1_MODULAR_PLAN.md`.

  This file (B1+B2): the Umegaki modular-energy identity and the Casini modular-energy bound, assembled
  from the repo's Donald identities (`relEntropy_eq_crossEntropy_sub_entropy`, `crossEntropy_self`) and
  Klein positivity (`relEntropy_nonneg`).
-/

import QIQTH.QuantumRelativeEntropy
import Mathlib.Tactic

namespace QIQTH
namespace ModularEnergyBound

open QIQTH.QuantumEntropy
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **modular Hamiltonian** `K_σ = −log σ` — the generator of the modular (Tomita–Takesaki) flow
    of the faithful state `σ`. (Finite-dim / Type-I corner; `log σ = matLog`.) -/
noncomputable def modHam {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) : Matrix n n ℂ := -matLog hσ

/-- The **modular energy** `⟨K_σ⟩_ρ = tr(ρ·K_σ) = tr(ρ·(−log σ)) = −tr(ρ log σ)` — which is exactly the
    cross entropy `crossEntropy(ρ,σ)`. For the wedge vacuum with `K_σ = 2π B_boost` (Bisognano–Wichmann)
    this is `2π` times the boost energy (the Unruh modular energy). -/
noncomputable def modEnergy (ρ : Matrix n n ℂ) {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) : ℝ :=
  crossEntropy ρ hσ

/-- `modEnergy` is literally the modular-Hamiltonian expectation `tr(ρ·K_σ).re`. -/
lemma modEnergy_eq_trace (ρ : Matrix n n ℂ) {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    modEnergy ρ hσ = (ρ * modHam hσ).trace.re := by
  unfold modEnergy modHam crossEntropy
  rw [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]

/-- **B1 — the Umegaki modular-energy identity.**
    `D(ρ‖σ) = (⟨K_σ⟩_ρ − ⟨K_σ⟩_σ) − (S(ρ) − S(σ))`, with the modular Hamiltonian `K_σ = −log σ`.
    Assembled from the repo's Donald identities `D = crossEnt(ρ,σ) − S(ρ)` and `crossEnt(σ,σ) = S(σ)`. -/
theorem modular_relEnt_identity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρd : IsDensity ρ) (hσd : IsDensity σ) :
    relEntropy hρ.1 hσ.1
      = (modEnergy ρ hσ.1 - modEnergy σ hσ.1) - (vonNeumannEntropy hρd - vonNeumannEntropy hσd) := by
  unfold modEnergy
  rw [relEntropy_eq_crossEntropy_sub_entropy hρ hσ hρd, crossEntropy_self hσ hσd]
  ring

/-- **B2 — the Casini modular-energy bound** (the honest, derivable core of Route 1).
    `S(ρ) − S(σ) ≤ ⟨K_σ⟩_ρ − ⟨K_σ⟩_σ`, i.e. the entropy variation is bounded by the modular-energy
    variation — from relative-entropy positivity (`relEntropy_nonneg`, Klein). With the one-particle
    Bisognano–Wichmann identification `K_σ = 2π B_boost` this is `ΔS ≤ 2π Δ⟨B_boost⟩` (the Unruh bound).

    ⚠ This is the free-field modular bound — **NOT** the holographic `S ≤ A/4G` bound; the `A/4G`
    identification is a gravitational input, not derivable here (see file header). -/
theorem modular_casini_bound {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρd : IsDensity ρ) (hσd : IsDensity σ) :
    vonNeumannEntropy hρd - vonNeumannEntropy hσd ≤ modEnergy ρ hσ.1 - modEnergy σ hσ.1 := by
  have hid := modular_relEnt_identity hρ hσ hρd hσd
  have hnn := relEntropy_nonneg hρ hσ hρd.trace_one hσd.trace_one
  linarith [hid, hnn]

/-- The **boost energy** `⟨K_boost⟩_ρ = tr(ρ·K_boost).re` — the expectation of the Lorentz boost generator. -/
noncomputable def boostEnergy (ρ K : Matrix n n ℂ) : ℝ := (ρ * K).trace.re

/-- Under the **Bisognano–Wichmann identification** `K_σ = 2π·K_boost + c·1`, the modular energy is
    `2π·⟨K_boost⟩_ρ + c` (the additive constant shifts by `c` because `tr ρ = 1`). -/
lemma modEnergy_of_BW {ρ σ : Matrix n n ℂ} (hρd : IsDensity ρ) (hσ : σ.IsHermitian)
    (Kboost : Matrix n n ℂ) (c : ℝ)
    (hBW : modHam hσ = (2 * Real.pi) • Kboost + c • (1 : Matrix n n ℂ)) :
    modEnergy ρ hσ = 2 * Real.pi * boostEnergy ρ Kboost + c := by
  rw [modEnergy_eq_trace, hBW]
  unfold boostEnergy
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul, hρd.trace_one, Complex.one_re, mul_one]

/-- **B3 — the Casini / Bisognano–Wichmann modular-energy bound** (the honest free-field Route-1 content).
    If the (finite-corner) modular Hamiltonian is the compressed boost generator up to a constant,
    `K_σ = 2π·K_boost + c·1` (the **BW/KMS identification, carried as an EXPLICIT hypothesis** — a generic
    corner does *not* preserve BW modular flow, so this is where the modular-invariant-corner assumption lives,
    not silently), then the entropy variation is bounded by the **boost energy** (the Unruh `2π`):
    `S(ρ) − S(σ) ≤ 2π (⟨K_boost⟩_ρ − ⟨K_boost⟩_σ)`.

    ⚠ Formalized modular QFT — **NOT** the holographic `S ≤ A/4G` bound. The `A/4G` identification of the boost
    generator's expectation with a geometric area is a *gravitational input*, not derivable here (file header). -/
theorem finiteCorner_wedge_Casini_BW {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρd : IsDensity ρ) (hσd : IsDensity σ) (Kboost : Matrix n n ℂ) (c : ℝ)
    (hBW : modHam hσ.1 = (2 * Real.pi) • Kboost + c • (1 : Matrix n n ℂ)) :
    vonNeumannEntropy hρd - vonNeumannEntropy hσd
      ≤ 2 * Real.pi * (boostEnergy ρ Kboost - boostEnergy σ Kboost) := by
  have hcasini := modular_casini_bound hρ hσ hρd hσd
  rw [modEnergy_of_BW hρd hσ.1 Kboost c hBW, modEnergy_of_BW hσd hσ.1 Kboost c hBW] at hcasini
  linarith [hcasini]

end ModularEnergyBound
end QIQTH
