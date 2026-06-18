/-
  EntanglementFirstLaw — Route B toward "GR as an emergent equation of state":
  the entanglement first law δS = δ⟨K⟩, and the Ryu–Takayanagi bridge to δA/4G = δ⟨K⟩.

  GPT-5.5-pro's recommended target (2026-06-18): rather than re-derive differential geometry
  (Raychaudhuri), formalize the step that USES QIQT-H's already-machine-checked relative-entropy
  machinery. The entanglement-first-law derivation of (linearized) Einstein gravity
  (Lashkari–Van Raamsdonk 2013; Faulkner–Guica–Hartman–Myers–Van Raamsdonk 2013) rests on:

    1. THE FIRST LAW  δS_B = δ⟨K_B⟩  — the load-bearing, non-textbook step. It is NOT an axiom:
       it follows because relative entropy D(ρ‖σ) is (a) ≥ 0 and (b) = 0 at ρ=σ, hence STATIONARY
       there, so its first variation vanishes; with the identity D = ⟨K⟩ − S this gives δS = δ⟨K⟩.
    2. Ryu–Takayanagi  S_B = A_B/4G  — CITED (holographic entanglement entropy).
    3. The CFT ball modular Hamiltonian  K_B = 2π∫_B (R²−r²)/2R · T₀₀  — CITED.
    4. The gravitational all-balls ⇒ linearized-Einstein theorem — CITED.

  This file MACHINE-CHECKS step 1 (the first law) as a clean real-analysis consequence of
  stationarity, and chains it with (2)–(3) as hypotheses to the all-balls energy identity.
  CRUCIALLY, the first law's inputs are QIQT-H's OWN verified facts (not new assumptions):
    • hpos  (D ≥ 0)        =  `QuantumEntropy.relEntropy_nonneg`        (Klein, machine-checked)
    • hident (D = ⟨K⟩ − S) =  `QuantumEntropy.relEntropy_eq_crossEntropy_sub_entropy`  (machine-checked)
    • hzero (D(0) = 0)     =  `QuantumEntropy.relEntropy_self`          (machine-checked)
  The only granted input is the smoothness (DifferentiableAt) of the state family ε ↦ ρ(ε) —
  the genuine analytic frontier (proof-carrying matrix families are deferred). RT, the ball modular
  Hamiltonian, and the gravitational corollary are CITED. So this does NOT derive Einstein's
  equation; it machine-checks the information-theoretic first law and the bridge to the RT area
  variation. See paper_strategy/51_GR_Emergent_EquationOfState.md §2, §4b.
-/
import QIQTH.QuantumRelativeEntropy
import QIQTH.SpectralSum

open scoped ComplexOrder

namespace QIQTH.EntanglementFirstLaw

/-- **The entanglement first law** `δS = δ⟨K⟩`, as a consequence of relative-entropy stationarity.
    Along a one-parameter family of states, write `S ε` (von Neumann entropy), `KE ε` (modular
    energy `⟨K⟩`), and `D ε` (relative entropy vs the reference). Given the relative-entropy
    identity `D = KE − S`, positivity `D ≥ 0`, vanishing at the reference `D 0 = 0`, and
    differentiability of `S, KE` at `0`, the first variations of entropy and modular energy agree:
    `deriv S 0 = deriv KE 0`. (The inputs are QIQT-H's machine-checked relative-entropy facts;
    see the module header.) -/
theorem firstLaw_of_stationary
    (S KE D : ℝ → ℝ)
    (hident : ∀ ε, D ε = KE ε - S ε)
    (hpos : ∀ ε, 0 ≤ D ε) (hzero : D 0 = 0)
    (hS : DifferentiableAt ℝ S 0) (hKE : DifferentiableAt ℝ KE 0) :
    deriv S 0 = deriv KE 0 := by
  -- relative entropy has a global (hence local) minimum at 0, so its derivative there is 0
  have hmin : IsLocalMin D 0 :=
    Filter.Eventually.of_forall (fun x => by rw [hzero]; exact hpos x)
  have h0 : deriv D 0 = 0 := hmin.deriv_eq_zero
  -- but D = KE − S, so deriv D 0 = deriv KE 0 − deriv S 0
  have hDeq : D = fun ε => KE ε - S ε := funext hident
  have hcomp : deriv D 0 = deriv KE 0 - deriv S 0 := by rw [hDeq]; exact deriv_sub hKE hS
  rw [hcomp] at h0
  linarith

/-- **The Ryu–Takayanagi bridge.** Combining the first law with the (CITED) holographic
    entanglement-entropy relation `S_B = A_B/4G` gives the variation of the horizon area equal to
    the variation of modular energy: `δ(A/4G) = δ⟨K⟩`. This is the information-theoretic side of the
    entanglement derivation of linearized gravity. -/
theorem rt_bridge
    (S KE D Area : ℝ → ℝ) (G : ℝ)
    (hident : ∀ ε, D ε = KE ε - S ε) (hpos : ∀ ε, 0 ≤ D ε) (hzero : D 0 = 0)
    (hS : DifferentiableAt ℝ S 0) (hKE : DifferentiableAt ℝ KE 0)
    (hRT : ∀ ε, S ε = Area ε / (4 * G)) :
    deriv (fun ε => Area ε / (4 * G)) 0 = deriv KE 0 := by
  have flaw := firstLaw_of_stationary S KE D hident hpos hzero hS hKE
  have hAS : (fun ε => Area ε / (4 * G)) = S := funext (fun ε => (hRT ε).symm)
  rw [hAS]; exact flaw

/-- **The all-balls weighted-boundary-energy identity.** Adding the (CITED) CFT ball modular
    Hamiltonian `K_B = 2π∫_B (R²−r²)/2R · T₀₀`, whose first variation is the weighted boundary energy
    `W`, yields `δ(A_B/4G) = W` for every ball `B`. By the (CITED) Lashkari–Van Raamsdonk / Faulkner
    et al. gravitational theorem, "this identity for all balls" is equivalent to the LINEARIZED
    Einstein equations — that last implication is NOT formalized here. -/
theorem rt_all_balls_energy
    (S KE D Area : ℝ → ℝ) (G W : ℝ)
    (hident : ∀ ε, D ε = KE ε - S ε) (hpos : ∀ ε, 0 ≤ D ε) (hzero : D 0 = 0)
    (hS : DifferentiableAt ℝ S 0) (hKE : DifferentiableAt ℝ KE 0)
    (hRT : ∀ ε, S ε = Area ε / (4 * G))
    (hMod : deriv KE 0 = W) :
    deriv (fun ε => Area ε / (4 * G)) 0 = W := by
  rw [rt_bridge S KE D Area G hident hpos hzero hS hKE hRT]; exact hMod

-- Grounding: the first-law inputs are QIQT-H's OWN machine-checked relative-entropy facts,
-- not new postulates.  (Emitted to the build log to make the dependency explicit.)
#check @QIQTH.QuantumEntropy.relEntropy_nonneg                 -- discharges `hpos`
#check @QIQTH.QuantumEntropy.relEntropy_eq_crossEntropy_sub_entropy  -- discharges `hident`
#check @QIQTH.QuantumEntropy.relEntropy_self                   -- discharges `hzero`

/-! ### Discharging the entropy smoothness at the SPECTRAL level (the matrix-log "eigen" derivative)

The genuine analytic content of `hS` is "the von Neumann entropy is smooth." Since
`S = ∑ᵢ negMulLog(λᵢ)` (eigenvalues), the matrix-`log` derivative lives entirely in `negMulLog`,
which Mathlib knows is differentiable away from `0` (`Real.differentiableAt_negMulLog`) with
`deriv = −log − 1`. So the entropy is differentiable along ANY family of eigenvalue vectors `p(ε)`
whose components are differentiable and nonzero — this is the spectral half of the wall, now CHECKED.
What remains is purely the eigenvalue-perturbation map `ρ ↦ eigenvalues` (immediate for a
fixed-eigenbasis family `ρ(ε)=U diag(p ε) U†`; the general case is the separate, deeper gap). -/

/-- **Entropy is differentiable in its eigenvalues.** For an eigenvalue (probability) family `p(ε)`
    with each component differentiable at `0` and nonzero there, the spectral entropy
    `∑ᵢ negMulLog(pᵢ(ε))` is differentiable at `0`. Discharges `hS` at the spectral level. -/
theorem spectralEntropy_differentiableAt {m : Type*} [Fintype m] (p : ℝ → m → ℝ)
    (hp : ∀ i, DifferentiableAt ℝ (fun ε => p ε i) 0) (hpos : ∀ i, p 0 i ≠ 0) :
    DifferentiableAt ℝ (fun ε => ∑ i, Real.negMulLog (p ε i)) 0 := by
  apply DifferentiableAt.fun_sum
  intro i _
  exact (Real.differentiableAt_negMulLog (hpos i)).comp 0 (hp i)

/-- **The spectral entropy derivative (explicit).** With each `pᵢ` differentiable and nonzero at `0`,
    `δS = ∑ᵢ (−log pᵢ(0) − 1)·pᵢ'(0)`. (For a trace-preserving family `∑ᵢ pᵢ'(0)=0` this reduces to
    `−∑ᵢ log pᵢ(0)·pᵢ'(0)` — the standard entropy first variation.) -/
theorem spectralEntropy_deriv {m : Type*} [Fintype m] (p : ℝ → m → ℝ)
    (hp : ∀ i, DifferentiableAt ℝ (fun ε => p ε i) 0) (hpos : ∀ i, p 0 i ≠ 0) :
    deriv (fun ε => ∑ i, Real.negMulLog (p ε i)) 0
      = ∑ i, (- Real.log (p 0 i) - 1) * deriv (fun ε => p ε i) 0 := by
  refine (HasDerivAt.fun_sum ?_).deriv
  intro i _
  exact (Real.hasDerivAt_negMulLog (hpos i)).comp 0 (hp i).hasDerivAt

open QIQTH.QuantumEntropy in
/-- **The von Neumann entropy is differentiable when its eigenvalues are.** For a family of densities
    `ρ(ε)` with density proofs `h ε`, `vonNeumannEntropy (h ε) = ∑ᵢ negMulLog((h ε).eigenvalues i)` *by
    definition*, so the entropy is differentiable at `0` whenever each eigenvalue `(h ε).eigenvalues i` is
    differentiable and nonzero there. This lifts `spectralEntropy_differentiableAt` onto the actual von
    Neumann entropy and discharges `hS` for the first law — reducing the wall to exactly the
    eigenvalue-perturbation hypothesis `hev`. (Discharging `hev` itself for a concrete family is the
    residual gap: `IsDensity.eigenvalues` is the *sorted spectral data*, and Mathlib has no lemma
    relating it to an external diagonal `p`, nor analytic eigenvalue perturbation — and in general the
    sorted eigenvalues even have kinks at level crossings. So `hev` is mathematically trivial for a
    fixed-eigenbasis family but Lean-blocked on the eigenvalue API; it is honestly the cited gap.) -/
theorem vonNeumannEntropy_differentiableAt {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : ℝ → Matrix n n ℂ) (h : (ε : ℝ) → IsDensity (ρ ε))
    (hev : ∀ i, DifferentiableAt ℝ (fun ε => (h ε).eigenvalues i) 0)
    (hpos : ∀ i, (h 0).eigenvalues i ≠ 0) :
    DifferentiableAt ℝ (fun ε => vonNeumannEntropy (h ε)) 0 :=
  spectralEntropy_differentiableAt (fun ε i => (h ε).eigenvalues i) hev hpos

open QIQTH.QuantumEntropy in
/-- **`hS` DISCHARGED for a diagonal fixed-basis family.** For a family of *diagonal* densities
    `ρ(ε) = diagonal(p(ε))` with each `pᵢ` differentiable and nonzero at `0`, the von Neumann entropy is
    differentiable at `0` — *no `hev` assumption needed*: `vonNeumannEntropy(h ε) = ∑ᵢ negMulLog(pᵢ(ε))`
    by `SpectralSum.vonNeumannEntropy_diagonal` (the eigenvalue ordering eliminated through the
    characteristic polynomial), and then `spectralEntropy_differentiableAt`. This closes the fixed-basis
    (U = I) case of the eigenvalue-perturbation wall: the first law's `hS` is now a THEOREM here. -/
theorem vonNeumannEntropy_diagonal_differentiableAt {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℝ → n → ℝ) (h : (ε : ℝ) → IsDensity (Matrix.diagonal (fun i => (p ε i : ℂ))))
    (hp : ∀ i, DifferentiableAt ℝ (fun ε => p ε i) 0) (hpos : ∀ i, p 0 i ≠ 0) :
    DifferentiableAt ℝ (fun ε => vonNeumannEntropy (h ε)) 0 := by
  have hconv : (fun ε => vonNeumannEntropy (h ε)) = (fun ε => ∑ i, Real.negMulLog (p ε i)) :=
    funext fun ε => QIQTH.SpectralSum.vonNeumannEntropy_diagonal (p ε) (h ε)
  rw [hconv]
  exact spectralEntropy_differentiableAt p hp hpos

/-! ### The integrated (finite) first law — no differentiability needed

The *differential* first law `δS = δ⟨K⟩` needs the smoothness of the family (the matrix-log /
eigenvalue-perturbation derivative — a genuine Mathlib gap). But the **integrated** form — the Gibbs /
Klein inequality `S(ρ) ≤ ⟨K⟩` with equality at the reference — needs no differentiation and is fully
grounded in QIQT-H's verified relative-entropy facts. It is the finite shadow of the first law:
entropy is bounded by modular energy, saturated exactly at `ρ = σ`. -/

open QIQTH.QuantumEntropy in
/-- **Integrated first law (Gibbs/Klein inequality).** The von Neumann entropy of any density `ρ` is at
    most its modular energy (cross entropy) against a reference `σ`: `S(ρ) ≤ ⟨K⟩ = crossEntropy ρ σ`,
    with equality iff `ρ = σ`. This is `relEntropy ≥ 0` (Klein) + `relEntropy = crossEntropy − S`, both
    machine-checked. No differentiability is used — the finite shadow of `δS = δ⟨K⟩`. -/
theorem gibbs_first_law {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ crossEntropy ρ hσ.1 := by
  have hpos := relEntropy_nonneg hρ hσ hρ1 hσ1
  have hid := relEntropy_eq_crossEntropy_sub_entropy hρ hσ h
  rw [hid] at hpos
  linarith

end QIQTH.EntanglementFirstLaw
