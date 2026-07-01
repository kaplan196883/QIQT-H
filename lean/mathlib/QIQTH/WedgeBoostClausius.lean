/-
  BRIDGE C1 — the wedge modular Hamiltonian as the geometric boost: the Clausius datum, packaged.

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified). The free-field modular flow is DONE and axiom-free
    (`ModularHamiltonianOp.lean`): `Δ^{it} = modUnitary S t` is a `C¹` one-parameter unitary group with Stone
    generator `−iK` (`K = modK S = ∫kFn dE_R`), and the modular correlator derivative is DERIVED:
    `d/dt⟪ξ, Δ^{it}ξ⟫|₀ = i·(−cgpEntropy S ξ)` (`hasDerivAt_inner_modUnitary`). What is NOT derived — the
    **Bisognano–Wichmann identification** of the modular flow with the geometric (Rindler) wedge boost — is a
    physical input; here it is packaged as a CARRIED structure field (`WedgeBoostPackage.hBW`), never a Lean axiom
    (exactly hypothesis #3 of `WedgeKMSToGR.WedgeKMSFlux`).

  Payload: GIVEN the BW identification, the **geometric boost correlator** inherits the derived modular derivative —
  `d/dt⟪ξ, V_t ξ⟫|₀ = i·(−S)` with `S` the modular (CGP) entanglement entropy — and its **heat-flux/Clausius datum
  is UNIQUE** (`boost_flux_unique`, by derivative uniqueness): any candidate flux `c` with `d/dt⟪ξ,V_tξ⟫|₀ = i·c`
  MUST equal `−S`. δ⟨K_boost⟩ = −δS is forced, not chosen — the first-law/Clausius datum the assembly (ASM) and the
  GR chain consume. The real (physical) form: the imaginary part of the boost correlator has slope `−S`.

  ⚠ Honest labels: the BW identification and the Rindler-weight formula for `K_boost` (`2π∫x¹T₀₀`) are CARRIED
    physics (the weight is packaged only at the level the existing theorems support — the correlator-derivative
    datum); free-field / RvD standard-subspace setting; this is C1 packaging, NOT a derivation of BW and NOT the
    area law (D). `hdom` = finite modular energy; `hspec` = the separating spectral condition.
-/
import Mathlib
import QIQTH.ModularHamiltonianOp

namespace QIQTH.WedgeBoost

open QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The C1 package: a geometric wedge boost, BW-identified with the modular flow on the state.**
    `boost t` is the geometric (Rindler) boost flow through the wedge (rescaled `t ↦ boost(−2πt)` in the GR-chain
    convention); `hBW` is the **carried Bisognano–Wichmann identification** `V_t ξ = Δ^{it} ξ` — a structure field
    (hypothesis), NEVER a Lean axiom. This is exactly input #3 of `WedgeKMSToGR.WedgeKMSFlux`, isolated. -/
structure WedgeBoostPackage (S : StandardSubspace H) (ξ : H) where
  /-- the geometric boost flow `t ↦ V_t` -/
  boost : ℝ → H → H
  /-- CARRIED Bisognano–Wichmann: the geometric boost acts on the state as the modular flow -/
  hBW : ∀ t, boost t ξ = modUnitary S t ξ

variable {S : StandardSubspace H} {ξ : H}

/-- **The geometric boost correlator inherits the derived modular derivative:**
    `d/dt⟪ξ, V_t ξ⟫|₀ = i·(−S)` with `S = cgpEntropy S ξ` the modular entanglement entropy. The DERIVED
    modular-correlator theorem (`hasDerivAt_inner_modUnitary`), transported through the carried BW identification —
    the geometric boost energy flux of the state is the modular entropy. -/
theorem boost_correlator_hasDerivAt (P : WedgeBoostPackage S ξ)
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ (P.boost t ξ))
      (Complex.I * ((-cgpEntropy S ξ : ℝ) : ℂ)) 0 := by
  have heq : (fun t : ℝ => inner ℂ ξ (P.boost t ξ))
      = fun t : ℝ => inner ℂ ξ (modUnitary S t ξ) := by
    funext t; rw [P.hBW t]
  rw [heq]
  exact _root_.QIQTH.StandardSubspaceModular.hasDerivAt_inner_modUnitary S hdom hspec

/-- **The Clausius datum is UNIQUE (forced):** any candidate heat-flux value `c` for the geometric boost
    correlator (`d/dt⟪ξ,V_tξ⟫|₀ = i·c`) must equal `−cgpEntropy S ξ`. By derivative uniqueness, the
    first-law/Clausius datum `δ⟨K_boost⟩ = −δS` is *forced* by the modular machinery + the carried BW
    identification — not a choice. This is the wedge-side input the assembly (ASM) and the GR chain
    (`WedgeKMSFlux` #6, there derived; #3, here carried) consume. -/
theorem boost_flux_unique (P : WedgeBoostPackage S ξ) (c : ℝ)
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2)
    (hc : HasDerivAt (fun t : ℝ => inner ℂ ξ (P.boost t ξ)) (Complex.I * (c : ℂ)) 0) :
    c = -cgpEntropy S ξ := by
  have h := hc.unique (boost_correlator_hasDerivAt P hdom hspec)
  have h' : (c : ℂ) = ((-cgpEntropy S ξ : ℝ) : ℂ) := mul_left_cancel₀ Complex.I_ne_zero h
  exact_mod_cast h'

/-- **The real (physical) Clausius form:** the imaginary part of the geometric boost correlator has slope
    `−S` at `t = 0` — `d/dt Im⟪ξ, V_t ξ⟫|₀ = −cgpEntropy S ξ`. The real observable carrying the first-law
    datum (the real part is stationary). -/
theorem boost_correlator_im_hasDerivAt (P : WedgeBoostPackage S ξ)
    (hdom : ξ ∈ (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).fcDomain
      (fun ω : spectrum ℝ (rvdRC S) => kFn ω.val))
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), (ω : spectrum ℝ (rvdRC S)).val ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt (fun t : ℝ => (inner ℂ ξ (P.boost t ξ) : ℂ).im) (-cgpEntropy S ξ) 0 := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (boost_correlator_hasDerivAt P hdom hspec)
  simpa [Complex.mul_im] using h

end QIQTH.WedgeBoost
