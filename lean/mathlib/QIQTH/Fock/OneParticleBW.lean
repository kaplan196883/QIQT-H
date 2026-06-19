import QIQTH.StandardSubspaceModularFlow

/-!
# One-particle Bisognano–Wichmann — Phase 0: the scalar spectral identity

Toward the one-particle BW identification `modUnitary 𝒦_wedge t = boostUnitary(−2π t)` (the
standard-subspace modular flow IS the geometric Lorentz boost), following GPT-5.5's plan
(Route C — the RvD bridge: it suffices that the wedge RvD operator `R` is the **Fermi function** of the
boost generator `P`, `R = 2/(1+exp(2π P))`, since then `g(R) = log((2−R)/R) = 2π P`).

This file proves the **scalar core** of that spectral identity — fully self-contained, axiom-free:
the modular spectral character `modChar t r = exp(i·t·log((2−r)/r))` evaluated at `r = fermi x`
(`fermi x = 2/(1+e^{2π x})`) is exactly `exp(i·t·2π x)`.  This is the pointwise statement
`g(fermi x) = 2π x` behind `modUnitary(t) = exp(i·t·2π P) = boostUnitary(−2π t)`.

The physical wedge subspace, its standardness, and the operator identity `rvdRC 𝒦 = fermi(2π P)` are the
genuinely analytic inputs (one-particle Reeh–Schlieder / strip-KMS) — those will be isolated as labelled
conditional hypotheses, NOT proved here and NEVER Lean axioms.
-/

namespace QIQTH.Fock.OneParticleBW

open QIQTH.StandardSubspaceModular

/-- The **Fermi function** of the boost generator's spectral parameter:
    `fermi x = 2/(1 + e^{2π x})`.  This is the spectral form of the wedge RvD operator `R` in the
    momentum (`P = −i d/dθ`) representation: `R = fermi(2π P)`. -/
noncomputable def fermi (x : ℝ) : ℝ := 2 / (1 + Real.exp (2 * Real.pi * x))

theorem fermi_mem_Ioo (x : ℝ) : fermi x ∈ Set.Ioo (0 : ℝ) 2 := by
  have hE : (0 : ℝ) < Real.exp (2 * Real.pi * x) := Real.exp_pos _
  refine ⟨by unfold fermi; positivity, ?_⟩
  unfold fermi
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hE]

/-- **The scalar BW spectral identity** `g(fermi x) = 2π x`, in character form:
    `modChar t (fermi x) = exp(i·t·2π x)`.  Since `(2 − fermi x)/fermi x = e^{2π x}`, the modular
    generator `g(r) = log((2−r)/r)` evaluated at `fermi x` is `2π x` — the pointwise core of
    `modUnitary(t) = boostUnitary(−2π t)`. -/
theorem modChar_fermi (t x : ℝ) :
    modChar t (fermi x) = Complex.exp (Complex.I * (t : ℂ) * ((2 * Real.pi * x : ℝ) : ℂ)) := by
  have hE : (0 : ℝ) < Real.exp (2 * Real.pi * x) := Real.exp_pos _
  have h1E : (1 : ℝ) + Real.exp (2 * Real.pi * x) ≠ 0 := by positivity
  have hratio : (2 - fermi x) / fermi x = Real.exp (2 * Real.pi * x) := by
    unfold fermi
    field_simp
    ring
  have hlog : Real.log ((2 - fermi x) / fermi x) = 2 * Real.pi * x := by
    rw [hratio, Real.log_exp]
  unfold modChar
  rw [Set.piecewise_eq_of_mem _ _ _ (fermi_mem_Ioo x), hlog]

end QIQTH.Fock.OneParticleBW
