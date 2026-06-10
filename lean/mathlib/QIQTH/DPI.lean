/-
  Data Processing Inequality (DPI) — interface + regional corollary.

  Statement (axiomatized):  for any normal CP channel Φ,
      S(ω ∘ Φ ‖ σ ∘ Φ)  ≤  S(ω ‖ σ).

  At the AQFT/Araki level, DPI is a deep theorem (Lindblad/Uhlmann,
  Petz, …) requiring operator convexity of `−log` and full vN
  machinery (Lieb's concavity); Mathlib doesn't have it, so the
  inequality remains an interface axiom.  States now live in a
  `DonaldSystem` (the former `Donald.State`/`Donald.D`).
-/

import QIQTH.Donald

namespace QIQTH
namespace DPI

open DonaldSystem

variable {State : Type} [DonaldSystem State]

/-- A *channel* in the abstract Heisenberg sense. -/
axiom Channel : Type

/-- A channel acts on states by Schrödinger pullback. -/
axiom Channel.pull : Channel → State → State

/-- **Data Processing Inequality (axiom).**  For any channel `Φ` and states `ρ`, `σ`:
        D(Φ.pull ρ  ‖  Φ.pull σ)  ≤  D(ρ ‖ σ).
    Applying the same CPTP channel to both arguments of relative entropy can only decrease
    it.  This is the deep Lindblad/Uhlmann/Lieb theorem, not in Mathlib — kept as the
    interface axiom (over an arbitrary `DonaldSystem`). -/
axiom DPI_inequality (Φ : Channel) (ρ σ : State) :
    D (Φ.pull ρ) (Φ.pull σ) ≤ D ρ σ

/-- **Regional restriction is a channel.** -/
axiom restrict : ∀ (S R : Type), S → R → Channel

/-- **Regional monotonicity of relative entropy.**  Proof: DPI applied to the
    regional-restriction channel. -/
theorem regional_monotone
    {Stype Rtype : Type} (S' : Stype) (R' : Rtype)
    (ω_R σ_R : State) :
    let Φ := restrict Stype Rtype S' R'
    D (Φ.pull ω_R) (Φ.pull σ_R) ≤ D ω_R σ_R :=
  DPI_inequality _ _ _

/-- **DPI under composition.** -/
theorem DPI_comp
    (Φ Ψ : Channel) (ρ σ : State) :
    D ((Ψ.pull ∘ Φ.pull) ρ) ((Ψ.pull ∘ Φ.pull) σ) ≤ D ρ σ := by
  show D (Ψ.pull (Φ.pull ρ)) (Ψ.pull (Φ.pull σ)) ≤ D ρ σ
  exact le_trans (DPI_inequality Ψ _ _) (DPI_inequality Φ _ _)

end DPI
end QIQTH
