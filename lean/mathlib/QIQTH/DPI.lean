/-
  Data Processing Inequality (DPI) — interface + regional corollary.

  Statement (axiomatized):  for any normal CP channel Φ,
      S(ω ∘ Φ ‖ σ ∘ Φ)  ≤  S(ω ‖ σ).

  At the AQFT/Araki level, DPI is a deep theorem (Lindblad/Uhlmann,
  Petz, …) requiring operator convexity of `−log` and full vN
  machinery.  Mathlib doesn't have it.  We axiomatize the inequality
  as an `RelEntDPI` interface and prove the regional corollary
  (entropy on a subregion ≤ entropy on the containing region) as a
  consequence.
-/

import QIQTH.Donald

namespace QIQTH
namespace DPI

open Donald

/-- A *channel* in the abstract Heisenberg sense: an `Obs → Obs` map
    plus, for the DPI statement, a witness that pulling states back
    along it gives DPI on relative entropy. -/
axiom Channel : Type

/-- A channel acts on states by Schrödinger pullback. -/
axiom Channel.pull : Channel → State → State

/-- **Data Processing Inequality (axiom).**  For any channel `Φ` and
    states `ρ`, `σ`:
        D(Φ.pull ρ  ‖  Φ.pull σ)  ≤  D(ρ ‖ σ).
    Concretely: applying the same CPTP channel to both arguments of
    relative entropy can only decrease it. -/
axiom DPI_inequality (Φ : Channel) (ρ σ : State) :
    D (Φ.pull ρ) (Φ.pull σ) ≤ D ρ σ

/-- **Regional restriction is a channel.** Restricting from algebra
    `A(R)` to a subregion `A(S) ⊂ A(R)` is a CP map, hence a channel
    in the abstract sense. -/
axiom restrict : ∀ (S R : Type), S → R → Channel

/-- **Regional monotonicity of relative entropy.**  If `S ⊆ R` and
    the reference states are compatible, the regional relative
    entropy on the subregion is bounded by the regional relative
    entropy on the larger region.  This is what makes the
    holographic-capacity bounds compose correctly across nested
    regions.

    Proof: DPI applied to the regional-restriction channel. -/
theorem regional_monotone
    {Stype Rtype : Type} (S' : Stype) (R' : Rtype)
    (ω_R σ_R : State) :
    let Φ := restrict Stype Rtype S' R'
    D (Φ.pull ω_R) (Φ.pull σ_R) ≤ D ω_R σ_R :=
  DPI_inequality _ _ _

/-- **DPI under composition.**  If two channels both satisfy DPI
    individually (which our axiom gives them universally), then so
    does their composition. -/
theorem DPI_comp
    (Φ Ψ : Channel) (ρ σ : State) :
    D ((Ψ.pull ∘ Φ.pull) ρ) ((Ψ.pull ∘ Φ.pull) σ) ≤ D ρ σ := by
  show D (Ψ.pull (Φ.pull ρ)) (Ψ.pull (Φ.pull σ)) ≤ D ρ σ
  exact le_trans (DPI_inequality Ψ _ _) (DPI_inequality Φ _ _)

end DPI
end QIQTH
