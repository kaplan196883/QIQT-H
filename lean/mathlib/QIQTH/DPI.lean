/-
  Data Processing Inequality (DPI) — concrete mixed-unitary realization.

  Formerly this file declared `Channel`, `Channel.pull`, `DPI_inequality` and `restrict` as opaque
  AXIOMS over an abstract `DonaldSystem`.  They are now **DISCHARGED**: a mixed-unitary
  (random-unitary) channel is a concrete `structure`, its Schrödinger action a `def`, and the
  data-processing inequality a **theorem** (`QIQTH.Entropy.dpi_mixed_unitary`), proved from the
  joint convexity of the quantum relative entropy (Lieb's concavity → Carlen §6.3), built end to
  end from the `CStarMatrix` bridge.  This retires the 4 DPI axioms (budget 21 → 17).

  **HONEST SCOPE.**  This discharges DPI for the *mixed-unitary* CPTP class `Φ(ρ) = Σₖ pₖ Uₖ ρ Uₖ⋆`
  — a genuine but proper subclass (it includes e.g. the depolarizing and dephasing channels).
  Fully general CPTP DPI (in particular partial trace / regional restriction, the former `restrict`)
  additionally needs the Stinespring dilation / partial-trace averaging of Carlen §6.4, which is
  beyond the §6.3 joint convexity proved here; that remains the cited frontier.  The former
  `regional_monotone`/`DPI_comp` corollaries had no consumers and are dropped.
-/

import QIQTH.Entropy.RelEntropyDPI

namespace QIQTH
namespace DPI

open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A **mixed-unitary (random-unitary) channel**: a finite probability distribution `p` over
    unitaries `U`.  The concrete replacement for the former opaque `Channel` axiom. -/
structure MixedUnitaryChannel (n : Type) [Fintype n] [DecidableEq n] where
  /-- Kraus index type. -/
  κ : Type
  /-- Finite support of the distribution. -/
  s : Finset κ
  /-- The support is nonempty. -/
  hs : s.Nonempty
  /-- The weights. -/
  p : κ → ℝ
  /-- The weights are (strictly) positive. -/
  hp : ∀ k, 0 < p k
  /-- The weights on the support sum to one. -/
  hsum : ∑ k ∈ s, p k = 1
  /-- The unitaries. -/
  U : κ → unitary (Matrix n n ℂ)

/-- The channel's Schrödinger action `Φ(ρ) = Σₖ pₖ · Uₖ ρ Uₖ⋆`.  Replaces `Channel.pull`. -/
noncomputable def MixedUnitaryChannel.pull (Φ : MixedUnitaryChannel n) (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  ∑ k ∈ Φ.s, (Φ.p k : ℝ) • ((Φ.U k : Matrix n n ℂ) * ρ * (star (Φ.U k) : Matrix n n ℂ))

/-- **Data Processing Inequality (theorem).**  Applying a mixed-unitary channel to both arguments
    of the quantum relative entropy can only decrease it:  `D(Φρ ‖ Φσ) ≤ D(ρ‖σ)`.

    Discharged from the joint convexity of relative entropy (`QIQTH.Entropy.dpi_mixed_unitary`,
    Lindblad–Uhlmann via Lieb's concavity).  Formerly the opaque `DPI_inequality` axiom. -/
theorem DPI_inequality (Φ : MixedUnitaryChannel n) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hΦρ : (Φ.pull ρ).IsHermitian) (hΦσ : (Φ.pull σ).IsHermitian) :
    QIQTH.QuantumEntropy.relEntropy hΦρ hΦσ
      ≤ QIQTH.QuantumEntropy.relEntropy hρ.1 hσ.1 :=
  QIQTH.Entropy.dpi_mixed_unitary Φ.hs hρ hσ Φ.p Φ.hp Φ.hsum Φ.U hΦρ hΦσ

end DPI
end QIQTH
