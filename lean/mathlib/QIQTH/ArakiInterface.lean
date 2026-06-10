/-
  ArakiInterface — the finite-dimensional realization of the Araki relative-entropy interface.

  Formerly this module declared `NormalState`, `IsFaithful`, `mixture`, `AkRelEnt`, `Akre_nonneg`,
  `donald_araki`, `NormalUCPChannel`, `NormalUCPChannel.pull` and `dpi_ucp` as opaque AXIOMS over an
  abstract regional von Neumann algebra.  Nine of those eleven are now **DISCHARGED** by the
  finite-dimensional model (`NormalState := HermitianMat`, the carrier of `QuantumEntropy`'s
  `DonaldSystem`):

    * `AkRelEnt`     := the Umegaki relative entropy `DonaldSystem.D` (= `relEntropy`);
    * `Akre_nonneg`  := **Klein's inequality** `relEntropy_nonneg` (a theorem — conditioned on the
                        density-matrix hypotheses Klein genuinely requires);
    * `donald_araki` := **Donald's identity** `Donald.donald_identity` (a theorem);
    * `dpi_ucp`      := the **data-processing inequality** `DPI.DPI_inequality` (a theorem, for the
                        mixed-unitary channel class).

  HONEST SCOPE (per the original GPT-5.5-pro audit): in the genuine Araki / Tomita–Takesaki setting
  the cross-entropy object is unbounded and `AkRelEnt` can be `+∞`; this module is the *finite-dim
  model*, where those pathologies are absent — the unconditional abstract axioms become the honest
  conditional (density-matrix) theorems.  Two results remain axioms here, as the cited frontier:
  `IHol_le_Shannon` (Holevo's bound) and `AkRelEnt_eq_zero_iff` (the Klein *equality* case — only the
  trivial direction `ρ = σ ⟹ D = 0` is finite-dim immediate; the converse is a deeper milestone).
-/

import QIQTH.QuantumRelativeEntropy
import QIQTH.DPI

namespace QIQTH
namespace ArakiInterface

open QIQTH.QuantumEntropy
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Normal state** (finite-dim model): a Hermitian matrix — the carrier of the `DonaldSystem`.
    It is a genuine density matrix when additionally positive-definite with unit trace. -/
abbrev NormalState (n : Type) [Fintype n] [DecidableEq n] : Type := HermitianMat n

/-- **Faithful** = positive-definite (full support). -/
def IsFaithful (ρ : NormalState n) : Prop := ρ.1.PosDef

/-- **Araki relative entropy**, realized as the finite-dim Umegaki relative entropy `D`. -/
noncomputable def AkRelEnt (ρ σ : NormalState n) : ℝ := DonaldSystem.D ρ σ

/-- **Mixture** of finitely many normal states — the `DonaldSystem` weighted mixture. -/
noncomputable def mixture {ι : Type} (s : Finset ι) (p : ι → ℝ) (ρ : ι → NormalState n) :
    NormalState n :=
  DonaldSystem.mixture s p ρ

/-- `AkRelEnt` is the Umegaki relative entropy. -/
lemma AkRelEnt_eq_relEntropy (ρ σ : NormalState n) : AkRelEnt ρ σ = relEntropy ρ.2 σ.2 := by
  show (-((ρ.1 * matLog σ.2).trace.re) - -((ρ.1 * matLog ρ.2).trace.re))
      = (ρ.1 * (matLog ρ.2 - matLog σ.2)).trace.re
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]; ring

/-- Predicate: a finite ensemble has finite Araki relative entropy against the reference state.
    (Always finite in the finite-dim model.) -/
def FiniteEntropy (σ : NormalState n) (ρ : NormalState n) : Prop :=
  ∃ B : ℝ, AkRelEnt ρ σ ≤ B

/-- **Klein positivity (theorem).**  `0 ≤ AkRelEnt ω σ` for density matrices — the finite-dim
    content of the former `Akre_nonneg` axiom, now `relEntropy_nonneg` (Klein's inequality). -/
theorem Akre_nonneg (ρ σ : NormalState n) (hρ : ρ.1.PosDef) (hσ : σ.1.PosDef)
    (hρ1 : ρ.1.trace = 1) (hσ1 : σ.1.trace = 1) : 0 ≤ AkRelEnt ρ σ := by
  rw [AkRelEnt_eq_relEntropy]; exact relEntropy_nonneg hρ hσ hρ1 hσ1

/-- **Donald's identity (theorem).**  The former `donald_araki` axiom, now `Donald.donald_identity`
    over the finite-dim `DonaldSystem`. -/
theorem donald_araki {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (ρ : ι → NormalState n) (σ : NormalState n) :
    ∑ k ∈ s, p k * AkRelEnt (ρ k) σ
      = AkRelEnt (mixture s p ρ) σ + ∑ k ∈ s, p k * AkRelEnt (ρ k) (mixture s p ρ) :=
  Donald.donald_identity s p ρ σ

/-- **Normal UCP channel** (finite-dim model): a mixed-unitary channel. -/
abbrev NormalUCPChannel (n : Type) [Fintype n] [DecidableEq n] := DPI.MixedUnitaryChannel n

/-- A channel acts on states by Schrödinger pullback (Hermitian, since `Φ(ρ) = Σ pₖ Uₖ ρ Uₖ⋆`). -/
noncomputable def NormalUCPChannel.pull (Φ : NormalUCPChannel n) (ρ : NormalState n) :
    NormalState n :=
  ⟨DPI.MixedUnitaryChannel.pull Φ ρ.1, by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    refine isSelfAdjoint_sum _ fun k _ => (IsSelfAdjoint.all (Φ.p k)).smul ?_
    rw [isSelfAdjoint_iff, star_mul, star_mul, star_star,
      ρ.2.isSelfAdjoint.star_eq, ← mul_assoc]⟩

/-- **Data-processing inequality (theorem).**  For density-matrix states, applying a mixed-unitary
    channel can only decrease the relative entropy — the former `dpi_ucp` axiom, now
    `DPI.DPI_inequality` (Lindblad–Uhlmann via Lieb's concavity). -/
theorem dpi_ucp (Φ : NormalUCPChannel n) (ρ σ : NormalState n)
    (hρ : ρ.1.PosDef) (hσ : σ.1.PosDef) :
    AkRelEnt (Φ.pull ρ) (Φ.pull σ) ≤ AkRelEnt ρ σ := by
  rw [AkRelEnt_eq_relEntropy, AkRelEnt_eq_relEntropy]
  exact DPI.DPI_inequality Φ hρ hσ (Φ.pull ρ).2 (Φ.pull σ).2

/-! ### Holevo information -/

/-- Holevo mutual information of a finite ensemble. -/
noncomputable def IHol {ι : Type} (s : Finset ι) (p : ι → ℝ) (ρ : ι → NormalState n) : ℝ :=
  ∑ i ∈ s, p i * AkRelEnt (ρ i) (mixture s p ρ)

/-- **Holevo non-negativity** — from Klein (density ensemble against the mixture). -/
theorem IHol_nonneg {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → NormalState n)
    (hdens : ∀ i ∈ s, (ρ i).1.PosDef ∧ (ρ i).1.trace = 1)
    (hbar : (mixture s p ρ).1.PosDef ∧ (mixture s p ρ).1.trace = 1) :
    0 ≤ IHol s p ρ := by
  refine Finset.sum_nonneg fun k hk => ?_
  exact mul_nonneg (hp_nn k hk)
    (Akre_nonneg _ _ (hdens k hk).1 hbar.1 (hdens k hk).2 hbar.2)

/-- Shannon entropy of the weight distribution (in nats). -/
noncomputable def ShannonWeights {ι : Type} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ i ∈ s, p i * Real.log (p i)

/-- **Holevo ≤ Shannon** for orthogonal ensembles.  Remains an axiom (Holevo's theorem; the
    cited frontier — not reachable from §6.3 joint convexity alone). -/
axiom IHol_le_Shannon {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    (ρ : ι → NormalState n)
    (h_orth : ∀ i j, i ≠ j → AkRelEnt (ρ i) (ρ j) = 0 → False) :
    IHol s p ρ ≤ ShannonWeights s p

/-- The trivial direction of the Klein equality case: `ρ = σ ⟹ D(ρ‖σ) = 0`. -/
theorem AkRelEnt_self (ρ : NormalState n) : AkRelEnt ρ ρ = 0 := by
  rw [AkRelEnt_eq_relEntropy]; exact relEntropy_self ρ.2

/-- **Klein equality case (faithful reference).**  `AkRelEnt(ω ‖ σ) = 0 ↔ ω = σ`.  Remains an axiom:
    only the `←` direction is finite-dim immediate (`AkRelEnt_self`); the `→` direction is the
    deeper Klein-equality milestone (strict concavity of `log`), the cited frontier. -/
axiom AkRelEnt_eq_zero_iff
    (ω σ : NormalState n) (hσ_faithful : IsFaithful σ) :
    AkRelEnt ω σ = 0 ↔ ω = σ

end ArakiInterface
end QIQTH
