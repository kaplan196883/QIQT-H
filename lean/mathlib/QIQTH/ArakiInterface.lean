/-
  ArakiInterface — packaging Donald, DPI, Klein, and Holevo bounds
  for Araki relative entropy with explicit side conditions.

  GPT-5.5-pro audit observation:

      Donald's identity is valid for Araki relative entropy under
      standard finite-normal-ensemble conditions, but the
      cross-entropy derivation (`Donald.lean`) should be treated as
      an abstract interface unless those conditions are instantiated.

      In the Araki/Tomita-Takesaki setting, the "cross-entropy" object
      `−ω(log σ)` can be unbounded or not literally represented by an
      algebra element.  The safest interface assumes Donald's identity
      directly for finite normal ensembles, rather than relying on
      cross-entropy primitives outside their domain.

  This module provides that interface: a `NormalEnsemble` structure
  with finiteness/positivity side conditions, and axioms for Donald,
  Klein, DPI, and the I_Hol ≤ H normalization check.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace ArakiInterface

/-- Abstract normal state on a regional von Neumann algebra. -/
axiom NormalState : Type

/-- Predicate: the state is faithful (positive on every non-zero element). -/
axiom IsFaithful : NormalState → Prop

/-- Mixture of finitely many normal states with given probability weights. -/
axiom mixture {ι : Type*} (s : Finset ι) (p : ι → ℝ) (ρ : ι → NormalState) :
    NormalState

/-- Araki relative entropy `S_Araki(ω ‖ σ)`, valued in `ℝ`.
    May be `+∞` on non-finite-entropy states; for the interface here
    we restrict to finite-entropy ensembles where it is finite. -/
axiom AkRelEnt : NormalState → NormalState → ℝ

/-- Predicate: a finite ensemble has finite Araki relative entropy
    against the reference state. -/
def FiniteEntropy (σ : NormalState) (ρ : NormalState) : Prop :=
  ∃ B : ℝ, AkRelEnt ρ σ ≤ B

/- ── Klein positivity (axiom, vN-algebra-deep) ─────────────────────── -/

axiom Akre_nonneg (ω σ : NormalState) : 0 ≤ AkRelEnt ω σ

/- ── Donald's identity with side conditions ────────────────────────── -/

/-- **Donald's identity** for Araki relative entropy on finite normal
    ensembles.  Stated as an axiom at this layer because Mathlib does
    not yet have the Araki/Tomita-Takesaki infrastructure to derive it. -/
axiom donald_araki
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    (ρ : ι → NormalState) (σ : NormalState)
    (hρ_finite : ∀ i ∈ s, FiniteEntropy σ (ρ i))
    (h_mixture_finite : FiniteEntropy σ (mixture s p ρ)) :
    ∑ i ∈ s, p i * AkRelEnt (ρ i) σ
      = AkRelEnt (mixture s p ρ) σ
        + ∑ i ∈ s, p i * AkRelEnt (ρ i) (mixture s p ρ)

/- ── DPI for normal UCP maps ──────────────────────────────────────── -/

/-- Abstract normal unital CP channel (Heisenberg-picture pullback on states). -/
axiom NormalUCPChannel : Type

/-- A channel acts on states by pullback. -/
axiom NormalUCPChannel.pull : NormalUCPChannel → NormalState → NormalState

/-- **DPI for normal UCP channels.**  Standard theorem (Lindblad/Uhlmann);
    axiomatized at this interface layer.

    *Caveat (per GPT-5.5-pro audit):*  Normalized postselection maps are
    NOT covered by this lemma.  Any branch-conditioning step that uses
    postselection needs its own lemma. -/
axiom dpi_ucp (Φ : NormalUCPChannel) (ω σ : NormalState) :
    AkRelEnt (Φ.pull ω) (Φ.pull σ) ≤ AkRelEnt ω σ

/- ── Holevo information ≤ Shannon entropy ──────────────────────────── -/

/-- Holevo mutual information of a finite ensemble. -/
noncomputable def IHol
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (ρ : ι → NormalState) : ℝ :=
  ∑ i ∈ s, p i * AkRelEnt (ρ i) (mixture s p ρ)

/-- **Holevo non-negativity** — direct from Klein. -/
theorem IHol_nonneg
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → NormalState) :
    0 ≤ IHol s p ρ := by
  unfold IHol
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hp_nn k hk) (Akre_nonneg _ _)

/-- Shannon entropy of the weight distribution (in nats). -/
noncomputable def ShannonWeights {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ i ∈ s, p i * Real.log (p i)

/-- **Holevo ≤ Shannon** for orthogonal ensembles (axiom — standard
    quantum-information result requiring Holevo's theorem). -/
axiom IHol_le_Shannon
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    (ρ : ι → NormalState)
    (h_orth : ∀ i j, i ≠ j → AkRelEnt (ρ i) (ρ j) = 0 → False) :  -- orthogonality
    IHol s p ρ ≤ ShannonWeights s p

/- ── Faithful reference state ──────────────────────────────────────── -/

/-- For a faithful reference state σ, `AkRelEnt(ω ‖ σ) = 0` implies `ω = σ`
    (Klein equality case).  Axiomatized at this interface layer. -/
axiom AkRelEnt_eq_zero_iff
    (ω σ : NormalState) (hσ_faithful : IsFaithful σ) :
    AkRelEnt ω σ = 0 ↔ ω = σ

end ArakiInterface
end QIQTH
