/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# P4-MICRO ⟹ the Einstein field equations (free field) — the entropy slots, filled by finite capacity

This wires **Route 2 (P4-MICRO)** into the machine-checked Jacobson chain `QiqtToGR.qiqt_bekenstein_gives_gr`.
That capstone takes the QIQT-H entropy content along each local null generator as four hypotheses —
the capacity **bound** `hbound : S ≤ η·A`, **saturation** `hsat : S 0 = η·A 0`, and relative-entropy positivity
`hDnn`/`hD0` — together with the **cited** thermal/geometry inputs (`hFlux` = Bisognano–Wichmann boost flux,
`hFocus` = Raychaudhuri) and the structural inputs; it then yields `a·T = G + Λ·g`.

`hbound_hsat_of_capacity_family` shows the **first two slots are exactly P4-MICRO's outputs**: given a smooth family
of finite regional capacities — for each horizon patch `(x,v)` and deformation parameter `t`, a finite microstate
type `R x v t` with a Born record law `p` whose Shannon entropy is `S x v t`, and whose log-capacity tracks the area,
`log N(x,v,t) = η·A(x,v,t)` — the proved `area_floor_of_microstate` gives `hbound` and `area_floor_saturates` gives
`hsat`.  `gr_from_p4micro` then plugs these into the capstone.

HONEST SCOPE (do not overstate).  "P4-MICRO ⟹ GR" is **FALSE as a standalone implication**:
* P4-MICRO fills **only** the entropy slots (`hbound`, `hsat`).  `hDnn`/`hD0` are the entanglement first law
  (Klein positivity, proven elsewhere); `hFlux` (Unruh/Clausius, irreducibly **modular** — Bisognano–Wichmann) is
  the **thermal** input a microstate *count* can never supply (a count fixes a max-entropy *number*, not a Gibbs
  weight / temperature); `hFocus`, `hreg`, `conserv` are geometry/conservation.  For the **free scalar field** the
  thermal side is independently discharged via BW (`Fock.OneParticleBW`), but it is not P4-MICRO's doing.
* The **capacity-tracks-area** family (`log N(t) = η·A(t)`) and the identification of the record entropy with the
  horizon `dS` are the **Gap-2 localization** content — carried here as explicit hypotheses, NOT derived.
* The area coefficient (`η = 1/4ℓ_P²`) is a **free real**: the `1/4` *ratio* is derived (`SakharovRatio`), the value
  of `G` is the carried UV datum, never assigned.  The capacity postulate is a *typeclass hypothesis*, not a Lean
  `axiom`.  The Type II dual-weight trace (Route 1) stays the labelled open frontier that would *derive* the
  holographic capacity law rather than postulate it.
-/
import QIQTH.QiqtToGR
import QIQTH.FQBoundMicro

namespace QIQTH.GRFromMicro

open QIQTH.EinsteinEOS QIQTH.Curvature QIQTH.QiqtToGR Filter Topology

/-- **The P4-MICRO entropy slots `hbound` ∧ `hsat`, produced from a finite-capacity family.**  For each horizon
    patch `(x,v)` and deformation `t`, suppose there is a finite microstate type `R x v t` with a Born record law
    `p x v t` (nonnegative, summing to `1`) whose Shannon entropy is `S x v t` (`hSeq`), whose log-capacity tracks
    the area `log N = η·A` (`hcap`), with the reference record (`t = 0`) maximally mixed (`hunif`) on a nonempty
    `R x v 0` (`hne`).  Then `area_floor_of_microstate` (per `t`) gives the capacity **bound** `S ≤ η·A`
    (`∀ᶠ` near `0`, in fact for all `t`) and `area_floor_saturates` gives the **saturation** `S 0 = η·A 0` — exactly
    the two QIQT-H entropy hypotheses of `qiqt_bekenstein_gives_gr`.  Axiom-free. -/
theorem hbound_hsat_of_capacity_family
    {g : Point 4 → Fin 4 → Fin 4 → ℝ} {η : ℝ}
    {S A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ}
    (R : Point 4 → (Fin 4 → ℝ) → ℝ → Type) [hfin : ∀ x v t, Fintype (R x v t)]
    (p : ∀ x v t, R x v t → ℝ)
    (hp : ∀ x v t i, 0 ≤ p x v t i) (hp1 : ∀ x v t, ∑ i, p x v t i = 1)
    (hSeq : ∀ x v t, S x v t = QIQTH.BranchLedger.Shannon Finset.univ (p x v t))
    (hcap : ∀ x v t, Real.log (Fintype.card (R x v t)) = η * A x v t)
    (hne : ∀ x v, Nonempty (R x v 0))
    (hunif : ∀ x v, p x v 0 = fun _ => (Fintype.card (R x v 0) : ℝ)⁻¹) :
    (∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, S x v t ≤ η * A x v t)
      ∧ (∀ x v, BL (g x) v = 0 → S x v 0 = η * A x v 0) := by
  refine ⟨fun x v _ => ?_, fun x v _ => ?_⟩
  · filter_upwards with t
    letI : QIQTH.HolographicCapacityBound (R x v t) (η * A x v t) := ⟨le_of_eq (hcap x v t)⟩
    rw [hSeq x v t]
    exact QIQTH.area_floor_of_microstate (p x v t) (hp x v t) (hp1 x v t)
  · haveI := hne x v
    letI : QIQTH.HolographicCapacityExact (R x v 0) (η * A x v 0) := ⟨hcap x v 0⟩
    rw [hSeq x v 0, hunif x v]
    exact QIQTH.area_floor_saturates

/-- **★★★ P4-MICRO ⟹ the Einstein field equations (free field), with the entropy slots filled by finite capacity.**
    `qiqt_bekenstein_gives_gr` with its `hbound`/`hsat` discharged by `hbound_hsat_of_capacity_family` from a
    finite-capacity family.  The remaining hypotheses are *exactly* the honest residual: `hDnn`/`hD0` (entanglement
    first law / Klein positivity), `hFlux` (Bisognano–Wichmann boost flux — the irreducibly **modular** thermal
    input, derived for the free field via `Fock.OneParticleBW`, never by counting), `hFocus` (Raychaudhuri), `hreg`,
    `conserv`, plus the structural metric/Lorentzian inputs.  Conclusion: `∃ Λ, a·T = G + Λ·g`.

    This makes "P4-MICRO closes the entropy slots; the thermal slot is Route-1/BW" a **checkable Lean dependency**
    rather than prose.  It is NOT "P4-MICRO ⟹ GR" — see the module header (GR-T1/GR-T2). -/
theorem gr_from_p4micro
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hT_symm : ∀ x a' b, T x a' b = T x b a')
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * gm k l * P x l j)
    (S KE A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd kd ad : Point 4 → (Fin 4 → ℝ) → ℝ)
    (hS : ∀ x v, BL (g x) v = 0 → HasDerivAt (S x v) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0)
    -- the P4-MICRO finite-capacity family supplying hbound + hsat:
    (R : Point 4 → (Fin 4 → ℝ) → ℝ → Type) [∀ x v t, Fintype (R x v t)]
    (p : ∀ x v t, R x v t → ℝ)
    (hp : ∀ x v t i, 0 ≤ p x v t i) (hp1 : ∀ x v t, ∑ i, p x v t i = 1)
    (hSeq : ∀ x v t, S x v t = QIQTH.BranchLedger.Shannon Finset.univ (p x v t))
    (hcap : ∀ x v t, Real.log (Fintype.card (R x v t)) = η * A x v t)
    (hne : ∀ x v, Nonempty (R x v 0))
    (hunif : ∀ x v, p x v 0 = fun _ => (Fintype.card (R x v 0) : ℝ)⁻¹)
    -- relative-entropy positivity (entanglement first law / Klein):
    (hDnn : ∀ x v, BL (g x) v = 0 → ∀ t, 0 ≤ KE x v t - S x v t)
    (hD0 : ∀ x v, BL (g x) v = 0 → KE x v 0 - S x v 0 = 0)
    -- CITED thermal/geometry residual (NOT from P4-MICRO):
    (hFlux : ∀ x v, BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * BL (T x) v)
    (hFocus : ∀ x v, BL (g x) v = 0 → ad x v = BL (fun i j => ricci g gi i j x) v)
    (hreg : ∀ f : Point 4 → ℝ,
        (∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b) →
        (∀ x ρ, PdiffAt f ρ x) ∧
          Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y))
    (conserv : ∀ x ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    ∃ Λ : ℝ, ∀ x μ ν, a * T x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν :=
  have hbh := hbound_hsat_of_capacity_family (g := g) (η := η) (S := S) (A := A)
    R p hp hp1 hSeq hcap hne hunif
  qiqt_bekenstein_gives_gr g gi hsymm hsymm_gi hinv hCg hCgi T η hbar a hbar0 heta ha hT_symm
    P Pinv hPP hPP' hcong S KE A sd kd ad hS hK hA hbh.1 hbh.2 hDnn hD0 hFlux hFocus hreg conserv

end QIQTH.GRFromMicro
