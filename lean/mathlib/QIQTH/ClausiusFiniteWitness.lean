/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# T3-1 Stage 1 — the Clausius package as a theorem of the finite QIQT entropy model

The free-field QIQT→GR capstone (`QiqtGrFreeField.lean`) takes four labelled thermodynamic premises on each
null generator — the capacity **bound** `S ≤ η·A`, **saturation** `S(0)=η·A(0)`, relative-entropy
**positivity** `0 ≤ KE−S`, and its **tightness** `KE(0)−S(0)=0` — which `differential_area_law_of_relEntropy`
turns into the modular relation `δS = η δA = δ⟨K⟩`.  This file proves those four are NOT independent physical
assumptions: for a finite record model with the holographic area-capacity identification `η·A = log|R|`, the
constructed entropy/heat/area functionals satisfy all four, via the axiom-free finite core
(`shannon_le_log_card`, `shannon_uniform_eq_log_card`, `KL_classical_nonneg`).

What stays labelled (see `T3-1_H2_CLAUSIUS_PLAN.md` §2–§5) is only the *dynamical* area-capacity postulate
`η·A(t) = log|R_t|` (the FQ `Q_R = A/4ℓ_P²` input, irreducible) and the realization derivatives — not the
entropy inequalities themselves.

Axiom-free.
-/
import QIQTH.RecordContract
import QIQTH.RelEntPositivity
import QIQTH.EntropyDeriv

namespace QIQTH.ClausiusFiniteWitness

open QIQTH.BranchLedger QIQTH.RecordContract QIQTH.RelEntPositivity

/-- **The Clausius package from the finite QIQT entropy model.**  Given a finite record set `R`, a
    deformation-dependent record law `p t` (a probability distribution for every `t`, uniform at the reference
    `t=0`), and the holographic area-capacity identification `η·Acap = log|R|`, the constructed functionals

      `Sf t := Shannon (p t)`,   `KE t := Sf t + KL (p t ‖ p 0)`,   `A t := Acap`

    satisfy the four thermodynamic premises of the QIQT→GR area-law derivation:
    capacity bound, saturation, relative-entropy positivity, and its tightness at the reference.  Each is a
    direct consequence of the axiom-free finite core (Gibbs/Jensen, uniform saturation, classical Klein). -/
theorem clausius_package_from_finite_model
    {R : Type*} [Fintype R] [Nonempty R]
    (η Acap : ℝ)
    (p : ℝ → R → ℝ)
    (hp_nn : ∀ t r, 0 ≤ p t r)
    (hp1 : ∀ t, ∑ r, p t r = 1)
    (hp0 : p 0 = (fun _ : R => (Fintype.card R : ℝ)⁻¹))
    (hcap : η * Acap = Real.log (Fintype.card R)) :
    -- hbound:
    (∀ᶠ t in nhds 0, Shannon Finset.univ (p t) ≤ η * Acap)
    -- hsat:
    ∧ (Shannon Finset.univ (p 0) = η * Acap)
    -- hDnn:
    ∧ (∀ t, 0 ≤ (Shannon Finset.univ (p t) + KL Finset.univ (p t) (p 0)) - Shannon Finset.univ (p t))
    -- hD0:
    ∧ ((Shannon Finset.univ (p 0) + KL Finset.univ (p 0) (p 0)) - Shannon Finset.univ (p 0) = 0) := by
  have hcardpos : 0 < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  have hp0pos : ∀ r, 0 < p 0 r := fun r => by rw [hp0]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- hbound: Shannon(p t) ≤ log|R| = η·Acap, for every t (a fortiori eventually).
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hcap]
    exact shannon_le_log_card (p t) (hp_nn t) (hp1 t)
  · -- hsat: at the uniform reference, Shannon saturates the capacity.
    rw [hcap, hp0]
    exact shannon_uniform_eq_log_card
  · -- hDnn: KE − Sf = KL(p t ‖ p 0) ≥ 0 (classical Klein; reference is strictly positive).
    intro t
    have hKL : 0 ≤ KL Finset.univ (p t) (p 0) :=
      KL_classical_nonneg Finset.univ (p t) (p 0)
        (fun i _ => hp_nn t i) (fun i _ => hp0pos i) (hp1 t) (hp1 0)
    linarith
  · -- hD0: KL(p 0 ‖ p 0) = 0 termwise (log(p/p)=log 1=0).
    have hKL0 : KL Finset.univ (p 0) (p 0) = 0 := by
      unfold KL
      refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [div_self (hp0pos r).ne', Real.log_one, mul_zero]
    rw [hKL0]; ring

/-- **Stage A3 — the derivative package from the finite QIQT entropy model.**  Given the same finite record
    law `p t` (now assumed *differentiable* at the reference: per-component `HasDerivAt`, strictly-positive
    reference, probability for every `t`), the two HasDerivAt facts the GR capstones assume — `hS` (the
    Shannon entropy `Sf t = Shannon (p t)` has a derivative at `0`) and `hK` (the heat functional
    `Sf t + KL (p t ‖ p 0)` has a derivative at `0`) — are **theorems**, and they hold with the **same**
    rate: the relative-entropy correction is flat at the equilibrium reference (`EntropyDeriv.KE_hasDerivAt`).

    So the capstone's two derivative premises are not independent: `hK` follows from `hS` once the heat rate
    is identified with the entropy rate, and that identification is exactly "KL contributes nothing at
    equilibrium" — not a separate physical input.  (What stays labelled is only the *value* of the rate as a
    stress flux `2π/ℏ · T_kk`, i.e. the localization/calibration `hTkk`, and the FQ capacity `hcap` — the
    irreducible floor; this lemma touches neither.)  Axiom-free. -/
theorem clausius_deriv_package_from_finite_model
    {R : Type*} [Fintype R] [Nonempty R]
    (p : ℝ → R → ℝ) (pderiv : R → ℝ)
    (hpd : ∀ r, HasDerivAt (fun t => p t r) (pderiv r) 0)
    (hp0pos : ∀ r, 0 < p 0 r)
    (hp1 : ∀ t, ∑ r, p t r = 1) :
    -- hS: the Shannon entropy has a derivative at the reference …
    HasDerivAt (fun t => Shannon Finset.univ (p t))
        (-∑ r, (Real.log (p 0 r) + 1) * pderiv r) 0
    -- … and hK: the heat functional has the SAME derivative (KL flat at equilibrium).
    ∧ HasDerivAt (fun t => Shannon Finset.univ (p t) + KL Finset.univ (p t) (p 0))
        (-∑ r, (Real.log (p 0 r) + 1) * pderiv r) 0 :=
  ⟨QIQTH.EntropyDeriv.shannon_hasDerivAt Finset.univ p pderiv
      (fun r _ => hpd r) (fun r _ => hp0pos r),
   QIQTH.EntropyDeriv.KE_hasDerivAt Finset.univ p pderiv
      (fun r _ => hpd r) (fun r _ => hp0pos r) (fun t => hp1 t)⟩

end QIQTH.ClausiusFiniteWitness
