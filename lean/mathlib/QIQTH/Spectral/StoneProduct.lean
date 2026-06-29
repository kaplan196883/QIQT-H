/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The product of two commuting C₀ unitary groups — the SUM of commuting self-adjoint generators is self-adjoint

The crossed-product / P4-wall **Increment 1c** needs the JLMS *dressed* modular Hamiltonian
`K̃ = K_bulk + A_edge·(1/4ℓ_P²)` to be a genuine self-adjoint operator.  `K = modularGen` and `X = A_edge`
are each self-adjoint (`ModularGenerator.modularGen_isSelfAdjoint`, `CrossedProductGenerator.clockEnergy_is
SelfAdjoint`, via the now-built `Garding.stoneGen_isSelfAdjoint`), but the **sum of two unbounded self-adjoint
operators is not automatically self-adjoint** — it needs them to *strongly commute*.

This module supplies exactly that, in one-parameter-group form: if `A_t = e^{itK}` and `B_t = e^{itX}` are
strongly-continuous unitary groups that **commute** (`A_s B_t = B_t A_s`), then their pointwise product
`V_t = A_t B_t` is again a strongly-continuous unitary group (`V_t = e^{it(K+X)}`), so its Stone generator —
the **sum `K + X`** — is **self-adjoint** by the general `stoneGen_isSelfAdjoint`.  No new analytic input: the
five C₀-unitary-group hypotheses for `V` follow elementarily from those of `A`, `B`, and commutativity (the
group law uses commutativity; strong continuity is the diagonal `t ↦ A_t(B_t y)`, controlled by `A_t`
contractive + both groups strongly continuous).

So the dressed generator `K̃` is self-adjoint **as soon as the bulk modular flow and the clock flow commute**
(they act on different tensor factors of `L²(ℝ; H)`, so they do) — Increment 1c's operator-theoretic core,
axiom-free.  Wiring the specific `A_edge`/`K_bulk` flows into this is the crossed-product follow-on.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
-/
import QIQTH.Spectral.Garding

namespace QIQTH.Spectral

open ContinuousLinearMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **★ The product of two commuting C₀ unitary groups is a C₀ unitary group whose Stone generator (the SUM of
the two generators) is self-adjoint.**  For `A_t = e^{itK}`, `B_t = e^{itX}` strongly commuting unitary groups,
`V_t = A_t B_t = e^{it(K+X)}` and `stoneGen V = K + X` is self-adjoint.  The operator-theoretic core of the JLMS
dressed modular Hamiltonian `K̃ = K_bulk + A_edge·(1/4ℓ_P²)` (crossed-product / P4-wall Increment 1c): the sum of
two *commuting* unbounded self-adjoint operators is self-adjoint. -/
theorem stoneGen_prod_isSelfAdjoint
    (A B : ℝ → (H →L[ℂ] H))
    (hAgrp : ∀ s t, A (s + t) = A s ∘L A t) (hA0 : A 0 = 1)
    (hAinner : ∀ t a b, (inner ℂ (A t a) (A t b) : ℂ) = inner ℂ a b)
    (hAbd : ∀ (t : ℝ) (y : H), ‖A t y‖ ≤ ‖y‖) (hASC : ∀ y : H, Continuous (fun t => A t y))
    (hBgrp : ∀ s t, B (s + t) = B s ∘L B t) (hB0 : B 0 = 1)
    (hBinner : ∀ t a b, (inner ℂ (B t a) (B t b) : ℂ) = inner ℂ a b)
    (hBbd : ∀ (t : ℝ) (y : H), ‖B t y‖ ≤ ‖y‖) (hBSC : ∀ y : H, Continuous (fun t => B t y))
    (hcomm : ∀ s t, A s ∘L B t = B t ∘L A s) :
    IsSelfAdjoint (stoneGen (fun t => A t ∘L B t)) := by
  refine stoneGen_isSelfAdjoint (fun t => A t ∘L B t) ?_ ?_ ?_ ?_ ?_
  · -- group law `V (s+t) = V s ∘L V t`, using commutativity `A t (B s w) = B s (A t w)`
    intro s t
    apply ContinuousLinearMap.ext; intro y
    have hc : A t (B s (B t y)) = B s (A t (B t y)) :=
      ContinuousLinearMap.ext_iff.mp (hcomm t s) (B t y)
    simp only [ContinuousLinearMap.comp_apply, hAgrp, hBgrp]
    rw [hc]
  · -- `V 0 = 1`
    apply ContinuousLinearMap.ext; intro y
    simp only [ContinuousLinearMap.comp_apply, hA0, hB0, ContinuousLinearMap.one_apply]
  · -- inner-product preservation (`V_t` unitary): product of two isometries
    intro t a b
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hAinner, hBinner]
  · -- contraction `‖V_t y‖ ≤ ‖y‖`
    intro t y
    rw [ContinuousLinearMap.comp_apply]
    exact le_trans (hAbd t (B t y)) (hBbd t y)
  · -- strong continuity of the diagonal `t ↦ A_t (B_t y)`
    intro y
    rw [continuous_iff_continuousAt]; intro t₀
    -- bound: ‖V_t y − V_{t₀} y‖ ≤ ‖B_t y − B_{t₀} y‖ + ‖A_t(B_{t₀}y) − A_{t₀}(B_{t₀}y)‖
    have hbnd : ∀ t, ‖(A t ∘L B t) y - (A t₀ ∘L B t₀) y‖
        ≤ ‖B t y - B t₀ y‖ + ‖A t (B t₀ y) - A t₀ (B t₀ y)‖ := by
      intro t
      simp only [ContinuousLinearMap.comp_apply]
      calc ‖A t (B t y) - A t₀ (B t₀ y)‖
          = ‖(A t (B t y) - A t (B t₀ y)) + (A t (B t₀ y) - A t₀ (B t₀ y))‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖A t (B t y) - A t (B t₀ y)‖ + ‖A t (B t₀ y) - A t₀ (B t₀ y)‖ := norm_add_le _ _
        _ = ‖A t (B t y - B t₀ y)‖ + ‖A t (B t₀ y) - A t₀ (B t₀ y)‖ := by rw [map_sub]
        _ ≤ ‖B t y - B t₀ y‖ + ‖A t (B t₀ y) - A t₀ (B t₀ y)‖ := by
            gcongr; exact hAbd t _
    -- each summand → 0 at t₀
    have hg1 : Tendsto (fun t => ‖B t y - B t₀ y‖) (𝓝 t₀) (𝓝 0) := by
      have hc : Tendsto (fun t => B t y) (𝓝 t₀) (𝓝 (B t₀ y)) := (hBSC y).continuousAt
      have h0 : Tendsto (fun t => B t y - B t₀ y) (𝓝 t₀) (𝓝 0) := by
        simpa using hc.sub_const (B t₀ y)
      have hn := h0.norm
      rwa [norm_zero] at hn
    have hg2 : Tendsto (fun t => ‖A t (B t₀ y) - A t₀ (B t₀ y)‖) (𝓝 t₀) (𝓝 0) := by
      have hc : Tendsto (fun t => A t (B t₀ y)) (𝓝 t₀) (𝓝 (A t₀ (B t₀ y))) :=
        (hASC (B t₀ y)).continuousAt
      have h0 : Tendsto (fun t => A t (B t₀ y) - A t₀ (B t₀ y)) (𝓝 t₀) (𝓝 0) := by
        simpa using hc.sub_const (A t₀ (B t₀ y))
      have hn := h0.norm
      rwa [norm_zero] at hn
    have hsum : Tendsto (fun t => ‖B t y - B t₀ y‖ + ‖A t (B t₀ y) - A t₀ (B t₀ y)‖)
        (𝓝 t₀) (𝓝 0) := by simpa using hg1.add hg2
    -- squeeze: ‖V_t y − V_{t₀} y‖ → 0, hence ContinuousAt
    have hdiff : Tendsto (fun t => (A t ∘L B t) y - (A t₀ ∘L B t₀) y) (𝓝 t₀) (𝓝 0) :=
      squeeze_zero_norm hbnd hsum
    have := hdiff.add (tendsto_const_nhds (x := (A t₀ ∘L B t₀) y))
    simpa using this

/-- **★ Strong-family interchange:** if a *contraction* family `A_t` (`‖A_t y‖ ≤ ‖y‖`) is strongly continuous
with `A_0 = 1`, and `w_t → w₀` along a filter `l` that tends to `0` (`l ≤ 𝓝 0`), then `A_t (w_t) → w₀`.  The
ε/2 heart of one-parameter semigroup calculus — `‖A_t w_t − w₀‖ ≤ ‖w_t − w₀‖ + ‖A_t w₀ − w₀‖` — used to
differentiate a *product* of commuting flows `t ↦ A_t (B_t ξ)` (the JLMS generator-sum
`stoneGen(Δ̂^{i·} ∘ λ_·) = K_bulk + A_edge`, P4-wall Phase 6.2): the cross term `A_t·((B_t ξ − ξ)/t)` has limit
`1·(d/dt B_t ξ)` precisely by this lemma. -/
theorem tendsto_strongFamily_apply {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    (A : ℝ → (H →L[ℂ] H)) (hA0 : A 0 = 1)
    (hAbd : ∀ (t : ℝ) (y : H), ‖A t y‖ ≤ ‖y‖) (hAcont : ∀ y : H, Continuous fun t => A t y)
    {w : ℝ → H} {w₀ : H} (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun t => A t (w t)) l (𝓝 w₀) := by
  have hbound : ∀ t, ‖A t (w t) - w₀‖ ≤ ‖w t - w₀‖ + ‖A t w₀ - w₀‖ := by
    intro t
    calc ‖A t (w t) - w₀‖
        = ‖(A t (w t) - A t w₀) + (A t w₀ - w₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖A t (w t) - A t w₀‖ + ‖A t w₀ - w₀‖ := norm_add_le _ _
      _ = ‖A t (w t - w₀)‖ + ‖A t w₀ - w₀‖ := by rw [map_sub]
      _ ≤ ‖w t - w₀‖ + ‖A t w₀ - w₀‖ := by gcongr; exact hAbd t _
  have hg1 : Tendsto (fun t => ‖w t - w₀‖) l (𝓝 0) := by
    have h0 : Tendsto (fun t => w t - w₀) l (𝓝 0) := by simpa using hw.sub_const w₀
    have hn := h0.norm
    rwa [norm_zero] at hn
  have hg2 : Tendsto (fun t => ‖A t w₀ - w₀‖) l (𝓝 0) := by
    have hc : Tendsto (fun t => A t w₀) l (𝓝 w₀) := by
      have hc0 : Tendsto (fun t => A t w₀) (𝓝 0) (𝓝 w₀) := by
        have h := (hAcont w₀).tendsto 0
        simp only [hA0, ContinuousLinearMap.one_apply] at h
        exact h
      exact hc0.mono_left hl
    have h0 : Tendsto (fun t => A t w₀ - w₀) l (𝓝 0) := by simpa using hc.sub_const w₀
    have hn := h0.norm
    rwa [norm_zero] at hn
  have hsum : Tendsto (fun t => ‖w t - w₀‖ + ‖A t w₀ - w₀‖) l (𝓝 0) := by simpa using hg1.add hg2
  have hdiff : Tendsto (fun t => A t (w t) - w₀) l (𝓝 0) := squeeze_zero_norm hbound hsum
  simpa using hdiff.add (tendsto_const_nhds (x := w₀))

end QIQTH.Spectral
