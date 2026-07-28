/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckGenericPoint — generic evaluation-point versions of the van-Vleck split pieces

The two landed van-Vleck second-derivative bricks are pinned at the ray parameter `s = 1`:

* `QIQTH.ExpMap.logdet_gtilde_ray_secondDeriv` (VanVleckLogDetSplit.lean): the additive split
  `d²/ds²[log det g̃(s•v)]|₁ = 2·LJ'' + Lg''`.
* `QIQTH.ExpMap.logJ_ray_secondDeriv_eq` (LogJSecondDerivRescale.lean): the rescaling relation
  `LJ'' = LB'' + n`.

To evaluate the van-Vleck `−Ric` radial ODE at an **interior** point `t ∈ (0,1)` (avoiding the
`s = 1` endpoint of the exp-flow variation) we need both at a GENERIC point `t`.  This file lands:

* `logdet_gtilde_ray_secondDeriv_at` — the additive split at a generic `t`
  `d²/ds²[log det g̃(s•v)]|_t = 2·LJ'' + Lg''` (the original proof does not use `1`
  specifically, so `1 → t` is a pure mechanical substitution).

* `logJ_ray_secondDeriv_eq_at` — the rescaling second-derivative at a generic `t > 0`.  Because the
  `−n·log s` term of the rescaling contributes `deriv²(−n·log s)|_t = −n·deriv(s⁻¹)|_t
  = −n·(−(t²)⁻¹) = n/t²`, the clean relation becomes
  `LJ'' = LB'' + n / t²`
  (recovering `+ n` at `t = 1`).  A small helper `hresc_of_pos_at` re-derives the rescaling germ
  `log J(s•v) =ᶠ[𝓝 t] log det(B s) − n·log s` at `𝓝 t` (copying `hresc_of_pos`'s
  `Matrix.det_smul` computation with `1 → t`, using `t > 0` for `Set.Ioi 0 ∈ 𝓝 t`).

## What this is and is NOT

This is the generic-evaluation-point RE-INDEXING of the two split bricks ONLY.  It does **NOT**
assemble the interior-point van-Vleck identity, does **NOT** discharge the Raychaudhuri/`−Ric`
source term, and is **NOT** the heat-kernel coefficient `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckLogDetSplit
import QIQTH.LogJSecondDerivRescale
import QIQTH.JacobiRescale
import QIQTH.JacobianDet

set_option maxHeartbeats 1200000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.JacobianDet QIQTH.JacobianRegularity
open Matrix

variable {n : ℕ}

/-- **The additive `log det g̃` split at a GENERIC evaluation point `t`.**  Identical to
    `logdet_gtilde_ray_secondDeriv` but with every `𝓝 1` replaced by `𝓝 t` and every
    evaluation `(deriv …) 1` replaced by `(deriv …) t`.  The original proof uses only
    `EventuallyEq.deriv_eq` plus the additive / const-mul derivative rules at the point, none of
    which depend on the specific value `1`, so this is a pure `1 → t` re-indexing. -/
theorem logdet_gtilde_ray_secondDeriv_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) {t : ℝ}
    (hsplit : (fun s : ℝ =>
        Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))
      =ᶠ[nhds t]
        (fun s => 2 * Real.log (expJacobianDet g gi hC p (s • v))
          + Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)))
    (hLJev : ∀ᶠ s in nhds t,
        DifferentiableAt ℝ (fun u : ℝ => Real.log (expJacobianDet g gi hC p (u • v))) s)
    (hLgev : ∀ᶠ s in nhds t,
        DifferentiableAt ℝ
          (fun u : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (u • v)) a b).det)) s)
    {LJ'' Lg'' : ℝ}
    (hLJ2 : HasDerivAt
        (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) LJ'' t)
    (hLg2 : HasDerivAt
        (deriv (fun s : ℝ =>
          Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) Lg'' t) :
    deriv (deriv (fun s : ℝ =>
        Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))) t
      = 2 * LJ'' + Lg'' := by
  -- Abbreviations for the two ray-pieces.
  set LJ : ℝ → ℝ := fun s => Real.log (expJacobianDet g gi hC p (s • v)) with hLJdef
  set Lg : ℝ → ℝ :=
    fun s => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det) with hLgdef
  -- First ray-derivative of the split's RHS, valid eventually near `t`.
  have hev : deriv (fun s => 2 * LJ s + Lg s)
      =ᶠ[nhds t] fun s => 2 * deriv LJ s + deriv Lg s := by
    filter_upwards [hLJev, hLgev] with s hLJs hLgs
    have h1 : HasDerivAt (fun s => 2 * LJ s + Lg s) (2 * deriv LJ s + deriv Lg s) s :=
      (hLJs.hasDerivAt.const_mul 2).add hLgs.hasDerivAt
    exact h1.deriv
  -- The LHS `deriv (deriv F) t` equals `deriv (deriv (2·LJ + Lg)) t` via the eventual split.
  rw [hsplit.deriv.deriv_eq, hev.deriv_eq]
  -- Second derivative of `2·(deriv LJ) + deriv Lg` at `t`.
  have h2 : HasDerivAt (fun s => 2 * deriv LJ s + deriv Lg s) (2 * LJ'' + Lg'') t :=
    (hLJ2.const_mul 2).add hLg2
  exact h2.deriv

/-- **The rescaling germ `log J(s•v) =ᶠ[𝓝 t] log det(B s) − n·log s` at a GENERIC `t > 0`.**
    Generic-point version of `QIQTH.JacobianRegularity.hresc_of_pos`, obtained by copying its
    `Matrix.det_smul` / `Real.log_mul` / `Real.log_pow` computation with `1 → t`; positivity of
    `s` near `t` comes from `Set.Ioi 0 ∈ 𝓝 t` (needing `t > 0`). -/
theorem hresc_of_pos_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) {t : ℝ} (ht : 0 < t)
    (hpos : ∀ᶠ s in nhds t, 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)) :
    (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))
      =ᶠ[nhds t]
    (fun s => Real.log (((fun r => (r : ℝ) • QIQTH.JacobianDet.expJacobianMat g gi hC p (r • v)) s).det)
               - (n : ℝ) * Real.log s) := by
  -- `s > 0` in a neighbourhood of `t` (from `Set.Ioi 0 ∈ 𝓝 t`, using `t > 0`).
  have hs_pos : ∀ᶠ s in nhds t, (0:ℝ) < s :=
    (isOpen_Ioi).eventually_mem (Set.mem_Ioi.mpr ht)
  filter_upwards [hpos, hs_pos] with s hJpos hspos
  have hs0 : (0:ℝ) < s := hspos
  -- Unfold `expJacobianDet = det (expJacobianMat …)` so both sides share the matrix determinant.
  simp only [QIQTH.JacobianDet.expJacobianDet] at hJpos ⊢
  -- `det (s • M) = s ^ (card (Fin n)) • det M = sⁿ · det M`, then split the log.
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.log_mul (pow_ne_zero n hs0.ne') hJpos.ne', Real.log_pow]
  ring

/-- **The rescaling second-derivative relation `LJ'' = LB'' + n/t²` at a GENERIC `t > 0`.**

Generic-evaluation-point version of `logJ_ray_secondDeriv_eq`.  Differentiating the rescaling
germ `log J(s•v) =ᶠ[𝓝 t] log det B(s) − n·log s` (`hresc_of_pos_at`, with
`B s = s • expJacobianMat g gi hC p (s • v)`) twice at `s = t` gives
```
  deriv²(log J∘ray) t  =  deriv²(log det B∘ray) t  +  n / t².
```
The `n/t²` (rather than `+ n`) is `deriv²(−n·log s)|_t = −n·deriv(s⁻¹)|_t = −n·(−(t²)⁻¹) = n/t²`;
it recovers `+ n` at `t = 1`.  All carried data are genuine analytic facts near `s = t`: `hpos`
(positivity of `J`), `hLBev` (eventual differentiability of `log det B∘ray`), and `hLJ2`/`hLB2`
(the two second derivatives as `HasDerivAt`s of the first derivatives at `t`).  NOT the `−2 Ric`
van-Vleck ODE, `B'' = −R̃ B`, or `a₁ = R/6`. -/
theorem logJ_ray_secondDeriv_eq_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) {t : ℝ} (ht : 0 < t)
    (hpos : ∀ᶠ s in nhds t, 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v))
    (hLBev : ∀ᶠ s in nhds t,
      DifferentiableAt ℝ (fun u : ℝ =>
        Real.log (((fun r : ℝ => r • QIQTH.JacobianDet.expJacobianMat g gi hC p (r • v)) u).det)) s)
    {LJ'' LB'' : ℝ}
    (hLJ2 : HasDerivAt (deriv (fun s : ℝ =>
        Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))) LJ'' t)
    (hLB2 : HasDerivAt (deriv (fun s : ℝ =>
        Real.log (((fun r : ℝ => r • QIQTH.JacobianDet.expJacobianMat g gi hC p (r • v)) s).det)))
        LB'' t) :
    LJ'' = LB'' + (n : ℝ) / t ^ 2 := by
  -- The rescaling germ `log J(s•v) =ᶠ[𝓝 t] log det B(s) − n·log s` at `𝓝 t`.
  have hresc := hresc_of_pos_at g gi hC p v ht hpos
  -- Fold the two ray-functions.
  set f : ℝ → ℝ := fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)) with hf_def
  set h : ℝ → ℝ := fun s =>
    Real.log (((fun r : ℝ => r • QIQTH.JacobianDet.expJacobianMat g gi hC p (r • v)) s).det) with hh_def
  -- `s > 0` near `t`.
  have hs_pos : ∀ᶠ s in nhds t, (0:ℝ) < s :=
    (isOpen_Ioi).eventually_mem (Set.mem_Ioi.mpr ht)
  -- FIRST derivative on `𝓝 t`: `deriv f =ᶠ deriv h − n·(·)⁻¹`.
  have hd1 : deriv f =ᶠ[nhds t] fun s => deriv h s - (n : ℝ) * s⁻¹ := by
    filter_upwards [hresc.eventually_nhds, hs_pos, hLBev] with s hres_s hspos hdiff_s
    show deriv f s = deriv h s - (n : ℝ) * s⁻¹
    -- Local germ equality ⇒ equal `deriv` at `s`.
    rw [Filter.EventuallyEq.deriv_eq hres_s]
    -- Compute `deriv (fun u => h u − n·log u) s = deriv h s − n·s⁻¹`.
    have hh_d : HasDerivAt h (deriv h s) s := hdiff_s.hasDerivAt
    have hlog : HasDerivAt (fun u : ℝ => Real.log u) s⁻¹ s :=
      Real.hasDerivAt_log (ne_of_gt hspos)
    have hnlog : HasDerivAt (fun u : ℝ => (n : ℝ) * Real.log u) ((n : ℝ) * s⁻¹) s :=
      hlog.const_mul (n : ℝ)
    exact (hh_d.sub hnlog).deriv
  -- SECOND derivative at `t`: transport `hLJ2` across `hd1`, then differentiate the RHS.
  have hLJ2' : HasDerivAt (fun s => deriv h s - (n : ℝ) * s⁻¹) LJ'' t :=
    hd1.hasDerivAt_iff.mp hLJ2
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t :=
    hasDerivAt_inv ht.ne'
  have hninv : HasDerivAt (fun s : ℝ => (n : ℝ) * s⁻¹) ((n : ℝ) * -(t ^ 2)⁻¹) t :=
    hinv.const_mul (n : ℝ)
  have hRHS : HasDerivAt (fun s => deriv h s - (n : ℝ) * s⁻¹)
      (LB'' - (n : ℝ) * -(t ^ 2)⁻¹) t := hLB2.sub hninv
  -- Uniqueness of the derivative fixes `LJ''`, then `−n·(−(t²)⁻¹) = n/t²`.
  have hEq : LJ'' = LB'' - (n : ℝ) * -(t ^ 2)⁻¹ := hLJ2'.unique hRHS
  rw [hEq]; ring

end QIQTH.ExpMap
