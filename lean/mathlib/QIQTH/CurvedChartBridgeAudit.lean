/-
  CurvedChartBridgeAudit — the CURVED regression fixture that catches BOTH center-identity defects of
  the geodesic-pullback bridge `hpull` (carried by `RadialGaugeInterface` /
  `CurvedCenterIdentities.curved_centerIdentities_of_gaussPullback` and asserted by
  `AmpGeometryBundle.HjetsShape`), the curved companion of the FLAT `FlatChartBridgeAudit` (J4-978).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY / SCOPE FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, proves NOTHING new about `R/6`, and
  DISCHARGES NEITHER `hpull` NOR any member of `{hDuhamel, hDConv, hCConv}`.  It is a *regression /
  countermodel* audit: it converts a sympy/ODE finding (the genuine second-jet radial contraction of a
  geodesic inverse chart is a NONZERO Riemann-curvature term) into a machine-checked Lean fact, using
  an EXPLICIT curved-jet surrogate whose jets are GROUNDED as genuine derivatives.

  ## WHY A CURVED FIXTURE IS NEEDED (the gap J4-978 could not test).
  `FlatChartBridgeAudit` (J4-978) refuted the mis-SIGNED `hpullVP` (`= zᵢ`, true `= −zᵢ`) but its own
  header notes it CANNOT test the `VQ` leg: the flat metric is constant and the flat inverse chart is
  affine, so the second jet `Q = 0` and the `VQ` leg degenerates to `0 = 0`.  The `VQ` defect only
  appears with genuine CURVATURE, where the chart is NOT affine.  This file supplies exactly that.

  ## THE SETUP (matches the geodesic inverse chart to the order the center identities see).
  For the constant-curvature RNC witness `g^K = curvedRNCMetric κ`, the genuine geodesic inverse chart
  `W_z = exp_z⁻¹` obeys (numerically to 1e-3, ODE-integrated, n = 2, 3, several κ < 0, pure O(‖z‖²)):
      `∑ₖ W_z(0)ₖ·Qₖ = (2κ/3)(z_i² − ‖z‖²) + O(‖z‖⁴)   =   −(2/3)·R_{ikil}zᵏzˡ + O(‖z‖⁴)   ≠ 0`,
  where `Q_k = ∂²ᵢ W_z(x)_k|₀ = (D²W_z(0)[eᵢ,eᵢ])_k`.  (Convention: `R_{ikjl}(0)=κ(δ_{ij}δ_{kl}−δ_{il}δ_{kj})`
  for this metric; the leading term is `−(2/3)R_{ikil}zᵏzˡ`.)  So the banked center identity `hVQ = 0`
  is GEOMETRICALLY FALSE at general base `z`, not merely unproven — the true value is the very Riemann
  contraction `a₁ = R/6` is built from.

  This file realizes the leading behaviour EXACTLY with the explicit polynomial surrogate
      `Ŵ_z(x) = (x − z) + (κ/3)·(‖x−z‖²·z − ⟨z, x−z⟩·(x−z))`,
  which satisfies `Ŵ_z(0) = −z`, `⟨z, D Ŵ_z(0) eᵢ⟩ = zᵢ` (the CORRECTED first leg), and
  `⟨Ŵ_z(0), D²Ŵ_z(0)[eᵢ,eᵢ]⟩ = (2κ/3)(zᵢ² − ‖z‖²)` — its jets GROUNDED as genuine `HasDerivAt`
  slice-derivatives, in the exact `Function.update`-slice shape of `HjetsShape`'s `P`/`Q`.

  ## WHAT LANDS (all machine-checked, grounded jets, non-vacuous).
    * `surrW_center` — `Ŵ_z(0) = −z`.
    * `surrP_hasDerivAt` / `surrQ_hasDerivAt` — the closed-form first/second jets `surrP`/`surrQ` ARE the
      genuine `update`-slice derivatives (grounding = non-vacuity).
    * `surr_firstLeg_corrected` — `∑ₖ zₖ·(D Ŵ(0)eᵢ)ₖ = zᵢ` (the corrected first leg holds EXACTLY).
    * `surr_hVP_value` — `∑ₖ Ŵ(0)ₖ·(D Ŵ(0)eᵢ)ₖ = −zᵢ` (the genuine `hVP` value; banked wants `+zᵢ`).
    * `surr_hVQ_value` — `∑ₖ Ŵ(0)ₖ·Qₖ = (2κ/3)(zᵢ² − ‖z‖²)` (the genuine `hVQ` value; banked wants `0`).
    * `curved_hVP_fails` — ★ the banked `hVP` conclusion (`= zᵢ`) is REFUTED at `n = 2`, `z = 1`, `i = 0`,
      `κ = −3`: LHS `= −1 ≠ +1`.
    * `curved_hVQ_fails` — ★★ the banked `hVQ` conclusion (`= 0`) is REFUTED at the SAME instance:
      LHS `= 2 ≠ 0`.  This is the curvature defect flat models cannot see.

  ## PRECISE STATUS.  Establishes as a machine-checked fact that the banked center-identity triple
  `hVP`/`hVQ` is mis-STATED for a genuinely-curved (`κ ≠ 0`) chart — `hVP` mis-signed, `hVQ` mis-valued
  (nonzero Riemann contraction).  It does NOT identify the surrogate with the opaque
  `uniformInverseChart` (that is blocker J3), does NOT prove the corrected bridge in general, and does
  NOT touch `{hDuhamel, hDConv, hCConv}`.  ⚠ a₁ = R/6 remains STRICTLY CONDITIONAL.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.Curvature

open Finset
open QIQTH.Curvature
open scoped BigOperators

namespace QIQTH.CurvedChartBridgeAudit

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the explicit curved-jet surrogate chart and its closed-form jets.
    ############################################################################### -/

/-- **The explicit curved-jet surrogate inverse chart**
    `Ŵ_z(x) = (x − z) + (K/3)·(z·‖x−z‖² − ⟨z, x−z⟩·(x−z))` (componentwise).  It reproduces the geodesic
    inverse chart of `curvedRNCMetric K` to the order the center identities see: `Ŵ_z(0) = −z`, correct
    first leg, and a NONZERO second-jet radial contraction. -/
noncomputable def surrW (K : ℝ) (z : Point n) : Point n → Point n :=
  fun x k => (x k - z k)
    + (K / 3) * ((z k) * (∑ m, (x m - z m) ^ 2)
        - (∑ m, z m * (x m - z m)) * (x k - z k))

/-- **The closed-form first jet** `surrP = ∂ᵢ Ŵ_z` (the `update`-slice derivative value). -/
noncomputable def surrP (K : ℝ) (z : Point n) (i : Fin n) : Point n → Fin n → ℝ :=
  fun x k => (if k = i then (1 : ℝ) else 0)
    + (K / 3) * ((z k) * (2 * (x i - z i))
        - (z i * (x k - z k) + (∑ m, z m * (x m - z m)) * (if k = i then (1 : ℝ) else 0)))

/-- **The closed-form second jet** `surrQ = ∂ᵢ² Ŵ_z` at `0` (the `update`-slice derivative of `surrP`). -/
noncomputable def surrQ (K : ℝ) (z : Point n) (i : Fin n) : Fin n → ℝ :=
  fun k => (2 * K / 3) * (z k - z i * (if k = i then (1 : ℝ) else 0))

/-! ###############################################################################
    ### §2 — chart value at the origin: `Ŵ_z(0) = −z`.
    ############################################################################### -/

/-- **Chart value at the ambient origin**: `Ŵ_z(0)ₖ = −zₖ` (the curvature quadratic cancels). -/
theorem surrW_center (K : ℝ) (z : Point n) (k : Fin n) : surrW K z (0 : Point n) k = - z k := by
  simp only [surrW]
  have e1 : (∑ m, ((0 : Point n) m - z m) ^ 2) = ∑ m, z m * z m := by
    refine Finset.sum_congr rfl (fun m _ => ?_); simp only [Pi.zero_apply]; ring
  have e2 : (∑ m, z m * ((0 : Point n) m - z m)) = - ∑ m, z m * z m := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [Pi.zero_apply]; ring
  rw [e1, e2]
  simp only [Pi.zero_apply, zero_sub]; ring

/-! ###############################################################################
    ### §3 — grounding: the closed-form jets ARE genuine `update`-slice derivatives.
    ############################################################################### -/

/-- **First-jet grounding.**  For every base `x` and component `k`, `surrP K z i x k` is the genuine
    derivative of the `i`-slice `s ↦ Ŵ_z(update x i s)ₖ` at `s = xᵢ` — the exact `HjetsShape` shape. -/
theorem surrP_hasDerivAt (K : ℝ) (z : Point n) (i : Fin n) (x : Point n) (k : Fin n) :
    HasDerivAt (fun s => surrW K z (Function.update x i s) k) (surrP K z i x k) (x i) := by
  -- basic slice derivatives
  have h_dk : HasDerivAt (fun s => (Function.update x i s) k - z k)
      (if k = i then (1 : ℝ) else 0) (x i) := by
    rcases eq_or_ne k i with hk | hk
    · subst hk
      simp only [Function.update_self, if_pos rfl]
      simpa using (hasDerivAt_id (x k)).sub_const (z k)
    · have hfun : (fun s => (Function.update x i s) k - z k) = fun _ => x k - z k := by
        funext s; rw [Function.update_of_ne hk]
      rw [hfun, if_neg hk]; exact hasDerivAt_const (x i) (x k - z k)
  have h_S2 : HasDerivAt (fun s => ∑ m, ((Function.update x i s) m - z m) ^ 2)
      (2 * (x i - z i)) (x i) := by
    have hterm : ∀ m ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun s => ((Function.update x i s) m - z m) ^ 2)
          (if m = i then 2 * (x i - z i) else 0) (x i) := by
      intro m _
      rcases eq_or_ne m i with hm | hm
      · subst hm
        simp only [Function.update_self, if_pos rfl]
        simpa using (((hasDerivAt_id (x m)).sub_const (z m)).pow 2)
      · have hfun : (fun s => ((Function.update x i s) m - z m) ^ 2) = fun _ => (x m - z m) ^ 2 := by
          funext s; rw [Function.update_of_ne hm]
        rw [hfun, if_neg hm]; exact hasDerivAt_const (x i) ((x m - z m) ^ 2)
    have hsum := HasDerivAt.sum hterm
    have hval : (∑ m, if m = i then 2 * (x i - z i) else 0) = 2 * (x i - z i) := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
    rw [hval] at hsum
    rw [← Finset.sum_fn]
    exact hsum
  have h_S1 : HasDerivAt (fun s => ∑ m, z m * ((Function.update x i s) m - z m)) (z i) (x i) := by
    have hterm : ∀ m ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun s => z m * ((Function.update x i s) m - z m))
          (if m = i then z i else 0) (x i) := by
      intro m _
      rcases eq_or_ne m i with hm | hm
      · subst hm
        simp only [Function.update_self, if_pos rfl]
        simpa using (((hasDerivAt_id (x m)).sub_const (z m)).const_mul (z m))
      · have hfun : (fun s => z m * ((Function.update x i s) m - z m))
            = fun _ => z m * (x m - z m) := by
          funext s; rw [Function.update_of_ne hm]
        rw [hfun, if_neg hm]; exact hasDerivAt_const (x i) (z m * (x m - z m))
    have hsum := HasDerivAt.sum hterm
    have hval : (∑ m, if m = i then z i else 0) = z i := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
    rw [hval] at hsum
    rw [← Finset.sum_fn]
    exact hsum
  -- product S1 * dk
  have hprod : HasDerivAt
      (fun s => (∑ m, z m * ((Function.update x i s) m - z m)) * ((Function.update x i s) k - z k))
      (z i * (x k - z k) + (∑ m, z m * (x m - z m)) * (if k = i then (1 : ℝ) else 0)) (x i) := by
    have hmul := h_S1.mul h_dk
    simpa [Function.update_eq_self] using hmul
  -- inner bracket
  have hb : HasDerivAt
      (fun s => (z k) * (∑ m, ((Function.update x i s) m - z m) ^ 2)
        - (∑ m, z m * ((Function.update x i s) m - z m)) * ((Function.update x i s) k - z k))
      ((z k) * (2 * (x i - z i))
        - (z i * (x k - z k) + (∑ m, z m * (x m - z m)) * (if k = i then (1 : ℝ) else 0))) (x i) :=
    (h_S2.const_mul (z k)).sub hprod
  -- assemble
  have hfull := h_dk.add (hb.const_mul (K / 3))
  simpa only [surrW, surrP] using hfull

/-- **Second-jet grounding.**  `surrQ K z i k` is the genuine derivative of the `i`-slice
    `s ↦ (surrP K z i (update 0 i s))ₖ` at `s = 0` — the exact `HjetsShape` second-jet shape. -/
theorem surrQ_hasDerivAt (K : ℝ) (z : Point n) (i : Fin n) (k : Fin n) :
    HasDerivAt (fun s => surrP K z i (Function.update (0 : Point n) i s) k) (surrQ K z i k)
      ((0 : Point n) i) := by
  have hyi : HasDerivAt (fun s => (Function.update (0 : Point n) i s) i - z i) (1 : ℝ)
      ((0 : Point n) i) := by
    simp only [Function.update_self]
    simpa using (hasDerivAt_id ((0 : Point n) i)).sub_const (z i)
  have hyk : HasDerivAt (fun s => (Function.update (0 : Point n) i s) k - z k)
      (if k = i then (1 : ℝ) else 0) ((0 : Point n) i) := by
    rcases eq_or_ne k i with hk | hk
    · subst hk
      simp only [Function.update_self, if_pos rfl]
      simpa using (hasDerivAt_id ((0 : Point n) k)).sub_const (z k)
    · have hfun : (fun s => (Function.update (0 : Point n) i s) k - z k)
          = fun _ => (0 : Point n) k - z k := by
        funext s; rw [Function.update_of_ne hk]
      rw [hfun, if_neg hk]; exact hasDerivAt_const _ _
  have hSsum : HasDerivAt (fun s => ∑ m, z m * ((Function.update (0 : Point n) i s) m - z m))
      (z i) ((0 : Point n) i) := by
    have hterm : ∀ m ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun s => z m * ((Function.update (0 : Point n) i s) m - z m))
          (if m = i then z i else 0) ((0 : Point n) i) := by
      intro m _
      rcases eq_or_ne m i with hm | hm
      · subst hm
        simp only [Function.update_self, if_pos rfl]
        simpa using (((hasDerivAt_id ((0 : Point n) m)).sub_const (z m)).const_mul (z m))
      · have hfun : (fun s => z m * ((Function.update (0 : Point n) i s) m - z m))
            = fun _ => z m * ((0 : Point n) m - z m) := by
          funext s; rw [Function.update_of_ne hm]
        rw [hfun, if_neg hm]; exact hasDerivAt_const _ _
    have hsum := HasDerivAt.sum hterm
    have hval : (∑ m, if m = i then z i else 0) = z i := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
    rw [hval] at hsum
    rw [← Finset.sum_fn]
    exact hsum
  -- assemble surrP slice = const + (K/3)*( z k*(2*yi) - ( z i*yk + Ssum*(if..) ) )
  have ht2 : HasDerivAt (fun s => (z k) * (2 * ((Function.update (0 : Point n) i s) i - z i)))
      ((z k) * (2 * 1)) ((0 : Point n) i) := (hyi.const_mul 2).const_mul (z k)
  have ht3a : HasDerivAt (fun s => z i * ((Function.update (0 : Point n) i s) k - z k))
      (z i * (if k = i then (1 : ℝ) else 0)) ((0 : Point n) i) := hyk.const_mul (z i)
  have ht3b : HasDerivAt
      (fun s => (∑ m, z m * ((Function.update (0 : Point n) i s) m - z m)) * (if k = i then (1 : ℝ) else 0))
      (z i * (if k = i then (1 : ℝ) else 0)) ((0 : Point n) i) := by
    simpa using hSsum.mul_const (if k = i then (1 : ℝ) else 0)
  have hinner := ht2.sub (ht3a.add ht3b)
  have hconst : HasDerivAt (fun _ : ℝ => (if k = i then (1 : ℝ) else 0)) 0 ((0 : Point n) i) :=
    hasDerivAt_const _ _
  have hfull := hconst.add (hinner.const_mul (K / 3))
  have hval : (0 : ℝ) + (K / 3) * ((z k) * (2 * 1)
      - (z i * (if k = i then (1 : ℝ) else 0) + z i * (if k = i then (1 : ℝ) else 0)))
      = surrQ K z i k := by
    simp only [surrQ]; ring
  rw [← hval]
  simpa only [surrP] using hfull

/-! ###############################################################################
    ### §4 — the closed-form first jet at `0`, and the three center-identity contractions.
    ############################################################################### -/

/-- Closed form of the first jet at the origin:
    `surrP K z i 0 k = δ_{ki} + (K/3)·(−zᵢ zₖ + (∑ z²)·δ_{ki})`. -/
theorem surrP_zero (K : ℝ) (z : Point n) (i k : Fin n) :
    surrP K z i (0 : Point n) k
      = (if k = i then (1 : ℝ) else 0)
        + (K / 3) * (- (z i * z k) + (∑ m, z m * z m) * (if k = i then (1 : ℝ) else 0)) := by
  simp only [surrP, Pi.zero_apply, zero_sub]
  have e1 : (∑ m, z m * -z m) = - ∑ m, z m * z m := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun m _ => ?_); ring
  rw [e1]; ring

/-- **★ The CORRECTED first leg holds EXACTLY**: `∑ₖ zₖ·(D Ŵ(0)eᵢ)ₖ = zᵢ`.  (This is the J4-995
    identity `Aᵀz = z`, realized by the explicit surrogate.) -/
theorem surr_firstLeg_corrected (K : ℝ) (z : Point n) (i : Fin n) :
    (∑ k, z k * surrP K z i (0 : Point n) k) = z i := by
  simp only [surrP_zero]
  have key : ∀ k, z k * ((if k = i then (1 : ℝ) else 0)
      + (K / 3) * (- (z i * z k) + (∑ m, z m * z m) * (if k = i then (1 : ℝ) else 0)))
      = (if k = i then z i else 0)
        + (- (K / 3 * z i)) * (z k * z k)
        + (K / 3 * (∑ m, z m * z m)) * (if k = i then z i else 0) := by
    intro k; by_cases h : k = i <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ => z i)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ => z i)]
  simp only [Finset.mem_univ, if_true]
  ring

/-- **★ The genuine `hVP` value**: `∑ₖ Ŵ(0)ₖ·(D Ŵ(0)eᵢ)ₖ = −zᵢ`.  The banked center identity `hVP`
    demands this equal `+zᵢ` — MIS-SIGNED (holds only at `zᵢ = 0`).  Curved companion of J4-978. -/
theorem surr_hVP_value (K : ℝ) (z : Point n) (i : Fin n) :
    (∑ k, surrW K z (0 : Point n) k * surrP K z i (0 : Point n) k) = - z i := by
  have h : ∀ k, surrW K z (0 : Point n) k * surrP K z i (0 : Point n) k
      = - (z k * surrP K z i (0 : Point n) k) := by
    intro k; rw [surrW_center]; ring
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_neg_distrib, surr_firstLeg_corrected]

/-- **★★ The genuine `hVQ` value**: `∑ₖ Ŵ(0)ₖ·Qₖ = (2K/3)(zᵢ² − ‖z‖²)`, a NONZERO Riemann-curvature
    contraction (`= −(2/3)R_{ikil}zᵏzˡ` for this metric).  The banked center identity `hVQ` demands
    this equal `0` — MIS-VALUED.  This is exactly the curvature the `VQ` leg must carry and that a
    flat model cannot expose. -/
theorem surr_hVQ_value (K : ℝ) (z : Point n) (i : Fin n) :
    (∑ k, surrW K z (0 : Point n) k * surrQ K z i k)
      = (2 * K / 3) * (z i * z i - ∑ m, z m * z m) := by
  have h : ∀ k, surrW K z (0 : Point n) k * surrQ K z i k
      = (2 * K / 3) * (- (z k * z k)) + (2 * K / 3) * (if k = i then z i * z i else 0) := by
    intro k; rw [surrW_center]; simp only [surrQ]; by_cases hh : k = i <;> simp [hh] <;> ring
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_neg_distrib, Finset.sum_ite_eq' Finset.univ i (fun _ => z i * z i)]
  simp only [Finset.mem_univ, if_true]
  ring

/-! ###############################################################################
    ### §5 — ★ the banked center identities are REFUTED for a genuinely-curved surrogate.
    ############################################################################### -/

/-- **★ `curved_hVP_fails`.**  The banked `hVP` conclusion (`∑ₖ Ŵ(0)ₖ·Pₖ = zᵢ`) is FALSE for the
    genuine (grounded) surrogate jets at `n = 2`, `z = (1,1)`, `i = 0`, `K = −3`: LHS `= −1 ≠ +1`.
    Curved companion of J4-978's `current_hpullVP_fails`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hVP_fails :
    ¬ ((∑ k, surrW (-3 : ℝ) (fun _ => 1 : Point 2) (0 : Point 2) k
          * surrP (-3 : ℝ) (fun _ => 1 : Point 2) 0 (0 : Point 2) k)
        = (fun _ => 1 : Point 2) 0) := by
  rw [surr_hVP_value]; norm_num

/-- **★★ `curved_hVQ_fails`.**  The banked `hVQ` conclusion (`∑ₖ Ŵ(0)ₖ·Qₖ = 0`) is FALSE for the
    genuine (grounded) surrogate jets at `n = 2`, `z = (1,1)`, `i = 0`, `K = −3`: LHS `= 2 ≠ 0`.
    This is the CURVATURE defect no flat model can see — the genuine second-jet radial contraction is a
    nonzero Riemann term, so `hVQ = 0` is geometrically FALSE at general base, not merely unproven.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hVQ_fails :
    ¬ ((∑ k, surrW (-3 : ℝ) (fun _ => 1 : Point 2) (0 : Point 2) k
          * surrQ (-3 : ℝ) (fun _ => 1 : Point 2) 0 k) = 0) := by
  rw [surr_hVQ_value]
  simp only [Fin.sum_univ_two]
  norm_num

end QIQTH.CurvedChartBridgeAudit

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedChartBridgeAudit.surrW_center
#print axioms QIQTH.CurvedChartBridgeAudit.surrP_hasDerivAt
#print axioms QIQTH.CurvedChartBridgeAudit.surrQ_hasDerivAt
#print axioms QIQTH.CurvedChartBridgeAudit.surr_firstLeg_corrected
#print axioms QIQTH.CurvedChartBridgeAudit.surr_hVP_value
#print axioms QIQTH.CurvedChartBridgeAudit.surr_hVQ_value
#print axioms QIQTH.CurvedChartBridgeAudit.curved_hVP_fails
#print axioms QIQTH.CurvedChartBridgeAudit.curved_hVQ_fails
