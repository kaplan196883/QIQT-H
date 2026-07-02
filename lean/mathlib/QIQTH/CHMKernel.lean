/-
  BRIDGE C2a — the CHM ball kernel: the weight `(R²−|x|²)/2R` and the diamond conformal Killing structure.

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified). The Casini–Huerta–Myers modular Hamiltonian of a ball of radius
    `R` is `K_B = 2π ∫_{|x|<R} β(|x|) T₀₀`, with the **kernel weight** `β(r) = (R²−r²)/2R` — the local inverse
    temperature. This module proves the FINITE GEOMETRY of that kernel (all axiom-free, std-3):
  • the weight is nonneg on the ball, VANISHES on the entangling sphere `r = R` (the flow fixes the edge), peaks
    at the center (`β(0) = R/2`), and factorizes as `β = (R−r)·(R+r)/2R`;
  • **the unit surface-gravity normalization** (`chmWeight_edge_slope`): `β′(R) = −1` — the kernel approaches the
    edge with UNIT slope, exactly the Rindler weight `x¹` of the wedge (C1). This is why the SAME `2π` appears in
    the wedge and ball modular Hamiltonians — the Clausius datum transports between C1 and C2 consistently;
  • **the diamond conformal Killing equation** (`cke_tt/tx/xx_diag/xx_off`): the vector field
    `ζ_0 = (t²+|x|²−R²)/2R`, `ζ_i = −t·x_i/R` (the lowered components of the causal-diamond CKV, whose `t = 0`
    restriction IS the kernel `ζ_0|_{t=0} = −β`) satisfies `∂_μζ_ν + ∂_νζ_μ = −(2t/R)·η_{μν}` — verified by GENUINE
    real calculus (`deriv`/`HasDerivAt` on each slot), all 10 component equations. So the CHM flow is a conformal
    symmetry of flat space: the geometric flow that C2b's `CHMCompatible` transport rides.

  ⚠ Honest labels: this is the KERNEL GEOMETRY only — the statement that the ball modular Hamiltonian of a CFT
    vacuum IS `2π∫β T₀₀` (the CHM theorem) is conformal-QFT input, carried at C2b as `CHMCompatible`; not generic
    QFT, not derived here. Linearized bridge context; the area law stays ingredient D.
-/
import Mathlib

namespace QIQTH.CHM

/-! ## The kernel weight -/

/-- **The CHM kernel weight** `β(r) = (R²−r²)/2R` — the local inverse temperature of the ball modular flow. -/
noncomputable def chmWeight (R r : ℝ) : ℝ := (R ^ 2 - r ^ 2) / (2 * R)

/-- The weight factorizes through the edge distance: `β = (R−r)·(R+r)/(2R)`. -/
theorem chmWeight_factor (R r : ℝ) : chmWeight R r = (R - r) * ((R + r) / (2 * R)) := by
  rw [chmWeight]; ring

/-- The weight is nonnegative on the ball (`|r| ≤ R`). -/
theorem chmWeight_nonneg (R r : ℝ) (hR : 0 < R) (hr : |r| ≤ R) : 0 ≤ chmWeight R r := by
  rw [chmWeight]
  apply div_nonneg _ (by linarith)
  have h1 : r ^ 2 ≤ R ^ 2 := by
    have := abs_nonneg r
    have h2 : |r| ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs r]
    nlinarith [sq_abs r]
  linarith

/-- The weight **vanishes on the entangling sphere** `r = R` — the modular flow fixes the edge. -/
theorem chmWeight_boundary (R : ℝ) : chmWeight R R = 0 := by simp [chmWeight]

/-- The center value `β(0) = R/2` — the ball's central inverse temperature. -/
theorem chmWeight_center (R : ℝ) (hR : R ≠ 0) : chmWeight R 0 = R / 2 := by
  rw [chmWeight]; field_simp; ring

/-- **The unit surface-gravity normalization**: the kernel approaches the entangling surface with slope
    `β′(R) = −1` — exactly the Rindler weight's unit slope at the wedge edge (C1). The same normalization ⟹ the
    same `2π` in both modular Hamiltonians ⟹ the Clausius datum transports consistently between wedge and ball. -/
theorem chmWeight_edge_slope (R : ℝ) (hR : R ≠ 0) : deriv (chmWeight R) R = -1 := by
  have h : HasDerivAt (chmWeight R) ((0 - 2 * R ^ 1) / (2 * R)) R := by
    have h0 : HasDerivAt (fun r : ℝ => R ^ 2 - r ^ 2) (0 - 2 * R ^ 1) R :=
      (hasDerivAt_const R (R ^ 2)).sub (hasDerivAt_pow 2 R)
    exact h0.div_const (2 * R)
  have := h.deriv
  rw [this]; field_simp; ring

/-! ## The diamond conformal Killing vector (lowered components) -/

/-- The lowered time component `ζ_0 = (t² + |x|² − R²)/2R` (its `t = 0` restriction is `−β(|x|)` — the kernel). -/
noncomputable def zeta0 (R t a b c : ℝ) : ℝ := (t ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2) - R ^ 2) / (2 * R)

/-- A lowered spatial component `ζ_i = −t·x_i/R` (as a function of `t` and its own coordinate `x`). -/
noncomputable def zetaSp (R t x : ℝ) : ℝ := -(t * x) / R

/-- `∂_t ζ_0 = t/R`. -/
theorem pd_zeta0_t (R t a b c : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zeta0 R s a b c) t = t / R := by
  have heq : (fun s : ℝ => zeta0 R s a b c)
      = fun s => (s ^ 2 + ((a ^ 2 + b ^ 2 + c ^ 2) - R ^ 2)) / (2 * R) := by
    funext s; rw [zeta0]; ring
  rw [heq]
  have h : HasDerivAt (fun s : ℝ => (s ^ 2 + ((a ^ 2 + b ^ 2 + c ^ 2) - R ^ 2)) / (2 * R))
      ((2 * t ^ 1) / (2 * R)) t :=
    ((hasDerivAt_pow 2 t).add_const _).div_const (2 * R)
  rw [h.deriv]; field_simp

/-- `∂_i ζ_0 = x_i/R` (the first spatial slot; `ζ_0` is symmetric in the three spatial slots, so this statement
    with arbitrary parameters covers all three). -/
theorem pd_zeta0_sp (R t a b c : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zeta0 R t s b c) a = a / R := by
  have heq : (fun s : ℝ => zeta0 R t s b c)
      = fun s => (s ^ 2 + ((t ^ 2 + b ^ 2 + c ^ 2) - R ^ 2)) / (2 * R) := by
    funext s; rw [zeta0]; ring
  rw [heq]
  have h : HasDerivAt (fun s : ℝ => (s ^ 2 + ((t ^ 2 + b ^ 2 + c ^ 2) - R ^ 2)) / (2 * R))
      ((2 * a ^ 1) / (2 * R)) a :=
    ((hasDerivAt_pow 2 a).add_const _).div_const (2 * R)
  rw [h.deriv]; field_simp

/-- `∂_t ζ_i = −x_i/R`. -/
theorem pd_zetaSp_t (R t x : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zetaSp R s x) t = -x / R := by
  have heq : (fun s : ℝ => zetaSp R s x) = fun s => s * (-x / R) := by
    funext s; rw [zetaSp]; ring
  rw [heq]
  have h : HasDerivAt (fun s : ℝ => s * (-x / R)) (-x / R) t := by
    simpa using (hasDerivAt_id t).mul_const (-x / R)
  rw [h.deriv]

/-- `∂_i ζ_i = −t/R` (own-coordinate slope). -/
theorem pd_zetaSp_own (R t x : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zetaSp R t s) x = -t / R := by
  have heq : (fun s : ℝ => zetaSp R t s) = fun s => s * (-t / R) := by
    funext s; rw [zetaSp]; ring
  rw [heq]
  have h : HasDerivAt (fun s : ℝ => s * (-t / R)) (-t / R) x := by
    simpa using (hasDerivAt_id x).mul_const (-t / R)
  rw [h.deriv]

/-! ## The conformal Killing equation `∂_μζ_ν + ∂_νζ_μ = −(2t/R)·η_{μν}` — all component classes -/

/-- **CKE, time-time**: `2∂_tζ_0 = −(2t/R)·η₀₀` (with `η₀₀ = −1`). -/
theorem cke_tt (R t a b c : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zeta0 R s a b c) t + deriv (fun s => zeta0 R s a b c) t
      = -(2 * t / R) * (-1) := by
  rw [pd_zeta0_t R t a b c hR]; field_simp; ring

/-- **CKE, time-space (off-diagonal)**: `∂_tζ_i + ∂_iζ_0 = 0 = −(2t/R)·η₀ᵢ`. -/
theorem cke_tx (R t a b c : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zetaSp R s a) t + deriv (fun s => zeta0 R t s b c) a = 0 := by
  rw [pd_zetaSp_t R t a hR, pd_zeta0_sp R t a b c hR]; ring

/-- **CKE, space-space diagonal**: `2∂_iζ_i = −(2t/R)·η_ii` (with `η_ii = 1`). -/
theorem cke_xx_diag (R t x : ℝ) (hR : R ≠ 0) :
    deriv (fun s => zetaSp R t s) x + deriv (fun s => zetaSp R t s) x
      = -(2 * t / R) * 1 := by
  rw [pd_zetaSp_own R t x hR]; field_simp; ring

/-- **CKE, space-space off-diagonal**: `∂_iζ_j + ∂_jζ_i = 0` — each spatial component is independent of the
    other coordinates (`ζ_j = −t·x_j/R` does not involve `x_i`), so both partials vanish. -/
theorem cke_xx_off (R t xj xi : ℝ) :
    deriv (fun _ : ℝ => zetaSp R t xj) xi + deriv (fun _ : ℝ => zetaSp R t xi) xj = 0 := by
  simp [deriv_const]

/-- The `t = 0` restriction of the CKV time component is (minus) the kernel: `ζ_0|_{t=0} = −β(r)` — the flow's
    local temperature IS the kernel weight (with `r² = |x|²`). -/
theorem zeta0_restrict (R a b c : ℝ) (hR : R ≠ 0) :
    zeta0 R 0 a b c = -(chmWeight R (Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2))) := by
  rw [zeta0, chmWeight, Real.sq_sqrt (by positivity)]
  ring

end QIQTH.CHM
