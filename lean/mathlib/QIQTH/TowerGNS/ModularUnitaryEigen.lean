/-
  ID3 (THE_IDENTIFICATION_PLAN.md) — THE MODULAR UNITARY ON THE EIGENBASIS: `U_t` acts
  diagonally on the matrix-unit components — on a coerced pure matrix-unit component,
  `U_t` is the SAME pure phase as the physical flow:

      U_t ↑(of C (E_{nm} c)) = exp(i·t·(log w_n − log w_m)) • ↑(of C (E_{nm} c)),

  MATCHING `cornerFlow_single` (Generator.lean) / `towerFlow_of_eq_sum_single` (ID1)
  syntactically — the real-arithmetic step of the campaign.

  Route (the `towerModUnitary_cyclicVec` template with `½` replaced by `(1+δ)⁻¹`):

  • The GENERAL eigenvector evaluation `towerModUnitary_of_eigen`: if `Δ⟨x,hx⟩ = δ•x`
    with `0 < δ`, then `U_t x = exp(i·t·log δ)•x`.  Case `x = 0` trivial; else ID2's
    `towerResolvent_of_eigen` gives `R x = (1+δ)⁻¹•x`, so `(1+δ)⁻¹ ∈ σ(R)`
    (`mem_spectrum_of_eigenvector`) and the bounded Borel FC acts by evaluation of the
    symbol (`borelFC_apply_eigenvector`).  Since `0 < (1+δ)⁻¹ < 1`, the piecewise symbol
    takes the bulk branch `exp(i·t·log((1−r)/r))`, and the real arithmetic
    `(1 − (1+δ)⁻¹)/(1+δ)⁻¹ = δ` (with `1+δ ≠ 0`) evaluates the log to `log δ`.

  • The specialization at `δ = w_n/w_m` (ID2's `towerModularOp_of_single`, positivity from
    ID1's `gibbsWeight_div_pos`), with `Real.log_div` (weights ≠ 0 from `gibbsWeight_pos`)
    splitting `log(w_n/w_m) = log w_n − log w_m` into the exact `cornerFlow_single` shape.

  Deliverables:
  • `towerModUnitary_of_eigen` — the general Δ-eigenvector → U_t-evaluation transport;
  • `towerModUnitary_of_single` ★ — `U_t` is the `cornerFlow_single` phase on the coerced
    matrix-unit components (the input to ID4's dense-span identification).

  HONEST SCOPE (binding): eigenvector-evaluation statements for `U_t` only.  No
  identification `towerFlow = Δ^{it}` is claimed here (that is ID4); no Tomita statement
  (that is ID5). Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ModularEigenvectors
import QIQTH.TowerGNS.ModularUnitary

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.SpectralTheorem
open scoped Matrix DirectSum

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### ★ The general eigenvector evaluation Δ → U_t -/

/-- **★ THE EIGENVECTOR EVALUATION Δ → U_t**: a Δ-eigenvector with strictly positive
    eigenvalue is a `towerModUnitary`-eigenvector with the modular phase —
    `Δ⟨x, hx⟩ = δ • x` with `0 < δ` gives `U_t x = exp(i·t·log δ) • x`.
    Route (the `towerModUnitary_cyclicVec` template at `r = (1+δ)⁻¹` instead of `½`):
    `towerResolvent_of_eigen` puts `(1+δ)⁻¹ ∈ σ(R)` via `mem_spectrum_of_eigenvector`
    (case `x = 0` trivial), `borelFC_apply_eigenvector` evaluates the symbol, and the
    real arithmetic `(1 − (1+δ)⁻¹)/(1+δ)⁻¹ = δ` lands the bulk branch on `log δ`. -/
theorem towerModUnitary_of_eigen {x : TowerGNS L ω β}
    (hx : x ∈ towerModularDom L ω β) {δ : ℝ} (hδ : 0 < δ)
    (hΔ : towerModularOp L ω β ⟨x, hx⟩ = (δ : ℂ) • x) (t : ℝ) :
    towerModUnitary L ω β t x
      = Complex.exp (Complex.I * t * (Real.log δ : ℂ)) • x := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, smul_zero]
  · have h1δ : (0 : ℝ) < 1 + δ := by linarith
    -- the R-eigenvector equation, in the real-scalar form the FC calculus expects
    have hR : towerResolvent L ω β x = (((1 + δ)⁻¹ : ℝ) : ℂ) • x :=
      towerResolvent_of_eigen L ω β hx hδ hΔ
    -- (1+δ)⁻¹ ∈ σ(R)
    have hr : ((1 + δ)⁻¹ : ℝ) ∈ spectrum ℝ (towerResolvent L ω β) :=
      mem_spectrum_of_eigenvector (towerResolvent L ω β) hx0 hR
    -- the FC acts on x by evaluation of the symbol at (1+δ)⁻¹
    have hval := borelFC_apply_eigenvector (towerResolvent L ω β)
      (towerResolvent_isSelfAdjoint L ω β) (towerModSpecFun_measurable L ω β t)
      zero_le_one (towerModSpecFun_norm_le L ω β t) hr hR
    -- the symbol value: `u_t((1+δ)⁻¹) = exp(i·t·log δ)`
    have hsym : towerModSpecFun L ω β t ⟨((1 + δ)⁻¹ : ℝ), hr⟩
        = Complex.exp (Complex.I * t * (Real.log δ : ℂ)) := by
      show towerModChar t ((1 + δ)⁻¹ : ℝ) = _
      unfold towerModChar
      have hmem : ((1 + δ)⁻¹ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨inv_pos.mpr h1δ, inv_lt_one_of_one_lt₀ (by linarith)⟩
      rw [Set.piecewise_eq_of_mem _ _ _ hmem]
      have harg : ((1 : ℝ) - (1 + δ)⁻¹) / (1 + δ)⁻¹ = δ := by
        rw [div_inv_eq_mul, sub_mul, one_mul, inv_mul_cancel₀ h1δ.ne']
        ring
      rw [harg]
    rw [towerModUnitary, hval, hsym]

/-! ### ★ U_t is the cornerFlow phase on the matrix units -/

/-- **★ `U_t` IS THE PHYSICAL PHASE ON THE EIGENBASIS**: on a coerced pure matrix-unit
    component the modular unitary acts as EXACTLY the `cornerFlow_single` /
    `towerFlow_of_eq_sum_single` pure phase —
    `U_t ↑(of C (E_{nm} c)) = exp(i·t·(log w_n − log w_m)) • ↑(of C (E_{nm} c))`.
    The general evaluation at `δ = w_n/w_m` (`towerModularOp_of_single`,
    `gibbsWeight_div_pos`), with `Real.log_div` splitting the log of the weight ratio.
    The scalar shape matches the flow side SYNTACTICALLY — ID4's dense-span rewrite
    consumes it verbatim. -/
theorem towerModUnitary_of_single (t : ℝ) (C : Finset M) (n m : Micro L C) (c : ℂ) :
    towerModUnitary L ω β t
        ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β)
      = Complex.exp (Complex.I * t * ((Real.log (gibbsWeight L C ω β n)
          - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
        • ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  rw [towerModUnitary_of_eigen L ω β
      (of_mem_towerModularDom L ω β C (Matrix.single n m c))
      (gibbsWeight_div_pos L ω β C n m)
      (towerModularOp_of_single L ω β C n m c) t,
    Real.log_div (gibbsWeight_pos L C ω β n).ne' (gibbsWeight_pos L C ω β m).ne']

end QIQTH.TowerGNS
