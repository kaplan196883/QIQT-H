# RNC chart-surface estimates (hco / hVdisp / hJ3i / hJ3j / hJ3Q) — spec, sympy verification, and status

J4-796. The five Riemann-normal-coordinate (RNC) chart-geometry estimates that the mixed sliver
`MixedSliverXUniform.witness_sliver2_xuniform_mixed` carries as hypotheses, with `V = uniformInverseChart …`
the inverse chart, `Pi/Pj` its first jets, `Q` its second jet. `rncRadialSq v = ∑ (vᵢ)² = ‖v‖₂²`; the
ambient `Point n = Fin n → ℝ` norm `‖·‖` is the **sup** norm; `unitVec i = Pi.single i 1`.

| name    | exact statement (∀ z : Point n)                     | meaning                                  |
|---------|-----------------------------------------------------|------------------------------------------|
| `hco`   | `(1/2)·rncRadialSq z ≤ rncRadialSq (V z)`            | near-isometry / coercivity of the chart  |
| `hVdisp`| `‖V z + z‖ ≤ C_W·‖z‖²`                               | quadratic displacement (`V z ≈ −z`)      |
| `hJ3i`  | `‖Pi z − unitVec i‖ ≤ C_P·‖z‖`                       | first-jet gap, `i` direction (`DV ≈ id`) |
| `hJ3j`  | `‖Pj z − unitVec j‖ ≤ C_P·‖z‖`                       | first-jet gap, `j` direction             |
| `hJ3Q`  | `‖Q z‖ ≤ C_Q`                                        | second-jet (Hessian) bound               |

## Sympy verification (from-scratch, not trusting the Lean side)

`exp_p(v)ᵏ = vᵏ − ½·Γᵏ_{ab}(p)·vᵃvᵇ + O(|v|³)` in normal coordinates. Inverting to 2nd order:
`v = y + ½·Γ(y,y) + O(|y|³)`. Symbolic check (`rnc_taylor.py`, dims 2–4, symbolic Christoffel constants):
the inverse residual `exp(v(y)) − y` vanishes exactly through degree 2. This fixes the classical
exponents/constant shapes the five estimates must target:

- `hVdisp` — displacement `W(z)+z` has leading term `½·Γ(z,z)` ⟹ **exponent 2**, `C_W ~ ½·sup‖Γ‖`. ✓
- `hJ3i/hJ3j` — `P(z) = DW(z)`, `P(z) − eₖ = Γ(z,·) + O(z²)` ⟹ **exponent 1**, `C_P ~ sup‖Γ‖`. ✓
- `hJ3Q` — `Q` = 2nd jet `~ Γ` ⟹ **bounded constant** `C_Q ~ sup‖Γ‖`. ✓

The near-isometry `hco ⟸ hVdisp` constant (`nearisom.py`): with `‖·‖₂ ≤ √n‖·‖∞` and `‖·‖∞ ≤ ‖·‖₂`,
`‖V z‖₂ ≥ ‖z‖₂·(1 − √n·C_W·‖z‖₂)`, so `‖V z‖₂² ≥ ½‖z‖₂²` holds on `√n·C_W·‖z‖₂ ≤ 1 − 1/√2 ≈ 0.293`
(tight). A cleaner sufficient sup-norm radius (coordinatewise, used in Lean) is **`n·C_W·‖z‖ ≤ 1/4`**,
giving factor `≥ 3/4`, `(3/4)² = 9/16 ≥ 1/2`.

## Status (J4-796)

**`hco ⟸ hVdisp` reduction: DISCHARGED, abstractly and reusably.**
`QIQTH/RNCNearIsometryPointwise.lean` (std-3):
- `nearIsometry_lower_of_quadraticDisplacement` — the **chart-agnostic pointwise primitive**: for ANY
  `V : Point n → Point n`, `‖V z + z‖ ≤ C_W‖z‖²` (`hVdisp`) with `n·C_W·‖z‖ ≤ 1/4` gives
  `(1/2)·rncRadialSq z ≤ rncRadialSq (V z)` (`hco`), via a direct coordinatewise `∑`-expansion
  (`V z i = bᵢ − zᵢ`, `b := V z + z`; `rncRadialSq z − rncRadialSq(V z) = ∑(2bᵢzᵢ − bᵢ²) ≤ 2n·C_W‖z‖³
  ≤ ½·rncRadialSq z`).
- `chartW0_hco_ball` — routes the primitive through the banked `InverseChartDisplacement.chartW0_displacement`
  to discharge the sliver `hco` for the **concrete** van-Vleck chart `V = uniformInverseChart … z 0`,
  per-point on an explicit ball `‖z‖ < min r₁ (1/(4(n·C_W+1)))`, `z ∈ K`.

Note the concrete local `hco`/`hVdisp` already existed (base-0, over an active set `S ⊆ K ∩ ball 0 r`) as
`chartW0_nearIsometry` / `chartW0_displacement`. The new brick adds the **reusable per-point primitive**
in the sliver's `∀ z` hypothesis shape — the object a per-point discharge / future gating layer calls.

## Update (J4-797 / J4-798) — `hJ3i`/`hJ3j`/`hJ3Q` per-point BALL forms DISCHARGED.

The J4-556 "substrate-rebuild wall" for the jet gaps turned out to be a **don't-under-credit** case: the
`uniformChart_exists` spec did NOT need rebuilding. Both jet gaps transfer from ALREADY-BANKED forward-flow
regularity through the inverse-function-theorem chain rule, per-point on the injectivity ball.

**`hJ3i` / `hJ3j` — FIRST-jet gap (J4-797).** `QIQTH/InverseChartFirstJet.lean` (std-3):
- `clm_inverse_sub_one_le` — operator-inverse Neumann perturbation: `‖T−1‖ ≤ ρ ≤ 1/2 ⟹ IsUnit T ∧
  ‖T⁻¹−1‖ ≤ 2ρ`.
- `firstJet_gap_of_leftInverse` — chart-agnostic transfer: forward Jacobian `T` with `‖T−1‖ ≤ ρ`, ANY left
  inverse `P` (from the germ `W∘φ=id`) ⟹ `‖P e − e‖ ≤ 2ρ` for `‖e‖ ≤ 1`.
- `chartW0_firstJet_gap` — concrete: `‖fderiv(W_z) 0 (unitVec i) − unitVec i‖ ≤ 4·C_D·‖z‖` for `z ∈ K`,
  `‖z‖ < r`. Uses the banked forward gap `uniformFlowExp_fderiv_near_id_quant` (← `geodesicField_taylor_
  remainder_uniform`).

**`hJ3Q` — SECOND-jet (Hessian) bound (J4-798).** `QIQTH/InverseChartSecondJet.lean` (std-3):
- `secondJet_opNorm_le` — reusable operator-norm primitive: `I, D2` with `‖I‖ ≤ 2`, `‖D2‖ ≤ M` ⟹
  `‖(−mulLeftRight ℝ _ I I) ∘L (D2 ∘L I)‖ ≤ 8·M` (via `‖mulLeftRight I I‖ ≤ ‖I‖²` + `opNorm_comp_le`).
- `chartW0_secondJet_bound` — concrete: `‖fderiv(fun y => fderiv(W_z) y) 0‖ ≤ 8·M'` for `z ∈ K`, `‖z‖ < r`.
  Wires the per-`z` 2nd-order IFT identity `Q z = (−mulLeftRight I I) ∘L (D²φ_z(W_z 0) ∘L I)`
  (`Hid2Germ.hid2_discharged`) with `‖I‖ ≤ 2` (forward Jacobian gap + `clm_inverse_sub_one_le`) and the
  UNIFORM forward-Hessian bound R3 `uniformFlowExp_hessian_opNorm_le` (J4-70, already banked).
  This is exactly the "forward second Taylor's transfer to a uniform inverse Hessian is not plumbed here"
  step the earlier note flagged — now plumbed.

Together with `chartW0_hco_ball` (`hco`) and `chartW0_displacement` (`hVdisp`), the **per-point BALL forms of
ALL FIVE** RNC chart-surface estimates are now discharged.

**What remains open (precisely).**
1. **Global `∀ z` (the ONLY remaining wall).** The sliver's five estimates are literally global over all
   `Point n`. For the concrete `V = W₀` every bound holds only on the injectivity ball (off it the
   `.choose`-built chart is junk). The global form needs the **gating layer** (concrete instantiation setting
   `V = −id`, `Pi = eᵢ`, `Q = 0` off the gate), which is not built. The substrate-rebuild wall (a
   higher-order `uniformChart_exists` spec) is NO LONGER needed for the jet bounds — only this off-gate
   redefinition is.

a₁ = R/6 remains CONDITIONAL.
