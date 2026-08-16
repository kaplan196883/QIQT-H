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

**What remains open (precisely).**
1. **Global `∀ z`.** The sliver's `hco`/`hVdisp` are literally global over all `Point n`. For the concrete
   `V = W₀` the displacement bound holds only on the injectivity ball (off it the `.choose`-built chart is
   junk). The global form needs the **gating layer** (concrete instantiation setting `V = −id`, `Pi = eᵢ`,
   `Q = 0` off the gate), which is not built.
2. **`hJ3i` / `hJ3j` / `hJ3Q` (jet gaps).** One Fréchet order above `hVdisp`. The linear-in-`‖z‖` decay of
   the Jacobian gap needs a **uniform-in-`z` Jacobian Lipschitz / second-order Taylor** bound of the inverse
   chart, which the frozen `uniformChart_exists` spec (ApproximatesLinearOn = first-order + pointwise
   `ContDiffAt 2`) does **not** expose — the J4-556 substrate-rebuild wall. The forward geodesic Taylor
   machinery exists (`GeodesicTaylorCompact.geodesicField_taylor_remainder_uniform`) but is not plumbed into
   the inverse chart's spec. This is genuine multi-session substrate work, not a port.

a₁ = R/6 remains CONDITIONAL.
