import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Sakharov / induced-gravity `1/4` ratio — the circularity-clean algebraic core

This is the **Lean mirror of `scripts/sakharov_kg.py`** (the `SAKHAROV_KG_PLAN.md`, Stages A+B): the
machine-checked algebraic content of the claim that the Bekenstein–Hawking `1/4` of `S = A/4ℓ_P²` is the
**universal geometric ratio** `(conical-deficit 4π)/(Einstein–Hilbert 16π)`, forced by the matter sector's UV
structure and **independent of the matter coefficient and the UV regulator**.

## What is and is NOT formalized here (honest scope)

* **Formalized (this file):** the *algebraic cancellation*. Given the two heat-kernel (Seeley–DeWitt) outputs
  for the free minimally-coupled scalar — the leading entanglement-entropy density `S_ent = A·b/(48π·reg)` and
  the induced inverse Newton constant `1/G_ind = b/(12π·reg)` — the ratio `S_ent/(A/G_ind) = 1/4`, with the
  matter coefficient `b`, the regulator `reg`, the area `A`, and `π` **all cancelling**. This is exactly the
  `sympy` identity the script checks (with arbitrary `b`, `reg`): the `1/4` is the *output* `4π/16π`, never an
  input. This is the load-bearing **circularity-clean** statement (Stage B).
* **NOT formalized (the physics inputs / cited frontiers):** the heat-kernel coefficients `1/48π`, `1/12π`
  themselves (the Seeley–DeWitt `a₂` computation — reproduces Susskind–Uglum/Solodukhin, entered here as data);
  the **area-law scaling** `S ∝ A` from the lattice Williamson spectrum (the `M3` / `SAKHAROV_KG_PLAN` §2-C
  frontier); the **absolute value of `G_ind`/`ℓ_P`** (the species/UV datum — carried, never derived); and
  **cross-species universality** (free scalar only). See the per-mode entropy substrate in
  `QIQTH/GaussianStateEntropy.lean`.

So: the `1/4` *ratio* is machine-checked to be regulator- and matter-independent; the value of `G` stays the
carried UV datum.
-/

namespace QIQTH.Sakharov

open Real

/-- **The Sakharov ratio is `1/4`, circularity-clean.** For an arbitrary area `A`, an arbitrary matter
heat-kernel coefficient `b`, and an arbitrary UV regulator `reg` (all nonzero), the leading entanglement
entropy `S_ent = A·b/(48π·reg)` and the induced inverse Newton constant `1/G_ind = b/(12π·reg)` — which share
the *same* UV factor `b/reg` — give

`S_ent / (A / G_ind) = S_ent · G_ind / A = 1/4`.

The matter coefficient `b`, the regulator `reg`, the area `A`, and `π` **all cancel**: the `1/4` is fixed by
the two fixed geometric normalizations `48π` and `12π` alone, independent of the matter content and the cutoff.
This is the Lean mirror of `scripts/sakharov_kg.py` (Stage B, the circularity audit). -/
theorem sakharov_ratio (A b reg : ℝ) (hA : A ≠ 0) (hb : b ≠ 0) (hreg : reg ≠ 0) :
    (A * b / (48 * π * reg)) / (A * (b / (12 * π * reg))) = 1 / 4 := by
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-- **The geometric origin of the `1/4`:** it is the ratio of the conical-deficit normalization `4π` to the
Einstein–Hilbert normalization `16π`, `(4π)/(16π) = 1/4` — manifestly independent of any matter or cutoff
scale. This is *why* the Bekenstein–Hawking coefficient is universal: matter fixes `G_ind`, geometry fixes the
`1/4`. -/
theorem geometric_quarter : (4 * π) / (16 * π) = 1 / 4 := by
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-- **Consistency of the two presentations:** the ratio of the heat-kernel coefficients `(1/48π)/(1/12π)`
equals the geometric ratio `(4π)/(16π)` — both are the same `1/4`. The two ways the script prints the
universal coefficient agree. -/
theorem heatkernel_ratio_eq_geometric :
    (1 / (48 * π)) / (1 / (12 * π)) = (4 * π) / (16 * π) := by
  have hπ := Real.pi_ne_zero
  field_simp
  ring

end QIQTH.Sakharov
