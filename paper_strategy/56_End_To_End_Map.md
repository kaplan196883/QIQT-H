# Map 56 — the end-to-end theorem: `Bekenstein + QIQT-H ⟹ GR`, wired together

User directive: wire the pieces into one end-to-end theorem. Done: **`jacobson_einstein_equation_of_state`**
(`QIQTH/EinsteinFieldEquation.lean`) is the single machine-checked, axiom-free theorem from Jacobson's
one physics premise to the Einstein field equation `a·T_{μν} = G_{μν} + Λ·g_{μν}` with a genuine
constant `Λ`. This map states exactly what the theorem discharges and what it cites.

## The single theorem

```
pernull  (per-null Clausius relation, Jacobson's premise)
  + Lorentzian structure (g = Pᵀ·η·P, Sylvester)
  + hreg (the proportionality scalar f is regular — the one analytic residual)
  + conserv (∇^μ(a·T)=0)
  ─────────────────────────────────────────────────────────────────────────────  jacobson_einstein_equation_of_state
  ∃ Λ (constant),  a·T_{μν} = G_{μν} + Λ·g_{μν}          [G = genuine einsteinTensor]
```

## What is DISCHARGED inside it (all axiom-free, `#print axioms` clean)

| Step | Lean | Role |
|---|---|---|
| null-cone tensor lemma (Sylvester) | `crux_of_pernull` / `symmTensor_eq_smul_metric_of_null_general` | `pernull ⟹ a·T = R + f·g` |
| contracted Bianchi `∇^μG_{μν}=0` | `twice_contracted_bianchi` | fixes `f = −R/2 + Λ` |
| `Λ` is a true constant | `const_of_pd_zero` + `einstein_field_equation_real_global` | closure |

## What FEEDS the premise `pernull` (machine-checked elsewhere, referenced in the docstring)

| Input to `pernull` | Lean | Kind |
|---|---|---|
| Ricci focusing term `R_{σν}k^σk^ν` | `raychaudhuri_geodesic` (full Raychaudhuri) | **geometry, machine-checked** |
| Unruh temperature `T = ℏκ/2π` | `QIQTH.Unruh.kms_periodicity` (KMS at β=2π/a) | **QFT, machine-checked** (modulo the correlator form) |

## What is CITED (genuinely not in Lean — the irreducible residual)

1. **The area law `δS = ηδA`** — gap 1, the holographic postulate QIQT-H *assumes*. The real open physics.
2. **The Clausius relation `δQ = TδS`** — the thermodynamic assumption.
3. **The free-field two-point-function form** behind Unruh — deriving it from the quantized field
   (Fock/Bogoliubov or the algebraic free-field net) is the multi-year Type-III/continuum work.
4. **The integral step** that combines Raychaudhuri's `δA` and the heat flux `δQ` into `pernull`
   (Jacobson's "match integrands for all null k") — bundled into the `pernull` premise.
5. **`hreg`** — regularity of the proportionality scalar (an analytic, not physical, residual).

## Honest bottom line
The end-to-end theorem exists and is axiom-free: **modulo the cited physics (area law, Clausius, the
correlator form, the integral matching), the whole chain from the Clausius premise to `G+Λg=a·T` is one
machine-checked theorem, with every geometric step discharged and the thermal content of Unruh checked
separately.** It is NOT "GR from nothing": the area law (gap 1) is the genuine open physics, assumed not
derived; and `pernull` bundles the front-half integral argument as a premise. Frameworks: component
calculus on `Point 4` (not abstract manifolds — that is the separate gap-3 generality thread).
