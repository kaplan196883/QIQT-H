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

## Sharpened premise — the integral Clausius variant (`jacobson_einstein_from_clausius_integral`)

`ClausiusToPernull.lean` now **derives** the `pernull` premise from Jacobson's *raw* eq.(`dQ`)=eq.(`dA`),
so the end-to-end theorem can be stated with his actual integral equations instead of an assumed per-null
relation:

| Step | Lean | Role |
|---|---|---|
| integral matching `∫λf=∫λg ∀ε ⟹ f(0)=g(0)` | `value_at_zero_of_weighted_integral_proportional` (FTC + l'Hôpital) | the integrand-matching kernel |
| area substitution `δA=∫θ ↔ −∫λR_kk` (leading order) | `area_leadingCoeff_eq_neg_ricci` (TeX 275–282) | `θ(0)=σ(0)=0` + Raychaudhuri rate ⟹ same `ε²` coeff |
| integral Clausius ⟹ `pernull` | `pernull_of_clausius_integral` (`BL_smul_sub`) | `∫λ(a·T_kk)=∫λR_kk` ⟹ `BL(a·T−Ric)v=0` |
| wired end-to-end | `jacobson_einstein_from_clausius_integral` | premise is now eq.(`dQ`)=eq.(`dA`) verbatim |

## What FEEDS the premise `pernull` (machine-checked elsewhere, referenced in the docstring)

| Input to `pernull` | Lean | Kind |
|---|---|---|
| Ricci focusing term `R_{σν}k^σk^ν` | `raychaudhuri_geodesic` (full Raychaudhuri) | **geometry, machine-checked** |
| Unruh temperature `T = ℏκ/2π` | `QIQTH.Unruh.kms_periodicity` (KMS at β=2π/a) | **QFT, machine-checked** (modulo the correlator form) |

## What is CITED (genuinely not in Lean — the irreducible residual)

Verified against the actual paper (gr-qc/9504004, TeX in `refs/books_papers/jacobson9504004/`). These are
**exactly Jacobson's own assumptions** — he assumes 1–3 and treats the surface integrals heuristically:

1. **The area law `δS = ηδA`** — gap 1, the holographic postulate QIQT-H *assumes*. The real open physics.
2. **The Clausius relation `δQ = TδS`** — the thermodynamic assumption (Jacobson's `δQ=TdS`).
3. **The Unruh temperature `T = ℏκ/2π`** — a **cited input in Jacobson too** (his ref [unruh]); he never
   computes a Wightman function. Its *thermal character* (KMS periodicity) is separately machine-checked
   (`Unruh.kms_periodicity`); deriving the full correlator from a quantized field is the multi-year
   Type-III/continuum work and is **not needed for the GR result** (scope beyond Jacobson — see commit
   deleting `WightmanKernel`).
4. **The surface integrals themselves** — `δQ=∫T_{ab}χ^a dΣ^b` and `δA=∫θ dλ dA` as integrals over the
   horizon's null-generator pencil with its area element `dA`. The *integrand matching* and the *area
   substitution* are now machine-checked (above); what remains cited is the Lorentzian null-hypersurface
   **measure theory** (the area element, the boost-Killing flux measure) — absent from Mathlib, and
   treated heuristically by Jacobson himself.
5. **`hreg`** — regularity of the proportionality scalar (an analytic, not physical, residual).

## Honest bottom line
The end-to-end theorem exists and is axiom-free, in two forms: `jacobson_einstein_equation_of_state` (from
the per-null premise) and `jacobson_einstein_from_clausius_integral` (from Jacobson's *raw* integral
`δQ=TδS`). **Modulo exactly Jacobson's own cited physics — the area law (gap 1), Clausius, and the Unruh
temperature — the whole chain from the integral Clausius relation to `G+Λg=a·T` is machine-checked,
axiom-free, with every geometric step (Raychaudhuri, the integral matching, the area substitution, the
null-cone tensor upgrade, contracted Bianchi, the constant Λ) discharged.** It is NOT "GR from nothing":
the area law (gap 1) is the genuine open physics, assumed not derived; the only further gap below the
integral premise is the horizon **measure theory**, which Jacobson does not formalize either. Frameworks:
component calculus on `Point 4` (not abstract manifolds — that is the separate gap-3 generality thread).
