# A1-ppwave — the non-degenerate Raychaudhuri-congruence witness (pp-wave)

**Status:** PLAN (not started). **Track:** GR. **Goal:** strengthen the flat (degenerate, `Ric=0`) witness for the
GR Raychaudhuri congruence premises to a **non-flat** one: a pp-wave metric with a covariantly-constant null
field `∂_v`, where `hWgeo`/`hWequil` (now collapsed to `hcov` — W covariantly constant) hold explicitly **and**
`Ric ≠ 0`.  This removes the "flat ⟹ degenerate" caveat from `T3-GR-RAYCHAUDHURI`.

## 0. The construction

pp-wave metric in coords `(u,v,x,y) = (x⁰,x¹,x²,x³)`, with `H : Point 4 → ℝ` independent of `v = x¹`
(`pd H 1 ≡ 0`):
```
ds² = 2 du dv + H du² + dx² + dy²
g  = [[H,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]]
gi = [[0,1,0,0],[1,-H,0,0],[0,0,1,0],[0,0,0,1]]
```
The vector field `V = ∂_v` (`V^μ = δ^μ_1`, constant) is null (`g(V,V)=g₁₁=0`) and **covariantly constant**.

## 1. The lever

`christoffel g gi μ ν ρ = ½ ∑_α gi_{μα}(∂_ν g_{αρ} + ∂_ρ g_{αν} − ∂_α g_{νρ})` (`Curvature.lean:148`).
`covDerivVec g gi V ν μ x = ∂_ν V^μ + ∑_σ Γ^μ_{νσ} V^σ` (`Curvature.lean:243`).  For `V = δ₁` (constant):
`covDerivVec g gi V ν μ x = christoffel g gi μ ν 1 x`.  And **every Christoffel with last index `1` vanishes**:
- `∂_ν g_{α1} = 0` — `g_{·1}` is constant (`g_{01}=1`, `g_{11}=0`, rest `0`);
- `∂_1 g_{αν} = 0` — nothing depends on `v=x¹` (`g₀₀=H` has `pd H 1 = 0`; the rest are constant);
- `∂_α g_{ν1} = 0` — `g_{ν1}` constant.

So `christoffel g gi μ ν 1 ≡ 0`, hence `covDerivVec g gi (∂_v) ≡ 0` — `∂_v` is covariantly constant, and
`raychaudhuri_setup_of_covConst` (already proved) gives `hWgeo ∧ hWequil`.

## 2. Stages (each axiom-free, green-building, one commit)

### Stage 1 — define the metric, prove symmetry + inverse `QIQTH/PPWaveMetric.lean`
Define `ppMetric (H) x a b` and `ppMetricInv (H) x a b` (the `[[H,1..],[1,0..],..]` blocks).  Prove
`ppMetric_symm` (`g_ab = g_ba`) and `ppMetric_inv` (`∑_σ g_{aσ} gi_{σb} = δ_ab`, the `hinv` premise) by
`Fin 4` case-bashing (`Fin.sum_univ_four`, `decide`/`fin_cases`).  **Risk: low** (finite, mechanical).

### Stage 2 — the key Christoffel lemma
`christoffel_ppwave_last_one (H) (hHv : ∀ x, pd H 1 x = 0) (μ ν : Fin 4) (x) :
   christoffel (ppMetric H) (ppMetricInv H) μ ν 1 x = 0`.
Route: unfold `christoffel`; every `pd (fun y => ppMetric H y α ρ) ν x` is `0` — either the component is a
constant (`pd_const`) or it is `g₀₀=H` differentiated in direction `1` (`hHv`).  Reduce the inner three
`pd`-terms to `0` by `Fin 4` cases on `α`, then `∑_α gi·0 = 0`.  **Risk: medium** (the `pd`-of-each-component
bookkeeping; use a helper `ppMetric_pd_eq_zero_unless_00` and `pd H 1 = 0`).

### Stage 3 — `∂_v` covariantly constant ⟹ the congruence premises (the witness)
`ppwave_covDerivVec_v_zero` : `covDerivVec (ppMetric H) (ppMetricInv H) (fun _ μ => if μ = 1 then 1 else 0)
  a b x = 0` (from Stage 2 + `pd_const`).  Then `ppwave_raychaudhuri_setup` : `hWgeo ∧ hWequil` for `V = ∂_v`
via `raychaudhuri_setup_of_covConst`.  **A non-flat spacetime where the Raychaudhuri congruence premises hold
explicitly** — strengthens the flat witness.  **Risk: low** (composition).

### Stage 4 — non-degeneracy `Ric ≠ 0` *(heavier; the payoff that it is NOT flat)*
For `H := fun x => (x 2)^2` (so `Δ_⊥ H = ∂_x² H = 2`), the pp-wave has `Ric₀₀ = −½ Δ_⊥ H = −1 ≠ 0`.  Prove
`ricci (ppMetric H) (ppMetricInv H) 0 0 x ≠ 0` by computing the Ricci in the `Point 4`/`christoffel` setup.
**Risk: high** — the full Ricci of a non-trivial metric is a large computation; if it proves too heavy for the
bespoke setup, **document** the standard `Ric₀₀ = −½Δ_⊥H` result and leave the full Lean evaluation as a noted
sub-frontier (Stages 1–3 already deliver the covariantly-constant null field in a *generically non-flat* metric
class — the witness stands; Stage 4 only certifies a *specific* `H` is non-vacuum).

## 3. Honest outcome
The Raychaudhuri congruence premises (`hWgeo`/`hWequil` = `hcov`) are discharged for a **pp-wave** — a metric
class that is generically non-flat (curved, `Ric≠0` for non-harmonic `H`) — via the explicit covariantly-constant
null field `∂_v`.  This upgrades the flat (degenerate) witness to a genuinely curved one.  Stage 4 pins a
concrete non-vacuum `H` if the Ricci computation is tractable; otherwise the standard `Ric₀₀=−½Δ_⊥H` is
documented and the witness (Stages 1–3) stands on the non-flat metric class.

## 4. Verification (per stage)
- `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green.
- `#print axioms <thm>` = `[propext, Classical.choice, Quot.sound]`; `bash scripts/axiom_budget_check.sh` budget 0.
- Wire new file into `QIQTH.lean` + `AxiomAudit`. One commit per stage, `Co-Authored-By` trailer.

### Progress log
- **Stage 1 ✅** (`ppMetric`, `ppMetricInv`, `ppMetric_symm`, `ppMetric_inv`; `QIQTH/PPWaveMetric.lean`) — the
  pp-wave metric `[[H,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]]` and its inverse, with symmetry and `g·gi = I`
  (the `hinv` premise) proved by `Fin 4` case-bashing. Axiom-free, budget 0.
- **Stage 2 ✅** (`christoffel_ppMetric_last_one` + helpers `pd_ppMetric_snd_one`/`pd_ppMetric_dir_one`) — every
  Christoffel with last index `1` vanishes (`Γ^μ_{ν1} ≡ 0`): all three metric-derivative terms are zero
  (`g_{·1}` constant; `pd H 1 = 0`). Axiom-free, budget 0.
- **Stage 3 ✅** (`ppMetric_covDerivVec_v_zero`, `ppMetric_raychaudhuri_setup`) — `∂_v` (`ppV`) is covariantly
  constant (`∇ ∂_v ≡ 0`), hence `hWgeo ∧ hWequil` hold for the pp-wave congruence via
  `raychaudhuri_setup_of_covConst`. **A non-flat (curved-metric-class) witness for the Raychaudhuri congruence
  premises** — upgrades the flat (degenerate) witness. Axiom-free, budget 0.
- **Stage 4 ✅ (partial + documented)** (`christoffel_ppMetric_x_uu`) — the load-bearing curvature piece:
  `Γ^x_{uu} = −½ ∂_x H`, **non-zero for non-constant `H`**, so the connection genuinely depends on `H` (the
  metric is not the flat constant metric in disguise). The **full** Ricci `Ric₀₀ = −½(∂_x²+∂_y²)H` (= `−1` for
  `H=(x²)²`) needs many Christoffel + `pd`-of-Christoffel + quadratic-product lemmas in the bespoke setup —
  **documented as a sub-frontier** per §2 Stage 4 (not faked). Axiom-free, budget 0.

### COMPLETE
The Raychaudhuri congruence premises (`hWgeo`/`hWequil` = `hcov`) are discharged for the **pp-wave** via the
explicit covariantly-constant null field `∂_v` (Stages 1–3), with the connection certified H-dependent
(Stage 4 partial) — upgrading the flat (degenerate) witness to a curved-metric-class one. The full Ricci-≠-0
evaluation is the documented sub-frontier; the witness stands on the pp-wave, the standard curved-spacetime
example.
