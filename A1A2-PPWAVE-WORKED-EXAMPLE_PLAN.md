# A1+A2 — a concrete (pp-wave) worked example of the QIQT→GR capstone

**Status:** PLAN (not started). **Track:** GR. **Goal:** instantiate `qiqt_gr_freefield_complete_covCong` with an
**explicit curved spacetime** (the pp-wave metric + an explicit tetrad + a concrete Klein–Gordon field), so the
**geometry, frame, congruence, matter-EOM and Raychaudhuri** premises are all discharged for a concrete
non-flat model — yielding a single **"QIQT→GR holds for *this* pp-wave spacetime"** theorem.

## 0. Honest scope (stated up front)

The capstone has **irreducible** inputs that no worked example can discharge — they are the theory's physics:
`hbound` (dynamical FQ capacity bound), `hcap` (FQ area-capacity identification), `hK`/`hS`/`hA` (the
entropy/heat/area realization derivatives — Gap-2). So the deliverable is a **conditional** worked example: the
Einstein equations for the pp-wave follow **given** the FQ postulate + realization, with everything *geometric
and matter-kinematic* discharged concretely.  This is the honest analogue of `QiqtGrWitness`'s flat/vacuum
satisfiability witness (`qiqt_bekenstein_gives_gr_satisfiable`), upgraded to a **curved** spacetime and the
**most-discharged** capstone.

## 1. The pieces (what exists / what's needed)

Already proved (`PPWaveMetric.lean`): `ppMetric`/`ppMetricInv`, `ppMetric_symm`, `ppMetric_inv` (`hinv`),
`ppMetric_covDerivVec_v_zero` (`hcov` for `W=∂_v`).  `gm i j = if i=j then (if i=0 then -1 else 1) else 0`
(Minkowski).  Needed: smoothness, an explicit tetrad, the KG field.

## 2. Stages (each axiom-free, green-building, one commit)

### Stage 1 — pp-wave smoothness `hCg`/`hCgi` *(tractable)*
For a smooth `H` (use `H := fun x => (x 2)^2`, `ContDiff` via `(contDiff_apply ℝ ℝ 2).pow 2`): prove
`∀ a b, ContDiff ℝ ⊤ (fun y => ppMetric H y a b)` and the same for `ppMetricInv` — each component is `H`, `-H`,
or a constant, so `fin_cases a <;> fin_cases b <;> simp [ppMetric] <;> exact (contDiff/contDiff_const)`.
**Risk: low.**

### Stage 2 — the explicit tetrad `P`/`Pinv`, prove `hcong` + `hPP`/`hPP'` *(medium)*
The `(x,y)` block of `gm` is already `δ`; the `(u,v)` block `[[H,1],[1,0]]` (signature `(−,+)`) diagonalizes to
`diag(−1,1)` via the explicit frame (one valid choice, `a=1`):
```
P₀ = ((H−1)/2, 1, 0, 0),  P₁ = ((H+1)/2, 1, 0, 0),  P₂ = (0,0,1,0),  P₃ = (0,0,0,1)
```
giving `g_{ij} = ∑_{kl} P_{ki} gm_{kl} P_{lj}` (`hcong`).  Provide `Pinv` (the dual frame) and prove `hPP`/`hPP'`
(`P·Pinv = I`).  Both by `Fin 4` case-bashing + the `(u,v)` algebra in `H`.  **Risk: medium** (the explicit
inverse-frame algebra).

### Stage 3 — the pp-wave geometric data bundle *(compose)*
Package every *geometric* premise of the capstone (`hsymm`, `hsymm_gi`, `hinv`, `hCg`, `hCgi`, `hPP`, `hPP'`,
`hcong`, `W=∂_v`, `hWx`, `hWC`, `hcov`) into a reusable bundle/section, so the geometry side of
`complete_covCong` is concretely realized for the pp-wave.  **Risk: low** (composition).

### Stage 4 — a concrete KG field `hKG` *(hard — curved PDE; fallback documented)*
Construct `φ` with `boxField φ (ppMetric H) (ppMetricInv H) x = m² φ x`.  The pp-wave d'Alembertian is
`□ = 2∂_u∂_v − H∂_v² + ∂_x² + ∂_y² + (connection)`.  Attempt a tractable ansatz (e.g. `φ` linear in `v` plus a
transverse profile) and a matching `m`.  **Risk: high** — solving KG on a curved background in the bespoke
setup.  Fallback per discipline: if intractable, **document** the standard pp-wave KG mode and either (a) carry
`hKG` as a labelled input of the worked example, or (b) use the `m=0` massless case if it admits an explicit
solution.  Do **not** fake `boxField = m²φ`.

### Stage 5 — the worked-example theorem `qiqt_gr_ppwave`
Instantiate `qiqt_gr_freefield_complete_covCong` with the Stage-3 geometry + Stage-4 field (or carrying `hKG`),
leaving **only** the irreducible FQ/realization inputs (`hbound`/`hcap`/`hK`/`hS`/`hA`, plus the record-law
data) as hypotheses: **the Einstein equations `a·kgStress = G + Λg` for the explicit pp-wave spacetime,
conditional on the FQ postulate + realization.**  **Risk: medium** (threading the large signature).

## 3. Honest outcome
A concrete **curved-spacetime** instance of the QIQT→GR theorem: geometry, frame, congruence, Raychaudhuri
congruence (and, if Stage 4 lands, the matter EOM) all discharged explicitly for the pp-wave, with the
conclusion conditional on the genuine FQ postulate + Gap-2 realization (which no worked example can remove).
Upgrades the existing flat/vacuum witness to a curved, most-discharged one.

## 4. Verification (per stage)
- `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
  `bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit`; one commit per stage.

### Progress log
- **Stage 1 ✅** (`ppMetric_contDiff`, `ppMetricInv_contDiff`; `QIQTH/PPWaveMetric.lean`) — the metric and
  inverse components are `C^∞` for smooth `H` (each is `H`, `−H`, or a constant), giving `hCg`/`hCgi`.
  Axiom-free, budget 0.
- **Stage 2 ✅** (`ppFrame`/`ppFrameInv`, `ppFrame_cong`, `ppFrame_pp`, `ppFrame_pp'`, `ppMetricInv_symm`) — the
  explicit tetrad diagonalizing the `(u,v)` block `[[H,1],[1,0]] → diag(−1,1)`; `hcong` (`g = PᵀgmP`),
  `hPP`/`hPP'` (`P·Pinv=I`), and `hsymm_gi`. Axiom-free, budget 0.
- **Stage 3+4+5 ✅** (`qiqt_gr_ppwave`, `QIQTH/QiqtGrPPWave.lean`) — the worked-example theorem: the Einstein
  equations `a·kgStress = G + Λg` for `g = ppMetric H` (a curved pp-wave) with **every geometric premise
  discharged concretely** (symmetry, inverse, smoothness, the tetrad's congruence + invertibility). Per §0/§Stage4,
  the matter EOM `hKG` (curved-background KG field — documented frontier), the FQ/realization inputs
  (`hbound`/`hcap`/`hK`/`hS`/`hA`), the record-law data, and a covariantly-constant congruence `W` are **carried**
  (not faked). Axiom-free, budget 0.

### COMPLETE
A concrete **curved-spacetime** instance of QIQT→GR: all geometry (metric, inverse, smoothness, explicit tetrad
congruence) discharged for the pp-wave, the conclusion conditional on the genuine FQ postulate + Gap-2
realization + the matter field — a curved upgrade of the flat/vacuum `QiqtGrWitness`. The curved KG field
(Stage 4) is carried as the documented frontier per the no-faking discipline.

**Note (finding):** the most-discharged form `qiqt_gr_freefield_complete_covCong` (with `hcov` = `W` covariantly
constant) is instantiable here by *carrying* `W`; a fully-`W`-free pp-wave instantiation is blocked because only
`∂_v` is covariantly constant in the pp-wave, not congruences through *all* null directions — so the
covariant-constancy reduction trades the geodesic-ODE frontier for a per-generator existence one. Documented.
