# T3-GR-Raychaudhuri — discharge `hWgeo` / `hWequil` (finish the GR geometric floor)

**Status:** PLAN (not started). **Track:** GR. **Goal:** discharge the two Raychaudhuri congruence premises
`hWgeo` (geodesic) and `hWequil` (equilibrium) of the QIQT→GR capstones — the last *non-physics* labelled
inputs — by reducing them to a single clean geometric condition and discharging that for explicit metrics.

## 0. The target

`qiqt_gr_freefield_complete` (and the ladder `_localized'`/`_nullEnergy`/`_geom`/`_thermo`/`_gaussian`) take, per
null generator `(x,v)`, a congruence `W x v : Point 4 → Fin 4 → ℝ` with:

- `hWgeo  : ∀ y μ, ∑ ν, W x v y ν · covDerivVec g gi (W x v) ν μ y = 0`  (autoparallel / geodesic)
- `hWequil: ∑ μ ν, covDerivVec g gi (W x v) μ ν x · covDerivVec g gi (W x v) ν μ x = 0`  (shear+expansion = 0 at `x`)

plus `hWx : W x v x = v` and `hWC : smooth`.  `hFocus_of_raychaudhuri` consumes these to *prove* the focusing
identity `ad = R_kk`; so these are the genuine Jacobson local-Rindler-horizon **setup**.

## 1. The lever

`covDerivVec g gi V ν μ y = ∂_ν V^μ(y) + ∑_σ Γ^μ_{νσ}(y)·V^σ(y)`  (`Curvature.lean:243`).  If `V` is
**covariantly constant** — `covDerivVec g gi V ≡ 0` — then both premises hold *trivially* (substitute 0):
`hWgeo = ∑ν Vν·0 = 0`, `hWequil = ∑ 0·0 = 0`.  And for a **constant metric** (`christoffel_constMetric`,
`QiqtGrWitness.lean`, already proved: `Γ ≡ 0`) a **constant** congruence `W ≡ v` has `covDerivVec ≡ 0`
(`∂(const)=0` via `pd_const`, `Γ≡0`).  So the congruence bundle is fully dischargeable for flat space.

## 2. Stages (each axiom-free, green-building, one commit)

### Stage 1 — abstract reduction `raychaudhuri_setup_of_covConst` *(trivial; the clean statement)*
New file `QIQTH/RaychaudhuriCongruence.lean`.  Prove: for any `g gi` and vector field `V` with
`hcov : ∀ y μ ν, covDerivVec g gi V μ ν y = 0`, both
`(∀ y μ, ∑ ν, V y ν · covDerivVec g gi V ν μ y = 0)` and
`(∑ μ ν, covDerivVec g gi V μ ν x · covDerivVec g gi V ν μ x = 0)` hold.  Proof: `simp [hcov]`.
**This reduces `hWgeo`+`hWequil` to the single condition "W is covariantly constant."**  Risk: low.

### Stage 2 — flat covariantly-constant witness *(uses `christoffel_constMetric`)*
In the same file: for a constant metric `g := fun _ => G` and a constant congruence `W := fun _ _ => v`,
prove `covDerivVec g gi W ≡ 0` (via `pd_const` + `christoffel_constMetric`).  Hence `hWgeo`/`hWequil`/`hWx`/`hWC`
all hold.  **Discharges the full congruence bundle for flat space** — a non-vacuity certificate that the
Raychaudhuri premises are satisfiable.  Honest caveat: flat ⟹ `Ric=0` ⟹ the Einstein conclusion is the
*vacuum* case (the existing `QiqtGrWitness` already certifies that degenerate slice; this isolates the
congruence premises specifically).  Risk: low.

### Stage 3 — capstone variant `qiqt_gr_freefield_complete_covCong` *(wire the reduction in)*
New capstone built on `qiqt_gr_freefield_complete` that takes
`hcov : ∀ x v y μ ν, covDerivVec g gi (W x v) μ ν y = 0` instead of `hWgeo`+`hWequil`, deriving them via Stage 1.
Net: the two Raychaudhuri premises collapse to **one** clean geometric condition (W covariantly constant).
Point `tracks/gr.toml` at it (or keep `complete` and add this as spine).  Risk: low–medium (large signature).

### Stage 4 — the non-degenerate frontier *(document; attempt only if tractable)*
A genuinely non-flat witness: a **pp-wave** metric `ds² = 2 du dv + H(u,x,y) du² + dx² + dy²` admits the
covariantly-constant null field `∂_v` (so `covDerivVec(∂_v) ≡ 0`) with `Ric_uu = −½(∂_x²+∂_y²)H ≠ 0` — a
non-degenerate spacetime where the congruence bundle is explicitly satisfied.  Requires computing the pp-wave
Christoffels in the `Point 4`/`christoffel` setup (substantial).  If Mathlib-out-of-reach, **document as the
cited geometric frontier**: the general curved geodesic congruence needs geodesic-ODE / exp-map machinery
Mathlib lacks for this setup.

## 3. Honest outcome

`hWgeo`+`hWequil` **reduced** to the single condition "W covariantly constant" (Stage 1+3), and **fully
discharged** for flat space (Stage 2, non-vacuity for the congruence bundle).  The general curved case stays the
cited geometric frontier; the pp-wave (Stage 4) is the next concrete non-degenerate witness.  Removes the last
*non-physics* labelled input from the chain modulo that frontier — what remains is genuine physics
(`hbound`/`hcap`/`hK` = H2/FQ) + matter EOM `hKG` + geometry scaffolding.

## 4. Verification (per stage)
- `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green.
- `#print axioms <thm>` = `[propext, Classical.choice, Quot.sound]`; `bash scripts/axiom_budget_check.sh` = budget 0.
- Wire new files into `QIQTH.lean` + `AxiomAudit`. One commit per stage, `Co-Authored-By` trailer.
- After Stage 3, regenerate `tracks/gr.toml` report to record the surface change.

### Progress log
- **Stage 1 ✅** (`raychaudhuri_setup_of_covConst`, `QIQTH/RaychaudhuriCongruence.lean`) — `hWgeo`+`hWequil`
  reduced to the single condition "W covariantly constant" (`covDerivVec g gi V ≡ 0`). Axiom-free, budget 0.
- **Stage 2 ✅** (`covDerivVec_constMetric_const`, same file) — flat witness: in a constant metric a constant
  congruence is covariantly constant, so the congruence bundle holds for flat space (non-vacuity certificate).
  Axiom-free, budget 0. Next: Stage 3 (capstone variant `_complete_covCong` taking `hcov` instead of
  `hWgeo`+`hWequil`).
