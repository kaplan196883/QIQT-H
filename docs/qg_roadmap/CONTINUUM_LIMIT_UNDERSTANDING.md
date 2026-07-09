# Moving to the CONTINUUM — the honest understanding + tractable path

**Date:** 2026-07-09. **Basis:** the metric-from-state results (M1–M5, M3b, 2D grid) + GPT-5.5-pro
critical analysis. **Question:** we have geometry as an OUTPUT of an entangled state (a finite
graph-metric that *samples* a continuum metric at grid points). How do we genuinely move to the
continuum, and where is that honest vs. where does it become research-grade?

## 1. What we have vs. what "continuum" requires

**Have (SAMPLING):** `square_grid_scaledDist_eq_l1` proves the rescaled N×N grid graph-metric equals
the continuum L¹ (taxicab) metric on `[0,1]²` **exactly, at the N² grid points**. This is an equality
*at sample points*, NOT a limit.

**Continuum = a LIMIT/convergence statement.** The finite entanglement geometries `X_N` must converge,
as metric spaces, to a continuum `([0,1]^d, L¹)`. Two honest formulations:

- **Route A (ambient Hausdorff, tractable):** the grid points `S_N ⊂ [0,1]²` are an ε-net with
  `ε = 1/(N-1) → 0`; since the intrinsic grid metric already equals the ambient L¹ metric restricted
  to `S_N` (proved), continuum-emergence reduces to **net density** — every point of `[0,1]²` is within
  `1/(N-1)` of a grid point — giving `hausdorffDist(S_N, [0,1]²) → 0` in the common space.
- **Route B (intrinsic Gromov–Hausdorff, deeper):** the *abstract* finite metric spaces `X_N` converge
  in Mathlib's `GromovHausdorff.GHSpace` to `([0,1]², L¹)` — no pre-given ambient. Mathematically this
  FOLLOWS from Route A (an isometric ε-net embedding gives a GH bound `d_GH(X_N,Y) ≤ ε_N`), but as an
  *emergence* claim it is cleaner.

**Verdict (GPT-5.5-pro):** Route A is honest but **extrinsic** — it shows the finite geometries are
increasingly-fine isometric samples of a *presupposed* continuum; it does not derive the square, its
topology, dimension, or metric intrinsically. Route B is the invariant "emergence" statement, provable
*from* Route A. Best honest phrasing: **"embedded Hausdorff convergence to a presupposed L¹ continuum,
which yields the intrinsic GH convergence — but the construction still uses the chosen continuum model."**

## 2. The honesty caveats (what the continuum limit does NOT give)

1. **L¹/taxicab, NOT Euclidean/Riemannian.** The square lattice rescales to the taxicab (Finsler)
   metric — it CANNOT also converge to Euclidean (GH limits are unique up to isometry; the L¹ square is
   not isometric to the round square). Getting the Euclidean/Riemannian continuum is a genuine hard
   problem: fixed bounded-degree periodic lattices give *polyhedral norms* (square→L¹, hex→hexagonal),
   never the Euclidean disk. **Isotropy restoration** (the lattice→continuum rotation/Lorentz-invariance
   wall) is research-grade — tractable only via weighted/random-geometric/increasing-stencil graphs, and
   deriving it from a *local entanglement/dynamical* model is open.
2. **Dimension is put in** — the grid is 2D by construction; dimension does not emerge from entanglement
   scaling.
3. **The entanglement pattern is engineered** — a kinematic construction, not a dynamical theorem that a
   natural Hamiltonian/path-integral *produces* it (the dynamical-source wall).
4. **Topology + boundary are put in** (unit square with boundary — not derived).
5. **No measure/volume** (GH is metric-only; volume/measured-GH is a further step).
6. **No curvature/smooth structure** (GH to a metric space ≠ Riemannian curvature convergence).
7. **No Lorentzian/causal structure** (`GHSpace` is compact metric; QG spacetime is Lorentzian/causal/
   often noncompact — a different formal problem).
8. **No stability/universality** (one engineered family converges; robustness under perturbation unshown).

## 3. The tractable Lean path (Route A → B)

- **C1 (net density → Hausdorff, the honest continuum step):**
  `hausdorffDist_le_of_subset_of_net` (generic: `S ⊆ K`, every `y∈K` within `ε` of `S` ⟹
  `hausdorffDist S K ≤ ε`), then
  `square_grid_hausdorffDist_tendsto : Tendsto (fun N => hausdorffDist (gridSet (N+2)) univ) atTop (𝓝 0)`
  — converts the sampling theorem into a genuine continuum-limit theorem in `([0,1]², L¹)`. Net bound
  via nearest-integer `abs_sub_round` (`≤ 1/2` per axis ⟹ mesh `1/(N-1)`, or a looser floor bound).
  Effort: low/moderate. **This is the recommended next brick.**
- **C2 (GH bridge, Route B):** `ghDist_le_of_isometry_epsDense` (isometric ε-dense embedding ⟹
  `ghDist ≤ ε`) via the correspondence `R(x,y) ⟺ d_Y(fx,y) ≤ ε` (isometry ⟹ `|d_X−d_Y| ≤ 2ε`), then
  `square_grid_toGHSpace_tendsto : toGHSpace(X_N) → toGHSpace([0,1]²,L¹)`. Uses Mathlib
  `GromovHausdorff.toGHSpace` + a GH-inequality helper. Effort: moderate; don't start directly in
  `GHSpace` (fight the quotient API before the geometry).

Mathlib support confirmed present: `GromovHausdorff.GHSpace`/`toGHSpace`/`ghDist`, `Metric.hausdorffDist`
+ `hausdorffDist_le_of_mem_dist`/`hausdorffDist_le_iff`, `abs_sub_round` (nearest-integer ≤ 1/2).

## 4. The precise research-grade wall

Continuum *convergence* (Hausdorff/GH) is NOT the wall — it's tractable and honest as a **kinematic L¹
toy continuum limit**. The wall is:

> deriving an **intrinsically defined, dynamically produced, isotropic (Riemannian) or Lorentzian**
> continuum geometry — with dimension / topology / measure / curvature **emerging** rather than built
> into the graph family.

So the honest program: C1 (Hausdorff limit) → C2 (GH limit) gives a machine-checked "finite entanglement
geometries converge to a continuum metric space" — a real, novel formal result — while the leap to
Riemannian/Lorentzian/dynamical/emergent-dimension geometry stays the named QG frontier. Do NOT claim
the toy L¹ limit is emergent spacetime or QG.
