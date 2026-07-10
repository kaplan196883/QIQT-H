# LORENTZIAN LADDER campaign — causal structure as output: flat spacetime continuous, then curved

## STATUS: CAMPAIGN COMPLETE (2026-07-10) — all four bricks landed FULL, axiom-free, std-3, budget 0

- **L1+L2 DONE** — `700fbb1d` `MinkowskiDiamond.lean`: τ + the reverse triangle + flat midpoint
  uniqueness + **THE CAUSAL NO-GO** (unweighted longest chain = Manhattan time 2 ≠ √2 — the
  machine-checked reason causal sets need random sprinkling; BLMS/Brightwell–Gregory cited).
- **L3 DONE (the crux)** — `2a48488e` `CausalStencil.lean` (697 lines): the weighted causal
  stencil; exact upper (iterated reverse triangle), even-distribution lower, capstone
  `causal_stencil_pinch` — **FLAT SPACETIME CONTINUOUS** (two-sided uniform pinch, honest
  near-light-cone disjunction).
- **L4 DONE (the finale, no checkpoint needed)** — `ac30d08d` `DeSitterTime.lean` (502 lines):
  dS₂; `reversed_cauchy_schwarz` (STRONGER than planned: timelike w, ARBITRARY w');
  **`tauDS_reverse_triangle`** with the explicit opposite-cone branch hypothesis — to our
  knowledge the first machine-checked curved-spacetime reverse triangle inequality; geodesic
  additivity (equality case); `dS_strict_defect` + `dS_causal_horizon` vs
  `minkowski_common_future` (the non-Minkowski witnesses).
- **Convention correction (L4, vs the plan below):** the plan's τ = arccos(B)/bounded-by-π was
  the SPHERE convention — wrong for dS. Correct: timelike ⟺ B(p,q) > 1, τ = arcosh(B),
  unbounded. And the planned antipodal double-midpoint witness was geometrically wrong
  (B(p,−p) = −1 is NOT chronological; dS timelike geodesics do not refocus — antipodal
  horizons); replaced by the strict-defect + causal-horizon witnesses.
- Commits LOCAL, unpushed (standing constraint). The honest firewall below is binding and
  restated in every file header + AxiomAudit pin.

**Date:** 2026-07-10. **Parents:** the completed Riemannian/GH program + `HawkingWick.lean` (the
reverse-triangle Cauchy–Schwarz seed `sqrt_mul_add_le` is already in). **User directive:** run the
Lorentzian ladder (L1–L4).

## Why this is genuinely new
Spacetime is NOT a metric space: the fundamental object is a time-separation function τ with the
REVERSE triangle inequality (timelike geodesics MAXIMIZE). GH convergence does not apply; the
intrinsic Lorentzian convergence notion (Lorentzian length spaces, Kunzinger–Sämann) is research
mathematics with no Mathlib support — our convergence statements are EXTRINSIC-UNIFORM pinches
(the I3/G3 style), honestly labelled.

## Bricks

- **L1+L2 — `MinkowskiDiamond.lean` (one brick, both small): the flat target + the causal no-go.**
  L1: null coordinates on ℝ²; `causalLE p q := p.1 ≤ q.1 ∧ p.2 ≤ q.2`;
  `tau p q := if causal then √(2·Δu·Δv) else 0`. Theorems: nonneg, self = 0, τ > 0 ⟺ chronological
  (both strict), and **THE REVERSE TRIANGLE INEQUALITY** `tau p r ≥ tau p q + tau q r` for
  `p ≼ q ≼ r` — exactly `HawkingWick.sqrt_mul_add_le`.
  L2 (the causal no-go, the Lorentzian twin of IsotropyNoGo): on the causal lattice (grid, strict
  product order), every chain from (0,0) to (m,n) has ≤ m+n steps (the rank u+v strictly increases)
  and the staircase achieves it — so the scaled UNWEIGHTED longest-chain time at the full diagonal
  (N,N) is 2, while τ = √2, and **2 ≠ √2**: pure hop-counting on the deterministic causal lattice
  recovers the WRONG (Manhattan) time. This is the machine-checked reason the causal-set program
  (BLMS) needs random sprinkling.
- **L3 — `CausalStencil.lean` (the crux): flat spacetime continuous.** Stencil chains on the grid:
  steps (α, β) ∈ [1..R]² (chronological, stencil-bounded); chain weight = Σ √(2αᵢβᵢ)/N (per-step
  proper times). (a) UPPER: every chain weight ≤ τ — iterated `sqrt_mul_add_le` (induction; NO error
  term, exact). (b) LOWER: the even-distribution chain — waypoints `(⌊i·m/k⌋, ⌊i·n/k⌋)`, k ≈
  ⌈max(m,n)/R⌉, floor-difference steps in [⌊m/k⌋, ⌈m/k⌉] ⊆ [1..R]; total weight ≥ √(2(m−k)(n−k))
  ≥ τ·N − √(2k(m+n)) (√(a−b) ≥ √a − √b). (c) near-null pairs (min < k): τ itself ≤ the error scale —
  the bound is uniform. (d) CAPSTONE (R_N = Nat.sqrt N): ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ causal grid
  pairs: (∀ chains, weight ≤ τ) ∧ (∃ chain, weight ≥ τ − ε) — **the two-sided pinch of the discrete
  proper time, uniform on the diamond: FLAT SPACETIME CONTINUOUS** (stated via ∀/∃ bounds — no max
  operator needed; a Finset-sup packaging only if free).
- **L4 — `DeSitterTime.lean` (the curved target; CRUX, CHECKPOINT PERMITTED): dS₂.**
  The 2D de Sitter spacetime = the one-sheeted hyperboloid {x : ℝ³ // −x₀² + x₁² + x₂² = 1} with the
  ambient bilinear form B(x,y) = −x₀y₀ + x₁y₁ + x₂y₂; time separation of causally related points:
  τ = arccos(B(p,q)) (constant positive curvature — the LORENTZIAN SPHERE: timelike geodesic lengths
  bounded by π). Deliverables: τ well-defined + basic facts; **the reverse triangle inequality**
  (the Lorentzian mirror of Mathlib's spherical `angle_le_angle_add_angle` — the crux; attempt by
  mirroring that proof with signature flips / reversed Cauchy–Schwarz for timelike vectors);
  **the non-flatness theorem** — the antipodal pair (p, −p) at τ = π has MULTIPLE timelike midpoints
  (the fifth use of the midpoint invariant, now in reverse-triangle form: flat-Minkowski timelike
  midpoints are unique via the equality case of Cauchy–Schwarz). If the reverse triangle genuinely
  walls after sustained effort: CHECKPOINT with τ + the flat-midpoint-uniqueness half; L1–L3 is the
  shipped value. Discrete approximation of dS₂: CITED frontier (no Lorentzian GH exists to target).

## HONEST scope firewall (binding)
- The causal order, the stencil, and the per-step weights are INSERTED (the weights presuppose the
  local Minkowski interval — as the induced-metric clouds did); the "pure order + counting" ideal is
  precisely what L2 proves IMPOSSIBLE deterministically (randomness = cited).
- Convergence is EXTRINSIC-UNIFORM (pinch), not intrinsic-Lorentzian-GH (no settled notion exists).
- 1+1 dimensional; the diamond/dS₂ are INPUTS; smooth Einstein-grade curvature out of scope;
- the dynamical source remains THE open wall; NOT GR, NOT numerical-G, NOT QG.

## Discipline
Unchanged: ONE bg fable subagent per brick (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 probe + no-sorry grep); AxiomAudit pins; wire `QIQTH.lean`; full
budget check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths;
NO sorry; hypotheses never axioms; checkpoint precisely at genuine walls.

## SYNTHESIS (2026-07-10, post-campaign): how the Lorentz-gate verdict bears on this reconstruction

The three executed Lorentz gates (CPSUV stress test + diamond-tip + state-level, 2026-07-02; canonical
"single surviving conclusion" at `LEAN_RESULTS_INVENTORY.md` §2 top) and this ladder turn out to be two
views of the same structure:

1. **Lattices are codings, not ontology — the firewall is now FORCED, not optional.** Every discrete
   structure in the reconstruction program (stencil grids, the causal lattice, the state-wire) is a
   frame-anchored deterministic lattice. The gates prove that promoting any such structure to physical
   microstructure (a literal finite-capacity cutoff with interactions on it) radiatively generates
   unsuppressed `Δc²` and is experimentally dead. The GH limits and the L3 pinch are therefore
   *kinematic recoverability theorems* — the continuum is decodable from discrete data in one chosen
   frame, legitimate because the TARGET (the metric space; the invariant τ) is frame-independent. The
   alternative (ontic-lattice) reading is falsified, by theorem.

2. **L2/L3 is the geometric shadow of the CPSUV dichotomy.** Unweighted counting on the frame-anchored
   lattice (L2) leaves an O(1) defect NO refinement removes (Manhattan 2 vs τ = √2 — a speed-splitting
   floor); inserting the invariant per-step Minkowski weight BEFORE the limit (L3) makes the defect
   decouple (→ 0 uniformly). CPSUV says the identical thing radiatively: frame-anchored regulator →
   unsuppressed `g²/12π²`; covariance before the loop → `Δc² = 0` identically. Same moral, machine-checked
   twice: Lorentz invariance cannot be recovered in a limit from frame-anchored counting — it must be in
   the data before the limit.

3. **Compactness decides — why the Euclidean half could average and the Lorentzian half had to insert.**
   The Euclidean stencil program recovers isotropy in the limit (increasing stencil `R_N → ∞`) because
   `SO(d)` is COMPACT. The diamond-tip test proved the Lorentzian analogue impossible at the regulator
   level (`boostAvg_diverges` — boost noncompactness), and L2 is the deterministic-counting face of the
   same fact. Hence L3 *inserts* the invariant weight (and causal sets resort to RANDOM sprinkling — the
   only other frame-free option for discrete data).

4. **One wall, two names.** This program's cited frontier ("the dynamical source" — what dynamics supplies
   the weights/correlations we insert) and the gates' sole remaining LV door ("the dynamical-realization
   gap" — only a non-equivariant enforcement mechanism reopens Lorentz violation) are the SAME object.
   Sharpened constraint: whatever eventually supplies the stencil weights must be an EQUIVARIANT,
   state-level mechanism; a frame-carrying dynamical source is pre-falsified.

5. **Suggested next moves (not done):** (a) a *sprinkled L3* — formalize the Brightwell–Gregory
   random-geodesic statement (longest chain in a Poisson sprinkling ∝ τ), completing the L2/L3 story from
   the randomness side; (b) *state-level decoding* — decode geometry from per-diamond covariant entropy
   data (`Q_D` on the diamond net) instead of cut-rank profiles on a fixed wire, connecting
   geometry-as-output directly to the surviving branch of the capacity postulate. L4 (dS₂) is untouched
   by all of this — pure continuum target-side, no regulator anywhere in it.

Net: the gates threaten no theorem of this ladder — they fix its interpretation (codings, not ontology),
explain its internal pattern (insertion beats averaging; compactness decides), and fuse its open wall with
the capacity postulate's last open door into one target: an equivariant, state-level dynamical source.
