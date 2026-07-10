# LORENTZIAN LADDER campaign — causal structure as output: flat spacetime continuous, then curved

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
