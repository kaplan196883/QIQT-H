# HAWKING–EUCLIDEAN campaign — imaginary time: the cone as near-horizon geometry

**Date:** 2026-07-10. **Parents:** the cone campaign (B2a/B2b, K1–K4) + the modular core (BoostKMS).
**User directive:** "use Hawking's trick / imaginary time" — Wick rotation turns Lorentzian signature
into Riemannian, i.e. into exactly the metric-space world where the completed GH machinery lives.

## The dictionary (the physics reading of what is already proved)

- Wick-rotated flat sections ↔ the flat square/cube limits (DONE).
- **Periodic imaginary time = thermal state** (period β): `AddCircle β` IS compactified Euclidean
  time ↔ the torus/circle limits (DONE).
- **Euclidean Rindler / black-hole near-horizon geometry**: the (r, τ_E) section near a horizon is a
  CONE of angle θ = κ·β ↔ **our `Cone θ`** (DONE: metric space, curvature theorem, GH limits,
  intrinsic hop metric, state-decoded). Smoothness (no conical singularity) ⟺ θ = 2π ⟺ β = 2π/κ =
  **the Hawking–Unruh temperature**. Our `cone_no_isometric_embedding_into_inner` (θ < 2π) already
  says: off-temperature Euclidean sections are genuinely non-flat.
- The replica family = `Cone (2πn)`; the entropy derivative at θ = 2π = the conical-entropy formula
  (CITED, not attempted — needs partition functions/heat kernels).

## Bricks

- **E2 — `ConeFlat.lean` (the substantial brick, FIRST): flatness ⟺ θ = 2π.**
  (i) The explicit isometry `Cone (2π) → ℂ` (apex ↦ 0, `some (r, φ) ↦ r·e^{iφ}` via a representative;
  isometry because coneDist = lawCos(‖class‖) and the planar dist = lawCos(representative gap), equal
  by 2π-periodicity+evenness of cos — K2's `norm_sub_polar` is the bridge); range = the closed unit
  disk (surjectivity via `Complex.arg`, the K2 polar machinery). ℂ is a real inner-product space, so
  this is the exact CONVERSE of the no-embedding theorem.
  (ii) **THE CAPSTONE `cone_flat_iff` (0 < θ ≤ 2π)**: `(∃ f : Cone θ → ℂ isometric) ↔ θ = 2π` —
  forward = `cone_no_isometric_embedding_into_inner` (contrapositive), backward = (i). The geometric
  half of "the Unruh/Hawking temperature is the unique smooth period", machine-checked.
- **E3 — `HawkingWick.lean` (packaging): the Wick identities + the two-faces pairing.**
  (i) E1 content: `σ_L(t,x) = −t² + x²`, `σ_E(τ,x) = τ² + x²`, the continuation identity
  `σ_E(τ,x) = −(iτ)² + x²` over ℂ (ring), the null-coordinate identities (t² − x² = 2uv).
  (ii) The pairing: `cone_flat_iff` (geometric) alongside the repo's boost-KMS-at-2π
  (`stripKMSrvd_boostUnitary`, BoostKMS.lean — the algebraic face); a formal conjunction ONLY if the
  types align cheaply, else a docstring citation — do NOT force it.
  (iii) The thermal reread of the torus results (`AddCircle β` = thermal circle) — docstring-level +
  at most a thin renaming def.

## HONEST scope firewall (binding)
- The geometry is proved; **the physics dictionary (θ ↔ κβ, cone ↔ horizon, period ↔ temperature) is
  an INTERPRETATION documented in docstrings and CITED to the literature** (Gibbons–Hawking), not a
  formalized derivation from field theory.
- Wick rotation is legitimate for static/thermal situations — it does NOT deliver generic dynamical
  curved spacetime and it LOSES causal structure (no causal order in Euclidean signature); the
  Lorentzian ladder (L1–L4, separate plan) remains the honest path to causality-as-output.
- The replica/entropy derivative at θ = 2π: CITED frontier.
- θ/β remain INPUTS; the dynamical source remains the open wall; NOT GR, NOT numerical-G, NOT QG.

## Discipline
Unchanged: ONE bg fable subagent per brick (own module, NO git); independent verification (rebuild +
scratchpad `#print axioms` std-3 probe + no-sorry grep); AxiomAudit pins; wire `QIQTH.lean`; full
budget check (LONG ~420000ms, budget 0); commits LOCAL ONLY — DO NOT PUSH; explicit git paths;
NO sorry; hypotheses never axioms.
