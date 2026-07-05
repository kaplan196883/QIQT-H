# THE WILLIAMSON CAMPAIGN — N-mode symplectic diagonalization, Youla carried (W1–W6)

**Status:** ACTIVE (2026-07-05). **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
**Consult:** fable high-reasoning agent ae88cddd312739cba (2026-07-05) — NOT a wall; a genuine
4–6 increment house-style campaign, matrix sqrt de-risked in-repo, single carry = Youla.

## Binding verdict

Attempt the core, carry the analytic frontier (the lesson from max-flow=min-cut). Williamson's
theorem: for real symmetric PD 2n×2n M, ∃ symplectic S (Sᵀ J S = J) with Sᵀ M S = D⊕D,
D = diag(ν) the symplectic eigenvalues. Toward QG: the symplectic spectrum is the entropy/
holography input (`gaussStateEntropy`). DERIVED: symplectic algebra, matrix sqrt (CFC.sqrt,
proven-working in QIQTH/ArakiEntropy.lean:333), the S-construction, the entropy bridge.
CARRIED (the honest frontier, the `haug` analogue): the **Youla real skew normal form**
(∃ O orthogonal, Oᵀ A O = ⊕ₖ νₖ J₂) — 0 hits in Mathlib, genuinely absent.

Mathlib API (verified): `Matrix.J l R` (fromBlocks 0 (-1) 1 0), `Matrix.symplecticGroup l R`,
`SymplecticGroup.mem_iff'` (Aᵀ J A = J), `J_squared`/`J_transpose`/`symplectic_det` (IsUnit
det; det=1 is a Mathlib TODO — derive (det S)²=1 locally); `Matrix.IsHermitian.spectral_theorem`
+ eigenvalues/eigenvectorUnitary (real via RCLike ℝ); `CFC.sqrt` via `MatrixOrder` scoped
instances + `CFC.sqrt_mul_sqrt_self`/`sqrt_nonneg`/`nonneg_iff_posSemidef`/`inv_sqrt`. Index
type is `l ⊕ l` (NOT Fin 2n) — reuse Mathlib's, do NOT shadow. Repo: `oneModeSympEig` (√(ab−c²)
+ invariance), `gaussStateEntropy := ∑ gaussModeEntropy` + nonneg.

## The increments (new file `QIQTH/WilliamsonNormalForm.lean`)

- [x] **W1 — the WilliamsonDecomp structure + symplectic algebra (guaranteed green).**
  `structure WilliamsonDecomp (M : Matrix (l⊕l) (l⊕l) ℝ)` with fields S (∈ symplecticGroup),
  ν (l→ℝ, nonneg), hDiag : Sᵀ * M * S = fromBlocks (diagonal ν) 0 0 (diagonal ν). Plus
  `sympSpec := ν`; symplectic closure lemmas (one_mem/mul_mem/J_mem, cite Mathlib); det
  lemmas ((det S)²=1 from Sᵀ J S = J ⟹ (det S)²·det J = det J; product_of_diag via
  det_fromBlocks_zero₁₂ + det_diagonal). Risk VERY LOW.
- [x] **W2 — the carried Youla hypothesis.** `structure YoulaDecomp (A) (hA : Aᵀ = -A)`:
  O ∈ orthogonalGroup, ν : l→ℝ, Oᵀ A O = ⊕ₖ νₖ·(J₂ block) — CARRIED (the analytic frontier);
  prove trivial consequences (νₖ nonneg). Risk LOW (it's a def + trivialities).
- [ ] **W3 — ★ williamson_of_youla (the honest reduction, the payoff).** GIVEN M.PosDef + a
  YoulaDecomp of A := M^{1/2} J M^{1/2} (CFC.sqrt, the ArakiEntropy precedent; A antisymmetric
  via Jᵀ=−J + sqrt self-adjoint), CONSTRUCT S := M^{-1/2}·O·(block √ν scaling) and prove
  S ∈ symplecticGroup + Sᵀ M S = D⊕D. May split W3a (S symplectic) / W3b (S diagonalizes).
  Risk MEDIUM-HIGH (block matrix algebra — the campaign's effort). Attempt; checkpoint honestly.
- [ ] **W4 — oneModeSympEig consistency.** n=1 WilliamsonDecomp recovers √(ab−c²), wiring the
  repo lemma into the general structure. Risk LOW-MEDIUM.
- [ ] **W5 — the entropy connection (the QG payoff).**
  `gaussStateEntropy_of_williamson (W) : gaussStateEntropy (W.ν ∘ equiv)`, ≥ 0 given the
  Heisenberg floor ∀ i, ½ ≤ νᵢ (hypothesis). Plumbing to gaussStateEntropy_nonneg. Risk LOW.
- [ ] **W6 — checkpoint + audit** (verbatim HAVE/HAVE-NOT below); plan → COMPLETE.

Order: W1 (green scaffolding) → W2 (carried Youla) → W3 (the reduction, the effort) → W4 →
W5 (payoff) → W6. Each its own commit.

## The checkpoint language (verbatim, W6)

HAVE: "Williamson's symplectic-diagonalization theorem is machine-checked in reduction form on
real symmetric positive-definite covariance matrices: the WilliamsonDecomp structure (a
symplectic S with Sᵀ M S = D⊕D, the symplectic eigenvalues ν), the symplectic-form algebra
(closure, (det S)² = 1), and — the load-bearing content — `williamson_of_youla`: GIVEN the
Youla real-skew normal form of M^{1/2} J M^{1/2} (carried), the Williamson S is CONSTRUCTED
(via the matrix square root, proven-working in the repo) and Sᵀ M S = D⊕D is derived. The
n=1 case recovers the repo's oneModeSympEig = √(ab−c²), and the symplectic spectrum feeds
gaussStateEntropy (the Gaussian entanglement entropy = ∑ per-mode Srednicki entropy). This
reduces the N-mode Williamson gap to the single carried Youla decomposition. Axiom-free, std-3."

HAVE NOT: "The Youla real antisymmetric block-normal-form (∃ O orthogonal, Oᵀ A O = ⊕ νₖ J₂)
is CARRIED as a hypothesis — it is absent from Mathlib (0 hits) and is the genuine analytic
frontier of this campaign, the `haug` analogue. So Williamson is proved CONDITIONAL on Youla,
not unconditionally. No uniqueness of the symplectic spectrum up to permutation is claimed
(deferred); and — separately confirmed — the symplectic spectrum does NOT unlock the area-law
S∝A SCALING (the entropy machinery is area/volume-blind; the boundary-mode count is a distinct
wall). This is the linear-algebra core of Williamson, conditional on Youla, not the full
spectral theorem for antisymmetric matrices."

## Per-increment discipline

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit on
main with the Co-Authored-By: Claude Opus 4.8 trailer; **LOCAL ONLY — no push**; update this
checklist + Progress log AND LEAN_RESULTS_INVENTORY.md; NO sorry; carried inputs (Youla) as
hypotheses/structure fields NEVER Lean axioms; NEVER claim Williamson unconditionally, the
area-law unlocked, a type, or QG solved — honest HAVE/HAVE-NOT; NEVER call an increment too
hard without a genuine attempt + error shown (W3 especially — attempt it, split if needed);
check sibling jobs (stray website/.tex edits — LEAVE THEM) first; explicit git paths only.

## Progress log

- **2026-07-05** — Scoped (consult: NOT a wall; symplectic group + spectral theorem + matrix
  sqrt all in Mathlib/repo; single carry = Youla; W1 guaranteed green, W3 the effort). Applies
  the max-flow lesson (attempt the core, carry the analytic frontier) to the next attemptable
  wall. THE MAX-FLOW-MIN-CUT campaign closed immediately prior.

- **2026-07-05** — **W1+W2 LANDED (green first attempt).** WilliamsonNormalForm.lean:
  WilliamsonDecomp structure (S∈symplecticGroup, ν nonneg, Sᵀ M S = diag ν ⊕ diag ν) +
  sympSpec; symplectic algebra (one/mul/J_mem; ★ symplectic_det_sq (det S)²=1 via mem_iff'
  Sᵀ J S = J + J_det_mul_J_det; det_williamson_block = (∏ν)² via det_fromBlocks_zero₁₂);
  ★ the CARRIED YoulaDecomp (O∈orthogonalGroup, Oᵀ A O = fromBlocks 0 (diag ν) (−diag ν) 0
  — the real-skew normal form, the analytic frontier / haug analogue, a structure never an
  axiom). Mathlib confirmed: symplecticGroup, orthogonalGroup, J_det_mul_J_det,
  det_fromBlocks_zero₁₂ all present. Std-3, budget 0. Next: W3 (williamson_of_youla — the
  construction of S from Youla via matrix sqrt, the effort).
