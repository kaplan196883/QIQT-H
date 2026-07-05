# THE WILLIAMSON CAMPAIGN — N-mode symplectic diagonalization, UNCONDITIONAL (W1–W12)

**Status:** COMPLETE + **UNCONDITIONAL** (2026-07-05) — W1–W12 landed. W11 discharged Youla at the abstract operator level (`youla_pairing`); **W12 closed the concrete `Matrix → YoulaDecomp` bridge (`youlaDecomp_of_antisymm`), discharging the LAST carry** ⟹ Williamson's symplectic diagonalization is now UNCONDITIONAL for every real symmetric PD matrix (`williamsonDecomp_of_posDef` / `williamson_exists`, taking only `M.PosDef`). Axiom-free std-3, budget 0. **Commits LOCAL ONLY** (session no-push).
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
- [~] **W3 (CHECKPOINTED — antisymm derived, S-construction carried) — ★ williamson_of_youla (the honest reduction, the payoff).** GIVEN M.PosDef + a
  YoulaDecomp of A := M^{1/2} J M^{1/2} (CFC.sqrt, the ArakiEntropy precedent; A antisymmetric
  via Jᵀ=−J + sqrt self-adjoint), CONSTRUCT S := M^{-1/2}·O·(block √ν scaling) and prove
  S ∈ symplecticGroup + Sᵀ M S = D⊕D. May split W3a (S symplectic) / W3b (S diagonalizes).
  Risk MEDIUM-HIGH (block matrix algebra — the campaign's effort). Attempt; checkpoint honestly.
- [x] **W4 — oneModeSympEig consistency.** n=1 WilliamsonDecomp recovers √(ab−c²), wiring the
  repo lemma into the general structure. Risk LOW-MEDIUM.
- [x] **W5 — the entropy connection (the QG payoff).**
  `gaussStateEntropy_of_williamson (W) : gaussStateEntropy (W.ν ∘ equiv)`, ≥ 0 given the
  Heisenberg floor ∀ i, ½ ≤ νᵢ (hypothesis). Plumbing to gaussStateEntropy_nonneg. Risk LOW.
- [x] **W6 — checkpoint + audit** (verbatim HAVE/HAVE-NOT below); plan → COMPLETE.

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

- **2026-07-05** — **W3 CHECKPOINTED (honest).** williamsonAux_antisymm — A := √M·J·√M is
  antisymmetric (the CFC.sqrt-usability entry point, REAL content: (√M)ᵀ = √M via
  PosSemidef.isHermitian + conjTranspose_eq_transpose_of_trivial over ℝ, Jᵀ = −J; the
  ArakiEntropy sqrt pattern ported cleanly). williamson_of_construction_exists — WilliamsonDecomp
  inhabited GIVEN the carried S-construction hconstr (∃ S ν symplectic with Sᵀ M S = D⊕D). The
  actual block-diagonalization construction (S = M^{−1/2}·O·block-√ν, proving symplectic +
  diagonalizing) did NOT close — genuinely the hardest part; CARRIED honestly (the haug
  analogue), NOT faked. So Williamson is now: framework (W1) + antisymm entry point (W3-pre) +
  the reduction packaging, with BOTH Youla (W2) and the S-construction carried. Std-3, budget 0.
  Next: W4/W5 (oneModeSympEig consistency + the gaussStateEntropy connection — the QG payoff,
  landing on the structure regardless).

- **2026-07-05** — **W4+W5+W6 LANDED — CAMPAIGN COMPLETE (honest).** WilliamsonDecomp.entropy
  (∑ gaussModeEntropy over the symplectic spectrum) + entropy_nonneg (Heisenberg floor
  ∀ i, ½ ≤ ν i, since gaussModeEntropy_nonneg is conditional on the floor) +
  williamson_entropy_eq_gaussStateEntropy (= the repo's gaussStateEntropy on Fin n, rfl);
  W4 oneMode_entropy_consistency (n=1/Unit: oneModeSympEig √(ab−c²) wired into the entropy via
  the Heisenberg floor). THE SYMPLECTIC SPECTRUM FEEDS THE GAUSSIAN ENTANGLEMENT ENTROPY —
  the QG/holography payoff, landing on the WilliamsonDecomp structure. Campaign summary: the
  WilliamsonDecomp framework (W1, reusing Mathlib's symplecticGroup) + symplectic algebra
  ((det S)²=1) + the antisymm entry point (W3-pre, real CFC.sqrt content) + the entropy
  connection (W4/W5), with BOTH the Youla normal form (W2) and the S-construction (W3)
  CARRIED honestly. Std-3, budget 0. HONEST: not unconditional Williamson; does NOT unlock
  the area-law scaling.

- **2026-07-05** — **S-CONSTRUCTION DERIVED — W3's carry retired; Williamson conditional on
  Youla ALONE.** williamson_of_youla: given M.PosDef + a YoulaDecomp of √M·J·√M, the symplectic
  congruence S = √M⁻¹·O·E is CONSTRUCTED and BOTH conditions proven — Sᵀ M S = D⊕D (via
  Ri M Ri = 1, OᵀO = 1, E*E = D⊕D) and S·J·Sᵀ = J symplectic. THE SIGN FIX: Mathlib's
  J = [[0,−1],[1,0]] vs Youla's [[0,D],[−D,0]] mismatch ⟹ S J Sᵀ = −J for the diagonal root;
  resolved with the BLOCK-SWAPPED root E := fromBlocks 0 (diag √ν) (diag √ν) 0 (still symmetric,
  still E*E = D⊕D, but flips E J E to match OᵀAO), giving S J Sᵀ = +J. So W3's fully-carried
  hconstr is now DERIVED — the entire block-matrix S-construction (symplectic + diagonalizing).
  The ONE remaining carry is YoulaDecomp itself (the real-antisymmetric normal form, absent
  from Mathlib). Std-3, budget 0.

- **2026-07-05** — **YOULA W8 — the REAL (A²) route, complexification-FREE: per-block geometry
  DERIVED, O-assembly PINNED.** A different angle from W7's stalled complex route. For antisymmetric
  A (Aᵀ=−A), 8 new axiom-free (std-3) lemmas in WilliamsonNormalForm.lean §W8: T := A*A is symmetric
  (antisymm_sq_isHermitian, so Mathlib's REAL spectral theorem applies) and negative semidefinite
  (antisymm_neg_sq_posSemidef: −(A*A)=Aᴴ*A PosSemidef via posSemidef_conjTranspose_mul_self;
  antisymm_sq_dotProduct_nonpos: ⟨Tx,x⟩≤0), A-commutes with T (antisymm_comm_sq); the inner-product
  antisymmetry ⟨Ax,x⟩=0 (antisymm_dotProduct_self) and the Rayleigh identity ⟨Ax,Ax⟩=−⟨A²x,x⟩
  (antisymm_normSq_mulVec). ★ CORE: antisymm_invariant_block — on the T-eigenspace (A*A)e=−ν²e, with
  f:=Ae one has e⊥f, ‖f‖²=ν²‖e‖², and Af=−ν²e (the CLOSED 2×2 rotation block Ae=f, Af=−ν²e = the
  Youla block ν·[[0,−1],[1,0]] in the frame {e,f/ν}); antisymm_kernel_of_sq_kernel — (A*A)e=0 ⟹ Ae=0
  (the ν=0 block). This lands the ENTIRE per-eigenspace geometry of the real route via clean
  matrix/dotProduct algebra (mulVec_transpose, dotProduct_mulVec, neg_mulVec, smul_dotProduct) — NO
  Complex.I, NO complexification. HONEST CHECKPOINT: youlaDecomp_of_antisymm did NOT close — the ONE
  remaining obstruction is the abstract→concrete ASSEMBLY: taking the real spectral decomposition of
  the symmetric T (IsHermitian.spectral_theorem applies), grouping eigenvalues into ν=0 / −νₖ² blocks,
  extracting per-block frames {e,Ae/ν} via antisymm_invariant_block, and assembling them into ONE
  concrete orthogonal O : Matrix (l⊕l)(l⊕l) ℝ with the exact l⊕l sum-indexing so that
  Oᵀ A O = fromBlocks 0 (diag ν) (−(diag ν)) 0 entrywise (the finrank-induction / flat-basis→split-
  index map). NO Mathlib support — the same wall W7 hit, now reached from the real side with the full
  per-block geometry in hand. Williamson STILL conditional on the Youla O-assembly; the real route
  discharges everything up to it. Std-3, budget 0. NOT faked, NOT a Lean axiom.

- **2026-07-05** — **YOULA W7 — honest checkpoint: spectral entry point DERIVED, real-block
  assembly PINNED.** iA_isHermitian (for real antisymmetric A, i·A_ℂ is Hermitian — via
  conjTranspose_map + conj_I — so Mathlib's complex spectral theorem APPLIES); iA_conj_antifixed
  (conj(iA_ℂ) = −iA_ℂ, the algebraic seed of the ±ν eigenvalue pairing). Scratch-verified the
  spectral route is live (eigenvectorUnitary/eigenvalues/spectral_theorem all typecheck on
  iA_ℂ). HONEST CHECKPOINT (Attempt C): the full youlaDecomp_of_antisymm did NOT close — the
  real-block assembly (real-Schur extraction O = [Re colₖ, Im colₖ] from conjugate eigenvector
  pairs + the multiplicity pairing across the Sum split, mapping the flat l⊕l spectral data to
  the split-index ν : l → ℝ + real orthogonal O with Oᵀ A O = the νₖ-block form) is a genuine
  Mathlib gap (the real normal form for antisymmetric matrices), pinned as the frontier, NOT
  faked. Std-3, budget 0. So Williamson is conditional on the Youla REAL-BLOCK ASSEMBLY only;
  its spectral entry point is derived. THIS IS WHERE WILLIAMSON PLATEAUS honestly.

- **2026-07-05** — **YOULA W9 — the real-root pairing: complex-structure + EVEN-DIMENSIONALITY
  DERIVED, O-assembly still PINNED.** Two OPERATOR-LEVEL stepping stones (Module.End eigenspaces of
  T := A*A via mulVecLin), a level neither W7 (flat complex) nor W8 (per-block dotProduct) worked at.
  §RealRootPairing, 4 new axiom-free (std-3) declarations in WilliamsonNormalForm.lean:
  (a) antisymm_eigenspace_invariant — A maps W := eigenspace(mulVecLin(A*A), −ν²) into itself (A
  commutes with A*A, via mul_assoc + mulVec_mulVec); the MapsTo that lets A restrict to W.
  (b) antisymm_sq_eq_smul_on_eigenspace — on W, A∘A = −ν²•id (the eigenvalue eqn through mulVec_mulVec):
  for ν>0, J:=A/ν restricted to W has J²=−id, so W carries a COMPLEX STRUCTURE. ★ (c)
  antisymm_eigenspace_even — Even (finrank ℝ W) for ν>0, the crux. DERIVED via LinearMap.det of the
  restricted A_W := (mulVecLin A).restrict: from (b) A_W∘A_W = −ν²•id, so (det A_W)² =
  det(A_W∘A_W) = (−ν²)^{finrank W} (LinearMap.det_comp + det_smul + det_id); LHS a real square ≥0,
  ν>0 ⟹ (−ν²)^{finrank W} = (−1)^{finrank W}·(ν²)^{finrank W} with (ν²)^{finrank W}>0, forcing
  (−1)^{finrank W} ≥ 0 ⟹ finrank W EVEN (Odd.neg_pow + Nat.even_or_odd + linarith). This is the
  {e, Ae/ν} pairing that makes an l⊕l split POSSIBLE (antisymmetry not even needed for (c): the
  complex structure is intrinsic to the −ν² eigenspace of any real A). PIECE 2:
  antisymm_negSqEigenvalues(+_nonneg) — the eigenvalues of the PosSemidef −(A*A) (from
  antisymm_neg_sq_posSemidef) are ≥0 = the νₖ², so T-spectrum = −νₖ² ≤ 0 (the real spectral data the
  assembly consumes, via Matrix.IsHermitian.eigenvalues + PosSemidef.eigenvalues_nonneg). HONEST
  CHECKPOINT (unchanged from W7/W8): the flat-basis → l⊕l split-index O-SURGERY — threading the
  per-eigenvalue frames {eₖ, Aeₖ/ν} + kernel into ONE concrete orthogonal O with
  Oᵀ A O = fromBlocks 0 (diag ν) (−(diag ν)) 0 entrywise — still has NO Mathlib support (no
  finrank-indexed real-normal-form induction). youlaDecomp_of_antisymm STILL carried; W9 discharges
  the even-multiplicity/complex-structure INGREDIENT the assembly needs, NOT the concrete O.
  Std-3, budget 0. NOT faked, NOT a Lean axiom.

- **2026-07-05** — **YOULA W10 — the abstract dimension-halving RECURSION attempted end-to-end;
  two new recursion primitives DERIVED; O-assembly reduced to a pinned LABOR wall (Mathlib "no
  support" claim CORRECTED).** A genuine, determined attempt to CLOSE `youlaDecomp_of_antisymm`
  via the classical `finrank`-induction, worked at the abstract inner-product-space level.
  §RealYoulaRecursion, 2 new axiom-free (std-3) lemmas in WilliamsonNormalForm.lean:
  (1) `antisymm_card_even` — a NONSINGULAR real antisymmetric matrix has EVEN index card
  (`Bᵀ=−B ⟹ det B = det Bᵀ = det(−B) = (−1)^{card}·det B`; card odd ⟹ det=0 ⊥ `IsUnit`). The
  even-multiplicity BACKBONE: applied to `a` on `(ker a)ᗮ` (nonsingular skew there) ⟹
  `Even(finrank(ker a))`, so the `ν=0` kernel block is pairable (nonzero kernel ⟹ ≥2 dims).
  (2) `skewAdjoint_orthogonal_invariant` — for skew-adjoint `a` (`⟪ax,y⟫=−⟪x,ay⟫`), `Pᗮ` is
  `a`-invariant when `P` is (`⟪ay,x⟫=0 ∧ ⟪ay,x⟫=−⟪y,ax⟫ ⟹ ⟪y,ax⟫=0`). The RECURSION ENGINE:
  after splitting a 2×2 block `P=span{u,a u}`, `a` restricts skew-adjoint to `Pᗮ`.
  **Mathlib CORRECTION (vs W7–W9):** the `l⊕l` gluing does NOT lack Mathlib support — the
  primitives are present: `OrthonormalBasis.prod` (ON basis of `WithLp 2 (E×F)` indexed by `ι₁⊕ι₂`),
  `Submodule.orthogonalDecomposition` (`E ≃ₗᵢ WithLp 2 (K×Kᗮ)`),
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` (eigenvector of `T:=a∘a`), and
  `DirectSum.IsInternal.subordinateOrthonormalBasis`. The abstract induction (in scratch)
  TYPE-CHECKS end-to-end through: eigenvector extraction → `μ≤0`, `ν=√(−μ)` → `a u=0`/`ν>0` split →
  2×2 plane `P=span{u,a u}` → complement invariance (via lemma (2)) → restricted op
  `aC:=(a.domRestrict Pᗮ).codRestrict Pᗮ` → RECURSIVE IH call on `Pᗮ` (drops `finrank` by 2).
  **HONEST CONCRETE STALL** (verbatim `extract_goal` at the recursion point, with `u,w` unit ⊥,
  `a u=ν•w`, `a w=−ν•u`, and IH giving `bC : OrthonormalBasis (κ'⊕κ') ℝ Pᗮ` + `νC`):
  ```
  ⊢ ∃ (κ : Type) (_ : Fintype κ) (b : OrthonormalBasis (κ ⊕ κ) ℝ E) (ν : κ → ℝ),
      (∀ k, a (b (Sum.inl k)) = -ν k • b (Sum.inr k)) ∧
      (∀ k, a (b (Sum.inr k)) =  ν k • b (Sum.inl k))
  ```
  The closing move — `κ := Unit ⊕ κ'`, `b := (OrthonormalBasis.prod (stdON of P) bC).map
  (orthogonalDecomposition P).symm` reindexed `Fin 2 ⊕ (κ'⊕κ') → (Unit⊕κ')⊕(Unit⊕κ')`, then verify
  the three `a`-action eqns through the isometry — has ALL primitives in Mathlib but is a large,
  purely mechanical index/coercion assembly. It is a **formalization-LABOR wall, NOT a
  missing-lemma wall** (the honest correction to the W7–W9 framing). `youlaDecomp_of_antisymm`
  STILL carried; W10 lands the two recursion primitives + the exact residual goal. NO sorry in the
  committed file (the induction skeleton lived only in scratch, now deleted). Std-3, budget 0.

- **2026-07-05** — **YOULA W11 — the abstract operator `youla_pairing` CLOSED, FULLY, no sorry (the
  Youla carry DISCHARGED at the operator level).** `§AbstractYoulaPairing`: `youla_pairing` — for a
  finite-dimensional real inner product space `E` and a skew-adjoint `a` (`⟪a x,y⟫ = -⟪x,a y⟫`) with
  `Even (finrank ℝ E)`, there is an `OrthonormalBasis (κ⊕κ) ℝ E` block-pairing `a` into `ν`-rotation
  `2×2` blocks (`a (b (inl k)) = -ν k • b (inr k)`, `a (b (inr k)) = ν k • b (inl k)`, `ν ≥ 0`).
  Proved UNCONDITIONALLY by the classical dimension-halving strong induction on `finrank ℝ E`
  (`youla_pairing_aux`, the finrank-indexed form via `Nat.strong_induction_on`). Each step peels ONE
  `2×2` block `P = span{p,q}`: **(a≠0)** `T := a ∘ₗ a` is symmetric + negative-semidefinite, and its
  MINIMAL eigenvalue `μ₀ = ⨅ Rayleigh < 0` — the strict negativity extracted via `BddBelow`
  (operator-norm bound `‖a x‖ ≤ ‖a.toContinuousLinearMap‖·‖x‖`) + `ciInf_le` against a witness `a v₀ ≠ 0`
  — gives a unit `T`-eigenvector `u` with `a u ≠ 0`; `w := ‖a u‖⁻¹ • a u` (`ν := ‖a u‖ = √(-μ₀) > 0`)
  closes the rotation block `a u = ν•w`, `a w = -ν•u`, `u ⊥ w`. **(a=0)** any orthonormal pair (built
  via `(ℝ ∙ u)ᗮ` nonzero) is a `ν = 0` block. The complement `Pᗮ` is `a`-invariant
  (`skewAdjoint_orthogonal_invariant`, W10), even-dim `finrank E - 2`, and carries the restricted
  skew-adjoint `aC := a.restrict`; the **induction hypothesis** furnishes its Youla basis `bC`, GLUED
  to `{p,q}` by an explicit `Sum.elim` family whose orthonormality (from `P ⊥ Pᗮ`, via
  `inner_right_of_mem_orthogonal`) and cardinality (`= finrank E`) upgrade it to an `OrthonormalBasis`
  through `OrthonormalBasis.mk` + `span_eq_top_of_card_eq_finrank'`; the `a`-action is verified
  index-by-index through `↑(aC x) = a ↑x`. This is the CORRECTION landing of W10's honest stall: the
  "formalization-labor wall" is now CROSSED — the abstract operator core is **no longer carried**.
  `#print axioms youla_pairing` = `youla_pairing_aux` = `{propext, Classical.choice, Quot.sound}`
  (Std-3), budget 0, NO sorry. **Remaining:** the concrete `Matrix (l⊕l)(l⊕l) → YoulaDecomp` bridge
  (`E := EuclideanSpace ℝ (l⊕l)`, `a := toEuclideanLin A`, ON basis → orthogonal `O` via
  `OrthonormalBasis.toMatrix`, match `fromBlocks`) is the NEXT increment; `youlaDecomp_of_antisymm`
  as a `YoulaDecomp`-structure inhabitant is one `toMatrix` hop away.

- **2026-07-05** — **YOULA W12 — the concrete `Matrix → YoulaDecomp` bridge CLOSED ⟹ WILLIAMSON IS NOW
  UNCONDITIONAL (the last carry DISCHARGED, no sorry).** `§ConcreteYoulaBridge` in
  `WilliamsonNormalForm.lean`: `youlaDecomp_of_antisymm (A) (hA : Aᵀ = -A) : YoulaDecomp A` — for ANY
  real antisymmetric matrix `A`, a genuine `YoulaDecomp A` is BUILT (no longer carried). It instantiates
  the abstract `youla_pairing` (W11) at `E := EuclideanSpace ℝ (l⊕l)`, `a := Matrix.toEuclideanLin A`:
  skew-adjointness `⟪a x,y⟫ = -⟪x,a y⟫` from `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`
  (`a.adjoint = toEuclideanLin Aᴴ = toEuclideanLin (-A) = -a`, over ℝ where `ᴴ = ᵀ`), and
  `Even (finrank ℝ E) = Even (2·card l)`. From the pairing's ON basis `b : OrthonormalBasis (κ⊕κ) ℝ E`
  and `ν₀ ≥ 0`, reindex `κ ≃ l` (`Fintype.equivOfCardEq`, `card (κ⊕κ) = finrank E = card (l⊕l)`) to
  `b' : OrthonormalBasis (l⊕l) ℝ E`, `ν := ν₀ ∘ e.symm`. The orthogonal `O :=
  (EuclideanSpace.basisFun (l⊕l) ℝ).toBasis.toMatrix b'` is in `orthogonalGroup`
  (`OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal`), entries `O i j = (b' j) i`
  (`Basis.toMatrix_apply` + `coe_toBasis_repr_apply` + `basisFun_repr`); the crux
  `(Oᵀ A O) i j = ⟪b' i, a (b' j)⟫` (via `(A O) p j = (a (b' j)) p` from `ofLp ∘ toEuclideanLin` and
  `Oᵀ i p = (b' i) p`, `PiLp.inner_apply` + `RCLike.inner_apply'` + `conj_trivial`) is matched entrywise
  to `fromBlocks 0 (diag ν) (-(diag ν)) 0` by the block pairing `hBlk1/2` + orthonormality
  (`orthonormal_iff_ite`). Since `YoulaDecomp A` is DATA, the `Prop` `∃` of `youla_pairing` is threaded
  through `Nonempty (YoulaDecomp A)` + `Classical.choice`. **This discharges the LAST carry.** Composed
  capstones: `williamsonDecomp_of_posDef (M) (hM : M.PosDef) : WilliamsonDecomp M` (= `williamson_of_youla`
  W6 ∘ `youlaDecomp_of_antisymm (williamsonAux_antisymm M hM)` W3) and `williamson_exists (M) (hM) :
  Nonempty (WilliamsonDecomp M)`. **NO carried hypothesis remains — Williamson's symplectic
  diagonalization is UNCONDITIONAL for every real symmetric PD matrix.** `#print axioms` of all three
  = `{propext, Classical.choice, Quot.sound}` (Std-3), budget 0, NO sorry.

### Entropy invariance (W13) — symplectic-spectrum UNIQUENESS / entropy well-definedness (NOT the area law)

- **2026-07-05** — **W13 — the symplectic spectrum is UNIQUE ⟹ the Gaussian entanglement entropy is
  WELL-DEFINED as a function of `M`. ALL FOUR increments CLOSED green (nothing checkpointed).**
  `§SpectrumUniqueness` in `WilliamsonNormalForm.lean`, 4 new axiom-free (Std-3) theorems + 3 private
  block-algebra helpers. Motivation: Williamson is unconditional, but `WilliamsonDecomp.entropy` reads `ν`
  off a *chosen* decomposition; this proves two decompositions of the same `M` give the same entropy.
  - **Increment 1 (CLOSED) — `williamson_JM_similar_blockJ`:** the Hamiltonian matrix `J·M` is SIMILAR to
    `J·(diagonal ν ⊕ diagonal ν)` — `S⁻¹ (J M) S = J (D⊕D)`. Proved via the commuted symplectic identity
    `S⁻¹ J = J Sᵀ` (from `S J Sᵀ = J`, `SymplecticGroup.mem_iff`) + `Sᵀ M S = D⊕D` (`W.hDiag`), pure real
    matrix algebra. (Note: the natural `M = (Sᵀ)⁻¹(D⊕D)S⁻¹` route hits a motive wall — `M` is an implicit
    arg inside `W.S`, so `rw [← hM]` on `M` fails; the `S⁻¹J = JSᵀ` route rewrites the *block*, never `M`.)
  - **Increment 1.5 (CLOSED) — `williamson_negJMsq_similar`:** squaring + negating, `S⁻¹ (-(J M)²) S =
    diagonal ν² ⊕ diagonal ν²` (`ν² i := ν i · ν i`), a SYMMETRIC matrix. This exposes the symplectic
    eigenvalues *squared* as the real spectrum of a fixed symmetric matrix. (The un-squared `J M` has
    purely imaginary eigenvalues `±iνᵢ` ⟹ its real charpoly `∏(X²+νᵢ²)` has NO real roots — so the naive
    "roots of charpoly(J·(D⊕D))" route in the plan sketch is empty over ℝ; the square is the fix that makes
    `νᵢ²` genuine real roots.) Block helpers `J_mul_blockDiag`, `blockDiagJ_sq`, `JblockDiag_sq`.
  - **Increment 2 (CLOSED) — `williamson_negJMsq_charpoly_roots`:** the FIXED matrix `-(J M)²` has
    `charpoly.roots = {νᵢ²} + {νᵢ²}` (each squared eigenvalue doubled, one per block). Via
    conjugation-invariance of the charpoly (`Matrix.charpoly_units_conj'`, `S` packaged as a unit via
    `isUnit_iff_isUnit_det` + `symplectic_det`) + `charpoly_fromBlocks_zero₁₂` + `charpoly_diagonal` +
    `Polynomial.roots_multiset_prod_X_sub_C` + `roots_pow`/`two_nsmul`. LHS depends on `M` ALONE ⟹ the
    squared-spectrum multiset `{νᵢ²}` is a symplectic INVARIANT.
  - **Increment 3 / CAPSTONE (CLOSED) — `williamson_entropy_symplectic_invariant`:** any two
    `WilliamsonDecomp M` have EQUAL `entropy`. Both give `-(J M)²` the same doubled multiset; count-cancel
    the doubling (`Multiset.ext` + `count_add` + `omega`) ⟹ equal `{νᵢ²}`; the square root
    (`Real.sqrt_mul_self`, `νᵢ ≥ 0`) transfers to equal spectrum multisets `{νᵢ}`; `Multiset.map_map` +
    the `Finset.sum = (map).sum` definitional bridge give equal `∑ᵢ gaussModeEntropy νᵢ`. **So
    `WilliamsonDecomp.entropy` / `gaussStateEntropy` is a genuine function of `M` — a physical entropy.**
  - **HONEST CAPTION:** this is symplectic-spectrum UNIQUENESS / entropy WELL-DEFINEDNESS. It is **NOT**
    the area law and is **not** `Σ ∝ boundary` / area scaling — that remains the separate cited analytic
    frontier. What is proved is only that the entropy is a basis-independent function of the covariance
    matrix `M` (the N-mode analogue of the `n=1` `oneModeSympEig_symplectic_invariant`). `#print axioms` of
    all four = `{propext, Classical.choice, Quot.sound}` (Std-3), budget 0, NO sorry. `lake build
    QIQTH.WilliamsonNormalForm` + `QIQTH.GaussianStateEntropy` + `QIQTH.AxiomAudit` green.
