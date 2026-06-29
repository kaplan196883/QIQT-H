/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# CORNER CONSTRUCTION — storing & reading back fields in the microstate memory (D1…)

This module **deepens** the code–capacity bridge (`QIQTH.CodeCapacityBridge`, M0–M7) along the
honest direction certified by the GPT-5.5-pro audit (2026-06-29): a finite field/record code,
encoded into the capacity-bounded microstate space by an isometry `V : C_R ↪ 𝓗_R`, is represented
**faithfully** — the encoding is a `⋆`-homomorphism and preserves all record statistics — and it
lands in the **corner** `P · End(𝓗_R) · P`, `P := V Vᴴ`, the code projector.

THE AUDIT TRIPWIRE (honest scope).  Everything transported by `A ↦ V A Vᴴ` lands in the corner with
**corner unit `P`, not the ambient `1_𝓗`**.  We never silently replace `P` by `1_𝓗`; the encoding is
unital onto the corner, NOT onto `End 𝓗_R`.  `encode 1 = P` (`encode_one`), and `P = 1_𝓗` would force
the code to fill the whole microstate space.  This is *faithful encoding/read-back*, NOT emergence of
the field or its dynamics; capacity remains a CONSTRAINT, not a generator.  Covers the electron
(CAR Fock, `Fin (2^n)`) and the photon (truncated Fock, `Fin ((d+N).choose N)`) uniformly: the
corner core is dimension-agnostic.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
See `MICROSTATE_CONSTRUCTION_DEEPEN_PLAN.md`.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import QIQTH.CodeCapacityBridge
import QIQTH.RecordContract

namespace QIQTH.CornerConstruction

open Matrix

section Corner

variable {dC d𝓗 : Type*} [Fintype dC] [DecidableEq dC] [Fintype d𝓗] [DecidableEq d𝓗]

/-- The **code projector** `P := V Vᴴ` on the microstate space.  When `V` is a matrix isometry
(`Vᴴ V = 1`), `P` is the orthogonal projector onto the encoded code subspace `V(C_R) ⊆ 𝓗_R`, and it is
the **corner unit**: the identity of the encoded algebra `P · End(𝓗_R) · P`, generally `≠ 1_𝓗`. -/
noncomputable def codeProjector (V : Matrix d𝓗 dC ℂ) : Matrix d𝓗 d𝓗 ℂ := V * Vᴴ

/-- The **encoding map** `ι_V(A) := V A Vᴴ` carrying a code observable `A : End(C_R)` to the
microstate space.  Its image is the corner `P · End(𝓗_R) · P`. -/
noncomputable def encode (V : Matrix d𝓗 dC ℂ) (A : Matrix dC dC ℂ) : Matrix d𝓗 d𝓗 ℂ := V * A * Vᴴ

@[simp] theorem encode_def (V : Matrix d𝓗 dC ℂ) (A : Matrix dC dC ℂ) :
    encode V A = V * A * Vᴴ := rfl

/-- `P` is **idempotent**: `P P = P` (an orthogonal projector), using `Vᴴ V = 1`. -/
theorem codeProjector_mul_self (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) :
    codeProjector V * codeProjector V = codeProjector V := by
  unfold codeProjector
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]

/-- `P` is **self-adjoint**: `Pᴴ = P`. -/
theorem codeProjector_conjTranspose (V : Matrix d𝓗 dC ℂ) :
    (codeProjector V)ᴴ = codeProjector V := by
  unfold codeProjector
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- **★ D1 — the encoding is multiplicative** (`ι_V(A B) = ι_V(A) ι_V(B)`), the half-of-`⋆`-hom that
collapses the inner `Vᴴ V = 1`.  This is what makes encoded operator *products* — and hence n-point
record correlators — agree with the bare code. -/
theorem encode_mul (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (A B : Matrix dC dC ℂ) :
    encode V (A * B) = encode V A * encode V B := by
  simp only [encode_def, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V (B * Vᴴ), hV, Matrix.one_mul]

/-- **★ D1 — the encoding is `⋆`-preserving** (`ι_V(Aᴴ) = ι_V(A)ᴴ`). -/
theorem encode_conjTranspose (V : Matrix d𝓗 dC ℂ) (A : Matrix dC dC ℂ) :
    encode V Aᴴ = (encode V A)ᴴ := by
  simp only [encode_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **★ D1 — the corner unit (the tripwire, made explicit).**  The encoding sends the code identity to
the **code projector `P`, NOT the ambient `1_𝓗`**: `ι_V(1) = P`.  So `ι_V` is unital *onto the corner*
`P · End(𝓗_R) · P`, never onto all of `End 𝓗_R` (unless `P = 1_𝓗`, i.e. the code fills the microstate
space — see `codeProjector_eq_one_iff_encode_one`).  This is the formal guard against the overclaim of
identifying the field code space with the microstate space. -/
@[simp] theorem encode_one (V : Matrix d𝓗 dC ℂ) :
    encode V (1 : Matrix dC dC ℂ) = codeProjector V := by
  simp [encode_def, codeProjector]

/-- The honest guard restated as an iff: the encoding is ambient-unital (`ι_V(1) = 1_𝓗`) **iff** the
code projector is the full identity `P = 1_𝓗` — i.e. the code fills the entire microstate space.  For a
proper sub-code (`P ≠ 1_𝓗`) the encoded identity is the strictly smaller corner unit `P`. -/
theorem codeProjector_eq_one_iff_encode_one (V : Matrix d𝓗 dC ℂ) :
    encode V (1 : Matrix dC dC ℂ) = 1 ↔ codeProjector V = 1 := by
  rw [encode_one]

/-- The encoded product of a **nonempty** list of code observables equals the encoding of their
product: `ι_V(∏ l) = ∏ (l.map ι_V)`.  (Nonemptiness is essential — the empty product would compare the
code unit's image `P` with the ambient `1_𝓗`, the very identification the corner forbids.) -/
theorem encode_prod (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) :
    ∀ (l : List (Matrix dC dC ℂ)), l ≠ [] → (l.map (encode V)).prod = encode V l.prod
  | [a], _ => by rw [List.map_singleton, List.prod_singleton, List.prod_singleton]
  | (a :: b :: l), _ => by
      have hne : (b :: l) ≠ [] := by simp
      have hrhs : (a :: b :: l).prod = a * (b :: l).prod := List.prod_cons
      rw [hrhs, List.map_cons, List.prod_cons, encode_prod V hV (b :: l) hne,
        ← encode_mul V hV]

/-- **★★★ D1 — n-point record-correlator preservation (the backbone theorem).**  For any field state
`ρ` and any nonempty sequence of code/record observables `A₁,…,Aₙ`, the encoded correlator on the
microstate space equals the bare one on the code:

  `Tr_{𝓗}((VρVᴴ) · ι_V(A₁) ⋯ ι_V(Aₙ)) = Tr_{C}(ρ · A₁ ⋯ Aₙ)`.

So *storing the field in the capacity-bounded microstate memory and reading back any product of
records reproduces exactly the original statistics* — the precise sense in which the encoding is
faithful (generalizes M2 `encoded_record_expectation` from one observable to a full correlator).  This
is **preservation / faithful read-back, not emergence**: the dynamics/observables are supplied on the
code; the theorem only certifies that encoding distorts nothing. -/
theorem encoded_npoint (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (ρ : Matrix dC dC ℂ)
    (l : List (Matrix dC dC ℂ)) (hl : l ≠ []) :
    (V * ρ * Vᴴ * (l.map (encode V)).prod).trace = (ρ * l.prod).trace := by
  rw [encode_prod V hV l hl, encode_def]
  exact QIQTH.CodeCapacityBridge.encoded_record_expectation V hV ρ l.prod

/-- The two-point specialization (the physically central case), with no list machinery exposed:
`Tr((VρVᴴ) · ι_V(A) · ι_V(B)) = Tr(ρ · A · B)`. -/
theorem encoded_twopoint (V : Matrix d𝓗 dC ℂ) (hV : Vᴴ * V = 1) (ρ A B : Matrix dC dC ℂ) :
    (V * ρ * Vᴴ * (encode V A * encode V B)).trace = (ρ * (A * B)).trace := by
  rw [← encode_mul V hV, encode_def]
  exact QIQTH.CodeCapacityBridge.encoded_record_expectation V hV ρ (A * B)

end Corner

section Records

open QIQTH.BornEquiprobable QIQTH.NoBornFromNothing

/-- **★★ D2 — Born record entropy ≤ area (the entropy upgrade of M7).**  Where `record_log_card_le_area`
bounds the *log count* of distinguishable records, this bounds the actual **Shannon entropy** of the Born
record distribution `p : K → ℝ` (a probability law over the distinguishable outcomes `K`).  Once the
records fit the microstate space (`card K ≤ card 𝓗`, the capacity-fitting condition) under the
holographic postulate:

  `H(p) ≤ log(card K) ≤ log(card 𝓗) ≤ A/4ℓ_P²`.

The first step is the Gibbs/Jensen maximum-entropy bound `shannon_le_log_card`; the rest is the bridge's
fitting + capacity chain.  So the **information content of a region's distinguishable records is
holographically area-bounded** — the sharp (entropy, not cardinality) form of the record→area capstone. -/
theorem born_record_entropy_le_area {K 𝓗 : Type*} [Fintype K] [Fintype 𝓗] {areaTerm : ℝ}
    [hcap : HolographicCapacityBound 𝓗 areaTerm] (hfit : Fintype.card K ≤ Fintype.card 𝓗)
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) :
    QIQTH.BranchLedger.Shannon Finset.univ p ≤ areaTerm := by
  have hKpos : 0 < Fintype.card K := by
    rcases Nat.eq_zero_or_pos (Fintype.card K) with h0 | h0
    · haveI : IsEmpty K := Fintype.card_eq_zero_iff.mp h0
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h1
      exact absurd h1 (by norm_num)
    · exact h0
  calc QIQTH.BranchLedger.Shannon Finset.univ p
      ≤ Real.log (Fintype.card K) := QIQTH.RecordContract.shannon_le_log_card p hp h1
    _ ≤ Real.log (Fintype.card 𝓗) :=
        Real.log_le_log (by exact_mod_cast hKpos) (by exact_mod_cast hfit)
    _ ≤ areaTerm := hcap.bound

/-- The outcome-marginal of the uniform measure over the fine-graining is a normalized law: its weights
sum to one (`∑_k outcomeMarginal sec (1/|I|) k = 1`), since the marginals repartition the uniform total. -/
theorem sum_uniform_outcomeMarginal {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Nonempty I]
    (sec : I → K) :
    ∑ k, outcomeMarginal sec (fun _ => 1 / (Fintype.card I : ℝ)) k = 1 := by
  unfold outcomeMarginal
  rw [Finset.sum_comm]
  have hinner : ∀ γ : I, (∑ k, if sec γ = k then (1 / (Fintype.card I : ℝ)) else 0)
      = 1 / (Fintype.card I : ℝ) := fun γ => by
    rw [Finset.sum_ite_eq Finset.univ (sec γ) (fun _ => (1 / (Fintype.card I : ℝ)))]
    simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero)]

/-- **★★★ D2 (Layer-C tie) — the Born readout's entropy is area-bounded.**  Specializing
`born_record_entropy_le_area` to the *actual Born weights* of the unifying theorem: for an equal-amplitude
orthonormal fine-graining `f : I → 𝓗_R` with readout `sec : I → K`, the Born readout distribution
`p k = (sectorAmp f sec k)² = |c_k|²` (the uniform measure's outcome-marginal,
`uniform_marginal_eq_sectorAmp_sq`) has Shannon entropy bounded by the area, once the outcomes fit the
microstate space (`card K ≤ card 𝓗_R`):

  `H((sectorAmp ·)²) ≤ A/4ℓ_P²`.

So the **information carried by the electron's/photon's Born-weighted records is holographically
area-bounded** — joining the Born layer (the weights are `|c_k|²`, derived from typicality) to the
capacity layer (their entropy obeys the area floor) in entropy form.  Honest scope unchanged: a statement
about the field's *records*; it does not derive the field, `G`, or remove P5 / the capacity postulate. -/
theorem born_readout_entropy_le_area {d𝓗 : Type*} [Fintype d𝓗] {K : Type*} [Fintype K] [DecidableEq K]
    {areaTerm : ℝ} [HolographicCapacityBound d𝓗 areaTerm] (hfit : Fintype.card K ≤ Fintype.card d𝓗)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {f : I → EuclideanSpace ℂ d𝓗} (hf : Orthonormal ℂ f) (sec : I → K) :
    QIQTH.BranchLedger.Shannon Finset.univ (fun k => (sectorAmp f sec k) ^ 2) ≤ areaTerm := by
  refine born_record_entropy_le_area hfit _ (fun k => sq_nonneg _) ?_
  rw [← sum_uniform_outcomeMarginal sec]
  exact Finset.sum_congr rfl (fun k _ => (uniform_marginal_eq_sectorAmp_sq hf sec k).symm)

end Records

section Photon

open Matrix

/-- **★★ D3 — the finite Weyl obstruction (operational CCR no-go).**  Sharpens `no_finiteDim_CCR` from
the additive commutator to the **multiplicative Weyl form**.  If two *invertible* operators `U, V` on a
finite-dimensional space satisfy a Weyl/`q`-commutation `U V = q · V U`, then the phase is a root of
unity: `q^(dim) = 1`.  (Take determinants: `det U · det V = q^{dim} · det V · det U`, and cancel the
nonzero `det U · det V`.)  So the **continuous** Weyl relations of a bosonic mode — which require an
*irrational* / generic phase `q = e^{iθ}` with `θ ∉ 2πℚ`, hence `q^n ≠ 1` for all `n` — **cannot** be
realized in any finite-microstate sector.  This is the multiplicative companion to the photon's
additive-CCR impossibility: the bosonic oscillator is necessarily *truncated* in finite capacity. -/
theorem finite_weyl_qpow_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℂ) (hU : U.det ≠ 0) (hV : V.det ≠ 0) (q : ℂ)
    (h : U * V = q • (V * U)) : q ^ (Fintype.card n) = 1 := by
  have hdet : U.det * V.det = q ^ (Fintype.card n) * (V.det * U.det) := by
    have hc := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul] at hc
  rw [mul_comm V.det U.det] at hdet
  have hne : U.det * V.det ≠ 0 := mul_ne_zero hU hV
  have hcancel : q ^ (Fintype.card n) * (U.det * V.det) = 1 * (U.det * V.det) := by
    rw [one_mul]; exact hdet.symm
  exact mul_right_cancel₀ hne hcancel

/-- The **truncated lowering operator** `a` on the `N`-level Fock space `ℂ^N` (occupations `0,…,N-1`):
`a eₖ = √k e_{k-1}`, i.e. `a_{ij} = √j` exactly when `i+1 = j`, else `0`.  Its adjoint `aᴴ` is the
truncated raising operator, with `aᴴ e_{N-1} = 0` (the truncation: there is no level `N`). -/
noncomputable def lowering (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if (i : ℕ) + 1 = (j : ℕ) then (Real.sqrt (j : ℕ) : ℂ) else 0

/-- Value-form finite-sum: `∑_{j:Fin N} [a = (j)] g(j) = [a < N] g(a)`. -/
private lemma sum_fin_ite_val {N : ℕ} (a : ℕ) (g : ℕ → ℂ) :
    (∑ j : Fin N, (if a = (j : ℕ) then g (j : ℕ) else 0)) = if a < N then g a else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun jn => if a = jn then g jn else 0) N,
    Finset.sum_ite_eq (Finset.range N) a g]
  simp only [Finset.mem_range]

/-- Successor-form finite-sum: `∑_{j:Fin N} [(j)+1 = a] g(j) = [1 ≤ a ≤ N] g(a-1)`. -/
private lemma sum_fin_ite_succ {N : ℕ} (a : ℕ) (g : ℕ → ℂ) :
    (∑ j : Fin N, (if (j : ℕ) + 1 = a then g (j : ℕ) else 0))
      = if 1 ≤ a ∧ a ≤ N then g (a - 1) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun jn => if jn + 1 = a then g jn else 0) N]
  by_cases hcond : 1 ≤ a ∧ a ≤ N
  · obtain ⟨ha1, haN⟩ := hcond
    rw [if_pos ⟨ha1, haN⟩, Finset.sum_eq_single (a - 1)]
    · rw [Nat.sub_add_cancel ha1, if_pos rfl]
    · intro jn _ hne; rw [if_neg (by omega)]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · rw [if_neg hcond]
    refine Finset.sum_eq_zero (fun jn hjn => ?_)
    rw [Finset.mem_range] at hjn
    rw [if_neg (by omega)]

/-- The adjoint entry, made explicit: `aᴴ_{ij} = √i` exactly when `j+1 = i`, else `0` (the raising
operator). -/
private lemma lowering_conjTranspose_apply (N : ℕ) (i j : Fin N) :
    (lowering N)ᴴ i j = if (j : ℕ) + 1 = (i : ℕ) then (Real.sqrt (i : ℕ) : ℂ) else 0 := by
  simp only [Matrix.conjTranspose_apply, lowering, Matrix.of_apply, apply_ite star, star_zero,
    Complex.star_def, Complex.conj_ofReal]

/-- **The number operator** `aᴴ a = diag(0,1,…,N-1)` — the occupation `(aᴴ a) eₖ = k eₖ`. -/
theorem conjTranspose_lowering_mul (N : ℕ) :
    (lowering N)ᴴ * lowering N = Matrix.diagonal (fun i : Fin N => ((i : ℕ) : ℂ)) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    have hsum : (∑ j : Fin N, (lowering N)ᴴ i j * lowering N j i)
        = ∑ j : Fin N, if (j : ℕ) + 1 = (i : ℕ) then ((i : ℕ) : ℂ) else 0 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [lowering_conjTranspose_apply]
      simp only [lowering, Matrix.of_apply]
      split_ifs with h
      · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
      · ring
    rw [hsum, sum_fin_ite_succ (i : ℕ) (fun _ => ((i : ℕ) : ℂ))]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [if_neg (by omega), h0]; simp
    · rw [if_pos ⟨h0, by omega⟩]
  · rw [if_neg hik]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [lowering_conjTranspose_apply]
    simp only [lowering, Matrix.of_apply]
    have : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    split_ifs with h1 h2 <;>
      first
      | exact absurd (by omega : (i : ℕ) = (k : ℕ)) this
      | ring

/-- **The truncated raising∘lowering** `a aᴴ = diag(1,2,…,N-1,0)` — note the `0` at the top level
(`a aᴴ e_{N-1} = 0`, the truncation defect). -/
theorem lowering_mul_conjTranspose (N : ℕ) :
    lowering N * (lowering N)ᴴ
      = Matrix.diagonal (fun i : Fin N => if (i : ℕ) + 1 < N then (((i : ℕ) + 1 : ℕ) : ℂ) else 0) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    have hsum : (∑ j : Fin N, lowering N i j * (lowering N)ᴴ j i)
        = ∑ j : Fin N, if (i : ℕ) + 1 = (j : ℕ) then ((j : ℕ) : ℂ) else 0 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [lowering_conjTranspose_apply]
      simp only [lowering, Matrix.of_apply]
      split_ifs with h
      · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
      · ring
    rw [hsum, sum_fin_ite_val ((i : ℕ) + 1) (fun jn => ((jn : ℕ) : ℂ))]
  · rw [if_neg hik]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [lowering_conjTranspose_apply]
    simp only [lowering, Matrix.of_apply]
    have : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    split_ifs with h1 h2 <;>
      first
      | exact absurd (by omega : (i : ℕ) = (k : ℕ)) this
      | ring

/-- **★★ D3b — the truncated-oscillator commutator (the photon's finite-capacity defect, made
explicit).**  For the `N`-level truncated oscillator `a eₖ = √k e_{k-1}` on `ℂ^N`:

  `[a, aᴴ] = 1 − N · |N-1⟩⟨N-1|`,

i.e. the bosonic commutator equals the identity EXCEPT for a `−N` defect localized at the top level
`N-1` (`aᴴ a = diag(0,…,N-1)`, `a aᴴ = diag(1,…,N-1,0)`, so `[a,aᴴ] = diag(1,…,1,−(N-1))`).  This is the
CONCRETE form of `no_finiteDim_CCR` / `finite_weyl_qpow_eq_one`: the photon cannot satisfy exact CCR in
finite capacity, and the failure is exactly the top-level truncation — quantified, not hidden. -/
theorem truncated_ladder_commutator (N : ℕ) :
    lowering N * (lowering N)ᴴ - (lowering N)ᴴ * lowering N
      = Matrix.diagonal (fun i : Fin N => if (i : ℕ) + 1 = N then (1 - (N : ℂ)) else 1) := by
  rw [lowering_mul_conjTranspose, conjTranspose_lowering_mul, Matrix.diagonal_sub]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  have hiN : (i : ℕ) + 1 ≤ N := i.2
  by_cases htop : (i : ℕ) + 1 = N
  · rw [if_neg (by omega), if_pos htop]
    have : (N : ℂ) = ((i : ℕ) : ℂ) + 1 := by exact_mod_cast htop.symm
    rw [this]; ring
  · rw [if_pos (by omega), if_neg htop]
    push_cast; ring

end Photon

end QIQTH.CornerConstruction
