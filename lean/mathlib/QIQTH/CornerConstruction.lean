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

end QIQTH.CornerConstruction
