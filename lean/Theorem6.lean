/-
  QIQT-H Theorem 6 — Effective Macroscopic Definiteness (inner chain)
  -------------------------------------------------------------------
  Self-contained Lean 4 proof-of-concept. No Mathlib dependency.
  Verify with:  lean Theorem6.lean

  Informal statement (QIQT_Foundations_Paper §7.6 / QIQT_Math §9A):

    For a branch decomposition {(p̃_k, ω_{k,R})} of a global state
    relative to a region R, with

        D_k := χ_R(ω_{k,R}),     D̄ := χ_R(ω̄_R),
        I   := I_Hol^R,          C  := C(R) = A(∂R)/(4 ℓ_P²),

    Donald's identity says

        Σ_k p̃_k D_k  =  D̄ + I.

    Combined with the holographic bound (each D_k ≤ C, hence
    Σ p̃_k D_k ≤ C, since Σ p̃_k = 1) and D̄ ≥ 0, this gives

        I ≤ C.                     (Holographic capacity bounds Holevo info.)

    Chained with Holevo's theorem  (I_acc ≤ I)  and a Fano-style
    multiplicity bound  (H_ε ≤ I_acc + η_def),  together with an
    experimental slack  (B.I ≤ (C - I_0) + η_0):

        H_ε  ≤  (C - I_0 + η_0) + η_def.

  We formalize the inner Donald → holographic-bound step **rigorously**
  (no `sorry`s, no Mathlib). Holevo and Fano are taken as hypotheses
  to the outer theorem rather than axioms — they hold only for
  specific channels / record-definitions, so the caller supplies the
  proof for their experimental setup.

  Real arithmetic is axiomatized minimally: only the five facts the
  chain actually consumes are postulated. Each is a one-line lemma
  in any ordered field, so this file can be re-derived against
  `Mathlib.Data.Real.Basic` by discharging the five axioms.
-/

namespace QIQTH
namespace Theorem6

/- ── Minimal real-arithmetic axiomatization ─────────────────────── -/

axiom RealQ : Type
axiom zeroR : RealQ
axiom addR  : RealQ → RealQ → RealQ
axiom subR  : RealQ → RealQ → RealQ
axiom leR   : RealQ → RealQ → Prop

noncomputable instance : Zero RealQ := ⟨zeroR⟩
noncomputable instance : Add  RealQ := ⟨addR⟩
noncomputable instance : Sub  RealQ := ⟨subR⟩
instance : LE   RealQ := ⟨leR⟩
noncomputable instance : OfNat RealQ 0 := ⟨zeroR⟩

/- The exact five arithmetic facts the chain consumes.
   Each is provable in any ordered field. -/

axiom RealQ.le_refl : ∀ (a : RealQ), a ≤ a

axiom RealQ.le_trans :
    ∀ {a b c : RealQ}, a ≤ b → b ≤ c → a ≤ c

axiom RealQ.add_le_add_right :
    ∀ {a b : RealQ} (c : RealQ), a ≤ b → a + c ≤ b + c

axiom RealQ.sub_le_self_of_nonneg :
    ∀ (a : RealQ) {b : RealQ}, (0 : RealQ) ≤ b → a - b ≤ a

axiom RealQ.eq_sub_of_sum :
    ∀ {a b c : RealQ}, a = b + c → c = a - b

/- ── Branch decomposition data ───────────────────────────────────── -/

/-- Data of a branch decomposition relative to a region R, packaging
    exactly the quantities Theorem 6's inner chain consumes. -/
structure BranchData where
  /-- Σ_k p̃_k · χ_R(ω_{k,R}) — weighted single-branch relative entropy. -/
  S      : RealQ
  /-- χ_R(ω̄_R) — mixed-state relative entropy. -/
  D_bar  : RealQ
  /-- I_Hol^R — Holographic mutual information. -/
  I      : RealQ
  /-- C(R) = A(∂R)/(4 ℓ_P²) — holographic capacity. -/
  C      : RealQ
  /-- **Donald's identity**:  Σ p̃_k D_k = D̄ + I. -/
  donald          : S = D_bar + I
  /-- **Holographic bound** applied branchwise plus Σ p̃_k = 1:
      Σ p̃_k D_k ≤ C. -/
  sum_le_capacity : S ≤ C
  /-- Relative entropy is non-negative:  D̄ ≥ 0. -/
  D_bar_nonneg    : (0 : RealQ) ≤ D_bar

namespace BranchData

variable (B : BranchData)

/-- **Donald-bound lemma.**
    Donald's identity, the branchwise holographic bound, and
    non-negativity of the mixed-state relative entropy together
    imply that the Holographic mutual information is bounded by
    the holographic capacity:  I_Hol^R ≤ C(R). -/
theorem holevo_le_capacity : B.I ≤ B.C := by
  have h₁ : B.I = B.S - B.D_bar := RealQ.eq_sub_of_sum B.donald
  rw [h₁]
  exact RealQ.le_trans
    (RealQ.sub_le_self_of_nonneg B.S B.D_bar_nonneg)
    B.sum_le_capacity

end BranchData

/- ── Outer chain ─────────────────────────────────────────────────── -/

/-- **QIQT-H Theorem 6 — Effective Macroscopic Definiteness (inner-chain form).**

    Given:
      • A branch decomposition `B` satisfying the Donald + holographic
        + non-negativity premises (hence `B.I ≤ B.C` by
        `holevo_le_capacity`);
      • An "experimental slack" inequality `B.I ≤ (C - I_0) + η_0`
        — the actual Holevo info is at most capacity minus a baseline
        I_0 of admissible information, plus a slack η_0;
      • A Holevo accessibility bound  `I_acc ≤ B.I`;
      • A Fano-style multiplicity bound  `H_ε ≤ I_acc + η_def`;

    Conclude

        H_ε  ≤  (C(R) - I_0) + η_0 + η_def.

    The three hypotheses `acc_le`, `fano_le`, `capacity_le` package
    the Holevo, Fano, and "experimental baseline" steps — they are
    *not* asserted as axioms here because they only hold for specific
    channels and record-definitions; the caller supplies the proof
    appropriate to their setup. -/
theorem effective_definiteness
    (B : BranchData)
    (H_eps I_acc I_0 eta_0 eta_def : RealQ)
    (acc_le      : I_acc ≤ B.I)
    (fano_le     : H_eps ≤ I_acc + eta_def)
    (capacity_le : B.I ≤ (B.C - I_0) + eta_0) :
    H_eps ≤ ((B.C - I_0) + eta_0) + eta_def := by
  -- step 1:  I_acc + η_def  ≤  I + η_def       (acc_le on the left)
  have s₁ : I_acc + eta_def ≤ B.I + eta_def :=
    RealQ.add_le_add_right eta_def acc_le
  -- step 2:  H_ε  ≤  I + η_def                  (fano_le ▸ s₁)
  have s₂ : H_eps ≤ B.I + eta_def :=
    RealQ.le_trans fano_le s₁
  -- step 3:  I + η_def  ≤  (C - I_0 + η_0) + η_def
  have s₃ : B.I + eta_def ≤ ((B.C - I_0) + eta_0) + eta_def :=
    RealQ.add_le_add_right eta_def capacity_le
  -- chain.
  exact RealQ.le_trans s₂ s₃

end Theorem6
end QIQTH
