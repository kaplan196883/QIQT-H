/-
# Diamond-permuting action: a genuine non-trivial net automorphism (Prize Stage 1)

The Bool net (`FreeFieldNet`) has only the trivial order-automorphism, so its Poincaré action is
trivial.  GPT-5.5-pro's fix: a **2-atom diamond** poset `left, right ≤ top` — a 2-mode region
`top` (`Fin m × Fin m`) with two 1-mode sub-diamonds `left` (records mode 1, via `Prod.fst`) and
`right` (records mode 2, via `Prod.snd`).  The permutation **swapping `left ↔ right`** (fixing
`top`) is a genuine non-trivial order-isomorphism — a Poincaré-style action that actually MOVES
the geometry — and on the top fibre it acts by `Prod.swap`.  Naturality holds because
`snd ∘ swap = fst`: restricting to `left` after the swap equals restricting to `right` before.

This exercises the covariance machinery (`evaluation_covariance`) over a genuine orbit, with a
non-trivial restriction (marginalization), and the product Born measure swap-equivariant.
Axiom-free (standard three only).
-/
import QIQTH.LorentzSelection
import Mathlib.Tactic

namespace QIQTH.DiamondSwapNet

open LorentzSelection

/-- Three causal diamonds: two 1-mode sub-regions `left`, `right` inside a 2-mode region `top`. -/
inductive D3 | left | right | top
  deriving DecidableEq

open D3

/-- The diamond order: `left ≤ top`, `right ≤ top`, reflexive; `left`, `right` incomparable. -/
instance : Preorder D3 where
  le a b := a = b ∨ b = top
  le_refl _ := Or.inl rfl
  le_trans := by rintro a b c (rfl | rfl) (rfl | rfl) <;> first | exact Or.inl rfl | exact Or.inr rfl

instance : DecidableRel ((· ≤ ·) : D3 → D3 → Prop) :=
  fun a b => inferInstanceAs (Decidable (a = b ∨ b = top))

/-- Record fibres: `Fin m` on each 1-mode sub-region, `Fin m × Fin m` on the 2-mode region. -/
@[reducible] def D3X (m : ℕ) : D3 → Type
  | left => Fin m
  | right => Fin m
  | top => Fin m × Fin m

/-- Restriction: `top → left` records mode 1 (`Prod.fst`), `top → right` records mode 2
    (`Prod.snd`); reflexive steps are the identity; the incomparable pairs are impossible. -/
def D3restrict (m : ℕ) : ∀ {K D : D3}, K ≤ D → D3X m D → D3X m K
  | left, left, _ => fun x => x
  | right, right, _ => fun x => x
  | top, top, _ => fun x => x
  | left, top, _ => fun x => x.1
  | right, top, _ => fun x => x.2
  | left, right, h => absurd h (by decide)
  | right, left, h => absurd h (by decide)
  | top, left, h => absurd h (by decide)
  | top, right, h => absurd h (by decide)

/-- The 2-atom-diamond record presheaf with marginalizing restriction. -/
@[reducible] def Prec3 (m : ℕ) : RecordPresheaf D3 where
  X := D3X m
  restrict := D3restrict m
  restrict_id := by rintro (_ | _ | _) x <;> rfl
  restrict_comp := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) hLK hKD x <;>
      first | rfl | exact absurd hKD (by decide) | exact absurd hLK (by decide)

/- ── The swap: a genuine non-trivial diamond order-isomorphism ────────────── -/

/-- Swap the two sub-diamonds `left ↔ right`, fixing the full region `top`. -/
def swapD3 : D3 → D3
  | left => right
  | right => left
  | top => top

/-- The swap as an equivalence (it is an involution). -/
def swapEquiv : D3 ≃ D3 where
  toFun := swapD3
  invFun := swapD3
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

/-- The swap is an order-isomorphism of diamonds (it preserves `≤`, since it fixes `top`). -/
def swapIso : D3 ≃o D3 where
  toEquiv := swapEquiv
  map_rel_iff' := by rintro (_ | _ | _) (_ | _ | _) <;> decide

/-- **The diamond-permuting Poincaré action.**  The swap moves the geometry (`left ↦ right`) and
    acts on the 2-mode fibre by `Prod.swap`.  Naturality holds because `snd ∘ swap = fst`:
    restricting to `left` after the swap equals restricting to `right` before — a genuine
    equivariant-naturality square, not a trivial one. -/
def swapAction (m : ℕ) : PoincareAction (Prec3 m) where
  act := swapIso
  γ := fun D => match D with
    | left => Equiv.refl (Fin m)
    | right => Equiv.refl (Fin m)
    | top => Equiv.prodComm (Fin m) (Fin m)
  natural := by
    rintro (_ | _ | _) (_ | _ | _) h x <;>
      first | rfl | exact absurd h (by decide)

/-- A global section of the diamond net (record sector `0` everywhere). -/
def sec3 (m : ℕ) [NeZero m] : GlobalSection (Prec3 m) where
  val := fun D => match D with
    | left => (0 : Fin m)
    | right => (0 : Fin m)
    | top => ((0 : Fin m), (0 : Fin m))
  consistent := by rintro (_ | _ | _) (_ | _ | _) h <;> first | rfl | exact absurd h (by decide)

/-- **The action genuinely moves diamonds:** the swap sends `left` to `right` (contrast the
    Bool net's trivial action). -/
theorem swapAction_moves : (swapAction m).act left = right := rfl

/-- **Covariance over a non-trivial orbit.**  The selector is covariant under the genuine
    diamond-permuting swap: `A_{gD}[g·λ] = g · A_D[λ]` for every diamond `D` — exercising the
    covariance machinery (`evaluation_covariance`) over a real geometry permutation, with a
    non-trivial marginalizing restriction in the presheaf. -/
theorem swap_covariant_selection (m : ℕ) [NeZero m] (D : D3) :
    selector (actSection (swapAction m) (sec3 m)) ((swapAction m).act D)
      = (swapAction m).γ D (selector (sec3 m) D) :=
  evaluation_covariance (swapAction m) (sec3 m) D

end QIQTH.DiamondSwapNet
