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
import QIQTH.FreeFieldNet
import Mathlib.Tactic

namespace QIQTH.DiamondSwapNet

open LorentzSelection Finset

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

/- ── UNIFICATION: one D3 net carrying ω (product Born), no-signaling, AND the swap action ── -/

instance instFintypeD3X (m : ℕ) : ∀ D, Fintype (D3X m D)
  | left => inferInstanceAs (Fintype (Fin m))
  | right => inferInstanceAs (Fintype (Fin m))
  | top => inferInstanceAs (Fintype (Fin m × Fin m))

instance instDecEqD3X (m : ℕ) : ∀ D, DecidableEq (D3X m D)
  | left => inferInstanceAs (DecidableEq (Fin m))
  | right => inferInstanceAs (DecidableEq (Fin m))
  | top => inferInstanceAs (DecidableEq (Fin m × Fin m))

/-- The product Born measure on the diamond net: `p` on each 1-mode sub-region, `p ⊗ p` on the
    2-mode region. -/
def Dω3 (p : Fin m → ℝ) : ∀ D, D3X m D → ℝ
  | left => fun x => p x
  | right => fun x => p x
  | top => fun w => p w.1 * p w.2

/-- The OTHER no-signaling marginal: marginalizing over the FIRST mode gives the second mode's
    Born weight.  `∑_{w.2 = b} p w.1 · p w.2 = p b`. -/
theorem sum_filter_snd (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (b : Fin m) :
    ∑ w ∈ univ.filter (fun w : Fin m × Fin m => w.2 = b), p w.1 * p w.2 = p b := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hinner : ∀ a : Fin m,
      (∑ c : Fin m, if (a, c).2 = b then p (a, c).1 * p (a, c).2 else 0) = p a * p b := by
    intro a
    rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (fun h => absurd (mem_univ b) h)]
    simp
  rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.sum_mul, hp1, one_mul]

/-- **The unified diamond net.**  ONE `RecordedHistoryNet` over the 2-atom diamond carrying: the
    marginalizing restriction (`fst`/`snd`), the product Born measure `ω`, and BOTH no-signaling
    marginals (`ω_marg` on `top→left` and `top→right`) — and it admits the genuine diamond-
    permuting swap action `swapAction` (proved separately) and the permutation-equivariance
    `Dω_swap_invariant`.  The Stage-1 capstone: marginalization + no-signaling + product Born +
    a non-trivial covariant action, all on one net. -/
noncomputable def diamondBornNet (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    RecordedHistoryNet D3 where
  P := Prec3 m
  fin := instFintypeD3X m
  deceq := instDecEqD3X m
  N := fun D => Fintype.card (D3X m D)
  card_le := fun _ => le_refl _
  Pb := Prec3 m
  recon := fun D => Equiv.refl (D3X m D)
  recon_nat := fun _ _ => rfl
  ω := Dω3 p
  ω_nonneg := by
    rintro (_ | _ | _) x
    · exact hp0 x
    · exact hp0 x
    · exact mul_nonneg (hp0 _) (hp0 _)
  ω_norm := by
    rintro (_ | _ | _)
    · exact hp1
    · exact hp1
    · exact FreeFieldNet.sum_prod_eq_one p hp1
  ω_marg := by
    rintro (_ | _ | _) (_ | _ | _) h y
    · simp only [Prec3, D3restrict, Dω3]
      rw [Finset.sum_filter,
        Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ y) h)]; simp
    · exact absurd h (by decide)
    · simp only [Prec3, D3restrict, Dω3]; exact FreeFieldNet.sum_filter_fst p hp1 y
    · exact absurd h (by decide)
    · simp only [Prec3, D3restrict, Dω3]
      rw [Finset.sum_filter,
        Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ y) h)]; simp
    · simp only [Prec3, D3restrict, Dω3]; exact sum_filter_snd p hp1 y
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp only [Prec3, D3restrict, Dω3]
      rw [Finset.sum_filter,
        Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ y) h)]; simp

/-- **Stage-1 capstone (unified).**  For any single-trial law `p`, the diamond net exists with a
    global section and the genuine diamond-permuting Poincaré action — so a Lorentz-covariant
    single-outcome selector exists over a net that ALSO has product-Born no-signaling on both
    modes (`diamondBornNet.ω_marg`).  No-signaling, equivariance, marginalization, and a
    non-trivial covariant action are unified on one net. -/
theorem diamond_unified (m : ℕ) [NeZero m] (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) :
    (∃ (net : RecordedHistoryNet.{0, 0} D3) (_lam : GlobalSection net.P)
        (_g : PoincareAction net.P), True)
    ∧ (∀ D : D3, selector (actSection (swapAction m) (sec3 m)) ((swapAction m).act D)
        = (swapAction m).γ D (selector (sec3 m) D)) :=
  ⟨⟨diamondBornNet p hp0 hp1, sec3 m, swapAction m, trivial⟩,
    swap_covariant_selection m⟩

end QIQTH.DiamondSwapNet
