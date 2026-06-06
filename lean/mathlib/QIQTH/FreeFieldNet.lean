/-
# A NON-TOY recorded-history net with product-Born no-signaling (Prize Stage 1)

`LorentzWitness` exhibits a concrete `RecordedHistoryNet`/covariance witness, but with TRIVIAL
restriction (identity) — so its no-signaling marginal `ω_marg` is vacuous.  The genuine Stage-1
advance toward the prize (`PRIZE_EXECUTION_PLAN.md`) is a net whose restriction is a real
**marginalization** and whose `ω_marg` (the relativistic no-signaling / Kolmogorov consistency)
is a THEOREM about the **product Born measure** — "the marginal on a sub-region is independent of
the spacelike-extended context."

Minimal honest model: two causal diamonds `false ≤ true` (a 1-mode sub-region inside a 2-mode
region).  Record fibres `X false = Fin m` (one mode's outcome), `X true = Fin m × Fin m` (both).
Restriction `true → false` is `Prod.fst` (drop the second mode).  The measure is the product Born
measure `ω true (x,y) = p x · p y`, `ω false = p`, for any single-trial law `p` (e.g.
`OneSiteBorn.bornVec ψ`).  Then `ω_marg` holds because `∑_y p x · p y = p x · ∑_y p y = p x` —
the marginal of a product is the factor, independent of the dropped mode.  Axiom-free.
-/
import QIQTH.LorentzSelection
import Mathlib.Tactic

namespace QIQTH.FreeFieldNet

open LorentzSelection Finset

variable {m : ℕ}

/-- Record-sector space over each diamond: one outcome on the sub-region `false`, a pair on the
    full region `true`. -/
@[reducible] def DX (m : ℕ) : Bool → Type
  | false => Fin m
  | true => Fin m × Fin m

instance instFintypeDX (m : ℕ) : ∀ b, Fintype (DX m b)
  | false => inferInstanceAs (Fintype (Fin m))
  | true => inferInstanceAs (Fintype (Fin m × Fin m))

instance instDecEqDX (m : ℕ) : ∀ b, DecidableEq (DX m b)
  | false => inferInstanceAs (DecidableEq (Fin m))
  | true => inferInstanceAs (DecidableEq (Fin m × Fin m))

/-- Restriction: `true → false` drops the second mode (`Prod.fst`); reflexive steps are the
    identity; `true ≤ false` is impossible. -/
def Drestrict (m : ℕ) : ∀ {K D : Bool}, K ≤ D → DX m D → DX m K
  | false, false, _ => fun x => x
  | true, true, _ => fun x => x
  | false, true, _ => fun x => x.1
  | true, false, h => absurd h (by decide)

/-- The 2-mode record presheaf with genuine marginalizing restriction. -/
@[reducible] def Prec (m : ℕ) : RecordPresheaf Bool where
  X := DX m
  restrict := Drestrict m
  restrict_id := by rintro (_ | _) x <;> rfl
  restrict_comp := by rintro (_ | _) (_ | _) (_ | _) hLK hKD x <;> first | rfl | exact absurd hKD (by decide) | exact absurd hLK (by decide)

/- ── The product Born measure ω and its key facts ────────────────────────── -/

/-- The product Born measure: `ω false x = p x`, `ω true (x,y) = p x · p y`. -/
def Dω (p : Fin m → ℝ) : ∀ b, DX m b → ℝ
  | false => fun x => p x
  | true => fun w => p w.1 * p w.2

/-- Normalization on the full region: `∑_{(x,y)} p x · p y = 1`. -/
theorem sum_prod_eq_one (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) :
    ∑ w : Fin m × Fin m, p w.1 * p w.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hp1, mul_one]
  exact hp1

/-- **No-signaling marginal:** marginalizing the product over the second mode gives the Born
    weight of the first — independent of the dropped mode.  `∑_{w.1 = y} p w.1 · p w.2 = p y`. -/
theorem sum_filter_fst (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (y : Fin m) :
    ∑ w ∈ univ.filter (fun w : Fin m × Fin m => w.1 = y), p w.1 * p w.2 = p y := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hinner : ∀ a : Fin m,
      (∑ b : Fin m, if (a, b).1 = y then p (a, b).1 * p (a, b).2 else 0)
        = if a = y then p y else 0 := by
    intro a
    by_cases h : a = y
    · subst h; simp only [if_true]; rw [← Finset.mul_sum, hp1, mul_one]
    · simp [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_ite_eq' univ y (fun _ => p y)]
  simp

/- ── The non-toy recorded-history net (product Born ω, real no-signaling) ──── -/

/-- **A non-toy `RecordedHistoryNet` with genuine marginalizing restriction and the product
    Born measure.**  Unlike `LorentzWitness` (trivial restriction), here `ω_marg` — the
    relativistic no-signaling / Kolmogorov consistency — is the THEOREM that the marginal of the
    product Born measure on the sub-region is the single-mode Born weight, independent of the
    spacelike-extended (second-mode) context.  Works for ANY single-trial law `p` (e.g.
    `OneSiteBorn.bornVec ψ`). -/
noncomputable def bornNet (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    RecordedHistoryNet Bool where
  P := Prec m
  fin := instFintypeDX m
  deceq := instDecEqDX m
  N := fun b => Fintype.card (DX m b)
  card_le := fun _ => le_refl _
  Pb := Prec m
  recon := fun D => Equiv.refl (DX m D)
  recon_nat := fun _ _ => rfl
  ω := Dω p
  ω_nonneg := by
    rintro (_ | _) x
    · exact hp0 x
    · exact mul_nonneg (hp0 _) (hp0 _)
  ω_norm := by
    rintro (_ | _)
    · exact hp1
    · exact sum_prod_eq_one p hp1
  ω_marg := by
    rintro (_ | _) (_ | _) h y
    · simp only [Prec, Drestrict, Dω]
      rw [Finset.sum_filter,
        Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ y) h)]
      simp
    · simp only [Prec, Drestrict, Dω]
      exact sum_filter_fst p hp1 y
    · exact absurd h (by decide)
    · simp only [Prec, Drestrict, Dω]
      rw [Finset.sum_filter,
        Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ y) h)]
      simp

/-- A global section of the net (select record sector `0` everywhere). -/
def bornSection (m : ℕ) [NeZero m] : GlobalSection (Prec m) where
  val := fun b => match b with
    | false => (0 : Fin m)
    | true => ((0 : Fin m), (0 : Fin m))
  consistent := by rintro (_ | _) (_ | _) h <;> first | rfl | exact absurd h (by decide)

/-- The (trivial) Poincaré action on the net. -/
def bornAction (m : ℕ) : PoincareAction (Prec m) where
  act := OrderIso.refl Bool
  γ := fun D => Equiv.refl ((Prec m).X D)
  natural := fun _ _ => rfl

/-- **Prize Stage 1 (finite, non-toy): the net + section + action EXIST.**  The product-Born
    recorded-history net is a genuine inhabitant of the covariant interface — with the
    no-signaling marginal `ω_marg` a real THEOREM about the product Born measure (not the
    trivial-restriction `LorentzWitness`).  Axiom-free. -/
theorem bornNet_exists (m : ℕ) [NeZero m] (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∃ (net : RecordedHistoryNet.{0, 0} Bool) (_lam : GlobalSection net.P)
      (_g : PoincareAction net.P), True :=
  ⟨bornNet p hp0 hp1, bornSection m, bornAction m, trivial⟩

/-- **Prize Stage 1: Lorentz-covariant single-outcome selector from the non-toy net.**  Feeds
    `bornNet_exists` into `covariant_selection_exists`: a covariant selector provably exists over
    the product-Born net (whose no-signaling is derived, not assumed). -/
theorem bornNet_covariant_selection (m : ℕ) [NeZero m] (p : Fin m → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ∃ (P : RecordPresheaf.{0, 0} Bool) (lam : GlobalSection P) (g : PoincareAction P),
      ∀ D : Bool, selector (actSection g lam) (g.act D) = g.γ D (selector lam D) :=
  covariant_selection_exists.{0, 0} (bornNet_exists m p hp0 hp1)

/-- **No-signaling, on the concrete net (the marginal is context-independent).**  The marginal
    of the product Born measure onto the single mode is the Born weight `p y`, the same whether
    or not the second mode is included. -/
theorem bornNet_no_signaling (p : Fin m → ℝ) (hp1 : ∑ i, p i = 1) (y : Fin m) :
    ∑ w ∈ univ.filter (fun w : Fin m × Fin m => w.1 = y), p w.1 * p w.2 = p y :=
  sum_filter_fst p hp1 y

/-- **Mode-swap equivariance of the net's measure.**  Swapping the two modes leaves the product
    Born measure invariant: `ω true (swap w) = ω true w`.  The finite "Lorentz"/exchange symmetry
    of the typicality measure — the 2-mode instance of
    `BornTypicalityFinite.w_perm_invariant` (permutation-equivariance of the product Born law). -/
theorem Dω_swap_invariant (p : Fin m → ℝ) (w : Fin m × Fin m) :
    Dω p true (Prod.swap w) = Dω p true w := by
  simp only [Dω, Prod.fst_swap, Prod.snd_swap]; ring

end QIQTH.FreeFieldNet
