/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Ricci symmetry `R_{σν} = R_{νσ}`

Discharges the `hric_symm` hypothesis of the QIQT→GR capstone (Tier A1 of `QIQT_GR_DISCHARGEABLE_PLAN.md`):
the Ricci tensor of the Levi-Civita connection is symmetric.  Route: the lowered Riemann tensor
`R_{pqrs} = ∑α g_{pα} R^α_{qrs}` satisfies the pair-symmetry `R_{pqrs} = R_{rspq}` (the standard consequence of the
two antisymmetries `lowered_riemann_antisymm`/`riemann_antisymm` + the first Bianchi identity
`riemann_first_bianchi`), which contracts to `R_{σν} = R_{νσ}`.

Axiom-free.
-/
import QIQTH.Curvature

namespace QIQTH.Curvature

variable {n : ℕ}

/-- **Pair-symmetry of the lowered Riemann tensor** `R_{abcd} = R_{cdab}` (with `R_{pqrs} = ∑α g_{pα}R^α_{qrs}`).
    The classical algebraic consequence of: first-pair antisymmetry (`lowered_riemann_antisymm`), last-pair
    antisymmetry (`riemann_antisymm`), and the first Bianchi identity (`riemann_first_bianchi`).  Proof: sum the
    Bianchi identity over the four cyclic first-index placements; the cross terms cancel by the antisymmetries,
    leaving `2(R_{abcd} − R_{cdab}) = 0`. -/
theorem lowered_riemann_pair_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (a b c d : Fin n) (x : Point n) :
    (∑ α, g x a α * riemann g gi α b c d x) = (∑ α, g x c α * riemann g gi α d a b x) := by
  set R : Fin n → Fin n → Fin n → Fin n → ℝ :=
    fun p q r s => ∑ α, g x p α * riemann g gi α q r s x with hRdef
  -- first-pair antisymmetry `R(p,q,r,s) = −R(q,p,r,s)`
  have as1 : ∀ p q r s, R p q r s = - R q p r s := by
    intro p q r s
    have h := lowered_riemann_antisymm g gi hsymm hinv hCg hC p q r s x
    simp only [hRdef]; linarith [h]
  -- last-pair antisymmetry `R(p,q,r,s) = −R(p,q,s,r)`
  have as2 : ∀ p q r s, R p q r s = - R p q s r := by
    intro p q r s
    simp only [hRdef]
    rw [show (∑ α, g x p α * riemann g gi α q r s x)
          = ∑ α, g x p α * (- riemann g gi α q s r x) from
        Finset.sum_congr rfl (fun α _ => by rw [riemann_antisymm g gi α q r s x]),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  -- first Bianchi (cyclic on the last three slots) `R(p,q,r,s) + R(p,r,s,q) + R(p,s,q,r) = 0`
  have bi : ∀ p q r s, R p q r s + R p r s q + R p s q r = 0 := by
    intro p q r s
    simp only [hRdef]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro α _
    rw [← mul_add, ← mul_add, riemann_first_bianchi g gi hsymm α q r s x, mul_zero]
  show R a b c d = R c d a b
  linarith [bi a b c d, bi b c d a, bi c d a b, bi d a b c,
    as1 a b c d, as2 a b c d, as1 a c d b, as2 a c d b, as1 a d b c, as2 a d b c,
    as1 b c d a, as2 b c d a, as1 b d a c, as2 b d a c, as1 b a c d, as2 b a c d,
    as1 c d a b, as2 c d a b, as1 c a b d, as2 c a b d, as1 c b d a, as2 c b d a,
    as1 d a b c, as2 d a b c, as1 d b c a, as2 d b c a, as1 d c a b, as2 d c a b,
    as1 a c b d, as2 a c b d, as1 a d c b, as2 a d c b, as1 c a d b, as2 c a d b]

/-- The Ricci tensor as a `gi`-raised lowered-Riemann trace:
    `R_{pq} = ∑μ∑α gi^{μα} (∑β g_{αβ} R^β_{pμq})` (the `gi·g = δ` collapse reproduces `∑μ R^μ_{pμq}`). -/
private theorem ricci_eq_trace (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (p q : Fin n) (x : Point n) :
    ricci g gi p q x = ∑ μ, ∑ α, gi x μ α * (∑ β, g x α β * riemann g gi β p μ q x) := by
  rw [ricci]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [show (∑ α, gi x μ α * (∑ β, g x α β * riemann g gi β p μ q x))
        = ∑ β, (∑ α, gi x μ α * g x α β) * riemann g gi β p μ q x from by
      simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun α _ => by ring))]
  rw [Finset.sum_congr rfl (fun β _ => by
      rw [show (∑ α, gi x μ α * g x α β) = if β = μ then (1 : ℝ) else 0 from by
        rw [show (∑ α, gi x μ α * g x α β) = ∑ α, g x β α * gi x α μ from
          Finset.sum_congr rfl (fun α _ => by rw [hsymm_gi x μ α, hsymm x α β]; ring)]
        exact hinv x β μ])]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **★ Ricci symmetry `R_{σν} = R_{νσ}`** — discharges `hric_symm`.  Write the Ricci tensor as the `gi`-raised
    lowered-Riemann trace (`ricci_eq_trace`), apply the pair-symmetry of the lowered Riemann
    (`lowered_riemann_pair_symm`) termwise, then reconcile by `Finset.sum_comm` + symmetry of `gi`. -/
theorem ricci_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (σ ν : Fin n) (x : Point n) :
    ricci g gi σ ν x = ricci g gi ν σ x := by
  rw [ricci_eq_trace g gi hsymm hsymm_gi hinv σ ν x]
  -- pair-symmetry: `loweredR(α,σ,μ,ν) = loweredR(μ,ν,α,σ)`
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun α _ => by
      rw [lowered_riemann_pair_symm g gi hsymm hinv hCg hC α σ μ ν x]))]
  rw [Finset.sum_comm, ricci_eq_trace g gi hsymm hsymm_gi hinv ν σ x]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hsymm_gi x j i]

end QIQTH.Curvature
