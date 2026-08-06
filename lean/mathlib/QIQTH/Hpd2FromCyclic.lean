/-
  Hpd2FromCyclic — J4-349 brick of the `a₁ = R/6` heat-kernel campaign.

  ⚠ NOT `a₁ = R/6`.  This file proves NOTHING new about the numerical heat coefficient.  It supplies an
  INDEPENDENT algebraic derivation of the pullback second-jet radial identity `hpd2` from the proven
  cyclic 2-jet machinery (`NCGaussToCyclicT`), as a cross-check of the already-landed direct route
  (`PullbackMetric.expPullback_hpd2`, the `residFold` assembly).

  ═══════════════════════════════════════════════════════════════════════════════════════════════
  P0 — RECON (verdicts).

  (1) hpd2's EXACT shape (binder of `PullbackMetric.kappa_eq_one_sixth_expPullback_of_hpd2`):
        `hpd2 : ∀ α v,
           2 * (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x => g̃ x α k) j y) l 0 * v l * v j * v k)
             - (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x => g̃ x j k) α y) l 0 * v l * v j * v k) = 0`.
      Writing `T g̃ a b c d := pd (fun y => pd (fun w => g̃ w a b) d y) c 0 = ∂_c ∂_d g̃_{ab}(0)`
      (the `NCGaussToCyclicT.T` convention), the two brackets are, with `⟨·⟩ = ∑_{l,j,k} · v^l v^j v^k`,
        A := ⟨T g̃ α k l j⟩   (free index `α` in a COMPONENT slot),
        C := ⟨T g̃ j k l α⟩   (free index `α` in a DERIVATIVE slot),
      and hpd2 is exactly `2·A − C = 0`.

  (2) The `⊤`-usage map (the S0 smoothness verdict).  The proven cyclic machinery
        `NCGaussToCyclicT.cyclicT_of_hGauss` (⟹ `T abcd + T acbd + T bcad = 0`) and
        `NCGaussToCyclicT.cyclicT_gauss`     (⟹ `T irpq + T iqpr + T ipqr = 0`)
      BOTH demand `hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g̃ y a b)` — used through `pd_comm`/Schwarz
      (`Curvature.pd_comm`, hard-wired to `ContDiff ⊤`) and `NCGaussPd3.pd3_sum` (third partials).
      The exp-pullback metric `g̃ = PullbackMetric.expPullbackMetric` is only provably
      `ContDiffOn ℝ 2` on the exp-ball (`PullbackMetric.contDiffOn_expPullbackMetric`; the exp map is
      capped at `C³/C⁴` in the J4 tower).  So the cyclic lemmas CANNOT be instantiated at `g̃` at the
      current proven regularity: `cyclicT_of_hGauss` / `cyclicT_gauss` at `g̃` are SATISFIABLE carries
      (they hold for the genuine RNC metric; deriving them needs a finite-order Schwarz + `pd3` refactor
      of `NCGaussPd3`/`NCGaussToCyclicT`, or the still-open `g̃ ∈ C^∞`, the exp-regularity wall).

  (3) The consumer's conclusion.  `PullbackMetric.kappa_eq_one_sixth_expPullback_of_hpd2`, fed hpd2,
      concludes the a₁-accounting slot value `κ`-form `= (1/6 − ξ)·Rscl − m²` for `g̃` — i.e. `κ = 1/6`
      AT THE PULLBACK (NOT the general `a₁ = R/6`, NOT the value of `G`).

  ═══════════════════════════════════════════════════════════════════════════════════════════════
  P1 — THE index algebra (cyclic ⟹ hpd2), UNCONDITIONAL, no smoothness.

  Contract the cyclic identities against the totally-symmetric weight `v^l v^j v^k`.  Every contraction
  of `T abcd + T acbd + T bcad = 0` collapses (using Schwarz `T abcd = T abdc`) to `2A + C = 0`, and
  every contraction of the diagonal `T irpq + T iqpr + T ipqr = 0` (at `i = α`) collapses to `3A = 0`,
  i.e. `A = 0`.  Hence `C = 0` and `hpd2 = 2A − C = 0`.  The only non-trivial Lean content is the
  six-permutation reindex of the `v³`-contracted triple sums (the `reidx_*` helpers below, the
  `sum3_sym_contract` pattern).  `hpd2_of_cyclicT` states this over an ABSTRACT 2-jet array `Tg`.

  ═══════════════════════════════════════════════════════════════════════════════════════════════
  No `sorry` (this header prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable carry.
  All carries (the g̃-cyclic identities in P2/P3) are the conclusions of `cyclicT_of_hGauss` /
  `cyclicT_gauss` at `g̃`, satisfiable at the true RNC regularity.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PullbackMetric
import QIQTH.NCGaussToCyclicT

open QIQTH.Curvature
open scoped BigOperators

namespace QIQTH.Hpd2FromCyclic

variable {n : ℕ}

/-! ### The six-permutation reindex of a `v³`-contracted triple sum (the `sum3_sym_contract` pattern).

Each lemma equates the `v³`-contraction of `g` at a permuted argument triple to the base contraction
`∑ g l j k · v l v j v k`.  Adjacent transpositions (`reidx_lkj`, `reidx_jlk`) go via `Finset.sum_comm`
+ commutativity of the scalar weight; the 3-cycles / outer transposition compose them. -/

/-- Swap the last two arguments (inner adjacent transposition). -/
private theorem reidx_lkj (v : Fin n → ℝ) (g : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, g l k j * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- Swap the first two arguments (outer adjacent transposition). -/
private theorem reidx_jlk (v : Fin n → ℝ) (g : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, g j l k * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by ring

/-- The left 3-cycle `(l,j,k) ↦ (j,k,l)`. -/
private theorem reidx_jkl (v : Fin n → ℝ) (g : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, g j k l * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k :=
  (reidx_jlk v (fun l j k => g l k j)).trans (reidx_lkj v g)

/-- The right 3-cycle `(l,j,k) ↦ (k,l,j)`. -/
private theorem reidx_klj (v : Fin n → ℝ) (g : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, g k l j * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k :=
  (reidx_lkj v (fun l j k => g j l k)).trans (reidx_jlk v g)

/-- The outer transposition `(l,j,k) ↦ (k,j,l)`. -/
private theorem reidx_kjl (v : Fin n → ℝ) (g : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, g k j l * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, g l j k * v l * v j * v k :=
  (reidx_jlk v (fun l j k => g k l j)).trans (reidx_klj v g)

/-! ### P1 — the abstract cyclic ⟹ hpd2 algebra (unconditional). -/

/-- **`hpd2_of_cyclicT` — the pure index algebra.**  For an arbitrary four-index 2-jet array `Tg`
    (think `Tg a b c d = ∂_c ∂_d g̃_{ab}(0)`) satisfying Schwarz symmetry in the derivative slots
    (`hcd`), the four-instance cyclic identity (`hcyc`, the shape of `cyclicT_of_hGauss`) and the
    Gauss-diagonal cyclic identity (`hdiag`, the shape of `cyclicT_gauss`), the `v³`-contracted radial
    identity `2·⟨Tg α k l j⟩ − ⟨Tg j k l α⟩ = 0` (the hpd2 shape) holds.  NO smoothness, NO metric —
    pure multilinear algebra.  ⚠ NOT `a₁ = R/6`. -/
theorem hpd2_of_cyclicT (Tg : Fin n → Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) (α : Fin n)
    (hcd : ∀ a b c d, Tg a b c d = Tg a b d c)
    (hcyc : ∀ a b c d, Tg a b c d + Tg a c b d + Tg b c a d = 0)
    (hdiag : ∀ i p q r, Tg i r p q + Tg i q p r + Tg i p q r = 0) :
    2 * (∑ l, ∑ j, ∑ k, Tg α k l j * v l * v j * v k)
      - (∑ l, ∑ j, ∑ k, Tg j k l α * v l * v j * v k) = 0 := by
  -- reindexings (each summand is a permutation of the base pattern).
  have eT2 : (∑ l, ∑ j, ∑ k, Tg α j l k * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, Tg α k l j * v l * v j * v k :=
    reidx_lkj v (fun a b c => Tg α c a b)
  have eT3 : (∑ l, ∑ j, ∑ k, Tg α l j k * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, Tg α k l j * v l * v j * v k :=
    reidx_jkl v (fun a b c => Tg α c a b)
  have eU2 : (∑ l, ∑ j, ∑ k, Tg α l k j * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, Tg α k l j * v l * v j * v k :=
    reidx_kjl v (fun a b c => Tg α c a b)
  have eU3 : (∑ l, ∑ j, ∑ k, Tg k l j α * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, Tg j k l α * v l * v j * v k :=
    reidx_jkl v (fun a b c => Tg b c a α)
  -- diagonal (Gauss) contraction ⟹ `3A = 0`.
  have hdiag0 : (∑ l, ∑ j, ∑ k,
      (Tg α k l j + Tg α j l k + Tg α l j k) * v l * v j * v k) = 0 := by
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [hdiag α l j k]; ring
  have hdiag_dist : (∑ l, ∑ j, ∑ k,
        (Tg α k l j + Tg α j l k + Tg α l j k) * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k, Tg α k l j * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k, Tg α j l k * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k, Tg α l j k * v l * v j * v k) := by
    simp only [add_mul, Finset.sum_add_distrib]
  have hdiag_sum := hdiag_dist.symm.trans hdiag0
  -- four-instance cyclic contraction (+ Schwarz on the third term) ⟹ `2A + C = 0`.
  have hcyc0 : (∑ l, ∑ j, ∑ k,
      (Tg α k l j + Tg α l k j + Tg k l j α) * v l * v j * v k) = 0 := by
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [hcd k l j α, hcyc α k l j]; ring
  have hcyc_dist : (∑ l, ∑ j, ∑ k,
        (Tg α k l j + Tg α l k j + Tg k l j α) * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k, Tg α k l j * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k, Tg α l k j * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k, Tg k l j α * v l * v j * v k) := by
    simp only [add_mul, Finset.sum_add_distrib]
  have hcyc_sum := hcyc_dist.symm.trans hcyc0
  linarith [eT2, eT3, eU2, eU3, hdiag_sum, hcyc_sum]

open QIQTH.PullbackMetric QIQTH.NCGaussToCyclicT

/-! ### P2 — hpd2 at the exp-pullback metric, from the (satisfiable) g̃-cyclic carries.

The Schwarz slot-symmetry `hcd` of the `g̃` 2-jet is DISCHARGED unconditionally from the proved
`C²`-at-`0` regularity (`contDiffAt2_expPullbackMetric_zero` + Clairaut `isSymmSndFDerivAt`), so it is
NOT a carry.  The two remaining hypotheses `hcyc`/`hdiag` are exactly the conclusions of
`NCGaussToCyclicT.cyclicT_of_hGauss` / `cyclicT_gauss` at `g̃` — SATISFIABLE (they hold for the genuine
RNC metric) but not derivable at the current proven `C²`-on-a-ball regularity (they need three metric
partials / a finite-order refactor, or the open `g̃ ∈ C^∞`). -/

/-- **`hcd_expPullback` — Schwarz slot-symmetry of the `g̃` second jet, UNCONDITIONAL.**  The mixed
    coordinate second partial of the exp-pullback metric at `0` is symmetric in its two derivative
    slots: `∂_c ∂_d g̃_{ab}(0) = ∂_d ∂_c g̃_{ab}(0)`.  Discharged from `C²`-at-`0` via the second-Fréchet
    reduction `pd2_expPullbackMetric_eq_fderiv2` and Clairaut symmetry `ContDiffAt.isSymmSndFDerivAt`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hcd_expPullback (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (a b c d : Fin n) :
    T (expPullbackMetric g gi hC p) a b c d = T (expPullbackMetric g gi hC p) a b d c := by
  simp only [T]
  rw [pd2_expPullbackMetric_eq_fderiv2 g gi hC p hg a b c d,
      pd2_expPullbackMetric_eq_fderiv2 g gi hC p hg a b d c]
  exact ((contDiffAt2_expPullbackMetric_zero g gi hC p hg a b).isSymmSndFDerivAt (by simp)).eq _ _

/-- **`hpd2_expPullback_of_cyclic` — hpd2 for `g̃`, CONDITIONAL on the g̃-cyclic carries.**  The exact
    `hpd2` shape (the binder of `kappa_eq_one_sixth_expPullback_of_hpd2`) derived by the P1 index algebra
    from the two satisfiable cyclic carries `hcyc`/`hdiag` at `g̃` (the Schwarz slot-symmetry is
    discharged internally by `hcd_expPullback`).  ⚠ NOT `a₁ = R/6`; conditional on `hcyc`, `hdiag`. -/
theorem hpd2_expPullback_of_cyclic (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hcyc : ∀ a b c d, T (expPullbackMetric g gi hC p) a b c d
        + T (expPullbackMetric g gi hC p) a c b d
        + T (expPullbackMetric g gi hC p) b c a d = 0)
    (hdiag : ∀ i q r s, T (expPullbackMetric g gi hC p) i s q r
        + T (expPullbackMetric g gi hC p) i r q s
        + T (expPullbackMetric g gi hC p) i q r s = 0)
    (α : Fin n) (v : Fin n → ℝ) :
    2 * (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
            expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
      - (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
            expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k) = 0 :=
  hpd2_of_cyclicT (T (expPullbackMetric g gi hC p)) v α
    (hcd_expPullback g gi hC p hg) hcyc hdiag

/-! ### P3 — the κ = 1/6 capstone at the pullback, via the cyclic route.

Feeding P2 into the banked consumer `kappa_eq_one_sixth_expPullback_of_hpd2` gives the a₁-accounting slot
value `= (1/6 − ξ)·Rscl − m²` for `g̃`, CONDITIONAL on exactly the two g̃-cyclic carries plus the
consumer's own satisfiable inputs (`hframe`, ambient smoothness, `hκgeo`, `hRic`).  ⚠ This is κ = 1/6 AT
THE PULLBACK — NOT the general `a₁ = R/6`, NOT the value of `G`. -/

/-- **`kappa_eq_one_sixth_expPullback_via_cyclic` — κ = 1/6 at `g̃` via the cyclic route.**  Identical
    conclusion to `kappa_eq_one_sixth_expPullback_of_hpd2`, but with the radial `hpd2` obligation
    supplied by the INDEPENDENT cyclic derivation `hpd2_expPullback_of_cyclic` in place of the direct
    `residFold` route.  CONDITIONAL on the two satisfiable g̃-cyclic carries `hcyc`/`hdiag`.
    ⚠ NOT `a₁ = R/6`; NOT the value of `G`. -/
theorem kappa_eq_one_sixth_expPullback_via_cyclic
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (hcyc : ∀ a b c d, T (expPullbackMetric g₀ gi₀ hC p) a b c d
        + T (expPullbackMetric g₀ gi₀ hC p) a c b d
        + T (expPullbackMetric g₀ gi₀ hC p) b c a d = 0)
    (hdiag : ∀ i q r s, T (expPullbackMetric g₀ gi₀ hC p) i s q r
        + T (expPullbackMetric g₀ gi₀ hC p) i r q s
        + T (expPullbackMetric g₀ gi₀ hC p) i q r s = 0)
    (t : ℝ) (ht : 0 < t) (ξ m : ℝ) (κ : ℝ)
    (hκgeo : ∀ c d, (1 / 2) * pd (fun y => pd (fun w =>
          Real.sqrt (Matrix.det (expPullbackMetric g₀ gi₀ hC p w))) d y) c 0
        = -κ * ricci (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) c d 0)
    (hRic : ∃ c d, ricci (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) c d 0 ≠ 0)
    (Rscl : ℝ)
    (hR : Rscl = ∑ i, ricci (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) i i 0) :
    (1 / (2 * t)) * (κ * ∑ i, ∑ j,
        ricci (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) i j 0 *
          (∫ x : (Fin n → ℝ), (∏ k, QIQTH.HeatKernelA1.heatKernel1D t (x k)) * (x i * x j)))
        - ξ * Rscl - m ^ 2
      = (1 / 6 - ξ) * Rscl - m ^ 2 :=
  kappa_eq_one_sixth_expPullback_of_hpd2 g₀ gi₀ hC p hsymm0 hinvF hg hframe
    (fun α v => hpd2_expPullback_of_cyclic g₀ gi₀ hC p hg hcyc hdiag α v)
    t ht ξ m κ hκgeo hRic Rscl hR

end QIQTH.Hpd2FromCyclic
