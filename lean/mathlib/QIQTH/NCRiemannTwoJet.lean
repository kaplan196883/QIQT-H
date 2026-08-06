/-
  NCRiemannTwoJet — J4-335 bricks A3+A4 of the Sol-consult-#10 plan.  The (†)-derivation FINISHED:
  the linear-algebra PIN of the metric 2-jet atom `T` to the Riemann tensor (A3), and the `htr`
  threading that reduces the R3 Ricci-source wall entirely to the labelled `hGauss` gauge input (A4).

  ONE brick of the `a₁ = R/6` heat-kernel campaign.  ⚠ NOT `a₁ = R/6`; this file proves NOTHING new
  about `R/6`.  It closes the ALGEBRA between the Gauss-lemma gauge input `hGauss` (satisfiable — normal
  coordinates exist) and the capstone's carried `htr` binder, discharging the previously-opaque residue
  (†).  `hGauss` remains the ONE labelled gauge input (deriving it from the `exp`-pullback tower is a
  separate Gauss-lemma campaign, not attempted here).  No `:= True`, no new axioms, no vacuity.

  ═══════════════════════════════════════════════════════════════════════════════════════════════════
  ═══ THE WORKED LINEAR SYSTEM (A3 — `metric_secondJet_eq_riemann`) ═══
  ═══════════════════════════════════════════════════════════════════════════════════════════════════
  `T g a b c d = pd (fun y => pd (fun w => g w a b) d y) c 0 = ∂_c ∂_d g_{ab}(0)` (J4-334 convention:
  the LAST two indices `c d` are the derivative indices; the FIRST two `a b` the metric components).
  Two symmetries make `T` depend only on the UNORDERED component pair and the UNORDERED derivative pair:
    • `T_symm_ab` : `T g a b c d = T g b a c d`   (metric symmetry `g_{ab} = g_{ba}`),
    • `T_symm_cd` : `T g a b c d = T g a b d c`   (Schwarz `∂_c ∂_d = ∂_d ∂_c`).
  For four DISTINCT indices `{a,b,c,d}` the six independent atoms (3 pair-partitions × 2 comp/deriv
  choices) are J4-334's labels:
    A = T a b c d,  B = T a c b d,  C = T a d b c,  D = T b c a d,  E = T b d a c,  F = T c d a b.

  THE REAL RIEMANN AT 0 (`riemann_at_zero`, J4-318, general RNC first-order gauge — the honest
  `riemann g gi`, NOT abstract) is, in the `T`-atoms (`riemann_at_zero_T` below, defeq-repackaged):
    `R^ρ_{σμν}(0) = ½(T ρ ν μ σ − T ν σ μ ρ − T ρ μ ν σ + T μ σ ν ρ)`.
  Instantiating and normalizing (via `T_symm_ab`/`T_symm_cd`) to the A..F labels:
    `riemann a c b d 0 = ½(C − F − A + D)`,   `riemann a d b c 0 = ½(B − F − A + E)`,
  so
    `−(1/3)(riemann a c b d 0 + riemann a d b c 0) = −(1/6)(−2A + B + C + D + E − 2F)`.               (∗)

  THE CYCLIC GAUSS RELATIONS (`cyclicT_of_hGauss` at four index instances; `s` = the common derivative
  index):
    h_d (s=d): A + B + D = 0,   h_c (s=c): A + C + E = 0,
    h_b (s=b): B + C + F = 0,   h_a (s=a): D + E + F = 0.
  Summing all four: `A+B+C+D+E+F = 0`.  From `h_d + h_c`: `2A + B + C + D + E = 0`, i.e.
  `B+C+D+E = −2A`; combined with the total sum: `F = A`.  Substituting into (∗):
    `−(1/6)(−2A + (B+C+D+E) − 2F) = −(1/6)(−2A − 2A − 2A) = −(1/6)(−6A) = A = T a b c d`.
  ⇒ `T g a b c d = −(1/3)(riemann g gi a c b d 0 + riemann g gi a d b c 0)`.  This is (†) — the four-index
  NC metric 2-jet — now a THEOREM (given `hGauss` + the gauge/smoothness carries), closed by `linarith`
  on the OPAQUE `T`-atoms (`pd` never unfolded).

  ═══ THE `htr` THREADING (A4 — `htr_from_hGauss`) ═══
  Instantiate J4-318's `htr_of_geometry` with the CONCRETE `Rlow := riemann g gi · 0`,
  `Ric := ricci g gi · 0`:
    • hjet  = A3 (`metric_secondJet_eq_riemann`), verbatim after β/defeq;
    • hRic  = `ricci_diag_contract` (`ricci = ∑_μ riemann μ c μ d`, rfl-level);
    • hpair = `riemann_pair_symm_at_zero` : `riemann a b c d 0 = riemann c d a b 0`, DERIVED here from
              `riemann_at_zero_T` + `T_symm_ab`/`T_symm_cd` (a pure `linarith` identity on `T`-atoms —
              the two expansions coincide term-by-term after pair/Schwarz normalization; NO cyclic input).
  Result `htr_from_hGauss`:
    `∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = −(2/3)·ricci g gi c d 0`,
  the capstone's `htr` binder — the R3 wall reduced to `hGauss` + the standard gauge/smoothness carries.

  ═══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  `a₁ = R/6` remains CONDITIONAL after this brick.  `hGauss` (the normal-coordinate
  Gauss contraction) stays the ONE labelled, SATISFIABLE gauge input; the gauge carries `hgi0`/`hdg0`
  (RNC first order) and smoothness `hg`/`hgiC` are the standard normal-coordinate normalizations, all
  jointly satisfiable (flat metric `g ≡ I`, `gi ≡ I`).  R2 analytic walls untouched.  ⚠ NOT `a₁ = R/6`.

  No `sorry` (this header prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable carries.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.NCGaussToCyclicT
import QIQTH.RicciSourceCoeff

open QIQTH.Curvature
open QIQTH.NCGaussToCyclicT
open QIQTH.RicciSourceCoeff
open scoped BigOperators Topology

namespace QIQTH.NCRiemannTwoJet

variable {n : ℕ}

/-! ### `riemann_at_zero` repackaged in the `T`-atom convention (pure defeq). -/

/-- **`riemann_at_zero_T`.**  The J4-318 origin Riemann `riemann_at_zero` re-expressed in the J4-334
    2-jet atom `T` (each `pd (fun y => pd (fun w => g w · ·) · y) · 0` is *definitionally* a `T`-atom):
      `riemann g gi ρ σ μ ν 0 = ½(T ρ ν μ σ − T ν σ μ ρ − T ρ μ ν σ + T μ σ ν ρ)`.
    This is `riemann_at_zero` verbatim, only with the four second-partials named as `T`-atoms so the
    linear algebra of A3/A4 can run on opaque atoms (no `pd` unfolding).  ⚠ NOT `a₁ = R/6`. -/
theorem riemann_at_zero_T (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν (0 : Point n)
      = (1 / 2) * (T g ρ ν μ σ - T g ν σ μ ρ - T g ρ μ ν σ + T g μ σ ν ρ) :=
  riemann_at_zero g gi hg hgiC hgi0 hdg0 ρ σ μ ν

/-! ### A3 — the linear-algebra pin `T ⟹ (†)`. -/

/-- **A3 — `metric_secondJet_eq_riemann` (the residue (†), now a THEOREM).**  Under smoothness
    (`hg`/`hgiC`), metric symmetry (`hgsymm`), the RNC first-order gauge (`hgi0`/`hdg0`) and the
    labelled Gauss contraction (`hGauss`), the four-index normal-coordinate metric 2-jet equals the
    Riemann combination:
      `T g a b c d = −(1/3)(riemann g gi a c b d 0 + riemann g gi a d b c 0)`.
    PROOF = the worked linear system in the header: expand the two `riemann` via `riemann_at_zero_T`,
    normalize the eight atoms with `T_symm_ab`/`T_symm_cd`, and close by `linarith` against the FOUR
    cyclic Gauss relations `cyclicT_of_hGauss` (at `(a,b,c,d)`,`(a,b,d,c)`,`(a,c,d,b)`,`(b,c,d,a)`).
    The `T`-atoms stay OPAQUE.  This discharges the J4-318 wall `hjet`.  ⚠ NOT `a₁ = R/6`. -/
theorem metric_secondJet_eq_riemann (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))
    (a b c d : Fin n) :
    T g a b c d = -(1 / 3) * (riemann g gi a c b d 0 + riemann g gi a d b c 0) := by
  -- the two Riemann atoms in `T`-form
  have R1 := riemann_at_zero_T g gi hg hgiC hgi0 hdg0 a c b d
  have R2 := riemann_at_zero_T g gi hg hgiC hgi0 hdg0 a d b c
  -- normalization equalities (metric + Schwarz symmetry) connecting the non-canonical atoms
  have s1 := T_symm_ab g hgsymm d c b a   -- T d c b a = T c d b a
  have s2 := T_symm_cd g hg c d b a       -- T c d b a = T c d a b  (= F)
  have s3 := T_symm_cd g hg a b d c       -- T a b d c = T a b c d  (= A)
  have s4 := T_symm_cd g hg b c d a       -- T b c d a = T b c a d  (= D)
  have s5 := T_symm_cd g hg b d c a       -- T b d c a = T b d a c  (= E)
  have s6 := T_symm_cd g hg a d c b       -- T a d c b = T a d b c  (= C)
  have s7 := T_symm_cd g hg a c d b       -- T a c d b = T a c b d  (= B)
  -- the four cyclic Gauss relations
  have hd := cyclicT_of_hGauss g hg hgsymm hGauss a b c d   -- A + B + D = 0
  have hc := cyclicT_of_hGauss g hg hgsymm hGauss a b d c   -- (A) + C + E = 0
  have hb := cyclicT_of_hGauss g hg hgsymm hGauss a c d b   -- (B) + (C) + F = 0
  have ha := cyclicT_of_hGauss g hg hgsymm hGauss b c d a   -- (D) + (E) + (F) = 0
  linarith [R1, R2, s1, s2, s3, s4, s5, s6, s7, hd, hc, hb, ha]

/-! ### The lowered-Riemann pair symmetry at the origin (from `T`-symmetry alone, no cyclic input). -/

/-- **`riemann_pair_symm_at_zero`.**  At the origin in the RNC first-order gauge the (first-index-up)
    Riemann `riemann g gi` already satisfies the fully-lowered pair symmetry
      `riemann g gi p q r s 0 = riemann g gi r s p q 0`,
    because at `0` the two `riemann_at_zero_T` expansions coincide term-by-term after `T_symm_ab`/
    `T_symm_cd` normalization (a pure `linarith` identity on opaque `T`-atoms — NO cyclic/`hGauss`
    input needed).  This discharges the J4-318 `hpair` hypothesis.  ⚠ NOT `a₁ = R/6`. -/
theorem riemann_pair_symm_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (p q r s : Fin n) :
    riemann g gi p q r s 0 = riemann g gi r s p q 0 := by
  have Ep := riemann_at_zero_T g gi hg hgiC hgi0 hdg0 p q r s
  have Er := riemann_at_zero_T g gi hg hgiC hgi0 hdg0 r s p q
  have t1 := T_symm_cd g hg p s r q       -- T p s r q = T p s q r
  have t2a := T_symm_ab g hgsymm s q r p  -- T s q r p = T q s r p
  have t2b := T_symm_cd g hg q s r p      -- T q s r p = T q s p r
  have t3a := T_symm_ab g hgsymm p r s q  -- T p r s q = T r p s q
  have t3b := T_symm_cd g hg r p s q      -- T r p s q = T r p q s
  have t4 := T_symm_cd g hg r q s p       -- T r q s p = T r q p s
  linarith [Ep, Er, t1, t2a, t2b, t3a, t3b, t4]

/-! ### A4 — `htr` reduced entirely to `hGauss`. -/

/-- **A4 — `htr_from_hGauss` (the capstone `htr` binder, R3 wall reduced to `hGauss`).**  Threading A3
    into J4-318's `htr_of_geometry` with the CONCRETE curvature `Rlow := riemann g gi · 0`,
    `Ric := ricci g gi · 0`:
      `∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = −(2/3)·ricci g gi c d 0`.
    The three `htr_of_geometry` hypotheses are DISCHARGED: `hjet` = A3 (`metric_secondJet_eq_riemann`),
    `hRic` = `ricci_diag_contract` (rfl-level), `hpair` = `riemann_pair_symm_at_zero`.  So the entire
    R3 Ricci-source coefficient rests on `hGauss` (+ the standard gauge/smoothness carries) ALONE.
    ⚠ NOT `a₁ = R/6`; `hGauss` stays the labelled gauge input, `a₁ = R/6` stays CONDITIONAL. -/
theorem htr_from_hGauss (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))
    (c d : Fin n) :
    (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * ricci g gi c d 0 := by
  refine htr_of_geometry g (fun p q r t => riemann g gi p q r t 0)
    (fun c d => ricci g gi c d 0) ?_ ?_ ?_ c d
  · -- hRic : ricci c d 0 = ∑ a, riemann a c a d 0  (the definitional diagonal contraction)
    intro c' d'; exact ricci_diag_contract g gi c' d'
  · -- hpair : riemann p q r t 0 = riemann r t p q 0
    intro p q r t; exact riemann_pair_symm_at_zero g gi hg hgsymm hgiC hgi0 hdg0 p q r t
  · -- hjet : T a b c d = −(1/3)(riemann a c b d 0 + riemann a d b c 0)  (= A3, defeq on the LHS)
    intro a b c' d'
    exact metric_secondJet_eq_riemann g gi hg hgsymm hgiC hgi0 hdg0 hGauss a b c' d'

end QIQTH.NCRiemannTwoJet

/-! ## Axiom checks — every new theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.NCRiemannTwoJet
#print axioms riemann_at_zero_T
#print axioms metric_secondJet_eq_riemann
#print axioms riemann_pair_symm_at_zero
#print axioms htr_from_hGauss
end AxiomChecks
