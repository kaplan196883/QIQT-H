/-
  NCGaussToCyclicT — J4-334 brick A2 of the Sol-consult-#10 plan.  From the Gauss-lemma gauge input
  `hGauss` to the cyclic identity of the four-index metric 2-jet atom `T`.

  ONE brick of the `a₁ = R/6` heat-kernel campaign.  ⚠ NOT `a₁ = R/6`; this file proves NOTHING new
  about `R/6`.  It supplies the honest linear-algebra bridge from the (satisfiable) normal-coordinate
  Gauss identity to the cyclic 2-jet relation; `hGauss` is one further labelled GAUGE input (normal
  coordinates exist, so it is satisfiable — deriving it from the `exp`-pullback tower is a separate
  Gauss-lemma campaign, not attempted here).  No `:= True`, no new axioms, no vacuity.

  ═══════════════════════════════════════════════════════════════════════════════════════════════
  `T g a b c d := pd (fun y => pd (fun w => g w a b) d y) c 0`  is the mixed second coordinate partial
  `∂_c ∂_d g_{ab}(0)`, in the EXACT `pd`-nesting convention of the capstone's `htr` binder
  (`ProviderSideExports.lean:177` / `RicciSourceCoeff`): the diagonal `T g a a c d` is the `htr` summand
  `pd (fun y => pd (fun w => g w a a) d y) c 0`.

  CONTENT:
    • `pd_eventuallyEq`     — the germ-local partial `∂_i` propagates an eventual equality: if `F =ᶠ H`
                              near `x` then `∂_i F =ᶠ ∂_i H` near `x` (so the third partials of two
                              germ-equal fields agree).
    • `pd3_coord_zero`      — the third partial of a coordinate (linear) function vanishes.
    • `T`, `T_symm_cd`, `T_symm_ab` — the atom and its two symmetries (Schwarz + metric symmetry).
    • `cyclicT_gauss`       — (Q1) differentiate `hGauss` thrice: `T i r p q + T i q p r + T i p q r = 0`.
    • `cyclicT_of_hGauss`   — (Q2) the four-instance linear combination
                              `T a b c d + T a c b d + T b c a d = 0`.
  ═══════════════════════════════════════════════════════════════════════════════════════════════
  No `sorry` (this header prose excepted), no new axioms, no `:= True`, no vacuous/unsatisfiable carries.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.JacobianRadial
import QIQTH.NCGaussPd3

open QIQTH.Curvature
open QIQTH.NCGaussPd3
open scoped BigOperators Topology

namespace QIQTH.NCGaussToCyclicT

variable {n : ℕ}

/-! ### The germ-local partial propagates eventual equality. -/

/-- **`∂_i` lifts an eventual equality.**  If `F =ᶠ[𝓝 x] H` then `(fun z => ∂_i F z) =ᶠ[𝓝 x] (fun z => ∂_i H z)`:
    on a neighborhood of `x` the two fields agree, so at each nearby point their germs agree and the
    partials (germ-local, `pd_congr_of_eventuallyEq`) coincide. -/
theorem pd_eventuallyEq {F H : Point n → ℝ} {i : Fin n} {x : Point n}
    (hFH : F =ᶠ[𝓝 x] H) : (fun z => pd F i z) =ᶠ[𝓝 x] (fun z => pd H i z) := by
  have h2 : ∀ᶠ y in 𝓝 x, F =ᶠ[𝓝 y] H := hFH.eventually_nhds
  filter_upwards [h2] with y hy
  exact QIQTH.JacobianRadial.pd_congr_of_eventuallyEq hy

/-! ### The third partial of a coordinate function vanishes. -/

/-- **`∂_p ∂_q ∂_r (fun x => x i) (0) = 0`.**  The first partial is the constant Kronecker delta, whose
    further partials vanish. -/
theorem pd3_coord_zero (i p q r : Fin n) :
    pd (fun y => pd (fun z => pd (fun x => x i) r z) q y) p 0 = 0 := by
  have h1 : (fun z => pd (fun x : Point n => x i) r z)
      = (fun _ => (if i = r then (1 : ℝ) else 0)) := funext (fun z => pd_coord i r z)
  rw [h1]
  have h2 : (fun y => pd (fun _ : Point n => (if i = r then (1 : ℝ) else 0)) q y)
      = (fun _ => (0 : ℝ)) := funext (fun y => pd_const _ q y)
  rw [h2, pd_const]

/-! ### The 2-jet atom `T` and its symmetries. -/

/-- **The four-index metric 2-jet atom** `T g a b c d = ∂_c ∂_d g_{ab}(0)`, in the capstone's `htr`
    `pd`-nesting convention. -/
noncomputable def T (g : Point n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  pd (fun y => pd (fun w => g w a b) d y) c 0

/-- **Schwarz symmetry of `T` in its derivative indices** `∂_c ∂_d = ∂_d ∂_c`. -/
theorem T_symm_cd (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (a b c d : Fin n) :
    T g a b c d = T g a b d c := by
  simp only [T]
  exact pd_comm (fun w => g w a b) c d 0 (hg a b)

/-- **Metric symmetry of `T` in its component indices** `g_{ab} = g_{ba}`. -/
theorem T_symm_ab (g : Point n → Fin n → Fin n → ℝ)
    (hgsymm : ∀ y a b, g y a b = g y b a) (a b c d : Fin n) :
    T g a b c d = T g b a c d := by
  simp only [T]
  have h : (fun w => g w a b) = (fun w => g w b a) := funext (fun w => hgsymm w a b)
  rw [h]

/-! ### Q1 — the cyclic identity from the Gauss-lemma gauge input. -/

/-- **Q1 — `cyclicT_gauss`.**  Differentiating the Gauss identity `∑_j g_{ij} x^j = x^i` three times at
    the origin, via `pd3_sum` (LHS) and `pd3_coord_zero` (RHS, the linear function's third partial
    vanishes), gives the cyclic 2-jet relation `T i r p q + T i q p r + T i p q r = 0`.  The germ-local
    `pd_eventuallyEq` (applied twice) + `pd_congr_of_eventuallyEq` transfer the eventual equality through
    the three nested partials.  `hGauss` is the labelled gauge input (satisfiable). ⚠ NOT `a₁ = R/6`. -/
theorem cyclicT_gauss (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))
    (i p q r : Fin n) :
    T g i r p q + T g i q p r + T g i p q r = 0 := by
  -- commute the product to `P3`'s form and re-express the Gauss identity
  have hcomm : (fun x : Point n => ∑ j, g x i j * x j) = (fun x => ∑ j, x j * g x i j) :=
    funext (fun x => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
  have hG' : (fun x : Point n => ∑ j, x j * g x i j) =ᶠ[𝓝 0] (fun x => x i) := hcomm ▸ hGauss i
  -- transfer the eventual equality through the three nested partials
  have e1 := pd_eventuallyEq (i := r) hG'
  have e2 := pd_eventuallyEq (i := q) e1
  have hcong := QIQTH.JacobianRadial.pd_congr_of_eventuallyEq (i := p) e2
  -- evaluate the RHS (linear function) and the LHS (`P3`)
  rw [pd3_coord_zero i p q r] at hcong
  have hLHS : pd (fun y => pd (fun z => pd (fun x => ∑ j, x j * g x i j) r z) q y) p 0
      = T g i r p q + T g i q p r + T g i p q r := by
    have hsum := pd3_sum (n := n) (fun j => fun x => g x i j) (fun j => hg i j) p q r
    simpa only [T] using hsum
  rw [hLHS] at hcong
  exact hcong

/-! ### Q2 — the four-instance linear combination. -/

/-- **Q2 — `cyclicT_of_hGauss`.**  The cyclic identity `cyclicT_gauss` at four index choices, normalized
    by Schwarz (`T_symm_cd`) and metric symmetry (`T_symm_ab`), gives four linear relations
    `h₁ : A+B+C=0`, `h₂ : A+D+E=0`, `h₃ : B+D+F=0`, `h₄ : C+E+F=0` among the six 2-jet atoms
    `A=T abcd`, `B=T acbd`, `C=T adbc`, `D=T bcad`, `E=T bdac`, `F=T cdab`.  Then
    `2(A+B+D) = h₁+h₂+h₃−h₄ = 0`, i.e. `T a b c d + T a c b d + T b c a d = 0`.
    ⚠ NOT `a₁ = R/6`. -/
theorem cyclicT_of_hGauss (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))
    (a b c d : Fin n) :
    T g a b c d + T g a c b d + T g b c a d = 0 := by
  have h1 := cyclicT_gauss g hg hGauss a c d b
  rw [T_symm_cd g hg a d c b, T_symm_cd g hg a c d b] at h1
  -- h1 : T g a b c d + T g a d b c + T g a c b d = 0
  have h2 := cyclicT_gauss g hg hGauss b c d a
  rw [T_symm_ab g hgsymm b a c d, T_symm_cd g hg b d c a, T_symm_cd g hg b c d a] at h2
  -- h2 : T g a b c d + T g b d a c + T g b c a d = 0
  have h3 := cyclicT_gauss g hg hGauss c a b d
  rw [T_symm_ab g hgsymm c b a d, T_symm_ab g hgsymm c a b d] at h3
  -- h3 : T g c d a b + T g b c a d + T g a c b d = 0
  have h4 := cyclicT_gauss g hg hGauss d b c a
  rw [T_symm_ab g hgsymm d a b c, T_symm_cd g hg d c b a, T_symm_ab g hgsymm d c a b,
      T_symm_cd g hg d b c a, T_symm_ab g hgsymm d b a c] at h4
  -- h4 : T g a d b c + T g c d a b + T g b d a c = 0
  linarith [h1, h2, h3, h4]

end QIQTH.NCGaussToCyclicT
