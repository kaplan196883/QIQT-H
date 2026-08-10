import QIQTH.RNCExpansion
import QIQTH.CurvedRNCGaussWitness

/-!
# J4-524 — the `GaussHessianCyclic → hgauge` bridge

`RNCExpansion.rnc_htr_of_gauge` (the RNC3 metric-Hessian-trace theorem forcing
`tr ∂∂g(0) = −⅔ Ric`, hence the `⅙` measure coefficient) consumes the christoffel-symmetrization
**normal-coordinate gauge**

  `hgauge : ∀ i a b c, ∂_a Γ^i_{bc}(0) + ∂_b Γ^i_{ca}(0) + ∂_c Γ^i_{ab}(0) = 0`.

This file COLLAPSES that Christoffel-level gauge to a purely **metric-second-derivative** identity,
the **Gauss-Hessian cyclic gauge**

  `GaussHessianCyclic g : ∀ i p q r, ∂_q∂_p g_{ir}(0) + ∂_r∂_q g_{ip}(0) + ∂_p∂_r g_{iq}(0) = 0`,

which is the once-more-differentiated shadow of the radial Gauss gauge `∑_j g_{ij}(x) x^j = x^i`
(differentiate three times at `0`; the linear `x^j` factor forces exactly one derivative onto it,
leaving the cyclic Hessian sum, while the RHS `x^i` has vanishing third jet).

## What lands

* `GaussHessianCyclic`                 — the metric-Hessian cyclic gauge (the second-derivative form).
* `hgauge_of_gaussHessianCyclic`       — ★ the bridge: `GaussHessianCyclic g` (with `g(0)=δ` via `gi(0)=δ`,
                                          `∂g(0)=0`, `g` symmetric, smoothness) ⟹ the christoffel-symmetrization
                                          `hgauge` consumed by `rnc_htr_of_gauge`.  Pure jet algebra atop the
                                          banked `pd_christoffel_origin` (∂Γ(0) = ½·three-Hessian) + Schwarz
                                          (`pd_comm`) + metric symmetry.

## Curved-generic (the gate)

The bridge assumes ONLY the RNC conditions (`g(0)=δ`, `∂g(0)=0`, symmetry, smoothness) shared by the
flat metric AND the genuinely curved witness `CurvedRNCGaussWitness.curvedRNCMetric K` (`Ric(0)≠0` for
`K≠0`).  It NEVER forces `g=δ`.  `GaussHessianCyclic` itself holds for `g^K` (its `∂∂g^K(0)` cyclic sum
vanishes by δ-algebra), so the derived `hgauge`, fed through `rnc_htr_of_gauge`, carries the genuine
`htr = −⅔ Ric ≠ 0`.

⚠ SCOPE.  This is the `∂∂g → hgauge` (curvature-side) half of the radial-gauge chain
`MetricGaussGauge g → GaussHessianCyclic g → hgauge g`.  The remaining `MetricGaussGauge → GaussHessianCyclic`
link (triple-differentiating the radial gauge) is NOT in this file.  NOT `a₁ = R/6`.
-/

open QIQTH.Curvature QIQTH.RNCExpansion QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness
open QIQTH.ResidualFactorization
open scoped BigOperators

namespace QIQTH.GaussGaugeToHgauge

variable {n : ℕ}

/-- **The Gauss-Hessian cyclic gauge.**  The cyclic sum of the metric Hessian at the origin vanishes:
    `∂_q∂_p g_{ir}(0) + ∂_r∂_q g_{ip}(0) + ∂_p∂_r g_{iq}(0) = 0` (cyclic in `p,q,r` with `i` fixed as the
    first metric index).  This is the once-more-differentiated form of the radial Gauss gauge
    `∑_j g_{ij}(x) x^j = x^i`. -/
def GaussHessianCyclic (g : Point n → Fin n → Fin n → ℝ) : Prop :=
  ∀ i p q r : Fin n,
    pd (fun y => pd (fun w => g w i r) p y) q 0
    + pd (fun y => pd (fun w => g w i p) q y) r 0
    + pd (fun y => pd (fun w => g w i q) r y) p 0 = 0

/-- **★ THE BRIDGE — `GaussHessianCyclic g` discharges the christoffel-symmetrization gauge `hgauge`.**
    Given the RNC conditions (`g(0)=δ` via `gi(0)=δ`, `∂g(0)=0`, `g` symmetric, smoothness) and the
    metric-Hessian cyclic gauge, the totally-symmetrized Christoffel derivative vanishes at `0`.

    Route (pure jet algebra).  `pd_christoffel_origin` expands each `∂Γ^i(0)` to `½` of a three-term
    metric-Hessian sum.  The nine resulting Hessian atoms split into a "positive" block (the cyclic
    `∂∂g_{i·}` sum, `= 2·` a `GaussHessianCyclic` instance) and a "negative" block `N`
    (`∑ ∂∂ g_{··}` with `i` in a derivative slot); three further `GaussHessianCyclic` instances plus
    Schwarz (`pd_comm`) and metric symmetry force `N = 0`.  Both blocks vanish, so the symmetrized
    `∂Γ` sum is `0`. -/
theorem hgauge_of_gaussHessianCyclic
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hG3 : GaussHessianCyclic g)
    (i a b c : Fin n) :
    pd (fun y => christoffel g gi i b c y) a 0
      + pd (fun y => christoffel g gi i c a y) b 0
      + pd (fun y => christoffel g gi i a b y) c 0 = 0 := by
  rw [pd_christoffel_origin g gi hg hgi hgi0 hdg0 i b c a,
      pd_christoffel_origin g gi hg hgi hgi0 hdg0 i c a b,
      pd_christoffel_origin g gi hg hgi hgi0 hdg0 i a b c]
  -- Schwarz commutations pairing the doubled positive-block Hessians.
  have sB2 : pd (fun y => pd (fun w => g w i c) b y) a 0
      = pd (fun y => pd (fun w => g w i c) a y) b 0 :=
    pd_comm (fun w => g w i c) a b 0 (hg i c)
  have sC1 : pd (fun y => pd (fun w => g w i b) c y) a 0
      = pd (fun y => pd (fun w => g w i b) a y) c 0 :=
    pd_comm (fun w => g w i b) a c 0 (hg i b)
  have sC2 : pd (fun y => pd (fun w => g w i a) c y) b 0
      = pd (fun y => pd (fun w => g w i a) b y) c 0 :=
    pd_comm (fun w => g w i a) b c 0 (hg i a)
  -- The four Gauss-Hessian cyclic instances (positive block + three for `N`).
  have gF := hG3 i a b c
  have g1 := hG3 b i a c
  have g2 := hG3 c i b a
  have g3 := hG3 a i c b
  -- Bridge the `N`-block cross terms via symmetry + Schwarz.
  have eP1 : pd (fun y => pd (fun w => g w b i) a y) c 0
      = pd (fun y => pd (fun w => g w i b) c y) a 0 := by
    rw [show (fun w => g w b i) = (fun w => g w i b) from funext (fun w => hsymm w b i)]
    exact pd_comm (fun w => g w i b) c a 0 (hg i b)
  have eP2 : pd (fun y => pd (fun w => g w c i) b y) a 0
      = pd (fun y => pd (fun w => g w i c) b y) a 0 := by
    rw [show (fun w => g w c i) = (fun w => g w i c) from funext (fun w => hsymm w c i)]
  have eP3 : pd (fun y => pd (fun w => g w a i) c y) b 0
      = pd (fun y => pd (fun w => g w i a) c y) b 0 := by
    rw [show (fun w => g w a i) = (fun w => g w i a) from funext (fun w => hsymm w a i)]
  have eQ1 : pd (fun y => pd (fun w => g w b a) c y) i 0
      = pd (fun y => pd (fun w => g w a b) i y) c 0 := by
    rw [show (fun w => g w b a) = (fun w => g w a b) from funext (fun w => hsymm w b a)]
    exact pd_comm (fun w => g w a b) i c 0 (hg a b)
  have eQ2 : pd (fun y => pd (fun w => g w c b) a y) i 0
      = pd (fun y => pd (fun w => g w b c) i y) a 0 := by
    rw [show (fun w => g w c b) = (fun w => g w b c) from funext (fun w => hsymm w c b)]
    exact pd_comm (fun w => g w b c) i a 0 (hg b c)
  have eQ3 : pd (fun y => pd (fun w => g w a c) b y) i 0
      = pd (fun y => pd (fun w => g w c a) i y) b 0 := by
    rw [show (fun w => g w a c) = (fun w => g w c a) from funext (fun w => hsymm w a c)]
    exact pd_comm (fun w => g w c a) i b 0 (hg c a)
  linarith [sB2, sC1, sC2, gF, g1, g2, g3, eP1, eP2, eP3, eQ1, eQ2, eQ3]

/-! ## The curved witness `g^K` satisfies `GaussHessianCyclic` — self-contained curved inhabitant. -/

/-- **First metric derivative of the curved witness (as a function).**
    `∂_p g^K_{ir}(x) = −(K/3)(2 δ_{ir} x_p − (δ_{ip} x_r + δ_{rp} x_i))`. -/
theorem pd_curvedRNCMetric_fun (K : ℝ) (i r p : Fin n) :
    (fun x : Point n => pd (fun w => curvedRNCMetric K w i r) p x)
      = (fun x => -(K / 3) * (2 * (if i = r then (1:ℝ) else 0) * x p
          - ((if i = p then (1:ℝ) else 0) * x r + (if r = p then (1:ℝ) else 0) * x i))) := by
  funext x
  have hP1 : PdiffAt (fun _ : Point n => (if i = r then (1:ℝ) else 0)) p x :=
    PdiffAt_of_contDiff _ contDiff_const p x
  have hP3 : PdiffAt (fun w : Point n => rncRadialSq w * (if i = r then (1:ℝ) else 0)
      - w i * w r) p x :=
    PdiffAt_of_contDiff _ ((rncRadialSq_contDiff.mul contDiff_const).sub
      ((coord_contDiff i).mul (coord_contDiff r))) p x
  have hP2 : PdiffAt (fun w : Point n => K / 3 * (rncRadialSq w * (if i = r then (1:ℝ) else 0)
      - w i * w r)) p x :=
    PdiffAt_of_contDiff _ (contDiff_const.mul ((rncRadialSq_contDiff.mul contDiff_const).sub
      ((coord_contDiff i).mul (coord_contDiff r)))) p x
  have hP4 : PdiffAt (fun w : Point n => rncRadialSq w * (if i = r then (1:ℝ) else 0)) p x :=
    PdiffAt_of_contDiff _ (rncRadialSq_contDiff.mul contDiff_const) p x
  have hP5 : PdiffAt (fun w : Point n => w i * w r) p x :=
    PdiffAt_of_contDiff _ ((coord_contDiff i).mul (coord_contDiff r)) p x
  have hP6 : PdiffAt (rncRadialSq : Point n → ℝ) p x :=
    PdiffAt_of_contDiff _ rncRadialSq_contDiff p x
  have hP8 : PdiffAt (fun w : Point n => w i) p x :=
    PdiffAt_of_contDiff _ (coord_contDiff i) p x
  have hP9 : PdiffAt (fun w : Point n => w r) p x :=
    PdiffAt_of_contDiff _ (coord_contDiff r) p x
  simp only [curvedRNCMetric]
  rw [pd_sub _ _ p x hP1 hP2, pd_const, pd_const_mul _ _ p x hP3,
      pd_sub _ _ p x hP4 hP5, pd_mul _ _ p x hP6 hP1, pd_mul _ _ p x hP8 hP9]
  simp only [pd_const, pd_rncRadialSq, pd_coord]
  ring

/-- **Second metric derivative of the curved witness at the origin.**
    `∂_q∂_p g^K_{ir}(0) = −(K/3)(2 δ_{ir} δ_{pq} − (δ_{ip} δ_{rq} + δ_{rp} δ_{iq}))`. -/
theorem curvedRNCMetric_pd_pd (K : ℝ) (i r p q : Fin n) :
    pd (fun y => pd (fun w => curvedRNCMetric K w i r) p y) q 0
      = -(K / 3) * (2 * (if i = r then (1:ℝ) else 0) * (if p = q then (1:ℝ) else 0)
          - ((if i = p then (1:ℝ) else 0) * (if r = q then (1:ℝ) else 0)
             + (if r = p then (1:ℝ) else 0) * (if i = q then (1:ℝ) else 0))) := by
  rw [pd_curvedRNCMetric_fun]
  have h1 : PdiffAt (fun x : Point n => 2 * (if i = r then (1:ℝ) else 0) * x p
      - ((if i = p then (1:ℝ) else 0) * x r + (if r = p then (1:ℝ) else 0) * x i)) q 0 :=
    PdiffAt_of_contDiff _ (((contDiff_const.mul (coord_contDiff p)).sub
      ((contDiff_const.mul (coord_contDiff r)).add (contDiff_const.mul (coord_contDiff i)))))
      q (0 : Point n)
  have h2 : PdiffAt (fun x : Point n => 2 * (if i = r then (1:ℝ) else 0) * x p) q (0 : Point n) :=
    PdiffAt_of_contDiff _ (contDiff_const.mul (coord_contDiff p)) q 0
  have h3 : PdiffAt (fun x : Point n => (if i = p then (1:ℝ) else 0) * x r
      + (if r = p then (1:ℝ) else 0) * x i) q (0 : Point n) :=
    PdiffAt_of_contDiff _ ((contDiff_const.mul (coord_contDiff r)).add
      (contDiff_const.mul (coord_contDiff i))) q 0
  have h4 : PdiffAt (fun x : Point n => (if i = p then (1:ℝ) else 0) * x r) q (0 : Point n) :=
    PdiffAt_of_contDiff _ (contDiff_const.mul (coord_contDiff r)) q 0
  have h5 : PdiffAt (fun x : Point n => (if r = p then (1:ℝ) else 0) * x i) q (0 : Point n) :=
    PdiffAt_of_contDiff _ (contDiff_const.mul (coord_contDiff i)) q 0
  have hxp : PdiffAt (fun x : Point n => x p) q (0 : Point n) :=
    PdiffAt_of_contDiff _ (coord_contDiff p) q 0
  have hxr : PdiffAt (fun x : Point n => x r) q (0 : Point n) :=
    PdiffAt_of_contDiff _ (coord_contDiff r) q 0
  have hxi : PdiffAt (fun x : Point n => x i) q (0 : Point n) :=
    PdiffAt_of_contDiff _ (coord_contDiff i) q 0
  rw [pd_const_mul _ _ q 0 h1, pd_sub _ _ q 0 h2 h3, pd_add _ _ q 0 h4 h5,
      pd_const_mul _ _ q 0 hxp, pd_const_mul _ _ q 0 hxr, pd_const_mul _ _ q 0 hxi]
  simp only [pd_coord]

/-- **★ The curved witness satisfies the Gauss-Hessian cyclic gauge.**  A concrete `∂∂g^K(0)`
    computation: the cyclic sum of Hessians vanishes by δ-algebra, for every `K`, `n`. -/
theorem curvedRNCMetric_gaussHessianCyclic (K : ℝ) :
    GaussHessianCyclic (curvedRNCMetric (n := n) K) := by
  intro i p q r
  rw [curvedRNCMetric_pd_pd K i r p q, curvedRNCMetric_pd_pd K i p q r,
      curvedRNCMetric_pd_pd K i q r p]
  simp only [@eq_comm _ r q, @eq_comm _ r p, @eq_comm _ q p]
  ring

/-- `∂g^K(0) = 0`: the curved witness sits in normal-coordinate gauge at the origin. -/
theorem curvedRNCMetric_pd_zero (K : ℝ) (a b e : Fin n) :
    pd (fun y => curvedRNCMetric K y a b) e 0 = 0 := by
  have h := congrFun (pd_curvedRNCMetric_fun K a b e) (0 : Point n)
  rw [h]; simp

/-! ## Self-contained curved witness: `g^K` discharges `hgauge` (via its flat inverse `δ`). -/

/-- **★ The curved witness `g^K` discharges the christoffel-symmetrization gauge `hgauge`.**  The FIRST
    genuinely curved (`Ric(0)≠0`) inhabitant of the normal-coordinate Christoffel gauge, obtained by
    feeding the concrete `GaussHessianCyclic (g^K)` through the bridge (with the flat inverse `δ`, whose
    only role in `pd_christoffel_origin`/`rnc_htr_of_gauge` at the origin is `gi(0)=δ`). -/
theorem curvedRNCMetric_hgauge (K : ℝ) (i a b c : Fin n) :
    pd (fun y => christoffel (curvedRNCMetric K) (flatMetric n) i b c y) a 0
      + pd (fun y => christoffel (curvedRNCMetric K) (flatMetric n) i c a y) b 0
      + pd (fun y => christoffel (curvedRNCMetric K) (flatMetric n) i a b y) c 0 = 0 :=
  hgauge_of_gaussHessianCyclic (curvedRNCMetric K) (flatMetric n)
    (fun a b => curvedRNCMetric_contDiff K a b)
    (fun a b => by simp only [flatMetric]; exact contDiff_const)
    (fun i j => by simp [flatMetric, Matrix.one_apply])
    (fun a b e => curvedRNCMetric_pd_zero K a b e)
    (fun y a b => curvedRNCMetric_symm K y a b)
    (curvedRNCMetric_gaussHessianCyclic K) i a b c

/-- **★ `htr` for `g^K` DERIVED FROM ITS GAUGE.**  The metric-Hessian trace equals `−⅔ Ric`, now
    obtained through `rnc_htr_of_gauge` from the (concretely discharged) Christoffel gauge — no longer a
    carried datum. -/
theorem curvedRNCMetric_htr_from_gauge (K : ℝ) (c d : Fin n) :
    (∑ a, pd (fun y => pd (fun w => curvedRNCMetric K w a a) d y) c 0)
      = -(2 / 3) * ricci (curvedRNCMetric K) (flatMetric n) c d 0 :=
  rnc_htr_of_gauge (curvedRNCMetric K) (flatMetric n)
    (fun a b => curvedRNCMetric_contDiff K a b)
    (fun a b => by simp only [flatMetric]; exact contDiff_const)
    (fun i j => by simp [flatMetric, Matrix.one_apply])
    (fun a b e => curvedRNCMetric_pd_zero K a b e)
    (fun y a b => curvedRNCMetric_symm K y a b)
    (fun i a b c => curvedRNCMetric_hgauge K i a b c) c d

/-- **★ The Ricci tensor of `g^K` PINNED by the gauge.**  Combining the gauge-derived `htr` with the
    direct metric-Hessian trace `curvedRNCMetric_ricci_trace` forces `Ric(0) = (n−1)K δ` — genuine,
    nonzero curvature for `K ≠ 0`, `n ≥ 2`, derived from `g^K`'s single exact radial Gauss gauge. -/
theorem curvedRNCMetric_ricci_from_gauge (K : ℝ) (c d : Fin n) :
    ricci (curvedRNCMetric K) (flatMetric n) c d 0
      = ((n : ℝ) - 1) * K * (if d = c then (1:ℝ) else 0) := by
  have hS' : (∑ a : Fin n, (if a = d then (1:ℝ) else 0) * (if a = c then (1:ℝ) else 0))
      = if d = c then (1:ℝ) else 0 := by
    rw [show (∑ a : Fin n, (if a = d then (1:ℝ) else 0) * (if a = c then (1:ℝ) else 0))
          = ∑ a : Fin n, (if a = d then (if a = c then (1:ℝ) else 0) else 0) from
        Finset.sum_congr rfl (fun a _ => by by_cases h : a = d <;> simp [h]),
        Finset.sum_ite_eq' Finset.univ d (fun a => if a = c then (1:ℝ) else 0)]
    simp
  have hsum : (∑ a, pd (fun y => pd (fun w => curvedRNCMetric K w a a) d y) c 0)
      = -(2 / 3) * ((n : ℝ) - 1) * K * (if d = c then (1:ℝ) else 0) := by
    have hcomp : ∀ a : Fin n, pd (fun y => pd (fun w => curvedRNCMetric K w a a) d y) c 0
        = -(K / 3) * 2 * (if d = c then (1:ℝ) else 0)
          - -(K / 3) * 2 * ((if a = d then (1:ℝ) else 0) * (if a = c then (1:ℝ) else 0)) := by
      intro a
      have haa : (if a = a then (1:ℝ) else 0) = 1 := if_pos rfl
      rw [curvedRNCMetric_pd_pd K a a d c, haa]; ring
    rw [Finset.sum_congr rfl (fun a _ => hcomp a), Finset.sum_sub_distrib, Finset.sum_const,
        ← Finset.mul_sum, hS']
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h1 := curvedRNCMetric_htr_from_gauge K c d
  linear_combination (3 / 2 : ℝ) * h1 - (3 / 2 : ℝ) * hsum

end QIQTH.GaussGaugeToHgauge

section AxiomChecks
open QIQTH.GaussGaugeToHgauge
#print axioms hgauge_of_gaussHessianCyclic
#print axioms curvedRNCMetric_gaussHessianCyclic
#print axioms curvedRNCMetric_hgauge
#print axioms curvedRNCMetric_htr_from_gauge
#print axioms curvedRNCMetric_ricci_from_gauge
end AxiomChecks
