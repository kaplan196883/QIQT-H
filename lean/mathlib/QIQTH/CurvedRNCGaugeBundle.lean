import QIQTH.GaussGaugeToHgauge

/-!
# J4-525 — the `g^K` inverse-metric gauge bundle (`hinvF`/`hgi`/`hgiC`/`hΓ` + packaging)

The `a₁ = R/6` curved-signature capstone `A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary`
carries a GEOMETRIC-GAUGE half of its ~250-binder antecedent.  For the genuinely curved RNC witness
`CurvedRNCGaussWitness.curvedRNCMetric K` (`g^K = δ − (K/3)(‖x‖²δ − x⊗x)`, `Ric(0) = (n−1)Kδ ≠ 0`) the
`g`-only members (`hg`, `hgsymm`, `hg0`, `hdg0`, `hGauss`) are already banked (J4-523/524).  The MISSING
members are the ones that mention the **inverse metric** `gi`, which the antecedent binds as a FREE
function paired with `g` via

  `hinvF : ∀ y c d, (∑ σ, g y c σ · gi y σ d) = δ_{cd}`   (the inverse identity on ALL `y`).

## ★ The inverse must be the TRUE inverse — flat `δ` fails

`hinvF` with `gi = δ` collapses to `g y c d = δ_{cd}` for every `y`, i.e. FLATNESS — false for `g^K`
off the origin.  So `gi` must be the genuine Sherman–Morrison inverse.  Writing `α(x) = 1 − (K/3)‖x‖²`,
`β = K/3`, and using `α + β‖x‖² = 1`,

  `gi^K(x)_{ij} = (1/α(x))·(δ_{ij} − (K/3) x_i x_j)`   (`curvedRNCInv`).

For `K < 0` we have `α(x) = 1 + (|K|/3)‖x‖² ≥ 1 > 0` EVERYWHERE, so `gi^K` is globally smooth and the
inverse identity holds for ALL `y` (Sol-confirmed: `K > 0` has `α = 0` on `‖x‖² = 3/K`, so no global
inverse exists there — `K < 0` is the clean global move, and it keeps `Ric(0) = (n−1)Kδ ≠ 0`).

## What lands (all `gi := curvedRNCInv K`, `K < 0`, genuinely curved)

* `curvedRNCInv_zero`            — `gi^K(0) = δ`                         (`hgi`).
* `curvedRNCInv_contDiff`        — each `gi^K_{ij}` is `C^∞` (`K ≤ 0`)   (`hgiC`).
* `curvedRNCMetric_hinvF`        — ★ `∑_σ g^K_{cσ} gi^K_{σd} = δ_{cd}` ∀`y` (`K ≤ 0`) via the exact
                                   radial Gauss lemma — the FIRST curved inhabitant of `hinvF`.
* `curvedRNCMetric_christoffel_zero` — `Γ[g^K,gi^K](0) = 0`             (`hΓ`; any `gi`, from `∂g(0)=0`).
* `curvedRNC_geomGaugeBundle`    — ★ the packaged conjunction of the geometric-gauge half of the
                                   capstone antecedent for `g^K` (reusing banked `hg`/`hgsymm`/`hg0`/
                                   `hdg0`/`hGauss` + the new inverse-metric members).

⚠ SCOPE.  This packages the geometric+gauge HALF of the antecedent for `g^K`.  It does NOT make the full
capstone antecedent non-vacuous: the ANALYTIC piles (heat-operator Gaussian dominations `hEbound`/
`hEdom`/`hFdom`/`hgate`, Levi-series integrability/envelope, joint continuity on compact strips,
differentiation-under-∫ families) remain — those are genuine curved heat-kernel estimates, NOT
consequences of `g^K` being a smooth polynomial metric.  `hgpos` (`det g^K > 0`) is a further geometric
member left for a follow-on (clean via `Matrix.PosDef.det_pos` + Cauchy–Schwarz).  NOT `a₁ = R/6`.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.GaussLemmaGauge
open QIQTH.CurvedRNCGaussWitness QIQTH.GaussGaugeToHgauge
open scoped BigOperators Topology

namespace QIQTH.CurvedRNCGaugeBundle

variable {n : ℕ}

/-- **The true (Sherman–Morrison) inverse of the curved RNC witness** `g^K`.
    `gi^K(x)_{ij} = (1/(1 − (K/3)‖x‖²))·(δ_{ij} − (K/3) x_i x_j)`.  For `K < 0` the denominator
    `α(x) = 1 − (K/3)‖x‖² ≥ 1` is never zero, so `gi^K` is globally defined and `g^K·gi^K = δ`. -/
noncomputable def curvedRNCInv (K : ℝ) : Point n → Fin n → Fin n → ℝ :=
  fun x i j => (1 / (1 - (K / 3) * rncRadialSq x)) * ((if i = j then (1 : ℝ) else 0) - (K / 3) * x i * x j)

/-- The inverse witness at the centre is `δ`: `gi^K(0)_{ij} = δ_{ij}` (the `hgi` binder). -/
theorem curvedRNCInv_zero (K : ℝ) (i j : Fin n) :
    curvedRNCInv K (0 : Point n) i j = if i = j then (1 : ℝ) else 0 := by
  simp [curvedRNCInv]

/-- Each inverse component `x ↦ gi^K_{ij}(x)` is `C^∞` for `K ≤ 0` (the `hgiC` binder).  The denominator
    `α(x) = 1 − (K/3)‖x‖² ≥ 1 > 0` never vanishes, so `(α)⁻¹` is smooth and multiplies a polynomial. -/
theorem curvedRNCInv_contDiff (K : ℝ) (hK : K ≤ 0) (i j : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => curvedRNCInv K x i j) := by
  have hαne : ∀ x : Point n, (1 - (K / 3) * rncRadialSq x) ≠ 0 := by
    intro x
    have h1 : (K / 3) * rncRadialSq x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (rncRadialSq_nonneg x)
    exact ne_of_gt (by linarith)
  have hα : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : Point n => 1 - (K / 3) * rncRadialSq x) :=
    contDiff_const.sub (contDiff_const.mul rncRadialSq_contDiff)
  have hinv : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : Point n => (1 - (K / 3) * rncRadialSq x)⁻¹) :=
    hα.inv hαne
  have hpoly : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x : Point n => (if i = j then (1 : ℝ) else 0) - (K / 3) * x i * x j) :=
    contDiff_const.sub ((contDiff_const.mul (coord_contDiff i)).mul (coord_contDiff j))
  have hmul := hinv.mul hpoly
  simpa only [curvedRNCInv, one_div] using hmul

/-- **★ THE CURVED `hinvF` — `g^K · gi^K = δ` on ALL of `Point n`** (`K ≤ 0`).  The FIRST inhabitant of
    the inverse-identity binder beyond the flat metric.  The proof pulls `(1/α)` out and reduces the
    remaining sum to two pieces: `∑_σ g^K_{cσ}·δ_{σd} = g^K_{cd}` and — crucially — the EXACT radial
    Gauss lemma `∑_σ g^K_{cσ}·x_σ = x_c` (`metricGaussGauge_curvedRNC`), after which the correction
    terms cancel and `g^K_{cd} − (K/3) x_d x_c = δ_{cd}·α`, giving `(1/α)·α·δ_{cd} = δ_{cd}`. -/
theorem curvedRNCMetric_hinvF (K : ℝ) (hK : K ≤ 0) (y : Point n) (c d : Fin n) :
    (∑ σ, curvedRNCMetric K y c σ * curvedRNCInv K y σ d) = if c = d then (1 : ℝ) else 0 := by
  have hαne : (1 - (K / 3) * rncRadialSq y) ≠ 0 := by
    have h1 : (K / 3) * rncRadialSq y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (rncRadialSq_nonneg y)
    exact ne_of_gt (by linarith)
  -- per-term split, pulling `(1/α)` out.
  have hterm : ∀ σ : Fin n, curvedRNCMetric K y c σ * curvedRNCInv K y σ d
      = (1 / (1 - (K / 3) * rncRadialSq y)) *
        (curvedRNCMetric K y c σ * (if σ = d then (1 : ℝ) else 0)
          - (K / 3) * y d * (curvedRNCMetric K y c σ * y σ)) := by
    intro σ; simp only [curvedRNCInv]; ring
  -- the two reduced sums.
  have hgauss : (∑ σ, curvedRNCMetric K y c σ * y σ) = y c := metricGaussGauge_curvedRNC K y c
  have hite : (∑ σ, curvedRNCMetric K y c σ * (if σ = d then (1 : ℝ) else 0))
      = curvedRNCMetric K y c d := by
    have h1 : (∑ σ, curvedRNCMetric K y c σ * (if σ = d then (1 : ℝ) else 0))
        = ∑ σ, (if σ = d then curvedRNCMetric K y c σ else 0) :=
      Finset.sum_congr rfl (fun σ _ => by by_cases h : σ = d <;> simp [h])
    rw [h1, Finset.sum_ite_eq' Finset.univ d (fun σ => curvedRNCMetric K y c σ)]
    simp
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hite, hgauss,
      show curvedRNCMetric K y c d - (K / 3) * y d * y c
          = (if c = d then (1 : ℝ) else 0) * (1 - (K / 3) * rncRadialSq y) from by
        simp only [curvedRNCMetric]; ring,
      one_div, mul_comm (if c = d then (1 : ℝ) else 0) (1 - (K / 3) * rncRadialSq y),
      ← mul_assoc, inv_mul_cancel₀ hαne, one_mul]

/-- **`Γ[g^K, gi^K](0) = 0`** (the `hΓ` binder).  Holds for ANY inverse `gi` because every metric
    derivative `∂g^K(0)` vanishes (`curvedRNCMetric_pd_zero`): the witness sits in RNC gauge at `0`. -/
theorem curvedRNCMetric_christoffel_zero (K : ℝ) (k i j : Fin n) :
    christoffel (curvedRNCMetric K) (curvedRNCInv K) k i j (0 : Point n) = 0 := by
  simp only [christoffel]
  have hz : (∑ α, curvedRNCInv K (0 : Point n) k α *
        (pd (fun y => curvedRNCMetric K y α j) i (0 : Point n)
          + pd (fun y => curvedRNCMetric K y α i) j (0 : Point n)
          - pd (fun y => curvedRNCMetric K y i j) α (0 : Point n))) = 0 := by
    apply Finset.sum_eq_zero
    intro α _
    rw [curvedRNCMetric_pd_zero, curvedRNCMetric_pd_zero, curvedRNCMetric_pd_zero]; ring
  rw [hz, mul_zero]

/-- **★ THE PACKAGED GEOMETRIC-GAUGE BUNDLE for `g^K`** (`K < 0`, genuinely curved).  The conjunction of
    the geometric+gauge half of the capstone antecedent, with `g := curvedRNCMetric K`,
    `gi := curvedRNCInv K` — banked `g`-only members (`hg`, `hgsymm`, `hg0`, `hdg0`, `hGauss`) plus the
    new inverse-metric members (`hgi`, `hgiC`, `hinvF`) and the RNC Christoffel vanishing (`hΓ`).  Ready
    to feed the analytic instantiation of the antecedent.  ⚠ Does NOT include the analytic piles or
    `hgpos` — see file header; NOT `a₁ = R/6`. -/
theorem curvedRNC_geomGaugeBundle (K : ℝ) (hK : K < 0) :
    -- hg
    (∀ a b : Fin n, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCMetric K y a b))
    -- hgsymm
    ∧ (∀ (y : Point n) (a b : Fin n), curvedRNCMetric K y a b = curvedRNCMetric K y b a)
    -- hgiC
    ∧ (∀ a b : Fin n, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCInv K y a b))
    -- hg0
    ∧ (∀ i j : Fin n, curvedRNCMetric K (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    -- hgi
    ∧ (∀ i j : Fin n, curvedRNCInv K (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    -- hΓ
    ∧ (∀ k i j : Fin n, christoffel (curvedRNCMetric K) (curvedRNCInv K) k i j (0 : Point n) = 0)
    -- hdg0
    ∧ (∀ a b e : Fin n, pd (fun y : Point n => curvedRNCMetric K y a b) e (0 : Point n) = 0)
    -- hGauss (germ form the capstone consumes)
    ∧ (∀ i : Fin n, (fun x : Point n => ∑ j, curvedRNCMetric K x i j * x j)
        =ᶠ[𝓝 (0 : Point n)] (fun x : Point n => x i))
    -- hinvF
    ∧ (∀ (y : Point n) (c d : Fin n),
        (∑ σ, curvedRNCMetric K y c σ * curvedRNCInv K y σ d) = if c = d then (1 : ℝ) else 0) :=
  ⟨fun a b => curvedRNCMetric_contDiff K a b,
   fun y a b => curvedRNCMetric_symm K y a b,
   fun a b => curvedRNCInv_contDiff K (le_of_lt hK) a b,
   fun i j => curvedRNCMetric_zero K i j,
   fun i j => curvedRNCInv_zero K i j,
   fun k i j => curvedRNCMetric_christoffel_zero K k i j,
   fun a b e => curvedRNCMetric_pd_zero K a b e,
   fun i => hGaussGerm_curvedRNC K i,
   fun y c d => curvedRNCMetric_hinvF K (le_of_lt hK) y c d⟩

end QIQTH.CurvedRNCGaugeBundle

section AxiomChecks
open QIQTH.CurvedRNCGaugeBundle
#print axioms curvedRNCInv_zero
#print axioms curvedRNCInv_contDiff
#print axioms curvedRNCMetric_hinvF
#print axioms curvedRNCMetric_christoffel_zero
#print axioms curvedRNC_geomGaugeBundle
end AxiomChecks
