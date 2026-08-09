/-
  TransportEqZero — J4-505: the REDUCTION of the k=0 van-Vleck transport equation `hT0`
  (`𝒯u₀ = 0`, re-expressed as `𝒢·u₀ − 2·C(u₀) = 0`) to a clean scalar RADIAL equation, via the
  banked flat-Gaussian gradient calculus — plus the exact isolation of the residual geodesic input.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  This file does **NOT** derive `hT0`, and proves NOTHING new about `a₁ = R/6`.
  It performs the *tractable half* of the J4-505 attack: it rewrites the OFF-diagonal cross-gradient
  `C(u₀) = Σᵢⱼ gⁱʲ ∂ᵢG ∂ⱼu₀` EXACTLY, using ONLY the banked flat-Gaussian gradient
  `∂ᵢG = −(xᵢ/2t)·G` (`FlatHeatEquation.gaussDdim_pd_i`), into
      `C(u) = −(1/2t)·G·R_g(u)`,   `R_g(u) := Σᵢⱼ gⁱʲ xᵢ ∂ⱼu`  (the *metric radial field*).
  Consequently `hT0` collapses to the scalar RADIAL equation
      hRad :  𝒢·u₀ + (1/t)·G·R_g(u₀) = 0        (`⇔  𝒢·u₀ = −(1/t)·G·R_g(u₀)`),
  and `hT0_of_radial` DISCHARGES `hT0` from `hRad` (feeding `ResidualFactorization` unchanged).

  The CLOSURE of `hRad` is NOT here.  Per the eikonal decomposition (Sol J4-505),
      𝒢·u₀ − 2C(u₀) = (G/4t²)(‖x‖² − Σᵢⱼgⁱʲxᵢxⱼ)·u₀ + (G/2t)·[(tr g⁻¹ − n − ΣgⁱʲΓᵏᵢⱼxₖ)·u₀ + 2R_g(u₀)],
  closing `hRad` needs the coordinate **Gauss lemma** `Σᵢ gⁱʲ xᵢ = xʲ` (giving `R_g = radialDeriv`,
  the Euler field, and `Σgⁱʲxᵢxⱼ = ‖x‖²`) plus the contracted **volume/Laplacian identity**
  `Δ_g(½‖x‖²) = n + r∂_r log√det g` — the checkpointed geodesic `r∂_r` machinery
  (`HeatTransportRecursion` STRETCH #4, absent from Mathlib).  `metricRadial_eq_radialDeriv_of_gaussLemma`
  isolates EXACTLY that Gauss-lemma input as an explicit hypothesis.  We CARRY `hRad`; we do NOT derive it.
  No `sorry`, no `:= True`, no new axioms, std-3.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── WHAT LANDS (ns `QIQTH.TransportEqZero`).
    • `metricRadial`                       — the metric radial field `R_g(u) = Σᵢⱼ gⁱʲ xᵢ ∂ⱼu`.
    • `crossGrad_eq_metricRadial`          — ★ the banked cross-gradient reduction `C = −(1/2t)·G·R_g`.
    • `transportOffDiag_eq_radial`         — ★ the EXACT rewrite `𝒢·u − 2C(u) = 𝒢·u + (1/t)·G·R_g(u)`.
    • `hT0_of_radial`                      — ★★ `hT0` discharged FROM the scalar radial input `hRad`.
    • `residual_factorization_of_radial`   — the banked factorization with `hT0` replaced by `hRad`.
    • `metricRadial_eq_radialDeriv_of_gaussLemma` — isolates the Gauss-lemma input `Σᵢ gⁱʲxᵢ = xʲ`
                                             that turns `R_g` into the Euler field `radialDeriv`.
    • `metricRadial_flat_eq_radialDeriv`   — flat check: `R_δ(u) = radialDeriv u` (Gauss lemma trivial).
    • `metricRadial_flat_rncRadialSq`      — non-vacuity: `R_δ(r²)(v) = 2r²` (genuine ∀v, ≠ diagonal).
    • `radialInput_flat_witness`           — `hRad` INHABITED (flat metric, `u₀=1`, all `x`, all `t>0`).

  ⚠  a₁ = R/6 remains CONDITIONAL.  This discharges `hT0` MODULO the scalar radial input `hRad`; the
  closure of `hRad` (Gauss lemma + volume identity) and the k=1 equation `hT1` remain carried.
-/
import Mathlib
import QIQTH.ResidualFactorization
import QIQTH.FlatHeatEquation
import QIQTH.LaplaceBeltrami
import QIQTH.RadialDistance
import QIQTH.Curvature

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidualFactorization
open scoped BigOperators

namespace QIQTH.TransportEqZero

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ## 0.  The metric radial field `R_g(u) = Σᵢⱼ gⁱʲ xᵢ ∂ⱼu`. -/

/-- **The metric radial field** `R_g(u)(x) = Σᵢⱼ gⁱʲ(x) xᵢ ∂ⱼu(x)`.  This is the object the
    flat-Gaussian cross-gradient reduces to; under the coordinate Gauss lemma `Σᵢ gⁱʲxᵢ = xʲ` it
    becomes the Euler radial derivative `radialDeriv u = Σⱼ xʲ ∂ⱼu`. -/
noncomputable def metricRadial (gi : Point n → Fin n → Fin n → ℝ) (u : Point n → ℝ)
    (x : Point n) : ℝ :=
  ∑ i, ∑ j, gi x i j * x i * pd u j x

/-! ## 1.  ★ THE BANKED CROSS-GRADIENT REDUCTION `C(u) = −(1/2t)·G·R_g(u)`. -/

/-- **★ The cross-gradient reduction (pure banked calculus).**  Using ONLY the flat-Gaussian gradient
    `∂ᵢG = −(xᵢ/2t)·G` (`gaussDdim_pd_i`), the residual cross-gradient collapses to the metric radial
    field: `crossGrad gi t u x = −(1/(2t))·gaussDdim t x·metricRadial gi u x`.  No metric structure,
    no geodesic input — the Gaussian gradient is the whole content. -/
theorem crossGrad_eq_metricRadial (gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (u : Point n → ℝ) (x : Point n) :
    crossGrad gi t u x = -(1 / (2 * t)) * gaussDdim t x * metricRadial gi u x := by
  have key : ∀ i j : Fin n, gi x i j * pd (fun y => gaussDdim t y) i x * pd u j x
      = -(1 / (2 * t)) * gaussDdim t x * (gi x i j * x i * pd u j x) := by
    intro i j; rw [gaussDdim_pd_i t ht x i]; ring
  unfold crossGrad metricRadial
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => key i j)

/-! ## 2.  ★ THE EXACT REDUCTION `𝒢·u − 2C(u) = 𝒢·u + (1/t)·G·R_g(u)`. -/

/-- **★ The exact off-diagonal → radial rewrite.**  Substituting the cross-gradient reduction, the
    carried k=0 combination becomes a scalar radial expression:
      `heatOpFun g gi gaussDdim t x · u x − 2·crossGrad gi t u x`
        `= heatOpFun g gi gaussDdim t x · u x + (1/t)·gaussDdim t x·metricRadial gi u x`.
    Pure algebra (`crossGrad_eq_metricRadial` + `field_simp`/`ring`); the `−2·(−1/2t)` collapses to
    `1/t`.  This is the exact backbone of the `hT0`→radial reduction. -/
theorem transportOffDiag_eq_radial (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (u : Point n → ℝ) (x : Point n) :
    heatOpFun g gi gaussDdim t x * u x - 2 * crossGrad gi t u x
      = heatOpFun g gi gaussDdim t x * u x
        + (1 / t) * gaussDdim t x * metricRadial gi u x := by
  have ht' : t ≠ 0 := ne_of_gt ht
  rw [crossGrad_eq_metricRadial gi t ht u x]
  field_simp
  ring

/-- **★★ `hT0` DISCHARGED from the scalar radial input `hRad`.**  Given the carried radial equation
      `hRad : 𝒢·u₀ + (1/t)·G·R_g(u₀) = 0`   (`⇔ 𝒢·u₀ = −(1/t)·G·R_g(u₀)`),
    the k=0 transport cancellation `hT0 : 𝒢·u₀ − 2·C(u₀) = 0` holds.  Immediate from the exact
    rewrite `transportOffDiag_eq_radial`.  ⚠ This REDUCES `hT0` to `hRad`; it does NOT close `hRad`
    (that is the Gauss-lemma + volume-identity wall). -/
theorem hT0_of_radial (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (u₀ : Point n → ℝ) (x : Point n)
    (hRad : heatOpFun g gi gaussDdim t x * u₀ x
            + (1 / t) * gaussDdim t x * metricRadial gi u₀ x = 0) :
    heatOpFun g gi gaussDdim t x * u₀ x - 2 * crossGrad gi t u₀ x = 0 := by
  rw [transportOffDiag_eq_radial g gi t ht u₀ x]; exact hRad

/-- **The banked residual factorization with `hT0` replaced by the radial input `hRad`.**  Composes
    `hT0_of_radial` into `ResidualFactorization.residual_factorization`: given the scalar radial
    equation `hRad` (for `u₀`) and the carried k=1 equation `hT1`, the two-term parametrix residual
    factorizes as `−t·G·Δ_g u₁`.  Exhibits `hT0` as fully replaceable by `hRad`. -/
theorem residual_factorization_of_radial (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Point n) (u₀ u₁ : Point n → ℝ)
    (hu₀C : ContDiff ℝ ⊤ u₀) (hu₁C : ContDiff ℝ ⊤ u₁)
    (hgisymm : ∀ i j, gi x i j = gi x j i)
    (hRad : heatOpFun g gi gaussDdim t x * u₀ x
            + (1 / t) * gaussDdim t x * metricRadial gi u₀ x = 0)
    (hT1 : t * (heatOpFun g gi gaussDdim t x * u₁ x - 2 * crossGrad gi t u₁ x)
            + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0) :
    heatOpFun g gi (fun s y => gaussDdim s y * ampLin u₀ u₁ s y) t x
      = - (t * gaussDdim t x * laplaceBeltrami g gi u₁ x) :=
  residual_factorization g gi t ht x u₀ u₁ hu₀C hu₁C hgisymm
    (hT0_of_radial g gi t ht u₀ x hRad) hT1

/-! ## 3.  ISOLATING the Gauss-lemma input: `R_g = radialDeriv` under `Σᵢ gⁱʲxᵢ = xʲ`. -/

/-- **The Gauss-lemma isolation.**  The residual carried content is EXACTLY the coordinate Gauss
    lemma `Σᵢ gⁱʲ(x) xᵢ = xʲ`: under it, the metric radial field IS the Euler radial derivative,
    `metricRadial gi u x = radialDeriv u x`.  This pins the STRETCH-#4 geodesic input to a single
    per-coordinate hypothesis — `hGauss` is the missing geometry, not derived here. -/
theorem metricRadial_eq_radialDeriv_of_gaussLemma (gi : Point n → Fin n → Fin n → ℝ)
    (u : Point n → ℝ) (x : Point n) (hGauss : ∀ j, ∑ i, gi x i j * x i = x j) :
    metricRadial gi u x = radialDeriv u x := by
  unfold metricRadial radialDeriv
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, hGauss j]

/-! ## 4.  FLAT checks — `R_g` collapses to the Euler field; non-vacuity; `hRad` inhabited. -/

/-- **Flat check.**  For the flat metric `gⁱʲ = δⁱʲ` (Gauss lemma trivially `Σᵢ δⁱʲxᵢ = xʲ`) the
    metric radial field is exactly the Euler radial derivative: `R_δ(u) = radialDeriv u`. -/
theorem metricRadial_flat_eq_radialDeriv (u : Point n → ℝ) (x : Point n) :
    metricRadial (flatMetric n) u x = radialDeriv u x := by
  refine metricRadial_eq_radialDeriv_of_gaussLemma (flatMetric n) u x (fun j => ?_)
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun i _ hi => by simp [flatMetric, if_neg (fun h : i = j => hi h)])]
  simp [flatMetric]

/-- **Non-vacuity of the reduced radial object.**  For the flat metric and `u = r² = Σᵢ(xⁱ)²`,
    `R_δ(r²)(v) = 2r²` (via Euler's identity `radialDeriv_rncRadialSq`).  This is `≠ 0` for `v ≠ 0`,
    so the reduction's radial field is the GENUINE off-diagonal Euler content — NOT the vacuous
    diagonal (`x = 0`) case already banked. -/
theorem metricRadial_flat_rncRadialSq (v : Point n) :
    metricRadial (flatMetric n) rncRadialSq v = 2 * rncRadialSq v := by
  rw [metricRadial_flat_eq_radialDeriv, radialDeriv_rncRadialSq]

/-- **`hRad` is INHABITED (satisfiability gate).**  For the flat metric and `u₀ = 1`, the scalar
    radial input `hRad` holds for ALL `x` and ALL `t > 0`: the flat eikonal defect `𝒢 = 0`
    (`gaussDdim_heat_eqn` + `laplaceBeltrami_at_rnc_center`) and `R_δ(1) = radialDeriv 1 = 0`.  The
    genuine `∀x` (not single-point) satisfiability witness for the carried radial equation. -/
theorem radialInput_flat_witness (t : ℝ) (ht : 0 < t) (x : Point n) :
    heatOpFun (flatMetric n) (flatMetric n) gaussDdim t x * (fun _ => (1 : ℝ)) x
      + (1 / t) * gaussDdim t x * metricRadial (flatMetric n) (fun _ => (1 : ℝ)) x = 0 := by
  -- `R_δ(1) = radialDeriv 1 = 0`.
  have hmr : metricRadial (flatMetric n) (fun _ => (1 : ℝ)) x = 0 := by
    rw [metricRadial_flat_eq_radialDeriv]
    unfold radialDeriv
    exact Finset.sum_eq_zero (fun i _ => by rw [pd_const]; ring)
  -- the flat eikonal defect `𝒢 = 0`.
  have hgi : ∀ i j, flatMetric n x i j = if i = j then (1 : ℝ) else 0 := fun i j => rfl
  have hpc : ∀ (a b i : Fin n), pd (fun y => flatMetric n y a b) i x = 0 := by
    intro a b i
    have e : (fun y : Point n => flatMetric n y a b)
        = (fun _ => (if a = b then (1 : ℝ) else 0)) := rfl
    rw [e, pd_const]
  have hΓ : ∀ k i j, christoffel (flatMetric n) (flatMetric n) k i j x = 0 := by
    intro k i j
    unfold christoffel
    simp only [hpc, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]
  have h𝒢 : heatOpFun (flatMetric n) (flatMetric n) gaussDdim t x = 0 := by
    simp only [heatOpFun]
    rw [laplaceBeltrami_at_rnc_center (flatMetric n) (flatMetric n) (fun y => gaussDdim t y) x hgi hΓ,
        gaussDdim_heat_eqn t ht x]
    ring
  rw [hmr, h𝒢]; ring

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms crossGrad_eq_metricRadial
#print axioms transportOffDiag_eq_radial
#print axioms hT0_of_radial
#print axioms residual_factorization_of_radial
#print axioms metricRadial_eq_radialDeriv_of_gaussLemma
#print axioms metricRadial_flat_eq_radialDeriv
#print axioms metricRadial_flat_rncRadialSq
#print axioms radialInput_flat_witness

end AxiomChecks

end QIQTH.TransportEqZero

/-! ## THE REDUCTION LEDGER — J4-505.

  ── WHAT IS BANKED (before this brick).
    • `ResidualFactorization.residual_factorization` — the residual `E = −t·G·Δ_g u₁` MODULO the two
      carried transport equations `hT0`, `hT1`.
    • `FlatHeatEquation.gaussDdim_pd_i` — the flat-Gaussian gradient `∂ᵢG = −(xᵢ/2t)·G`.
    • `RadialDistance.radialDeriv` (+`radialDeriv_rncRadialSq`) — the Euler radial field `r∂_r`.
    • `HeatTransportRecursion` STRETCH #4 — the geodesic `r∂_r` / Gauss-lemma / van-Vleck ODE wall.

  ── WHAT J4-505 ADDS.
      role                                                         status
      ───────────────────────────────────────────────────────────  ──────────────────────────────────
      the cross-gradient reduction `C(u) = −(1/2t)·G·R_g(u)`        ★ LANDED — `crossGrad_eq_metricRadial`
      the exact `hT0 → radial` rewrite                             ★ LANDED — `transportOffDiag_eq_radial`
      `hT0` discharged from the scalar radial input `hRad`         ★★ LANDED — `hT0_of_radial`
      factorization with `hT0` replaced by `hRad`                  LANDED — `residual_factorization_of_radial`
      the Gauss-lemma input isolated (`R_g = radialDeriv`)         LANDED — `…_of_gaussLemma`
      the scalar radial equation `hRad` itself (curved)           CARRIED — the Gauss-lemma + volume wall

  ── HONEST DISTANCE.  This turns `hT0` from an opaque carried pointwise cancellation into a REDUCTION
    onto a single scalar radial equation `hRad : 𝒢·u₀ = −(1/t)·G·R_g(u₀)`, discharging the entire
    OFF-diagonal cross-gradient double sum via banked flat-Gaussian calculus.  The residual carried
    content is EXACTLY the coordinate Gauss lemma `Σᵢ gⁱʲxᵢ = xʲ` (isolated in
    `metricRadial_eq_radialDeriv_of_gaussLemma`) plus the contracted volume identity
    `Δ_g(½‖x‖²) = n + r∂_r log√det g` — the checkpointed STRETCH-#4 geodesic-`r∂_r` wall, NOT closed here.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Recommended J4-506: either (i) the k=1 equation `hT1` (same
    cross-gradient reduction applies to `C(u₁)`, leaving its own radial input), or (ii) the STRETCH-#4
    sub-campaign closing `hRad` — the coordinate Gauss lemma `Σᵢ gⁱʲxᵢ = xʲ` in RNC (`RadialDistance`
    header's deferred item) is the smallest genuinely-geodesic sub-lemma.
-/
