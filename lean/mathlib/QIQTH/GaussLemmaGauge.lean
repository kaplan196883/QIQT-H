/-
  GaussLemmaGauge — J4-507: NAME the single geometric input that closes BOTH radial transport
  equations `hRad0`, `hRad1` — the coordinate GAUSS LEMMA in Riemann normal coordinates — and reduce
  the residual factorization to that ONE recognized geometric hypothesis (plus the two Euler-field
  radial equations), with the genuine `∀x` flat-model witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  This file does **NOT** derive the Gauss lemma and proves NOTHING new about
  `a₁ = R/6`.  It is the PACKAGING brick: it names the exact `∀x` coordinate identity that the J4-505/506
  transport reductions consume, exhibits it as INHABITED by the flat metric for ALL `x` (not the vacuous
  `x = 0` diagonal), and shows BOTH carried radial inputs collapse to Euler-field radial equations under
  this SINGLE named gauge.  It also records that this is the SAME `∀x` geometric content the `a₁ = R/6`
  mainline already carries as its labelled input `hGauss` (the mainline germ `=ᶠ[𝓝 0]` shape follows
  from the `∀x` pointwise gauge by `Filter.eventually_of_forall`).

  AUDIT VERDICT (J4-507).  The coordinate Gauss lemma `∀ x j, Σᵢ gⁱʲ(x) xᵢ = xʲ` (equivalently the
  radial-geodesic condition `Γⁱ_jk(x) xʲ xᵏ = 0 ∀x`, equivalently `⟨exp*g|_v (v,·) = g_p(v,·)⟩`) is:
    • NOT derivable from the FINITE RNC gauge `hgauge` (the symmetrized `∂Γ(0) = 0` 2-jet at the origin).
      Counterexample (Sol): `g_ij(x) = (1+ε‖x‖⁴)δ_ij` has the SAME 2-jet at `0` (satisfies `hgauge`,
      `g(0)=δ`, `∂g(0)=0`) yet `Σⱼ g_ij x^j = (1+ε‖x‖⁴)x^i ≠ x^i` for `x ≠ 0`.  A finite jet cannot
      capture an all-orders `∀x` identity.  So verdict (a) DERIVABLE-FROM-hgauge is REFUTED.
    • The IRREDUCIBLE geodesic/exp-map input (verdict (c)): Mathlib has NO exponential-map / geodesic
      normal-coordinate infrastructure, so the Gauss lemma cannot be discharged against a construction.
      It is the geometric FLOOR.  ⚠ Don't-undercredit: the repo has NOT left it bare — the in-Lean
      geodesic machinery (`GaussLemmaFirstVariation`…`GaussLemmaFlowData`: `expTube`/`expMap`/Jacobi
      fields/`geodesic_energy_conservation`/`gauss_coordinate_contraction`/`hGauss_pullback`) DERIVES the
      germ form of the Gauss lemma for the exp-pullback metric down to a single residue `hgball` (the
      per-point first-variation Gauss identity on the geodesic tube).  This file simply NAMES the floor.

  ── WHAT LANDS (ns `QIQTH.GaussLemmaGauge`).
    • `CoordGaussGauge`                        — ★ the SINGLE named geometric input `∀ x j, Σᵢ gⁱʲ xᵢ = xʲ`
                                                  (inverse-metric coordinate Gauss lemma, the `∀x` floor).
    • `MetricGaussGauge`                       — the DUAL metric-form gauge `∀ x i, Σⱼ g_ij x^j = xⁱ`.
    • `metricRadial_eq_radialDeriv_of_coordGaussGauge` — ★ `R_g(u) = radialDeriv u` (∀u) under the gauge.
    • `residual_factorization_of_gauge`        — ★★ the residual `E = −t·G·Δ_g u₁` from the ONE named gauge
                                                  + the two EULER-FIELD radial equations (both `hRad0`,
                                                  `hRad1` reduced to a single recognized geometric input).
    • `coordGaussGauge_flat` / `metricGaussGauge_flat` — the gauges are INHABITED by the flat metric, ∀x.
    • `metricGaussGauge_imp_hGaussGerm`        — the `∀x` metric gauge ⟹ the mainline `a₁` germ `hGauss`.
    • `coordGaussGauge_flat_rncRadialSq`       — non-vacuity: at the flat gauge `R_δ(r²)(v) = 2r²` (∀v).

  ⚠  a₁ = R/6 remains CONDITIONAL.  This NAMES and inhabits the geometric floor; it does not derive it.
-/
import Mathlib
import QIQTH.ResidualFactorization
import QIQTH.TransportEqZero
import QIQTH.TransportEqOne
import QIQTH.FlatHeatEquation
import QIQTH.LaplaceBeltrami
import QIQTH.RadialDistance
import QIQTH.Curvature

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidualFactorization
open QIQTH.TransportEqZero QIQTH.TransportEqOne
open scoped BigOperators

namespace QIQTH.GaussLemmaGauge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## 0.  The single named geometric input — the coordinate Gauss lemma. -/

/-- **★ The coordinate GAUSS LEMMA gauge (inverse-metric form).**  The exact, all-orders `∀x` identity
    `Σᵢ gⁱʲ(x) xᵢ = xʲ` — in Riemann normal coordinates this is the statement that the metric radial
    field IS the Euler field, i.e. radial geodesics are straight rays through the origin.  This is the
    SINGLE recognized geometric hypothesis that closes BOTH k=0/k=1 radial transport equations; it is
    the geodesic/exp-map floor (NOT derivable from the finite RNC 2-jet gauge `hgauge`). -/
def CoordGaussGauge (gi : Point n → Fin n → Fin n → ℝ) : Prop :=
  ∀ (x : Point n) (j : Fin n), ∑ i, gi x i j * x i = x j

/-- **The dual metric-form Gauss lemma gauge.**  `Σⱼ g_ij(x) xʲ = xⁱ`, the lowered form.  Equivalent
    to `CoordGaussGauge` given `g·gi = I`; this is the shape the `a₁ = R/6` mainline carries as its
    labelled input `hGauss` (via its germ `=ᶠ[𝓝 0]` weakening). -/
def MetricGaussGauge (g : Point n → Fin n → Fin n → ℝ) : Prop :=
  ∀ (x : Point n) (i : Fin n), ∑ j, g x i j * x j = x i

/-! ## 1.  ★ The shared reduction `R_g(u) = radialDeriv u` (∀u) under the gauge. -/

/-- **★ The metric radial field is the Euler field under the Gauss gauge (∀u).**  Packages the banked
    `TransportEqZero.metricRadial_eq_radialDeriv_of_gaussLemma` with the `∀x` gauge: for EVERY scalar
    field `u` and point `x`, `metricRadial gi u x = radialDeriv u x`.  This is the single step that
    collapses BOTH `R_g(u₀)` and `R_g(u₁)` to the Euler field — the shared content of `hRad0`, `hRad1`. -/
theorem metricRadial_eq_radialDeriv_of_coordGaussGauge
    (gi : Point n → Fin n → Fin n → ℝ) (hgauge : CoordGaussGauge gi)
    (u : Point n → ℝ) (x : Point n) :
    metricRadial gi u x = radialDeriv u x :=
  metricRadial_eq_radialDeriv_of_gaussLemma gi u x (hgauge x)

/-! ## 2.  ★★ The residual factorization from the ONE named gauge + Euler-field radial equations. -/

/-- **★★ The residual factorization from a SINGLE named geometric input.**  Under the coordinate Gauss
    gauge `hgauge : CoordGaussGauge gi`, BOTH carried radial transport inputs are recognized EULER-FIELD
    radial equations:
      `hEul0 : 𝒢·u₀ + (1/t)·G·(r∂_r u₀) = 0`,
      `hEul1 : t·(𝒢·u₁ + (1/t)·G·(r∂_r u₁)) + G·(u₁ − Δ_g u₀) = 0`,
    (`r∂_r = radialDeriv`).  The two-term parametrix residual then factorizes as `−t·G·Δ_g u₁`.  This
    exhibits the whole radial-transport wall `{hRad0, hRad1}` as resting on ONE recognized geometric
    hypothesis (the Gauss lemma) plus the eikonal/van-Vleck Euler-field equations — NOT two ad-hoc
    radial identities.  ⚠ NOT `a₁ = R/6`; `hgauge` is the carried geodesic floor, not derived here. -/
theorem residual_factorization_of_gauge (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Point n) (u₀ u₁ : Point n → ℝ)
    (hu₀C : ContDiff ℝ ⊤ u₀) (hu₁C : ContDiff ℝ ⊤ u₁)
    (hgisymm : ∀ i j, gi x i j = gi x j i)
    (hgauge : CoordGaussGauge gi)
    (hEul0 : heatOpFun g gi gaussDdim t x * u₀ x
            + (1 / t) * gaussDdim t x * radialDeriv u₀ x = 0)
    (hEul1 : t * (heatOpFun g gi gaussDdim t x * u₁ x
              + (1 / t) * gaussDdim t x * radialDeriv u₁ x)
            + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0) :
    heatOpFun g gi (fun s y => gaussDdim s y * ampLin u₀ u₁ s y) t x
      = - (t * gaussDdim t x * laplaceBeltrami g gi u₁ x) := by
  have hRad0 : heatOpFun g gi gaussDdim t x * u₀ x
      + (1 / t) * gaussDdim t x * metricRadial gi u₀ x = 0 := by
    rw [metricRadial_eq_radialDeriv_of_coordGaussGauge gi hgauge u₀ x]; exact hEul0
  have hRad1 : t * (heatOpFun g gi gaussDdim t x * u₁ x
              + (1 / t) * gaussDdim t x * metricRadial gi u₁ x)
            + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0 := by
    rw [metricRadial_eq_radialDeriv_of_coordGaussGauge gi hgauge u₁ x]; exact hEul1
  exact residual_factorization_of_radial01 g gi t ht x u₀ u₁ hu₀C hu₁C hgisymm hRad0 hRad1

/-! ## 3.  Bridge to the `a₁ = R/6` mainline labelled input `hGauss`. -/

/-- **The `∀x` metric Gauss gauge implies the mainline germ `hGauss`.**  The `a₁ = R/6` façade
    (`A1R6FromLabelled.a1_R6_from_labelled`, `NCGaussToCyclicT.cyclicT_of_hGauss`) carries the labelled
    input in GERM form `hGauss : ∀ i, (fun x => Σⱼ g x i j · xʲ) =ᶠ[𝓝 0] (fun x => xⁱ)`.  This follows
    from the `∀x` pointwise `MetricGaussGauge` by `Filter.eventually_of_forall` — establishing that the
    a₁ mainline input and the transport-side input `CoordGaussGauge` are the SAME geometric content
    (the coordinate Gauss lemma), differing only metric-vs-inverse (dual given `g·gi = I`) and
    pointwise-vs-germ. -/
theorem metricGaussGauge_imp_hGaussGerm (g : Point n → Fin n → Fin n → ℝ)
    (hgauge : MetricGaussGauge g) :
    ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[nhds (0 : Point n)] (fun x => x i) :=
  fun i => Filter.Eventually.of_forall (fun x => hgauge x i)

/-! ## 4.  THE SATISFIABILITY GATE — the gauges are inhabited by the flat metric, ∀x. -/

/-- **★ `CoordGaussGauge` is INHABITED — the flat metric satisfies it for ALL `x`.**  `Σᵢ δⁱʲ xᵢ = xʲ`
    holds at every `x` (genuine `∀x`, NOT the vacuous `x = 0` diagonal).  The `∀x` satisfiability
    witness for the named geometric floor. -/
theorem coordGaussGauge_flat : CoordGaussGauge (flatMetric n) := by
  intro x j
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun i _ hi => by simp [flatMetric, if_neg (fun h : i = j => hi h)])]
  simp [flatMetric]

/-- **`MetricGaussGauge` is INHABITED — the flat metric satisfies it for ALL `x`.**  `Σⱼ δ_ij xʲ = xⁱ`
    at every `x`. -/
theorem metricGaussGauge_flat : MetricGaussGauge (flatMetric n) := by
  intro x i
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => by simp [flatMetric, if_neg (fun h : i = j => hj h.symm)])]
  simp [flatMetric]

/-- **Non-vacuity of the reduced object under the gauge.**  At the flat gauge and `u = r² = Σᵢ(xⁱ)²`,
    the metric radial field is `R_δ(r²)(v) = 2r²` (Euler's identity), `≠ 0` for `v ≠ 0`.  Confirms the
    gauge acts on GENUINE off-diagonal radial content, not the trivial `x = 0` case. -/
theorem coordGaussGauge_flat_rncRadialSq (v : Point n) :
    metricRadial (flatMetric n) rncRadialSq v = 2 * rncRadialSq v :=
  metricRadial_flat_rncRadialSq v

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms metricRadial_eq_radialDeriv_of_coordGaussGauge
#print axioms residual_factorization_of_gauge
#print axioms metricGaussGauge_imp_hGaussGerm
#print axioms coordGaussGauge_flat
#print axioms metricGaussGauge_flat
#print axioms coordGaussGauge_flat_rncRadialSq

end AxiomChecks

end QIQTH.GaussLemmaGauge

/-! ## THE AUDIT LEDGER — J4-507.

  ── THE QUESTION.  The coordinate Gauss lemma `∀ x j, Σᵢ gⁱʲ(x) xᵢ = xʲ` is the SHARED input closing
    BOTH `hRad0` (J4-505) and `hRad1` (J4-506) — is it (a) derivable from the finite RNC gauge `hgauge`,
    (b) reducible to one cleaner geodesic gauge, or (c) the irreducible geodesic/exp-map floor?

  ── VERDICT: (c), the geometric FLOOR — but the repo has already NAMED and (partially) DERIVED it.
    • (a) REFUTED.  `hgauge` is a finite 2-jet at the origin; the Gauss lemma is an all-orders `∀x`
      identity.  Counterexample (Sol): `g = (1+ε‖x‖⁴)δ` matches `hgauge`/`g(0)=δ`/`∂g(0)=0` yet fails
      `Σⱼ g_ij x^j = x^i` off-origin.  A finite jet cannot imply the `∀x` identity.
    • (c) CONFIRMED.  Mathlib has no exp-map/geodesic infrastructure, so the Gauss lemma is carried, not
      discharged against a construction.  The cleanest single recognized condition to CARRY is the
      coordinate Gauss lemma itself (Sol: equivalently `⟨exp*g|_v(v,·) = g_p(v,·)⟩`, the radial gauge).

  ── WHAT THIS BRICK ADDS.
      role                                                          status
      ────────────────────────────────────────────────────────────  ─────────────────────────────────
      NAME the single geometric floor `CoordGaussGauge`             ★ LANDED
      `R_g = radialDeriv` (∀u) from the ONE gauge                   ★ LANDED
      residual factorization from ONE gauge + Euler equations       ★★ LANDED — `residual_factorization_of_gauge`
      flat `∀x` inhabitation of BOTH gauge forms                    LANDED — `coordGaussGauge_flat` / `metricGaussGauge_flat`
      bridge `∀x` metric gauge ⟹ mainline germ `hGauss`            LANDED — `metricGaussGauge_imp_hGaussGerm`
      the Gauss lemma itself (curved, `∀x`)                        CARRIED — the geodesic/exp-map floor

  ── HONEST DISTANCE.  Before this brick the two radial inputs `{hRad0, hRad1}` each carried their own
    `metricRadial` term.  Now BOTH are shown to rest on ONE named geometric hypothesis `CoordGaussGauge`
    (plus the eikonal/van-Vleck Euler-field equations), which is the SAME `∀x` content the `a₁ = R/6`
    mainline carries as `hGauss`.  This is the geometric FLOOR: Mathlib genuinely lacks the exp-map to
    derive it, so it stays carried — though the repo's in-Lean geodesic machinery
    (`GaussLemmaFlowData.hGauss_pullback`) already reduces its germ form to the single tube residue
    `hgball` (the per-point first-variation Gauss identity), one level deeper than a bare axiom.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Recommended J4-508: either (i) close the volume/Laplacian identity
    `Δ_g(½‖x‖²) = n + r∂_r log√det g` (the OTHER geometric input in the amplitude Euler equations, via
    the banked van-Vleck radial ODE), or (ii) push `hgball` (the exp-tube first-variation residue) —
    the last genuinely-geodesic sub-lemma between the built exp-map machinery and the germ Gauss lemma.
-/
