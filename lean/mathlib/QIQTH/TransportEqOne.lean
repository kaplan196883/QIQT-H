/-
  TransportEqOne — J4-506: the REDUCTION of the k=1 van-Vleck transport equation `hT1`
  (`(𝒯+1)u₁ = Δ_g u₀`, re-expressed as the cancellation `t·(𝒢·u₁ − 2·C(u₁)) + G·(u₁ − Δ_g u₀) = 0`)
  to a clean scalar RADIAL equation `hRad1`, via the SAME banked flat-Gaussian cross-gradient calculus
  used for `hT0` in J4-505 — plus the flat-model satisfiability witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  This file does **NOT** derive `hT1`, and proves NOTHING new about `a₁ = R/6`.
  It performs the *tractable, mechanical* half of the J4-506 attack: the banked cross-gradient
  reduction `crossGrad_eq_metricRadial` / `transportOffDiag_eq_radial` is GENERIC in `u`, so it
  applies to `C(u₁)` verbatim.  The k=1 source `G·(u₁ − Δ_g u₀)` rides along UNTOUCHED — it carries
  no extra banked identity (no `Δu₀` calculus needed here, the source is already an explicit field).
  Consequently `hT1` collapses to the scalar RADIAL equation
      hRad1 :  t·(𝒢·u₁ + (1/t)·G·R_g(u₁)) + G·(u₁ − Δ_g u₀) = 0,
  and `hT1_of_radial1` DISCHARGES `hT1` from `hRad1` (feeding `ResidualFactorization` unchanged).
  Combined with J4-505's `hT0_of_radial`, the residual factorization becomes a THEOREM modulo the
  TWO scalar radial inputs `{hRad0, hRad1}` — BOTH members of the same coordinate-Gauss-lemma family
  `Σᵢ gⁱʲxᵢ = xʲ` (the STRETCH-#4 geodesic wall, Mathlib-absent), since `R_g(u₁)` reduces to the Euler
  field `radialDeriv u₁` under EXACTLY that same Gauss lemma (`metricRadial_eq_radialDeriv_of_gaussLemma`,
  applied here to `u₁`).  We CARRY `hRad1`; we do NOT derive it.
  No `sorry`, no `:= True`, no new axioms, std-3.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── WHAT LANDS (ns `QIQTH.TransportEqOne`).
    • `hT1_of_radial1`                    — ★★ `hT1` discharged FROM the scalar radial input `hRad1`.
    • `residual_factorization_of_radial01` — the banked factorization with BOTH `hT0`, `hT1` replaced
                                             by the scalar radial inputs `hRad0`, `hRad1`.
    • `radialInput1_flat_witness`         — `hRad1` INHABITED (flat metric, `u₀=1`, `u₁=0`, all `x`, `t>0`).

  ⚠  a₁ = R/6 remains CONDITIONAL.  This discharges `hT1` MODULO the scalar radial input `hRad1`; the
    closure of `hRad0`, `hRad1` (the shared coordinate Gauss lemma + volume identity) remains carried.
-/
import Mathlib
import QIQTH.ResidualFactorization
import QIQTH.TransportEqZero
import QIQTH.FlatHeatEquation
import QIQTH.LaplaceBeltrami
import QIQTH.RadialDistance
import QIQTH.Curvature

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidualFactorization QIQTH.TransportEqZero
open scoped BigOperators ContDiff

namespace QIQTH.TransportEqOne

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ## 1.  ★★ `hT1` DISCHARGED from the scalar radial input `hRad1`. -/

/-- **★★ `hT1` DISCHARGED from the scalar radial input `hRad1`.**  The banked cross-gradient reduction
    `transportOffDiag_eq_radial` is GENERIC in `u`, so applied to `u₁` it rewrites the k=1 off-diagonal
    bracket `𝒢·u₁ − 2·C(u₁) = 𝒢·u₁ + (1/t)·G·R_g(u₁)`.  Given the carried radial equation
      `hRad1 : t·(𝒢·u₁ + (1/t)·G·R_g(u₁)) + G·(u₁ − Δ_g u₀) = 0`,
    the k=1 transport cancellation
      `hT1 : t·(𝒢·u₁ − 2·C(u₁)) + G·(u₁ − Δ_g u₀) = 0`
    holds.  The k=1 SOURCE term `G·(u₁ − Δ_g u₀)` is untouched — it carries no extra banked identity.
    ⚠ This REDUCES `hT1` to `hRad1`; it does NOT close `hRad1` (the Gauss-lemma + volume-identity wall,
    shared with `hRad0`). -/
theorem hT1_of_radial1 (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (u₀ u₁ : Point n → ℝ) (x : Point n)
    (hRad1 : t * (heatOpFun g gi gaussDdim t x * u₁ x
              + (1 / t) * gaussDdim t x * metricRadial gi u₁ x)
            + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0) :
    t * (heatOpFun g gi gaussDdim t x * u₁ x - 2 * crossGrad gi t u₁ x)
      + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0 := by
  rw [transportOffDiag_eq_radial g gi t ht u₁ x]; exact hRad1

/-! ## 2.  The banked factorization with BOTH `hT0`, `hT1` replaced by the radial inputs. -/

/-- **The residual factorization modulo BOTH scalar radial inputs `hRad0`, `hRad1`.**  Composes
    `TransportEqZero.hT0_of_radial` and `hT1_of_radial1` into
    `ResidualFactorization.residual_factorization`: given the two scalar radial equations `hRad0`
    (for `u₀`) and `hRad1` (for `u₁`), the two-term parametrix residual factorizes as `−t·G·Δ_g u₁`.
    Exhibits BOTH carried transport equations `hT0`, `hT1` as fully replaceable by scalar radial
    inputs — the same coordinate-Gauss-lemma family.  ⚠ NOT `a₁ = R/6`; `hRad0`, `hRad1` are the
    carried radial-transport wall, not derived here. -/
theorem residual_factorization_of_radial01 (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Point n) (u₀ u₁ : Point n → ℝ)
    (hu₀C : ContDiff ℝ ⊤ u₀) (hu₁C : ContDiff ℝ ⊤ u₁)
    (hgisymm : ∀ i j, gi x i j = gi x j i)
    (hRad0 : heatOpFun g gi gaussDdim t x * u₀ x
            + (1 / t) * gaussDdim t x * metricRadial gi u₀ x = 0)
    (hRad1 : t * (heatOpFun g gi gaussDdim t x * u₁ x
              + (1 / t) * gaussDdim t x * metricRadial gi u₁ x)
            + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0) :
    heatOpFun g gi (fun s y => gaussDdim s y * ampLin u₀ u₁ s y) t x
      = - (t * gaussDdim t x * laplaceBeltrami g gi u₁ x) :=
  residual_factorization g gi t ht x u₀ u₁ hu₀C hu₁C hgisymm
    (hT0_of_radial g gi t ht u₀ x hRad0)
    (hT1_of_radial1 g gi t ht u₀ u₁ x hRad1)

/-! ## 3.  FLAT witness — `hRad1` inhabited (satisfiability gate). -/

/-- **`hRad1` is INHABITED (satisfiability gate).**  For the flat metric and `u₀ = 1`, `u₁ = 0`, the
    scalar k=1 radial input `hRad1` holds for ALL `x` and ALL `t > 0`: the flat eikonal defect `𝒢 = 0`
    (`gaussDdim_heat_eqn` + `laplaceBeltrami_at_rnc_center`), `R_δ(0) = radialDeriv 0 = 0`, and the
    k=1 source `G·(0 − Δ_δ 1) = G·(0 − 0) = 0`.  The genuine `∀x` (not single-point) satisfiability
    witness for the carried k=1 radial equation. -/
theorem radialInput1_flat_witness (t : ℝ) (ht : 0 < t) (x : Point n) :
    t * (heatOpFun (flatMetric n) (flatMetric n) gaussDdim t x * (fun _ => (0 : ℝ)) x
          + (1 / t) * gaussDdim t x * metricRadial (flatMetric n) (fun _ => (0 : ℝ)) x)
      + gaussDdim t x * ((fun _ => (0 : ℝ)) x
          - laplaceBeltrami (flatMetric n) (flatMetric n) (fun _ => (1 : ℝ)) x) = 0 := by
  -- `R_δ(0) = radialDeriv 0 = 0`.
  have hmr : metricRadial (flatMetric n) (fun _ => (0 : ℝ)) x = 0 := by
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
  -- the k=1 source: `Δ_δ 1 = 0` (constant field).
  have hlapc : laplaceBeltrami (flatMetric n) (flatMetric n) (fun _ => (1 : ℝ)) x = 0 := by
    unfold laplaceBeltrami
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have h1 : pd (fun y => pd (fun _ => (1 : ℝ)) j y) i x = 0 := by
      have e : (fun y : Point n => pd (fun _ => (1 : ℝ)) j y) = (fun _ => (0 : ℝ)) :=
        funext (fun y => pd_const 1 j y)
      rw [e, pd_const]
    have h2 : (∑ k, christoffel (flatMetric n) (flatMetric n) k i j x
        * pd (fun _ => (1 : ℝ)) k x) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [pd_const]; ring
    rw [h1, h2]; ring
  rw [hmr, h𝒢, hlapc]; simp

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms hT1_of_radial1
#print axioms residual_factorization_of_radial01
#print axioms radialInput1_flat_witness

end AxiomChecks

end QIQTH.TransportEqOne

/-! ## THE REDUCTION LEDGER — J4-506.

  ── WHAT IS BANKED (before this brick).
    • `ResidualFactorization.residual_factorization` — `E = −t·G·Δ_g u₁` MODULO `hT0`, `hT1`.
    • `TransportEqZero.transportOffDiag_eq_radial` — ★ the GENERIC (in `u`) off-diagonal → radial
      rewrite `𝒢·u − 2C(u) = 𝒢·u + (1/t)·G·R_g(u)`, via the flat-Gaussian gradient.
    • `TransportEqZero.hT0_of_radial` — `hT0` discharged from the k=0 radial input `hRad0`.
    • `TransportEqZero.metricRadial_eq_radialDeriv_of_gaussLemma` — `R_g = radialDeriv` under
      `Σᵢ gⁱʲxᵢ = xʲ` (the shared Gauss-lemma input; applies to `u₁` identically).

  ── WHAT J4-506 ADDS.
      role                                                         status
      ───────────────────────────────────────────────────────────  ──────────────────────────────────
      `hT1` discharged from the scalar radial input `hRad1`        ★★ LANDED — `hT1_of_radial1`
      factorization with BOTH `hT0`, `hT1` replaced by radial      LANDED — `residual_factorization_of_radial01`
      `hRad1` inhabited (flat witness, genuine ∀x)                 LANDED — `radialInput1_flat_witness`
      the scalar radial equations `hRad0`, `hRad1` (curved)        CARRIED — the shared Gauss-lemma wall

  ── HONEST DISTANCE.  With J4-505 + J4-506, the residual factorization is a THEOREM modulo the TWO
    scalar radial inputs `{hRad0, hRad1}`.  Both are members of the SAME coordinate-Gauss-lemma family
    `Σᵢ gⁱʲxᵢ = xʲ` (`metricRadial_eq_radialDeriv_of_gaussLemma`, generic in `u`): closing that single
    per-coordinate identity turns `R_g(u₀)`, `R_g(u₁)` into the Euler field `radialDeriv`, collapsing
    both radial equations to eikonal/volume identities.  The k=1 source `G·(u₁ − Δ_g u₀)` needs NO
    extra input — it rides along untouched.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Recommended J4-507: the coordinate GAUSS LEMMA `Σᵢ gⁱʲxᵢ = xʲ`
    in RNC — the SHARED input closing BOTH `hRad0` and `hRad1` — audit whether it is derivable from the
    banked RNC gauge (`hgauge` / `rnc_htr_of_gauge` family) or is the irreducible geodesic wall.
-/
