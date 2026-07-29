/-
  CutoffAnnulusBounds — discharging the χ/metric annulus-boundedness carries of the C4c
  cutoff-parametrix global residual bound via COMPACTNESS.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DELIVERS (honest FLOOR = F1).

  The just-landed `cutoffResidual_global_gaussianWide_bound` (in `CutoffResidualGlobalBound`) carries
  three annulus-boundedness hypotheses on the COMPACT annulus `{a² ≤ rncRadialSq ≤ b²}`:

    • `hgibd`   : `|gⁱʲ w| ≤ Kg`                                (inverse-metric bound),
    • `hDchi`   : `|∂ᵢ(radialCutoff a b) w| ≤ Kc1`             (cutoff-gradient bound),
    • `hLapChi` : `|Δ_g(radialCutoff a b) w| ≤ Kc2`            (`Δ_gχ` bound),

  each of the shape `∀ w, a² ≤ rncRadialSq w → rncRadialSq w ≤ b² → |…| ≤ K`.

  THE KEY GEOMETRIC FACT.  The annulus `A = {w | a² ≤ rncRadialSq w ∧ rncRadialSq w ≤ b²}` is
  COMPACT: it is CLOSED (`A = rncRadialSq⁻¹(Icc a² b²)`, preimage of a closed interval under the
  continuous `rncRadialSq`) and BOUNDED (`rncRadialSq w ≤ b²` ⟹ each `(wⁱ)² ≤ b²` ⟹ `‖w‖ ≤ |b|`),
  and `Point n = Fin n → ℝ` is a finite-dimensional real normed space, hence a `ProperSpace`
  (`Metric.isCompact_of_isClosed_isBounded`).  A CONTINUOUS real function attains a bound on a
  compact set (`IsCompact.exists_bound_of_continuousOn`), so all three functions — being continuous
  (`gⁱʲ`/`Γ` carried continuous, `radialCutoff a b` is `C∞` hence its `pd`, `pd pd`, and `Δ_g` are
  continuous) — are bounded on the annulus.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CARRIED CONTINUITY HYPOTHESES (all GENUINE, load-bearing, NONE vacuous).  These are honest
  regularity facts about the metric, satisfied by the concrete Riemann-normal-coordinate metric:
    • `hgi_cont   : ∀ i j, Continuous (fun w => gi w i j)`             (inverse metric continuous);
    • `hchris_cont : ∀ k i j, Continuous (fun w => christoffel g gi k i j w)`  (Christoffel cont.).
  The cutoff's own regularity (`radialCutoff a b` is `C∞`, `radialCutoff_contDiff`) is NOT carried —
  it is proved.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  FLOOR STATUS = F1 (all three + the general helper).  Delivered:
    • `annulus_isCompact`               — the annulus is compact (closed+bounded, `ProperSpace`);
    • `exists_bound_on_annulus`         — general compactness→bound helper for a continuous `f`;
    • `laplaceBeltrami_radialCutoff_continuous` — `Δ_g χ` is continuous (χ `C∞` + metric cont.);
    • `gi_bound_on_annulus`             — `hgibd` (uniform over the finite index set `Fin n × Fin n`);
    • `pd_radialCutoff_bound_on_annulus`— `hDchi` (uniform over `Fin n`; self-contained, χ `C∞`);
    • `laplaceBeltrami_radialCutoff_bound_on_annulus` — `hLapChi`.

  This discharges the `hgibd`/`hDchi`/`hLapChi` carries of `cutoffResidual_global_gaussianWide_bound`
  toward the far-field / unconditional `a₁ = R/6`.  It is NOT itself `a₁ = R/6`.  No `sorry`, no new
  axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.SmoothCutoff
import QIQTH.CutoffAnnulusSupport
import QIQTH.RadialDistance
import QIQTH.LaplaceBeltrami
import QIQTH.CutoffResidualGlobalBound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The annulus is compact -/

/-- The closed radial annulus `{a² ≤ rncRadialSq ≤ b²}` is COMPACT: it is closed (preimage of the
    closed interval `Icc a² b²` under the continuous `rncRadialSq`) and bounded (`rncRadialSq ≤ b²`
    forces `‖w‖ ≤ |b|`), and `Point n = Fin n → ℝ` is a finite-dimensional real normed space (hence a
    `ProperSpace`), so `Metric.isCompact_of_isClosed_isBounded` applies. -/
theorem annulus_isCompact (a b : ℝ) :
    IsCompact {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · -- closed: preimage of `Icc a² b²` under continuous `rncRadialSq`
    have hset : {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2}
        = rncRadialSq ⁻¹' Set.Icc (a ^ 2) (b ^ 2) := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
    rw [hset]
    exact isClosed_Icc.preimage rncRadialSq_contDiff.continuous
  · -- bounded: contained in the closed ball of radius `|b|`
    refine (Metric.isBounded_closedBall (x := (0 : Point n)) (r := |b|)).subset ?_
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (abs_nonneg b)]
    intro i
    have hle : (w i) ^ 2 ≤ b ^ 2 :=
      calc (w i) ^ 2 ≤ ∑ j, (w j) ^ 2 :=
            Finset.single_le_sum (f := fun j => (w j) ^ 2)
              (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = rncRadialSq w := rfl
        _ ≤ b ^ 2 := hw.2
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs b]
    exact Real.sqrt_le_sqrt hle

/-! ### General compactness → uniform bound on the annulus -/

/-- **The compactness→bound helper.**  A CONTINUOUS real function `f` is bounded on the compact
    annulus `{a² ≤ rncRadialSq ≤ b²}`: `∃ K ≥ 0, ∀ w in the annulus, |f w| ≤ K`.  Proved via
    `IsCompact.exists_bound_of_continuousOn` on `annulus_isCompact`, taking `K = max C 0` to secure
    nonnegativity (the annulus may be empty, e.g. `n = 0`). -/
theorem exists_bound_on_annulus (f : Point n → ℝ) (hf : Continuous f) (a b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |f w| ≤ K := by
  obtain ⟨C, hC⟩ := (annulus_isCompact a b).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w h1 h2 => ?_⟩
  have hw := hC w ⟨h1, h2⟩
  rw [Real.norm_eq_abs] at hw
  exact hw.trans (le_max_left _ _)

/-! ### `Δ_g χ` is continuous -/

/-- The Laplace–Beltrami of the smooth cutoff is CONTINUOUS.  `Δ_gχ = ∑ᵢⱼ gⁱʲ (∂ᵢ∂ⱼχ − ∑ₖ Γᵏᵢⱼ ∂ₖχ)`
    is a finite sum of products of continuous factors: `gⁱʲ` and `Γ` are carried continuous, while
    `∂ᵢ∂ⱼχ` and `∂ₖχ` are continuous because `radialCutoff a b` is `C∞` (`radialCutoff_contDiff`,
    `contDiff_pd_inf`). -/
theorem laplaceBeltrami_radialCutoff_continuous
    (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (hgi_cont : ∀ i j, Continuous (fun w => gi w i j))
    (hchris_cont : ∀ k i j, Continuous (fun w => christoffel g gi k i j w)) :
    Continuous (fun w => laplaceBeltrami g gi (radialCutoff a b) w) := by
  simp only [laplaceBeltrami]
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_finsetSum _ fun j _ => ?_
  refine (hgi_cont i j).mul (Continuous.sub ?_ ?_)
  · exact (contDiff_pd_inf (fun y => pd (radialCutoff a b) j y)
      (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) j) i).continuous
  · refine continuous_finsetSum _ fun k _ => ?_
    exact (hchris_cont k i j).mul
      (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) k).continuous

/-! ### The three discharged annulus bounds -/

/-- **`hgibd`.**  The inverse metric is uniformly bounded on the annulus.  Applies
    `exists_bound_on_annulus` to each component `w ↦ gⁱʲ w` (carried continuous) and takes the finite
    sum `Kg = ∑ᵢⱼ K i j` over `Fin n × Fin n`, which dominates every component (all summands
    nonnegative). -/
theorem gi_bound_on_annulus (gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (hgi_cont : ∀ i j, Continuous (fun w => gi w i j)) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |gi w i j| ≤ Kg := by
  classical
  have hbd : ∀ i j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |gi w i j| ≤ K :=
    fun i j => exists_bound_on_annulus (fun w => gi w i j) (hgi_cont i j) a b
  choose K hK0 hKbd using hbd
  refine ⟨∑ i, ∑ j, K i j, Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hK0 i j, ?_⟩
  intro w i j h1 h2
  refine (hKbd i j w h1 h2).trans ?_
  calc K i j ≤ ∑ j', K i j' :=
        Finset.single_le_sum (f := fun j' => K i j')
          (fun j' _ => hK0 i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', K i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', K i' j')
          (fun i' _ => Finset.sum_nonneg fun j' _ => hK0 i' j') (Finset.mem_univ i)

/-- **`hDchi`.**  The cutoff gradient is uniformly bounded on the annulus.  Self-contained (no metric
    input): `radialCutoff a b` is `C∞`, so each `w ↦ ∂ᵢχ w` is continuous; `exists_bound_on_annulus`
    per index `i`, then `Kc1 = ∑ᵢ K i` dominates each. -/
theorem pd_radialCutoff_bound_on_annulus (a b : ℝ) :
    ∃ Kc1 : ℝ, 0 ≤ Kc1 ∧ ∀ (w : Point n) (i : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (radialCutoff a b) i w| ≤ Kc1 := by
  classical
  have hbd : ∀ i : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (radialCutoff a b) i w| ≤ K :=
    fun i => exists_bound_on_annulus (fun w => pd (radialCutoff a b) i w)
      (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) i).continuous a b
  choose K hK0 hKbd using hbd
  refine ⟨∑ i, K i, Finset.sum_nonneg fun i _ => hK0 i, ?_⟩
  intro w i h1 h2
  refine (hKbd i w h1 h2).trans ?_
  exact Finset.single_le_sum (f := fun i' => K i') (fun i' _ => hK0 i') (Finset.mem_univ i)

/-- **`hLapChi`.**  `Δ_gχ` is uniformly bounded on the annulus.  Direct application of
    `exists_bound_on_annulus` to the continuous `Δ_gχ` (`laplaceBeltrami_radialCutoff_continuous`,
    using the carried metric/Christoffel continuity). -/
theorem laplaceBeltrami_radialCutoff_bound_on_annulus
    (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (hgi_cont : ∀ i j, Continuous (fun w => gi w i j))
    (hchris_cont : ∀ k i j, Continuous (fun w => christoffel g gi k i j w)) :
    ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2 :=
  exists_bound_on_annulus (fun w => laplaceBeltrami g gi (radialCutoff a b) w)
    (laplaceBeltrami_radialCutoff_continuous g gi a b hgi_cont hchris_cont) a b

end QIQTH.HeatResidualBound
