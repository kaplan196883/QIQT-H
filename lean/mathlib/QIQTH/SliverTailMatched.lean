/-
  QIQTH / HeatResidualBound — SliverTailMatched.lean   (J4-354, Sol consult #13 brick 1)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It supplies the ON-COLLAR,
  TAIL-MATCHED term-1 estimate (Sol consult #13, brick 1) — the matched-pair architecture that
  repairs the log-divergent naive on/off-collar split diagnosed in Sol #13.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  ★ THE SOL #13 DESIGN (followed verbatim).

  The naive split of the term-1 sliver integral into a collar part and an off-collar tail does NOT
  close: `∫_{off}|H_τ| = a(c)/τ` (τ-independent numerator) drives the truncated constant mode to a
  LOG-divergent `∫ dτ/τ` at the endpoint.  The FIX is the matched-pair split: the tail moment
  `T_τ := ∫_{off} H_{τ,i}` must stay PAIRED with the on-collar integral.

  Notation.
    • `hessGaussFactor i τ z  =  H_{τ,i}(z) := (z_i² − 2τ)/(4τ²)·G_τ(z)`   (the Hessian-Gaussian factor);
    • `collar R               =  C_τ := { ‖z‖ ≤ R }` (with `R = c·√τ` at the call site — the √ε collar);
    • `(collar R)ᶜ            =  O_τ` (the off-collar tail region);
    • `tailMoment i τ R       =  T_τ := ∫_{O_τ} H_{τ,i}`   (the BARE tail moment, NO amplitude);
    • `A₀ := q 0`             (the leading amplitude at the RNC center; concretely `Aamp τ 0·F s 0 0`).

  The matched target (`sliver_term1_on_collar_matched`):
        ‖ I_on  +  A₀·T_τ ‖  ≤  L·(15/2·n)/√τ ,   where  I_on := ∫_{C_τ} H_{τ,i}·q .
  (This is the Sol-shaped `‖I_on + A₀·T_τ‖ ≤ B₀/√τ + B₁` with `B₀ = L·(15/2·n)` and `B₁ = 0`.)

  The proof route (EXACT, per Sol #13).
    Split `q(z) = q(0) + (q(z) − q(0))`.
    (i)  The A₀-part is EXACT — no estimate.  `∫_{C_τ} H = ∫_{ℝⁿ} H − ∫_{O_τ} H = 0 − T_τ = −T_τ`
         (the FULL-SPACE cancellation `∫ (z_i²−2τ)/(4τ²)·G = 0`, banked
         `gaussian_hessian_moment_zero`, plus additivity over `C_τ ⊔ O_τ`), so `q 0·∫_{C_τ} H = −A₀·T_τ`.
         Hence the `A₀·T_τ` term cancels EXACTLY against the on-collar A₀-moment, leaving only:
    (ii) The increment part.  `|Aamp(z) − Aamp(0)| ≤ L·‖z‖` on the collar (the collar-restricted
         Lipschitz carry `hq`, taken as the honest input — see below), so
           `|∫_{C_τ} H·(q − q0)|  ≤  ∫ |H|·L·‖z‖  ≤  L·Σₖ ∫ |H|·|z_k|  ≤  L·(15/2·n)/√τ`
         (the classical √τ-gain moment `hk_coord_integral_le`; the collar integral is dominated by
         the full-space one since the integrand's norm is nonneg).

  THE HONEST COLLAR-LIPSCHITZ CARRY.  The hypothesis `hq : ∀ z w, |q z − q w| ≤ L·dist z w` is the
  load-bearing physical input.  Per Sol #13 it is SATISFIABLE collar-restricted from
  `Lip(ρ·A_chart) ≤ K·L_chart + M_chart·K·C_r·c²/4`, GIVEN the quantitative cubic-contact gradient
  estimate `‖∇(r_z − r_{W₀z})‖ ≤ C_r·‖z‖²` (tangent-isometry + C^{1,1} control — exactly what brick 2
  also needs).  Here it is carried parametrically as a genuine, non-vacuous Lipschitz hypothesis
  (the increment bound FAILS without it; `L ≥ 0` is the standard sign).  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERABLES.
    (T1)  `hessGaussFactor_integral_zero`  — the full-space moment `∫ H = 0` (re-export).
          `collarMoment_eq_neg_tail`        — the EXACT collar-moment pairing `∫_{C_τ} H = −T_τ`.
    (T2)  `hessGaussIncrement_norm_full_le`  — `∫ ‖H·(q−q0)‖ ≤ L·(15/2·n)/√τ`  (the √τ-gain).
          `hessGaussIncrement_collar_norm_le`— `‖∫_{C_τ} H·(q−q0)‖ ≤ L·(15/2·n)/√τ`.
    (T3)  `sliver_term1_on_collar_matched`   — ★ the assembled matched estimate.
    (T4)  `tailMoment_bound`                 — the sanity scaling `|T_τ| ≤ 1/τ` (the crude a(c)/τ; NOT
          used in the assembly — it documents WHY the split had to be matched, per Sol #13).

  WHAT BRICK 2 (off-collar matched domination) NEEDS.  The dual estimate
  `‖I_off − A₀·T_τ‖ ≤ B₀'/√τ + B₁'`: compare the chart-native leading term DIRECTLY with `H_τ·A₀`
  via the weighted `|G_τ^chart − G_τ| ≤ C‖z‖³/τ·G_{C'τ}` plus the amplitude increment (NEVER estimate
  ρ alone off-collar; use `G_τ·ρ = G_τ^chart`).  It reuses the SAME `tailMoment`/`hessGaussFactor`
  infrastructure banked here and the SAME cubic-contact gradient carry.  Brick 3 then cancels `A₀·T_τ`
  between bricks 1 and 2, recovering the unchanged `hbnd` with c-dependent constants absorbed.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SliverEstimates
import QIQTH.GaussianHessianCancel

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution
open scoped Interval Topology

namespace QIQTH.SliverTailMatched

open QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    The named infrastructure: the Hessian-Gaussian factor, the collar, the tail moment.
    ############################################################################### -/

/-- **`hessGaussFactor i τ z = H_{τ,i}(z) := (z_i² − 2τ)/(4τ²)·G_τ(z)`** — the Hessian-Gaussian
    factor whose full-space integral vanishes (the exact cancellation) and whose collar-restricted
    moment is `−T_τ`.  This is the pure kernel factor of the sliver term-1; the amplitude/`F` pairing
    is carried in the multiplier `q`.  ⚠ NOT `a₁ = R/6`. -/
noncomputable def hessGaussFactor (i : Fin n) (τ : ℝ) (z : Point n) : ℝ :=
  (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z

/-- **`collar R = C_τ := { ‖z‖ ≤ R }`** — the collar (with `R = c·√τ` at the sliver call site). -/
def collar (R : ℝ) : Set (Point n) := {z : Point n | ‖z‖ ≤ R}

/-- **`tailMoment i τ R = T_τ := ∫_{O_τ} H_{τ,i}`** — the BARE off-collar tail moment (no amplitude);
    `O_τ = (collar R)ᶜ = { ‖z‖ > R }`.  This is the object that must stay PAIRED with the on-collar
    integral (Sol #13); its `|·| ≤ 1/τ` bound documents the log-divergence that forced the match. -/
noncomputable def tailMoment (i : Fin n) (τ R : ℝ) : ℝ :=
  ∫ z in (collar R)ᶜ, hessGaussFactor i τ z

/-- The Hessian-Gaussian factor is integrable (re-export of `hessCoeff_gaussDdim_integrable`). -/
theorem hessGaussFactor_integrable (τ : ℝ) (hτ : 0 < τ) (i : Fin n) :
    Integrable (fun z : Point n => hessGaussFactor i τ z) volume := by
  show Integrable (fun z : Point n => (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z) volume
  exact hessCoeff_gaussDdim_integrable τ hτ i

/-- The collar `{ ‖z‖ ≤ R }` is measurable (closed half-space of the norm). -/
theorem collar_measurableSet (R : ℝ) : MeasurableSet (collar (n := n) R) := by
  simp only [collar]
  exact (isClosed_le continuous_norm continuous_const).measurableSet

/-! ###############################################################################
    (T1) — the exact full-space cancellation and the matched collar-moment pairing.
    ############################################################################### -/

/-- **(T1) THE FULL-SPACE MOMENT.**  `∫_z H_{τ,i}(z) = 0` — the exact Hessian-Gaussian cancellation
    `∫ (z_i²−2τ)/(4τ²)·G_τ = 0` (second moment `2τ` minus mass-one `2τ`), re-exported from
    `gaussian_hessian_moment_zero`.  This is the source of the matched pairing.  ⚠ NOT `a₁ = R/6`. -/
theorem hessGaussFactor_integral_zero (τ : ℝ) (hτ : 0 < τ) (i : Fin n) :
    ∫ z : Point n, hessGaussFactor i τ z = 0 := by
  simp only [hessGaussFactor]
  exact gaussian_hessian_moment_zero τ hτ i

/-- **(T1) ★ THE MATCHED COLLAR-MOMENT PAIRING (EXACT).**  `∫_{C_τ} H_{τ,i} = −T_τ`.  By additivity
    over `C_τ ⊔ O_τ` and the full-space cancellation `∫_{ℝⁿ} H = 0`: the collar moment is minus the
    tail moment, with NO estimate.  This is what makes the `A₀·T_τ` term cancel EXACTLY against the
    on-collar leading (A₀) moment in `sliver_term1_on_collar_matched`.  ⚠ NOT `a₁ = R/6`. -/
theorem collarMoment_eq_neg_tail (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (R : ℝ) :
    (∫ z in collar R, hessGaussFactor i τ z) = - tailMoment i τ R := by
  have hsum := integral_add_compl (collar_measurableSet (n := n) R) (hessGaussFactor_integrable τ hτ i)
  rw [hessGaussFactor_integral_zero τ hτ i] at hsum
  simp only [tailMoment]
  linarith [hsum]

/-! ###############################################################################
    (T2) — the increment estimate (the √τ-gain moment).
    ############################################################################### -/

/-- **(T2) THE FULL-SPACE INCREMENT NORM BOUND.**  For `q` Lipschitz with constant `L ≥ 0`,
      `∫_z ‖H_{τ,i}(z)·(q z − q 0)‖ ≤ L·(15/2·n)/√τ`.
    The Lipschitz increment `|q z − q 0| ≤ L·Σₖ|z_k|` pairs with the classical √τ-gain per-coordinate
    moment `∫ |H_{τ,i}|·|z_k| ≤ (15/2)/√τ` (`hk_coord_integral_le`).  This is the √τ-gain core of the
    on-collar estimate; the collar version follows by domination.  ⚠ NOT `a₁ = R/6`. -/
theorem hessGaussIncrement_norm_full_le (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w) :
    ∫ z : Point n, ‖hessGaussFactor i τ z * (q z - q 0)‖ ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ := by
  simp only [hessGaussFactor]
  have hbound_pt : ∀ z : Point n,
      ‖(z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (q z - q 0)‖
        ≤ ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z)]
    have hdist : |q z - q 0| ≤ L * ∑ k, |z k| := by
      refine (hq z 0).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [dist_pi_le_iff (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
      intro j
      rw [Real.dist_eq]
      simp only [Pi.zero_apply, sub_zero]
      exact Finset.single_le_sum (f := fun k => |z k|) (fun k _ => abs_nonneg (z k))
        (Finset.mem_univ j)
    calc |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |q z - q 0|
        ≤ |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * (L * ∑ k, |z k|) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (abs_nonneg _) (gaussDdim_nonneg' τ z))
      _ = ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by ring)
  have hB_int : Integrable
      (fun z : Point n => ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|))
      volume :=
    integrable_finsetSum _ (fun k _ => (hessAbs_coord_gaussDdim_integrable τ hτ i k).const_mul L)
  calc ∫ z : Point n, ‖(z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (q z - q 0)‖
      ≤ ∫ z : Point n, ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|) :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hB_int
          (ae_of_all _ hbound_pt)
    _ = ∑ k, L * ∫ z : Point n, |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k| := by
        rw [integral_finsetSum _
          (fun k _ => (hessAbs_coord_gaussDdim_integrable τ hτ i k).const_mul L)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [integral_const_mul]
    _ ≤ ∑ _k : Fin n, L * (15 / 2 / Real.sqrt τ) :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hk_coord_integral_le τ hτ i k) hL)
    _ = L * (15 / 2 * (n : ℝ)) / Real.sqrt τ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The increment `H_{τ,i}·(q − q 0)` is integrable on `Point n` (dominated by the finset-sum
    `Σₖ L·|H_{τ,i}|·|z_k|` of `hk_coord`-integrable moments; `q` measurable + Lipschitz).  ⚠ NOT
    `a₁ = R/6`. -/
theorem hessGaussIncrement_integrable (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) :
    Integrable (fun z : Point n => hessGaussFactor i τ z * (q z - q 0)) volume := by
  show Integrable
    (fun z : Point n => (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (q z - q 0)) volume
  have hbound_pt : ∀ z : Point n,
      ‖(z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (q z - q 0)‖
        ≤ ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z)]
    have hdist : |q z - q 0| ≤ L * ∑ k, |z k| := by
      refine (hq z 0).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [dist_pi_le_iff (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
      intro j
      rw [Real.dist_eq]
      simp only [Pi.zero_apply, sub_zero]
      exact Finset.single_le_sum (f := fun k => |z k|) (fun k _ => abs_nonneg (z k))
        (Finset.mem_univ j)
    calc |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |q z - q 0|
        ≤ |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * (L * ∑ k, |z k|) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (abs_nonneg _) (gaussDdim_nonneg' τ z))
      _ = ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by ring)
  have hB_int : Integrable
      (fun z : Point n => ∑ k, L * (|(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z * |z k|))
      volume :=
    integrable_finsetSum _ (fun k _ => (hessAbs_coord_gaussDdim_integrable τ hτ i k).const_mul L)
  refine Integrable.mono' hB_int ?_ (ae_of_all _ hbound_pt)
  exact ((hessCoeff_gaussDdim_integrable τ hτ i).aestronglyMeasurable).mul
    (hqmeas.sub aestronglyMeasurable_const)

/-- **(T2) THE ON-COLLAR INCREMENT BOUND.**  `‖∫_{C_τ} H_{τ,i}·(q − q 0)‖ ≤ L·(15/2·n)/√τ`.  The
    collar integral of the increment is dominated by the full-space `∫ ‖·‖` (norm-integral inequality
    + `restrict ≤ self`), giving the √τ-gain uniformly over the collar radius.  ⚠ NOT `a₁ = R/6`. -/
theorem hessGaussIncrement_collar_norm_le (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (R : ℝ) :
    ‖∫ z in collar R, hessGaussFactor i τ z * (q z - q 0)‖
      ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ := by
  calc ‖∫ z in collar R, hessGaussFactor i τ z * (q z - q 0)‖
      ≤ ∫ z in collar R, ‖hessGaussFactor i τ z * (q z - q 0)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, ‖hessGaussFactor i τ z * (q z - q 0)‖ :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ (fun z => norm_nonneg _))
          (hessGaussIncrement_integrable τ hτ i q L hL hq hqmeas).norm
    _ ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ :=
        hessGaussIncrement_norm_full_le τ hτ i q L hL hq

/-! ###############################################################################
    (T3) — the assembled matched estimate.
    ############################################################################### -/

/-- **(T3) ★★★ THE ON-COLLAR TAIL-MATCHED ESTIMATE (Sol #13 brick 1).**
      `‖ (∫_{C_τ} H_{τ,i}·q)  +  A₀·T_τ ‖  ≤  L·(15/2·n)/√τ`,   with  `A₀ := q 0`.
    The `A₀·T_τ` term cancels EXACTLY against the on-collar leading (A₀) moment
    (`∫_{C_τ} H = −T_τ`, `collarMoment_eq_neg_tail`), leaving only the increment `∫_{C_τ} H·(q − q 0)`,
    bounded by the √τ-gain (`hessGaussIncrement_collar_norm_le`).  This is the matched-pair split that
    repairs the log-divergent naive on/off-collar split (Sol #13).  The granularity matches
    `SliverEstimates.sliver2_bound`'s term 1 (`q = Aamp·F` at the call site), so brick 3 re-assembles
    directly.  `B₀ = L·(15/2·n)`, `B₁ = 0`.  ⚠ NOT `a₁ = R/6`. -/
theorem sliver_term1_on_collar_matched (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (R : ℝ) :
    ‖(∫ z in collar R, hessGaussFactor i τ z * q z) + q 0 * tailMoment i τ R‖
      ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ := by
  -- integrability of the increment and the constant leg on the collar
  have hincr_on : IntegrableOn (fun z : Point n => hessGaussFactor i τ z * (q z - q 0))
      (collar R) volume :=
    (hessGaussIncrement_integrable τ hτ i q L hL hq hqmeas).integrableOn
  have hconst_on : IntegrableOn (fun z : Point n => hessGaussFactor i τ z * q 0)
      (collar R) volume :=
    ((hessGaussFactor_integrable τ hτ i).mul_const (q 0)).integrableOn
  -- split I_on = increment + A₀-moment
  have key : (∫ z in collar R, hessGaussFactor i τ z * q z)
      = (∫ z in collar R, hessGaussFactor i τ z * (q z - q 0))
        + (∫ z in collar R, hessGaussFactor i τ z * q 0) := by
    rw [← integral_add hincr_on hconst_on]
    exact integral_congr_ae (ae_of_all _ (fun z => by ring))
  have hconst_eval : (∫ z in collar R, hessGaussFactor i τ z * q 0)
      = (∫ z in collar R, hessGaussFactor i τ z) * q 0 := integral_mul_const _ _
  -- the exact matched pairing: A₀-moment = −A₀·T_τ
  have hmatch : (∫ z in collar R, hessGaussFactor i τ z * q z) + q 0 * tailMoment i τ R
      = ∫ z in collar R, hessGaussFactor i τ z * (q z - q 0) := by
    rw [key, hconst_eval, collarMoment_eq_neg_tail τ hτ i R]; ring
  rw [hmatch]
  exact hessGaussIncrement_collar_norm_le τ hτ i q L hL hq hqmeas R

/-! ###############################################################################
    (T4, sanity) — the tail-moment scaling `|T_τ| ≤ 1/τ`.
    ############################################################################### -/

/-- The full-space absolute Hessian-Gaussian moment `∫ |H_{τ,i}| ≤ 1/τ` (`τ`-linear divergence).
    Factorizes coordinatewise: the `i`-factor is the 1-D raw hessian moment `≤ τ⁻¹`
    (`hk_absHess_moment_le`), all other factors are the mass-one Gaussian.  ⚠ NOT `a₁ = R/6`. -/
theorem hessAbs_gaussDdim_integral_le (τ : ℝ) (hτ : 0 < τ) (i : Fin n) :
    ∫ z : Point n, |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z ≤ τ⁻¹ := by
  have hpt : (fun z : Point n => |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z)
      = fun z => ∏ k, heatKernel1D τ (z k)
          * (if k = i then |(z k ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  rw [hpt, integral_fintype_prod_volume_eq_prod
    (fun k (y : ℝ) => heatKernel1D τ y * (if k = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1))]
  have hprodeq : (∏ k : Fin n, ∫ y : ℝ,
        heatKernel1D τ y * (if k = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1))
      = ∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| := by
    calc (∏ k : Fin n, ∫ y : ℝ,
          heatKernel1D τ y * (if k = i then |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| else 1))
        = ∏ k : Fin n, (if k = i
            then (∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)|) else 1) := by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          by_cases hk : k = i
          · simp [hk]
          · simp only [if_neg hk, mul_one]; exact gaussianZerothMoment_oneD τ hτ
      _ = ∫ y : ℝ, heatKernel1D τ y * |(y ^ 2 - 2 * τ) / (4 * τ ^ 2)| := Fintype.prod_ite_eq' i _
  rw [hprodeq]; exact hk_absHess_moment_le τ hτ

/-- **(T4, sanity) THE TAIL-MOMENT SCALING.**  `|T_τ| ≤ 1/τ`.  A crude-but-explicit `a(c)/τ` bound
    (here `a(c) = 1`, ignoring the Gaussian tail decay): `|T_τ| = |∫_{O_τ} H| ≤ ∫_{O_τ} |H| ≤
    ∫_{ℝⁿ} |H| ≤ 1/τ`.  This is NOT used in the assembly (`sliver_term1_on_collar_matched`) — per
    Sol #13 it documents WHY the naive split gives a LOG-divergent `∫ dτ/τ` (the `τ`-independent `1`
    numerator), forcing the matched-pair architecture.  The sharp `poly(c)·e^{−κc²}` refinement is
    deferred (not needed downstream).  ⚠ NOT `a₁ = R/6`. -/
theorem tailMoment_bound (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (R : ℝ) :
    |tailMoment i τ R| ≤ τ⁻¹ := by
  simp only [tailMoment, hessGaussFactor]
  calc |∫ z in (collar R)ᶜ, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z|
      = ‖∫ z in (collar R)ᶜ, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z in (collar R)ᶜ, ‖(z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, ‖(z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z‖ :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ (fun z => norm_nonneg _))
          (hessCoeff_gaussDdim_integrable τ hτ i).norm
    _ = ∫ z : Point n, |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| * gaussDdim τ z := by
        refine integral_congr_ae (ae_of_all _ (fun z => ?_))
        dsimp only
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z)]
    _ ≤ τ⁻¹ := hessAbs_gaussDdim_integral_le τ hτ i

end QIQTH.SliverTailMatched

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SliverTailMatched.hessGaussFactor_integral_zero
#print axioms QIQTH.SliverTailMatched.collarMoment_eq_neg_tail
#print axioms QIQTH.SliverTailMatched.hessGaussIncrement_norm_full_le
#print axioms QIQTH.SliverTailMatched.hessGaussIncrement_collar_norm_le
#print axioms QIQTH.SliverTailMatched.sliver_term1_on_collar_matched
#print axioms QIQTH.SliverTailMatched.tailMoment_bound
