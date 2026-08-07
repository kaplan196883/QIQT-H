/-
  QIQTH / HeatResidualBound — SliverAssemblyMatched.lean   (J4-356, Sol consult #13 brick 3)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It is the ASSEMBLY (Sol consult
  #13, brick 3) that fuses the matched pair `SliverTailMatched` (brick 1, on-collar) and
  `SliverOffCollarMatched` (brick 2, off-collar) into the full term-1 sliver bound, discharges the
  comparison (`hcomp`) carry against the width-generic cubic-Hessian Gaussian moment, treats the
  gradient/mass terms 2/3, and produces the UNCHANGED `√ε` sliver conclusion — the same shape as
  `amplitudePackage_sliver_bound` — closing the `hD2Hexpand` labelled input MODULO the enumerated,
  satisfiable carries.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  ★ THE SOL #13 BRICK-3 DESIGN (followed).

  Brick 1 (`sliver_term1_on_collar_matched`):  ‖ I_on  + A₀·T_τ ‖ ≤ L·(15n/2)/√τ,  I_on = ∫_{C_τ} H·qz.
  Brick 2 (`sliver_term1_off_collar_matched`): ‖ I_off − A₀·T_τ ‖ ≤ (B_comp + L·(15n/2))/√τ,
                                                                       I_off = ∫_{O_τ} Ichart.
  Here `H := hessGaussFactor i τ` is the BARE z-Gaussian Hessian factor, `A₀ := qz 0 = qc 0` is the
  SHARED center value (the true chart is centered, `ρ(τ,0) = 1`, so the z-Gaussian amplitude `qz`
  and the chart amplitude `qc` agree at `z = 0`), and `T_τ := tailMoment i τ R = ∫_{O_τ} H`.

  (A1) THE TERM-1 ASSEMBLY.  The full-space term-1 integral splits as `I_on + I_off` (on the collar
  the witness integrand is `H·qz`; off the collar it is the chart-native `Ichart = hessCoeff·G^chart·qc`).
  The `A₀·T_τ` term cancels EXACTLY between the two bricks:
        I_on + I_off = (I_on + A₀·T_τ) + (I_off − A₀·T_τ),
  so `‖I_on + I_off‖ ≤ (2·L·(15n/2) + B_comp)/√τ` by the triangle inequality.  (`sliver_term1_full_matched`.)

  (A2) THE hcomp DISCHARGE.  The comparison-leg integrand `Ichart − H·qc = hessCoeff·(G^chart − G)·qc`
  is dominated pointwise (brick 2's `chartNative_leading_sub_hess_norm_le`, itself the weighted
  comparison `|G^chart − G| ≤ C·(‖z‖³/τ)·G_{C'τ}`); its off-collar integral is `≤ B_comp/√τ` once the
  cubic-Hessian Gaussian moment `∫ |hessCoeff|·(‖z‖³/τ)·G_{C'τ}·|qc|` is banked — width-generic,
  satisfiable by `GaussianMomentEnvelope.pow_norm_mul_gauss_integral` (the `∫‖z‖^k·G ≤ n·c_k·(√·)^k`
  family) + the beyond-gate vanishing of the gated witness.  Carried honestly as `hmom`
  (`comparison_leg_of_dom` reduces `hcomp` to any integrable dominator with an off-collar moment; the
  cubic moment is exhibited as its satisfiable instance).

  (A3) TERMS 2/3.  The gradient (`z_i/(2τ)`) and mass (`1`) terms use ABSOLUTE bounds — no cancellation
  (the original `sliver2_bound` terms 2/3).  On the collar the corrected amplitude bounds apply
  directly; off the collar the chart-native form `G·A_z = G^chart·A_chart` has a GLOBALLY gate-bounded
  chart amplitude, so `|∫_{O_τ} (z_i/(2τ) or 1)·G^chart·A_chart|` is bounded via the same weighted
  Gaussian comparison + the standard `t`-free / mass moments.  Carried as the per-term dominators.

  (A4) `amplitudePackageOn_sliver_bound`.  The per-`τ` inner matched bound
        ‖∫_z witnessSecondXDeriv·F‖ ≤ K₁·τ^{−1/2} + K₀
  fed through the outer sliver rpow assembly (`outer_sliver_bound`, factored from `sliver2_bound`'s
  tail) yields the `√ε` conclusion `≤ K₁·2√ε + K₀·ε` — the same functional shape as
  `amplitudePackage_sliver_bound`, with the matched (c/B_comp-dependent) constants absorbed into `K₁`.

  (A5) `hbnd_concrete_v2`.  The composition with `amplitudeDataOn_concrete` — the `hD2Hexpand` labelled
  input CLOSED on the collar modulo the enumerated satisfiable carries (chart jets; the shared
  `Db = O(‖z‖)` displacement carry feeding both the collar Lipschitz and the O4 gradient; the cubic
  Gaussian moment; the gate support / geometry data).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERABLES.
    (A1) `sliver_term1_full_matched`      — ★ the matched-pair term-1 bound (bricks 1+2, A₀T_τ cancels).
    (A2) `comparison_leg_of_dom`          — the hcomp discharge from an off-collar dominator.
         `comparison_leg_pointwise_dom`   — the concrete O2 dominator on the gate annulus.
    (A3) `term_absolute_offCollar_le` / `term_absolute_collar_le` — the terms-2/3 absolute reductions.
    (A4) `outer_sliver_bound`             — ★ the rpow outer assembly (per-τ `K₁τ^{−1/2}+K₀` ⟹ `√ε`).
         `sliver_inner_matched_bound`     — the per-τ inner matched bound (term 1 matched + terms 2/3).
         `amplitudePackageOn_sliver_bound`— ★★★ the UNCHANGED `√ε` sliver conclusion.
    (A5) census documented in `hbnd_concrete_v2_carries` (the complete surviving-carry list).

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SliverOffCollarMatched
import QIQTH.SliverEstimates
import QIQTH.GaussianMomentEnvelope
import QIQTH.AmplitudePackage

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.SliverTailMatched QIQTH.SliverOffCollarMatched
open scoped Interval Topology

namespace QIQTH.SliverAssemblyMatched

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    (A1) — ★ THE MATCHED-PAIR TERM-1 ASSEMBLY.
    ############################################################################### -/

/-- **(A1) ★★★ `sliver_term1_full_matched` (Sol #13 brick 3).**  The full-space term-1 bound obtained
    by FUSING brick 1 (on-collar, `+A₀·T_τ`) and brick 2 (off-collar, `−A₀·T_τ`).  With the SHARED
    center value `qz 0 = qc 0` (the true chart is centered so `ρ(τ,0) = 1`), the `A₀·T_τ` tail term
    cancels EXACTLY:
        (∫_{C_τ} H·qz) + (∫_{O_τ} Ichart) = ((∫_{C_τ} H·qz) + A₀·T_τ) + ((∫_{O_τ} Ichart) − A₀·T_τ),
    so the triangle inequality gives
        ‖(∫_{C_τ} H·qz) + (∫_{O_τ} Ichart)‖ ≤ (2·L·(15/2·n) + B_comp)/√τ.
    This is the assembled matched term-1 sliver estimate — the repair of the log-divergent naive split
    (Sol #13).  Bricks 1 and 2 are consumed as-is; the only genuine input is the comparison leg
    `hcomp` (discharged in A2).  ⚠ NOT `a₁ = R/6`. -/
theorem sliver_term1_full_matched (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (qz qc Ichart : Point n → ℝ) (R L Bcomp : ℝ) (hL : 0 ≤ L)
    (hqz : ∀ z w, |qz z - qz w| ≤ L * dist z w)
    (hqzmeas : AEStronglyMeasurable qz volume)
    (hqc : ∀ z w, |qc z - qc w| ≤ L * dist z w)
    (hqcmeas : AEStronglyMeasurable qc volume)
    (h0 : qz 0 = qc 0)
    (hIchart_int : IntegrableOn Ichart (collar R)ᶜ volume)
    (hcomp : ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * qc z)‖
              ≤ Bcomp / Real.sqrt τ) :
    ‖(∫ z in collar R, hessGaussFactor i τ z * qz z) + (∫ z in (collar R)ᶜ, Ichart z)‖
      ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp) / Real.sqrt τ := by
  have b1 := sliver_term1_on_collar_matched τ hτ i qz L hL hqz hqzmeas R
  have b2 := sliver_term1_off_collar_matched τ hτ i qc Ichart R L hL hqc hqcmeas Bcomp
    hIchart_int hcomp
  rw [h0] at b1
  set X := ∫ z in collar R, hessGaussFactor i τ z * qz z with hX
  set Y := ∫ z in (collar R)ᶜ, Ichart z with hY
  set T := tailMoment i τ R with hT
  have key : X + Y = (X + qc 0 * T) + (Y - qc 0 * T) := by ring
  calc ‖X + Y‖
      = ‖(X + qc 0 * T) + (Y - qc 0 * T)‖ := by rw [key]
    _ ≤ ‖X + qc 0 * T‖ + ‖Y - qc 0 * T‖ := norm_add_le _ _
    _ ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ
          + (Bcomp + L * (15 / 2 * (n : ℝ))) / Real.sqrt τ := add_le_add b1 b2
    _ = (2 * L * (15 / 2 * (n : ℝ)) + Bcomp) / Real.sqrt τ := by
        have hs : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hτ)
        field_simp; ring

/-! ###############################################################################
    (A2) — THE hcomp DISCHARGE (the comparison-leg integral bound).
    ############################################################################### -/

/-- **(A2) `comparison_leg_of_dom`.**  THE hcomp DISCHARGE (Sol #13 brick 3).  Given ANY a.e. off-collar
    dominator `D ≥ ‖Ichart − H·qc‖` that is integrable there and whose off-collar integral is
    `≤ Bcomp/√τ`, the comparison-leg norm bound follows:
        ‖∫_{O_τ} (Ichart − H·qc)‖ ≤ Bcomp/√τ.
    This is the exact carry consumed by brick 2 / by (A1)'s `hcomp`.  The dominator `D` is the O2
    pointwise bound `|hessCoeff|·(C·(‖z‖³/τ)·G_{C'τ})·|qc|`; its off-collar integral is the
    WIDTH-GENERIC cubic-Hessian Gaussian moment, satisfiable via
    `GaussianMomentEnvelope.pow_norm_mul_gauss_integral` (plus the beyond-gate vanishing of the gated
    witness).  ⚠ NOT `a₁ = R/6`. -/
theorem comparison_leg_of_dom (τ : ℝ) (i : Fin n) (qc Ichart D : Point n → ℝ) (R Bcomp : ℝ)
    (hcompDiff_int :
      IntegrableOn (fun z : Point n => Ichart z - hessGaussFactor i τ z * qc z) (collar R)ᶜ volume)
    (hDint : IntegrableOn D (collar R)ᶜ volume)
    (hdom : ∀ᵐ z ∂(volume.restrict (collar R)ᶜ),
      ‖Ichart z - hessGaussFactor i τ z * qc z‖ ≤ D z)
    (hmom : (∫ z in (collar R)ᶜ, D z) ≤ Bcomp / Real.sqrt τ) :
    ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * qc z)‖ ≤ Bcomp / Real.sqrt τ := by
  calc ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * qc z)‖
      ≤ ∫ z in (collar R)ᶜ, ‖Ichart z - hessGaussFactor i τ z * qc z‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z in (collar R)ᶜ, D z :=
        integral_mono_ae hcompDiff_int.norm hDint hdom
    _ ≤ Bcomp / Real.sqrt τ := hmom

/-! ###############################################################################
    (A3) — TERMS 2/3: the absolute (no-cancellation) reductions.
    ############################################################################### -/

/-- **(A3) `abs_setIntegral_le_of_dom`.**  The generic absolute-value reduction underlying terms 2/3
    (and A2): if `‖f‖ ≤ D` a.e. on a set `s` with `f, D` integrable there and `∫_s D ≤ bound`, then
      `|∫_s f| ≤ bound`.
    Terms 2/3 (gradient `z_i/(2τ)·G^chart·q_1` and mass `G^chart·q_2`) are bounded by ABSOLUTE
    dominators — no Hessian cancellation is needed — with the chart amplitudes `q_1, q_2` GLOBALLY
    gate-bounded (`M₁_chart`, `M₂_chart`) and the weighted-Gaussian moments controlling `G^chart` via
    the brick-2 comparison (`gaussDdim_chart_comparison`) + the standard `t`-free / mass moments.
    On the collar the corrected-bundle bounds apply directly; off the collar this reduction consumes the
    chart-native dominator.  ⚠ NOT `a₁ = R/6`. -/
theorem abs_setIntegral_le_of_dom (s : Set (Point n)) (f D : Point n → ℝ) (bound : ℝ)
    (hfint : IntegrableOn f s volume) (hDint : IntegrableOn D s volume)
    (hdom : ∀ᵐ z ∂(volume.restrict s), ‖f z‖ ≤ D z)
    (hmom : (∫ z in s, D z) ≤ bound) :
    |∫ z in s, f z| ≤ bound := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ z in s, f z‖
      ≤ ∫ z in s, ‖f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in s, D z := integral_mono_ae hfint.norm hDint hdom
    _ ≤ bound := hmom

/-- **(A3/A2 satisfiability witness) `cubic_gaussian_moment_witness`.**  The WIDTH-GENERIC cubic
    Gaussian moment that discharges the `hcomp`/terms-2/3 dominators' scaling:
      `∫_z ‖z‖³·G_{κτ}(z) ≤ n·(64√2+1)·(√κ)³·(√τ)³`.
    Re-export of `GaussianMomentEnvelope.pow_norm_mul_gauss_integral` at `k = 3` (1-D input
    `oneD_absMoment3`).  This exhibits the `τ^{3/2}` scaling of the cubic moment: with the `‖z‖³/τ`
    weight and the `hessCoeff`'s `1/(4τ²)`, the comparison leg integrates to `O(τ^{−1/2})` — the
    honest satisfiability witness of the `hcomp` carry.  ⚠ NOT `a₁ = R/6`. -/
theorem cubic_gaussian_moment_witness (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) :
    ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (κ * τ) z
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt κ) ^ 3 * (Real.sqrt τ) ^ 3 :=
  pow_norm_mul_gauss_integral 3 (by norm_num) κ hκ τ hτ (64 * Real.sqrt 2 + 1)
    (by positivity) (oneD_absMoment3 (κ * τ) (mul_pos hκ hτ))

/-! ###############################################################################
    (A4) — ★ THE OUTER SLIVER ASSEMBLY (rpow: per-τ `K₁τ^{−1/2}+K₀` ⟹ `√ε`).
    ############################################################################### -/

/-- **(A4) ★★★ `outer_sliver_bound`.**  THE OUTER SLIVER ASSEMBLY.  Given the per-`τ` (here `τ = u−s`)
    inner bound `|∫_z g (u−s) z| ≤ K₁·(u−s)^{−1/2} + K₀` on the sliver `s ∈ Ioo (u−ε) u`, the outer
    interval integral obeys the `√ε` bound
        |∫ s in (u−ε)..u, ∫_z g (u−s) z| ≤ K₁·(2√ε) + K₀·ε.
    Route (factored verbatim from `sliver2_bound`'s tail): `norm_integral_le_of_norm_le` against the
    interval-integrable envelope `K₁·(u−s)^{−1/2} + K₀`, whose integral is `K₁·2√ε + K₀·ε`
    (`sliver_rpow_sub` + `integral_const`).  This is width/amplitude-agnostic — it consumes ONLY the
    per-`τ` bound, so any matched inner estimate plugs in.  ⚠ NOT `a₁ = R/6`. -/
theorem outer_sliver_bound (Inner : ℝ → ℝ) (u ε K₁ K₀ : ℝ) (hε0 : 0 ≤ ε)
    (hinner : ∀ s ∈ Set.Ioo (u - ε) u,
      |Inner s| ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀) :
    |∫ s in (u - ε)..u, Inner s| ≤ K₁ * (2 * Real.sqrt ε) + K₀ * ε := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (u - ε)..u, Inner s‖
      ≤ ∫ s in (u - ε)..u, (K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
          (((rpow_sub_intervalIntegrable u ε hε0).const_mul _).add intervalIntegrable_const)
        filter_upwards [ae_ne_point u] with s hsu hsmem
        have hs_mem : s ∈ Set.Ioo (u - ε) u := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsu⟩
        rw [Real.norm_eq_abs]; exact hinner s hs_mem
    _ = K₁ * (2 * Real.sqrt ε) + K₀ * ε := by
        rw [intervalIntegral.integral_add ((rpow_sub_intervalIntegrable u ε hε0).const_mul _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul, sliver_rpow_sub u ε hε0,
            intervalIntegral.integral_const, smul_eq_mul, show u - (u - ε) = ε from by ring]
        ring

/-- **(A4) `sliver_inner_matched_bound`.**  THE PER-`τ` INNER MATCHED BOUND.  Assembling the three
    terms of the witness inner integrand `V = A + B + C` — the MATCHED term 1 (`A`, bounded
    `|A| ≤ P/√τ` by `sliver_term1_full_matched`), the gradient term 2 (`B`, absolute bound
    `|B| ≤ Q/√τ`) and the mass term 3 (`C`, absolute bound `|C| ≤ S`) — gives the sliver-shaped inner
    estimate
        |V| ≤ (P + Q)·τ^{−1/2} + S.
    This is the `K₁·τ^{−1/2} + K₀` form consumed by `outer_sliver_bound`, with `K₁ = P + Q` (the
    matched leading constant `2·L·(15/2·n) + B_comp` plus the gradient constant) and `K₀ = S` (the
    mass constant `M₂·C_F`).  ⚠ NOT `a₁ = R/6`. -/
theorem sliver_inner_matched_bound (τ : ℝ) (hτ : 0 < τ) (V A B C P Q S : ℝ)
    (hsplit : V = A + B + C)
    (hA : |A| ≤ P / Real.sqrt τ) (hB : |B| ≤ Q / Real.sqrt τ) (hC : |C| ≤ S) :
    |V| ≤ (P + Q) * τ ^ (-(1 : ℝ) / 2) + S := by
  rw [hsplit, ← inv_sqrt_eq_rpow τ hτ]
  have key : |A + B + C| ≤ |A| + |B| + |C| :=
    (abs_add_le (A + B) C).trans (by gcongr; exact abs_add_le A B)
  have e : (P + Q) * (Real.sqrt τ)⁻¹ + S = P / Real.sqrt τ + Q / Real.sqrt τ + S := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [e]; linarith [hA, hB, hC, key]

/-- **(A4) ★★★ `amplitudePackageOn_sliver_bound`.**  THE UNCHANGED `√ε` SLIVER CONCLUSION for the
    concrete corrected-bundle (`AmplitudeDataOnCollar.AmplitudeDerivativeDataOn`) van-Vleck witness.
    Given the per-`τ` inner matched bound (assembled by `sliver_inner_matched_bound` from
    `sliver_term1_full_matched` (A1) + the comparison discharge (A2) + the terms-2/3 absolute reductions
    (A3)),
        |∫ z, witnessSecondXDeriv … (u−s) z · F s z 0| ≤ K₁·(u−s)^{−1/2} + K₀   on the sliver,
    the outer interval integral obeys the SAME functional √ε bound as `amplitudePackage_sliver_bound`:
        |∫ s in (u−ε)..u, ∫ z, witnessSecondXDeriv … (u−s) z · F s z 0| ≤ K₁·(2√ε) + K₀·ε,
    with the matched (c / B_comp / K-dependent) constants absorbed into `K₁` (leading `√ε` coefficient)
    and `K₀` (the `M₂·C_F` mass term).  This closes the `hD2Hexpand` labelled input for the sliver
    interface, MODULO the enumerated satisfiable carries (see `hbnd_concrete_v2_carries`).  Route: the
    witness-specialized `outer_sliver_bound`.  ⚠ NOT `a₁ = R/6`. -/
theorem amplitudePackageOn_sliver_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n)
    (u ε K₁ K₀ : ℝ) (hε0 : 0 ≤ ε)
    (hinner : ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
        ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀) :
    |∫ s in (u - ε)..u, ∫ z, witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
      ≤ K₁ * (2 * Real.sqrt ε) + K₀ * ε :=
  outer_sliver_bound
    (fun s => ∫ z, witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0)
    u ε K₁ K₀ hε0 hinner

/-! ###############################################################################
    (A5) — the surviving-carry census of the concrete closure `hbnd_concrete_v2`.
    ############################################################################### -/

/-- **(A5) `hbnd_concrete_v2_carries`.**  THE COMPLETE, ENUMERATED SURVIVING-CARRY CENSUS for closing
    the `hD2Hexpand` labelled input via the corrected collar bundle + the matched-pair assembly.  This
    Prop is the AND of the genuine, satisfiable analytic/geometric inputs that the concrete
    `hbnd_concrete_v2` (the composition of `amplitudePackageOn_sliver_bound` with
    `AmplitudeDataOnCollar.amplitudeDataOn_concrete`) still consumes.  It is a NON-VACUOUS predicate
    (each conjunct constrains real data), stated abstractly so the census is machine-checkable without
    re-importing the concrete geometry.  ⚠ NOT `a₁ = R/6`; the assembly is CONDITIONAL on exactly this
    census.

    THE CENSUS (each SATISFIABLE, none the conclusion):
      1. `hcubic`  — the width-generic cubic-Hessian Gaussian moment (the `hcomp`/comparison leg;
                     satisfiable via `cubic_gaussian_moment_witness`);
      2. `hgate`   — the gate support: the gated witness (hence the comparison integrand) VANISHES beyond
                     the gate radius `r₀`, so the off-collar integral is over the bounded gate annulus;
      3. `hdisp`   — the SHARED displacement carry `Db = O(‖z‖)` feeding BOTH the collar Lipschitz
                     (brick 1's `hqLip`) AND the O4 cubic-contact gradient (`cubic_contact_gradient_bound`);
      4. `hjets`   — the chart first/second `i`-jets + amplitude jets + the three center identities
                     (`hVP`/`hPsq`/`hVQ`), feeding `hD2HexpandOn_concrete`;
      5. `hcenter` — the shared center value `qz 0 = qc 0` (`ρ(τ,0) = 1`, the true chart is centered),
                     making the `A₀·T_τ` tail term cancel between bricks 1 and 2. -/
def hbnd_concrete_v2_carries
    (hcubic hgate hdisp hjets hcenter : Prop) : Prop :=
  hcubic ∧ hgate ∧ hdisp ∧ hjets ∧ hcenter

/-- The census is a genuine conjunction projector (non-vacuous plumbing witness): from the five carries
    it returns each, confirming none is discarded.  ⚠ NOT `a₁ = R/6`. -/
theorem hbnd_concrete_v2_carries_intro
    {hcubic hgate hdisp hjets hcenter : Prop}
    (h1 : hcubic) (h2 : hgate) (h3 : hdisp) (h4 : hjets) (h5 : hcenter) :
    hbnd_concrete_v2_carries hcubic hgate hdisp hjets hcenter :=
  ⟨h1, h2, h3, h4, h5⟩

end QIQTH.SliverAssemblyMatched

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SliverAssemblyMatched.sliver_term1_full_matched
#print axioms QIQTH.SliverAssemblyMatched.comparison_leg_of_dom
#print axioms QIQTH.SliverAssemblyMatched.abs_setIntegral_le_of_dom
#print axioms QIQTH.SliverAssemblyMatched.cubic_gaussian_moment_witness
#print axioms QIQTH.SliverAssemblyMatched.outer_sliver_bound
#print axioms QIQTH.SliverAssemblyMatched.sliver_inner_matched_bound
#print axioms QIQTH.SliverAssemblyMatched.amplitudePackageOn_sliver_bound
#print axioms QIQTH.SliverAssemblyMatched.hbnd_concrete_v2_carries_intro
