/-
  QIQTH / HeatResidualBound — SliverOffCollarMatched.lean   (J4-355, Sol consult #13 brick 2)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It supplies the OFF-COLLAR,
  TAIL-MATCHED term-1 estimate (Sol consult #13, brick 2) — the dual of `SliverTailMatched`'s brick 1,
  which together repair the log-divergent naive on/off-collar split diagnosed in Sol #13.  NOT
  `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  ★ THE SOL #13 BRICK-2 DESIGN (followed verbatim).

  Brick 1 (`SliverTailMatched.sliver_term1_on_collar_matched`) proved
      ‖ I_on  + A₀·T_τ ‖ ≤ B₀/√τ + B₁,   T_τ := ∫_{O_τ} H_{τ,i},   A₀ := q 0.
  Brick 2 (THIS file) is the matched dual off-collar estimate
      ‖ I_off − A₀·T_τ ‖ ≤ B₀'/√τ + B₁',
  where the leading chart-native off-collar term `I_off = ∫_{O_τ} H^chart_{τ,i}·q` is compared DIRECTLY
  with `A₀·T_τ`.  The crux is the weighted Gaussian comparison (Sol: *never estimate ρ alone; use
  `G_τ·ρ = G_τ^chart`*):
      |G_τ^chart(z) − G_τ(z)| ≤ C·(‖z‖³/τ)·G_{C'τ}(z)   on the gate region,
  obtained from the EXACT ratio identity `G_τ^chart = ρ·G_τ` (`AmplitudeDataOnCollar.gauss_ratio_rho`,
  itself from `HrepGermFactorization.chartImageGauss_ratio`), the elementary `|eˣ − 1| ≤ |x|·e^{|x|}`,
  the near-isometry defect `|Δr| ≤ L·‖z‖·r_z ≤ L·n·‖z‖³`, and the WIDTH ALGEBRA
      e^{a·r_z/τ}·G_τ = (√C')ⁿ·G_{C'τ},   C' = (1 − L·r₀)⁻¹,
  which absorbs the exponential slack `e^{|x|}` into a widened Gaussian on the gate `‖z‖ ≤ r₀`
  (needs the smallness `L·r₀ < 1`, satisfiable by shrinking the gate — an HONEST hypothesis).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERABLES (Sol #13 brick 2).
    (O1)  `gaussDdim_ratio` / `exp_weight_gaussDdim'` / `abs_exp_sub_one_le`  — the algebra of the
          comparison; `gaussDdim_chart_comparison` — ★ THE WEIGHTED GAUSSIAN COMPARISON LEMMA
          `|G_τ^chart − G_τ| ≤ C·(‖z‖³/τ)·G_{C'τ}` (abstract in `w`); `chartGauss_comparison_concrete`
          — the concrete corollary at the true inverse chart `W z 0` (hiso from
          `chartW0_rncRadialSq_error`, gate shrunk so `L·r₀ < 1`).
    (O2)  `chartNative_leading_sub_hess` — the pointwise integrand difference
          `H^chart·q − H·q = hessCoeff·(G^chart − G)·q`; `chartNative_leading_sub_hess_norm_le` — its
          norm dominated via (O1) (the pointwise core brick 3 integrates for `B_comp`).
    (O3)  `hessGaussIncrement_offCollar_norm_le` — the off-collar √τ-gain increment leg (domination,
          FULLY PROVEN, brick-1 style); `sliver_term1_off_collar_matched` — ★ THE ASSEMBLED MATCHED
          ESTIMATE `‖I_off − A₀·T_τ‖ ≤ (B_comp + L·(15/2·n))/√τ` (Sol shape, `B₁' = 0`).  The
          Gaussian-comparison leg is carried as ONE honest, satisfiable analytic hypothesis
          `hcomp` (the width-generic cubic moment + the beyond-gate Gaussian tail — Sol's leg; it is
          NOT the conclusion, and its satisfiability is exactly what (O1)/(O2) exhibit).
    (O4)  `cubic_contact_gradient_bound` — ★ the cubic-contact GRADIENT reconstruction
          `‖∇_z(r_z − r_{W₀z})‖ ≤ C_r·‖z‖²` from the displacement magnitude `‖b‖ ≤ C_W‖z‖²` AND the
          honest derivative-level carry `‖Db‖ ≤ C_E‖z‖` (encoded as the two contraction bounds).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  ★ THE O4 VERDICT (the cubic-contact gradient recon).  With `W z 0 = −z + b(z)`, `‖b(z)‖ ≤ C_W‖z‖²`
  (`chartW0_displacement`, banked), the exact gradient is
      ∇_z(r_z − r_{W z 0}) = 2·b(z) + 2·(Db)ᵀz − 2·(Db)ᵀb(z).
  For the `O(‖z‖²)` cubic contact this needs `Db = O(‖z‖)` (the C^{1,1}/base-side C¹ control of the
  displacement).  The banked `chartW0_displacement` gives ONLY the C⁰ magnitude `‖b‖ ≤ C_W‖z‖²` — NOT
  derivative-level control; and per the `InverseChartDisplacement` / `BaseVaryingIFTPackage` /
  `FlowJointRegularity` firewalls the base-side C¹ regularity ("was never established") is NOT banked.
  VERDICT: the gradient estimate is NOT derivable from the banked displacement jets alone; the
  derivative bound `Db = O(‖z‖)` is THE honest carry (Sol #13 anticipated: "tangent-isometry + C^{1,1}
  control — also exactly what Brick 2 needs").  `cubic_contact_gradient_bound` is the honest CONDITIONAL
  lemma: GIVEN that carry (as the two contraction bounds `hu`/`hw`) the cubic contact follows.  NOT
  `a₁ = R/6`.

  WHAT BRICK 3 (the assembly) NEEDS.  It cancels `A₀·T_τ` between brick 1 (`+A₀T_τ`) and brick 2
  (`−A₀T_τ`), recovering the unchanged `hbnd` (SliverEstimates.sliver2_bound term 1) with the
  c-dependent constants `B₀ + B₀'` absorbed.  Brick 3 consumes: this file's `sliver_term1_off_collar_
  matched` (with `I_off = ∫_{O_τ} H^chart·q`) + brick 1's on-collar match; the residual analytic input
  is the single `hcomp` moment carry (satisfiable via `chartGauss_comparison_concrete` + the banked
  cubic Gaussian absorption `rncRadialCubed_mul_gaussDdim_le`) and the `hqLip` collar-Lipschitz carry
  (the O4 gradient bound feeds `Lip(ρ·A_chart)`).

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SliverTailMatched
import QIQTH.AmplitudeDataOnCollar

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.HeatResidualBound QIQTH.SliverTailMatched QIQTH.AmplitudeDataOnCollar
open scoped Interval Topology

namespace QIQTH.SliverOffCollarMatched

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    (O1a) — the elementary exponential increment `|eˣ − 1| ≤ |x|·e^{|x|}`.
    ############################################################################### -/

/-- **(O1a) `abs_exp_sub_one_le`.**  The two-sided exponential increment bound
      `|eˣ − 1| ≤ |x|·e^{|x|}`,   for all `x : ℝ`.
    Upper: `eˣ − 1 ≤ x·eˣ ≤ |x|·e^{|x|}` (via `e^{−x} ≥ 1 − x` multiplied by `eˣ`).  Lower:
    `eˣ − 1 ≥ x ≥ −|x| ≥ −(|x|·e^{|x|})` (`add_one_le_exp` + `e^{|x|} ≥ 1`).  This is where the ratio
    slack `ρ − 1 = e^{Δr/(4τ)} − 1` is turned into a controllable `|Δr|/(4τ)·e^{…}`.  ⚠ NOT `a₁ = R/6`. -/
theorem abs_exp_sub_one_le (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  have hlo : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hhi : Real.exp x - 1 ≤ x * Real.exp x := by
    have h := Real.add_one_le_exp (-x)
    have hpos := Real.exp_pos x
    have hmul : (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    nlinarith [hmul]
  have hE1 : (1 : ℝ) ≤ Real.exp |x| := Real.one_le_exp_iff.mpr (abs_nonneg x)
  have hxle : |x| ≤ |x| * Real.exp |x| := by nlinarith [abs_nonneg x, hE1]
  have hax : x * Real.exp x ≤ |x| * Real.exp |x| := by
    calc x * Real.exp x ≤ |x * Real.exp x| := le_abs_self _
      _ = |x| * Real.exp x := by rw [abs_mul, abs_of_pos (Real.exp_pos x)]
      _ ≤ |x| * Real.exp |x| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
          exact Real.exp_le_exp.mpr (le_abs_self x)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [hlo, neg_abs_le x, hxle]
  · linarith [hhi, hax]

/-! ###############################################################################
    (O1b) — the abstract Gaussian ratio and the width algebra.
    ############################################################################### -/

/-- **(O1b) `gaussDdim_ratio`.**  Since `gaussDdim τ v = (√(4πτ))⁻ⁿ·e^{−r_v/(4τ)}` depends on `v`
    only through `r_v = rncRadialSq v`, for ALL `z w : Point n`
      `gaussDdim τ w = e^{(r_z − r_w)/(4τ)} · gaussDdim τ z`.
    Unconditional algebra from `gaussDdim_eq_exp` (the abstract analogue of `chartImageGauss_ratio`).
    ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_ratio (τ : ℝ) (hτ : 0 < τ) (z w : Point n) :
    gaussDdim τ w
      = Real.exp ((rncRadialSq z - rncRadialSq w) / (4 * τ)) * gaussDdim τ z := by
  have h4τ : (4 : ℝ) * τ ≠ 0 := by positivity
  rw [gaussDdim_eq_exp τ w, gaussDdim_eq_exp τ z]
  rw [show Real.exp ((rncRadialSq z - rncRadialSq w) / (4 * τ))
        * (((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n * Real.exp (-(rncRadialSq z) / (4 * τ)))
      = ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n
        * (Real.exp ((rncRadialSq z - rncRadialSq w) / (4 * τ))
            * Real.exp (-(rncRadialSq z) / (4 * τ))) from by ring]
  rw [← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **(O1b) `exp_weight_gaussDdim'`.**  THE WIDTH ALGEBRA.  For `τ, C' > 0` and `a` with
    `4·C'·a = C' − 1` (so `a = (C'−1)/(4C')`), the exponentially-weighted Gaussian is a WIDENED
    Gaussian:
      `e^{a·r_v/τ} · gaussDdim τ v = (√C')ⁿ · gaussDdim (C'·τ) v`.
    The exponent `a/τ − 1/(4τ) = −1/(4·C'τ)` matches; the prefactor ratio is `(√C')ⁿ` (`√(4πτ)⁻¹ =
    √C'·√(4π·C'τ)⁻¹`).  This absorbs the `e^{|x|}` slack of (O1a) into a wider Gaussian.
    ⚠ NOT `a₁ = R/6`. -/
theorem exp_weight_gaussDdim' (τ C' : ℝ) (hτ : 0 < τ) (hC' : 0 < C') (v : Point n) (a : ℝ)
    (hrel : 4 * C' * a = C' - 1) :
    Real.exp (a * rncRadialSq v / τ) * gaussDdim τ v
      = Real.sqrt C' ^ n * gaussDdim (C' * τ) v := by
  have hC'ne : C' ≠ 0 := ne_of_gt hC'
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have ha : a = (C' - 1) / (4 * C') := by field_simp; linear_combination hrel
  have hsqC : Real.sqrt C' ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hC')
  have hsplit : Real.sqrt (4 * Real.pi * (C' * τ)) = Real.sqrt C' * Real.sqrt (4 * Real.pi * τ) := by
    rw [show 4 * Real.pi * (C' * τ) = C' * (4 * Real.pi * τ) from by ring, Real.sqrt_mul hC'.le]
  have hscalar : Real.sqrt C' * (Real.sqrt (4 * Real.pi * (C' * τ)))⁻¹
      = (Real.sqrt (4 * Real.pi * τ))⁻¹ := by
    rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ hsqC, one_mul]
  have hpref : ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n
      = Real.sqrt C' ^ n * ((Real.sqrt (4 * Real.pi * (C' * τ)))⁻¹) ^ n := by
    rw [← mul_pow, hscalar]
  have hexp : Real.exp (a * rncRadialSq v / τ) * Real.exp (-(rncRadialSq v) / (4 * τ))
      = Real.exp (-(rncRadialSq v) / (4 * (C' * τ))) := by
    rw [← Real.exp_add]; congr 1; rw [ha]; field_simp; ring
  rw [gaussDdim_eq_exp τ v, gaussDdim_eq_exp (C' * τ) v, hpref, ← hexp]; ring

/-! ###############################################################################
    (O1) — ★ THE WEIGHTED GAUSSIAN COMPARISON LEMMA.
    ############################################################################### -/

/-- **(O1) ★★★ `gaussDdim_chart_comparison`.**  THE WEIGHTED GAUSSIAN COMPARISON (Sol #13 brick 2).
    On the gate region (`‖z‖ ≤ r₀`, smallness `L·r₀ < 1`), with the near-isometry radial defect
    `|r_z − r_w| ≤ L·‖z‖·r_z`,
      `|gaussDdim τ w − gaussDdim τ z| ≤ (L·n/4)·(√C')ⁿ·(‖z‖³/τ)·gaussDdim (C'·τ) z`,
    where `C' = (1 − L·r₀)⁻¹`.  Route (Sol, exact): the ratio `gaussDdim τ w = eˣ·gaussDdim τ z`
    (`gaussDdim_ratio`, `x = (r_z−r_w)/(4τ)`) gives `|·| = |eˣ − 1|·G ≤ |x|·e^{|x|}·G` (`abs_exp_sub_one_le`);
    `|x| ≤ L·‖z‖·r_z/(4τ)` and `e^{|x|} ≤ e^{a·r_z/τ}` (`a = L·r₀/4`, using `‖z‖ ≤ r₀`); the width
    algebra `exp_weight_gaussDdim'` converts `e^{a·r_z/τ}·G` into `(√C')ⁿ·G_{C'τ}`; finally
    `‖z‖·r_z ≤ n·‖z‖³` (`rncRadialSq_le_nsq`).  ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_chart_comparison (τ : ℝ) (hτ : 0 < τ) (z w : Point n)
    (L r₀ : ℝ) (hL : 0 ≤ L) (hr0 : 0 ≤ r₀) (hzr : ‖z‖ ≤ r₀) (hsmall : L * r₀ < 1)
    (hiso : |rncRadialSq z - rncRadialSq w| ≤ L * ‖z‖ * rncRadialSq z) :
    |gaussDdim τ w - gaussDdim τ z|
      ≤ L * (n : ℝ) / 4 * Real.sqrt ((1 - L * r₀)⁻¹) ^ n
          * (‖z‖ ^ 3 / τ) * gaussDdim ((1 - L * r₀)⁻¹ * τ) z := by
  have hC'pos : 0 < 1 - L * r₀ := by linarith
  have hne : (1 - L * r₀) ≠ 0 := ne_of_gt hC'pos
  set C' : ℝ := (1 - L * r₀)⁻¹ with hC'def
  have hC'pos' : 0 < C' := by rw [hC'def]; exact inv_pos.mpr hC'pos
  have hrz0 : 0 ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have h4τ : (0 : ℝ) < 4 * τ := by positivity
  have hGz0 : 0 ≤ gaussDdim τ z := gaussDdim_nonneg' τ z
  -- the ratio and the exponent `x`
  have hratio : gaussDdim τ w
      = Real.exp ((rncRadialSq z - rncRadialSq w) / (4 * τ)) * gaussDdim τ z :=
    gaussDdim_ratio τ hτ z w
  set x : ℝ := (rncRadialSq z - rncRadialSq w) / (4 * τ) with hxdef
  -- |diff| = |eˣ − 1|·G
  have hdiff : |gaussDdim τ w - gaussDdim τ z| = |Real.exp x - 1| * gaussDdim τ z := by
    rw [hratio, show Real.exp x * gaussDdim τ z - gaussDdim τ z
          = (Real.exp x - 1) * gaussDdim τ z from by ring, abs_mul, abs_of_nonneg hGz0]
  -- |x| ≤ L‖z‖·r_z/(4τ)
  have hxabs : |x| ≤ L * ‖z‖ * rncRadialSq z / (4 * τ) := by
    rw [hxdef, abs_div, abs_of_pos h4τ]
    gcongr
  -- |x| ≤ a·r_z/τ  with a = L·r₀/4
  set a : ℝ := L * r₀ / 4 with hadef
  have hxabs2 : |x| ≤ a * rncRadialSq z / τ := by
    calc |x| ≤ L * ‖z‖ * rncRadialSq z / (4 * τ) := hxabs
      _ ≤ L * r₀ * rncRadialSq z / (4 * τ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzr hL) hrz0)
            (inv_nonneg.mpr h4τ.le)
      _ = a * rncRadialSq z / τ := by rw [hadef]; ring
  have hexpbound : Real.exp |x| ≤ Real.exp (a * rncRadialSq z / τ) := Real.exp_le_exp.mpr hxabs2
  -- step 1: |diff| ≤ |x|·e^{|x|}·G
  have hstep1 : |gaussDdim τ w - gaussDdim τ z| ≤ |x| * Real.exp |x| * gaussDdim τ z := by
    rw [hdiff]
    exact mul_le_mul_of_nonneg_right (abs_exp_sub_one_le x) hGz0
  -- step 2: bound |x| and e^{|x|}
  have hstep2 : |x| * Real.exp |x| * gaussDdim τ z
      ≤ (L * ‖z‖ * rncRadialSq z / (4 * τ)) * Real.exp (a * rncRadialSq z / τ) * gaussDdim τ z := by
    apply mul_le_mul_of_nonneg_right _ hGz0
    exact mul_le_mul hxabs hexpbound (Real.exp_pos _).le
      (div_nonneg (mul_nonneg (mul_nonneg hL hzn) hrz0) h4τ.le)
  -- the width algebra: e^{a·r_z/τ}·G = (√C')ⁿ·G_{C'τ}
  have hweight : Real.exp (a * rncRadialSq z / τ) * gaussDdim τ z
      = Real.sqrt C' ^ n * gaussDdim (C' * τ) z :=
    exp_weight_gaussDdim' τ C' hτ hC'pos' z a (by rw [hC'def, hadef]; field_simp; ring)
  have hXnn : 0 ≤ Real.sqrt C' ^ n * gaussDdim (C' * τ) z :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) n) (gaussDdim_nonneg' _ _)
  -- the cubic bound `‖z‖·r_z ≤ n·‖z‖³`
  have hcube : L * ‖z‖ * rncRadialSq z ≤ L * (n : ℝ) * ‖z‖ ^ 3 := by
    have hrzle : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := rncRadialSq_le_nsq z
    calc L * ‖z‖ * rncRadialSq z
        ≤ L * ‖z‖ * ((n : ℝ) * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hrzle (mul_nonneg hL hzn)
      _ = L * (n : ℝ) * ‖z‖ ^ 3 := by ring
  have hnum : L * ‖z‖ * rncRadialSq z / (4 * τ) ≤ L * (n : ℝ) * ‖z‖ ^ 3 / (4 * τ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcube (inv_nonneg.mpr h4τ.le)
  -- assemble
  calc |gaussDdim τ w - gaussDdim τ z|
      ≤ |x| * Real.exp |x| * gaussDdim τ z := hstep1
    _ ≤ (L * ‖z‖ * rncRadialSq z / (4 * τ)) * Real.exp (a * rncRadialSq z / τ) * gaussDdim τ z :=
        hstep2
    _ = (L * ‖z‖ * rncRadialSq z / (4 * τ)) * (Real.sqrt C' ^ n * gaussDdim (C' * τ) z) := by
        rw [mul_assoc, hweight]
    _ ≤ (L * (n : ℝ) * ‖z‖ ^ 3 / (4 * τ)) * (Real.sqrt C' ^ n * gaussDdim (C' * τ) z) :=
        mul_le_mul_of_nonneg_right hnum hXnn
    _ = L * (n : ℝ) / 4 * Real.sqrt C' ^ n * (‖z‖ ^ 3 / τ) * gaussDdim (C' * τ) z := by ring

/-- **(O1) `chartGauss_comparison_concrete`.**  The weighted comparison at the TRUE inverse chart
    `W z 0 = uniformInverseChart g gi hC hK z 0`.  The gate radius is shrunk to
    `r₀ = min (r₁/2) (1/(2(L+1)))` so the smallness `L·r₀ < 1` holds; `hiso` is supplied by the banked
    two-sided near-isometry `chartW0_rncRadialSq_error`.  This is the ready chart-level input for the
    off-collar comparison leg.  ⚠ NOT `a₁ = R/6`. -/
theorem chartGauss_comparison_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (hτ : 0 < τ) :
    ∃ r₀ > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ L * r₀ < 1 ∧ ∀ z ∈ K, ‖z‖ ≤ r₀ →
      |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|
        ≤ L * (n : ℝ) / 4 * Real.sqrt ((1 - L * r₀)⁻¹) ^ n * (‖z‖ ^ 3 / τ)
            * gaussDdim ((1 - L * r₀)⁻¹ * τ) z := by
  obtain ⟨r₁, hr₁, L, hL0, hraw⟩ := chartW0_rncRadialSq_error g gi hC hK
  have hLpos : (0 : ℝ) < 2 * (L + 1) := by linarith
  refine ⟨min (r₁ / 2) (1 / (2 * (L + 1))), lt_min (by linarith) (by positivity), L, hL0, ?_, ?_⟩
  · have h1 : min (r₁ / 2) (1 / (2 * (L + 1))) ≤ 1 / (2 * (L + 1)) := min_le_right _ _
    calc L * min (r₁ / 2) (1 / (2 * (L + 1)))
        ≤ L * (1 / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h1 hL0
      _ < 1 := by rw [mul_one_div, div_lt_one hLpos]; linarith
  · intro z hz hzr
    have hzr₁ : ‖z‖ < r₁ :=
      lt_of_le_of_lt (le_trans hzr (min_le_left _ _)) (by linarith)
    obtain ⟨hlo, hhi⟩ := hraw z hz hzr₁
    have hiso : |rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)|
        ≤ L * ‖z‖ * rncRadialSq z := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hr0nn : 0 ≤ min (r₁ / 2) (1 / (2 * (L + 1))) :=
      le_of_lt (lt_min (by linarith) (by positivity))
    have hsmall : L * min (r₁ / 2) (1 / (2 * (L + 1))) < 1 := by
      have h1 : min (r₁ / 2) (1 / (2 * (L + 1))) ≤ 1 / (2 * (L + 1)) := min_le_right _ _
      calc L * min (r₁ / 2) (1 / (2 * (L + 1)))
          ≤ L * (1 / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h1 hL0
        _ < 1 := by rw [mul_one_div, div_lt_one hLpos]; linarith
    exact gaussDdim_chart_comparison τ hτ z (uniformInverseChart g gi hC hK z 0)
      L (min (r₁ / 2) (1 / (2 * (L + 1)))) hL0 hr0nn hzr hsmall hiso

/-! ###############################################################################
    (O2) — the off-collar integrand difference decomposition.
    ############################################################################### -/

/-- **(O2) `chartNative_leading_sub_hess`.**  The pointwise algebraic identity that isolates the
    Gaussian comparison inside the off-collar leading term.  For the chart-native leading integrand
    `H^chart·q := (z_i²−2τ)/(4τ²)·gaussDdim τ w·q` and the bare Hessian factor `H := hessGaussFactor`,
      `H^chart·q − H·q = (z_i²−2τ)/(4τ²)·(gaussDdim τ w − gaussDdim τ z)·q`.
    (Pure `ring` once `hessGaussFactor` is unfolded.)  ⚠ NOT `a₁ = R/6`. -/
theorem chartNative_leading_sub_hess (τ : ℝ) (i : Fin n) (z w : Point n) (q : ℝ) :
    (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ w * q - hessGaussFactor i τ z * q
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * (gaussDdim τ w - gaussDdim τ z) * q := by
  simp only [hessGaussFactor]; ring

/-- **(O2) `chartNative_leading_sub_hess_norm_le`.**  The norm of the off-collar leading integrand
    difference, dominated by (O1): on the gate region,
      `‖H^chart·q − H·q‖ ≤ |hessCoeff|·(C·(‖z‖³/τ)·G_{C'τ})·|q|`.
    This is the pointwise core whose off-collar INTEGRAL is the comparison-leg constant `B_comp`
    consumed by `sliver_term1_off_collar_matched` — exhibiting that carry's satisfiability (the
    width-generic cubic Gaussian moment).  ⚠ NOT `a₁ = R/6`. -/
theorem chartNative_leading_sub_hess_norm_le (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (z w : Point n) (q : ℝ)
    (L r₀ : ℝ) (hL : 0 ≤ L) (hr0 : 0 ≤ r₀) (hzr : ‖z‖ ≤ r₀) (hsmall : L * r₀ < 1)
    (hiso : |rncRadialSq z - rncRadialSq w| ≤ L * ‖z‖ * rncRadialSq z) :
    ‖(z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ w * q - hessGaussFactor i τ z * q‖
      ≤ |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)|
          * (L * (n : ℝ) / 4 * Real.sqrt ((1 - L * r₀)⁻¹) ^ n * (‖z‖ ^ 3 / τ)
              * gaussDdim ((1 - L * r₀)⁻¹ * τ) z)
          * |q| := by
  rw [chartNative_leading_sub_hess τ i z w q, Real.norm_eq_abs, abs_mul, abs_mul]
  gcongr
  exact gaussDdim_chart_comparison τ hτ z w L r₀ hL hr0 hzr hsmall hiso

/-! ###############################################################################
    (O3) — the off-collar increment leg and the assembled matched estimate.
    ############################################################################### -/

/-- **(O3) `hessGaussIncrement_offCollar_norm_le`.**  The off-collar √τ-gain increment leg:
      `‖∫_{O_τ} H_{τ,i}·(q − q 0)‖ ≤ L·(15/2·n)/√τ`,   `O_τ = (collar R)ᶜ`.
    The off-collar integral of the increment is dominated by the FULL-SPACE `∫ ‖·‖`
    (`Measure.restrict_le_self`), giving the √τ-gain uniformly (brick-1 style, but on the complement).
    ⚠ NOT `a₁ = R/6`. -/
theorem hessGaussIncrement_offCollar_norm_le (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (R : ℝ) :
    ‖∫ z in (collar R)ᶜ, hessGaussFactor i τ z * (q z - q 0)‖
      ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ := by
  calc ‖∫ z in (collar R)ᶜ, hessGaussFactor i τ z * (q z - q 0)‖
      ≤ ∫ z in (collar R)ᶜ, ‖hessGaussFactor i τ z * (q z - q 0)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, ‖hessGaussFactor i τ z * (q z - q 0)‖ :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ (fun z => norm_nonneg _))
          (hessGaussIncrement_integrable τ hτ i q L hL hq hqmeas).norm
    _ ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ :=
        hessGaussIncrement_norm_full_le τ hτ i q L hL hq

/-- **(O3) ★★★ `sliver_term1_off_collar_matched` (Sol #13 brick 2).**
      `‖ (∫_{O_τ} Ichart)  −  A₀·T_τ ‖  ≤  (B_comp + L·(15/2·n))/√τ ‖`,   `A₀ := q 0`,
    where `Ichart` is the chart-native leading off-collar integrand (`= H^chart·q` at the call site),
    `T_τ = tailMoment i τ R = ∫_{O_τ} H`, and `O_τ = (collar R)ᶜ`.  The EXACT split
      `∫_{O_τ} Ichart − A₀·T_τ = ∫_{O_τ}(Ichart − H·q) + ∫_{O_τ} H·(q − q0)`
    separates the Gaussian-comparison leg (carried honestly as `hcomp`, the width-generic cubic moment
    + beyond-gate tail — NOT the conclusion; satisfiable via (O1)/(O2)) from the amplitude-increment leg
    (PROVEN by `hessGaussIncrement_offCollar_norm_le`, the √τ-gain).  This is the matched dual of
    brick 1: `A₀·T_τ` cancels between the two bricks in the assembly (brick 3).  The Sol shape has
    `B₀' = B_comp + L·(15/2·n)`, `B₁' = 0`.  ⚠ NOT `a₁ = R/6`. -/
theorem sliver_term1_off_collar_matched (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (q Ichart : Point n → ℝ) (R : ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume)
    (Bcomp : ℝ)
    (hIchart_int : IntegrableOn Ichart (collar R)ᶜ volume)
    (hcomp : ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * q z)‖
              ≤ Bcomp / Real.sqrt τ) :
    ‖(∫ z in (collar R)ᶜ, Ichart z) - q 0 * tailMoment i τ R‖
      ≤ (Bcomp + L * (15 / 2 * (n : ℝ))) / Real.sqrt τ := by
  -- integrabilities on the off-collar region
  have hHq0_int : IntegrableOn (fun z : Point n => hessGaussFactor i τ z * q 0) (collar R)ᶜ volume :=
    ((hessGaussFactor_integrable τ hτ i).mul_const (q 0)).integrableOn
  have hincr_int : IntegrableOn
      (fun z : Point n => hessGaussFactor i τ z * (q z - q 0)) (collar R)ᶜ volume :=
    (hessGaussIncrement_integrable τ hτ i q L hL hq hqmeas).integrableOn
  have hHq_int : IntegrableOn (fun z : Point n => hessGaussFactor i τ z * q z) (collar R)ᶜ volume :=
    (hincr_int.add hHq0_int).congr
      (ae_of_all _ (fun z => by
        show hessGaussFactor i τ z * (q z - q 0) + hessGaussFactor i τ z * q 0
            = hessGaussFactor i τ z * q z
        ring))
  have hcompDiff_int : IntegrableOn
      (fun z : Point n => Ichart z - hessGaussFactor i τ z * q z) (collar R)ᶜ volume :=
    hIchart_int.sub hHq_int
  -- the exact split
  have e1 : (∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * q z))
        + (∫ z in (collar R)ᶜ, hessGaussFactor i τ z * (q z - q 0))
      = ∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * q 0) := by
    rw [← integral_add hcompDiff_int hincr_int]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    ring
  have e2 : (∫ z in (collar R)ᶜ, Ichart z) - q 0 * tailMoment i τ R
      = ∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * q 0) := by
    rw [integral_sub hIchart_int hHq0_int, integral_mul_const, tailMoment]
    ring
  have hincr_le : ‖∫ z in (collar R)ᶜ, hessGaussFactor i τ z * (q z - q 0)‖
      ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ :=
    hessGaussIncrement_offCollar_norm_le τ hτ i q L hL hq hqmeas R
  rw [e2, ← e1]
  calc ‖(∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * q z))
          + (∫ z in (collar R)ᶜ, hessGaussFactor i τ z * (q z - q 0))‖
      ≤ ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * q z)‖
          + ‖∫ z in (collar R)ᶜ, hessGaussFactor i τ z * (q z - q 0)‖ := norm_add_le _ _
    _ ≤ Bcomp / Real.sqrt τ + L * (15 / 2 * (n : ℝ)) / Real.sqrt τ := add_le_add hcomp hincr_le
    _ = (Bcomp + L * (15 / 2 * (n : ℝ))) / Real.sqrt τ := by rw [add_div]

/-! ###############################################################################
    (O4) — ★ the cubic-contact gradient reconstruction (the honest carry made explicit).
    ############################################################################### -/

/-- **(O4) ★★★ `cubic_contact_gradient_bound`.**  THE CUBIC-CONTACT GRADIENT RECONSTRUCTION.
    The exact gradient of the radial defect `F(z) = r_z − r_{W z 0}` (with `W z 0 = −z + b(z)`) is
      `∇_z F = 2·b(z) + 2·(Db)ᵀz − 2·(Db)ᵀb(z)`
    (compute: `F = 2⟨z,b⟩ − ‖b‖²`).  Encoding the three terms as `2•b + 2•u + 2•w` with the
    displacement magnitude `‖b‖ ≤ C_W·‖z‖²` (banked, `chartW0_displacement`) and the two
    derivative-level contractions `‖u‖ ≤ C_E·‖z‖·‖z‖`, `‖w‖ ≤ C_E·‖z‖·‖b‖` (the HONEST CARRY
    `Db = O(‖z‖)` — see the O4 verdict in the header: base-side C¹ is NOT banked), the cubic contact
      `‖∇_z F‖ ≤ (2·C_W + 2·C_E + 2·C_E·C_W·r₀)·‖z‖²`
    follows on `‖z‖ ≤ r₀`.  Non-vacuous (constrains `grad`); satisfiable (e.g. `b=u=w=grad=0`).
    ⚠ NOT `a₁ = R/6`. -/
theorem cubic_contact_gradient_bound (z b u w grad : Point n) (C_W C_E r₀ : ℝ)
    (hCW : 0 ≤ C_W) (hCE : 0 ≤ C_E) (hr0 : 0 ≤ r₀) (hzr : ‖z‖ ≤ r₀)
    (hb : ‖b‖ ≤ C_W * ‖z‖ ^ 2) (hu : ‖u‖ ≤ C_E * ‖z‖ * ‖z‖) (hw : ‖w‖ ≤ C_E * ‖z‖ * ‖b‖)
    (hgrad : grad = (2 : ℝ) • b + (2 : ℝ) • u + (2 : ℝ) • w) :
    ‖grad‖ ≤ (2 * C_W + 2 * C_E + 2 * C_E * C_W * r₀) * ‖z‖ ^ 2 := by
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hcube3 : ‖z‖ ^ 3 ≤ r₀ * ‖z‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hzr (sq_nonneg ‖z‖)]
  have hw2 : ‖w‖ ≤ C_E * C_W * r₀ * ‖z‖ ^ 2 := by
    calc ‖w‖ ≤ C_E * ‖z‖ * ‖b‖ := hw
      _ ≤ C_E * ‖z‖ * (C_W * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hb (mul_nonneg hCE hzn)
      _ = C_E * C_W * ‖z‖ ^ 3 := by ring
      _ ≤ C_E * C_W * r₀ * ‖z‖ ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hcube3 (mul_nonneg hCE hCW)]
  have htri : ‖grad‖ ≤ 2 * ‖b‖ + 2 * ‖u‖ + 2 * ‖w‖ := by
    rw [hgrad]
    calc ‖(2 : ℝ) • b + (2 : ℝ) • u + (2 : ℝ) • w‖
        ≤ ‖(2 : ℝ) • b + (2 : ℝ) • u‖ + ‖(2 : ℝ) • w‖ := norm_add_le _ _
      _ ≤ ‖(2 : ℝ) • b‖ + ‖(2 : ℝ) • u‖ + ‖(2 : ℝ) • w‖ := by
          gcongr; exact norm_add_le _ _
      _ = 2 * ‖b‖ + 2 * ‖u‖ + 2 * ‖w‖ := by
          rw [norm_smul, norm_smul, norm_smul]; norm_num
  calc ‖grad‖ ≤ 2 * ‖b‖ + 2 * ‖u‖ + 2 * ‖w‖ := htri
    _ ≤ 2 * (C_W * ‖z‖ ^ 2) + 2 * (C_E * ‖z‖ * ‖z‖) + 2 * (C_E * C_W * r₀ * ‖z‖ ^ 2) := by
        gcongr
    _ = (2 * C_W + 2 * C_E + 2 * C_E * C_W * r₀) * ‖z‖ ^ 2 := by ring

end QIQTH.SliverOffCollarMatched

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SliverOffCollarMatched.abs_exp_sub_one_le
#print axioms QIQTH.SliverOffCollarMatched.gaussDdim_ratio
#print axioms QIQTH.SliverOffCollarMatched.exp_weight_gaussDdim'
#print axioms QIQTH.SliverOffCollarMatched.gaussDdim_chart_comparison
#print axioms QIQTH.SliverOffCollarMatched.chartGauss_comparison_concrete
#print axioms QIQTH.SliverOffCollarMatched.chartNative_leading_sub_hess
#print axioms QIQTH.SliverOffCollarMatched.chartNative_leading_sub_hess_norm_le
#print axioms QIQTH.SliverOffCollarMatched.hessGaussIncrement_offCollar_norm_le
#print axioms QIQTH.SliverOffCollarMatched.sliver_term1_off_collar_matched
#print axioms QIQTH.SliverOffCollarMatched.cubic_contact_gradient_bound
