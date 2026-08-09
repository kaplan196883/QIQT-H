/-
  WeightedPairingHelper — J4-451 (the SOL #21 INTEGRAL-LEVEL re-grounding of the a₁ = R/6 census
  `hProfRate`): replacing the RETRACTED pointwise chain `{hDHrefined, hLeviCap}` (J4-449/450) by the
  banked two-Gaussian product-to-single pairing, done UNDER THE INTEGRAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J4-450 RETRACTION (context).  `hLeviCap` — a TRUE `s,z`-uniform CONSTANT Levi cap — is
  UNSATISFIABLE for general `n` (on-diagonal `leviSeries s 0 0 ~ O(s^{N−n/2})` with the fixed witness
  `N = 1` DIVERGES for `n ≥ 3`).  Consequently `hProdPtwise` (the SINGLE-Gaussian POINTWISE product-
  moment domination) is itself unsound at `n ≥ 3` (the two-Gaussian product `G_{wA(u−s)}·G_{wF s}` does
  NOT collapse `s`-uniformly to one `G_{w(u−s)}`).  The J4-447..449 POINTWISE grounding chain is
  RETRACTED for general `n`; the `√τ` moment gain must be taken UNDER THE INTEGRAL.

  ## SOL #21 — THE INTEGRAL-LEVEL RE-GROUNDING (CONFIRMED with one centering condition).
  The weighted two-Gaussian pairing:
    · PRODUCT-TO-SINGLE:  `G_a(z−x)·G_b(z−y) = G_{a+b}(x−y)·G_h(z−c)`,  `h = ab/(a+b)`,
      `c = (b·x + a·y)/(a+b)` the weighted mean (the completed square).
    · THE HELPER:  `∫z |(z−x)_i|·G_a(z−x)·G_b(z−y) ≤ G_{a+b}(x−y)·(κ·√(ab/(a+b)) + (a/(a+b))·|(y−x)_i|)`,
      `κ = 3/2` (banked `absCoord_gaussDdim_integral_le`); via the coordinate triangle around `c`,
      translation invariance, and Gaussian mass one.
    · THE COUNT:  `a := wA(u−s)`, `b := wF·s` ⟹ `a+b = wA(u−s)+wF·s ≥ u·min(wA,wF) > 0` BOUNDED
      (the `s→0` danger absorbed by the integrated pairing); `√h ≤ √a = √wA·√(u−s)` ⟹ the
      `Q·(u−s)^{−1/2}` rate, `m`-free.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ★★★ THE CENTERING GATE (Sol #21's binding audit).

  THE TRAP.  The moment must be `|z_i − x_i|` RELATIVE TO the `dH`-Gaussian's OWN center `x`; a raw
  fixed-coordinate `|z_i|` paired with an OFF-center `G_a` (center `x ≠ 0`) yields `O((u−s)^{−1})` as
  `s ↑ u` — unacceptable; adding `|x_i| ≤ diam` does NOT close it.

  THE VERDICT — the trap is VOID for THIS census.  Audit of the standing carries:
    · `hDHrefined` supplies `|witnessFieldDeriv i (u−s) x z| ≤ CA/(2(u−s))·(|z_i|·gaussDdim (wA(u−s)) z)`
      — the field-derivative Gaussian is `gaussDdim (wA(u−s)) z`, CENTERED AT `0` (argument `z`, not
      `z − x`), and its moment is `|z_i| = |z_i − 0|`, RELATIVE TO that same center `0`.  ✔ the moment
      IS relative to the `dH`-Gaussian's own center.
    · `hFdomEvery` supplies `|leviSeries s z 0| ≤ CF·gaussDdim (wF·s) z` — the Levi Gaussian is also
      CENTERED AT `0`.
  Hence in the helper the two centers coincide (`x = y = 0`), the weighted mean `c = 0`, and the
  cross-term `(a/(a+b))·|(y−x)_i| = 0` VANISHES: NO corrected centered shape `hDHrefined'` is needed.
  The re-grounding rests on the STANDING centered carries `{hDHrefined, hFdomEvery}` (both already in
  the census) PLUS product measurability — the RETRACTED atoms `{hLeviCap, hProdPtwise, hProdMoment}`
  are GONE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.WeightedPairingHelper`).
    • `heatKernel1D_prod_to_single` — ★ the 1-D completed-square product-to-single identity.
    • `gaussDdim_prod_to_single`    — ★ the `n`-D product-to-single identity (coordinate-wise lift).
    • `gaussDdim_sq_pairing`        — the equal-center (`x = y`) specialization `G_a·G_b = G_{a+b}(0)·G_h`.
    • `weighted_pairing_helper`     — ★★ THE Sol #21 helper (general centers, with the cross term).
    • `pairing_moment_zero`         — the centered moment `∫|z_i|·G_a·G_b ≤ G_{a+b}(0)·(3/2)√h`.
    • `profRate_inner_bound`        — ★ the abstract lever: two centered envelopes ⟹ `Q·τ^{−1/2}`.
    • `profRate_integral`           — ★★ the EXACT census `hProfRate` shape, re-grounded on
      `{hDHrefined, hFdomEvery, hProdMeas}` (the retracted pointwise atoms GONE).
    • `hGint_regrounded`            — ★★ the census `hGint`, `hProfRate` re-grounded.
    • `perUCensus_phase8`           — ★★★ the fired per-`u` census, `hProfRate` re-grounded.

  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED Gaussian pairing/moment machinery + the two
  STANDING centered census envelopes into the exact census `hProfRate`/`hGint` shapes.  NONE proves
  `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, strictly lower-level than
  the conclusion, and never the conclusion.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no existing file edited.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio +
  geometric-wiring stack AND on the surviving enumerated carries.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ProdPtwiseWitness
import QIQTH.ProfRateTheorem
import QIQTH.CConvV2GaussianPairing
import QIQTH.GaussianConvolution

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.WeightedPairingHelper

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `heatKernel1D_prod_to_single` — the 1-D completed-square identity.
    ############################################################################### -/

/-- **★ `heatKernel1D_prod_to_single` — THE 1-D PRODUCT-TO-SINGLE (completed square).**
    `G_a(z−x)·G_b(z−y) = G_{a+b}(x−y)·G_h(z−c)` for the 1-D flat kernel, `h = ab/(a+b)`,
    `c = (b·x+a·y)/(a+b)`.  Prefactors combine (`√(4πa)·√(4πb) = √(4π(a+b))·√(4πh)` since
    `(a+b)h = ab`) and the exponents complete the square.  ⚠ NOT `a₁ = R/6`. -/
theorem heatKernel1D_prod_to_single (a b x y z : ℝ) (ha : 0 < a) (hb : 0 < b) :
    heatKernel1D a (z - x) * heatKernel1D b (z - y)
      = heatKernel1D (a + b) (x - y)
        * heatKernel1D (a * b / (a + b)) (z - (b * x + a * y) / (a + b)) := by
  have hab : 0 < a + b := by linarith
  have hane : a ≠ 0 := ha.ne'
  have hbne : b ≠ 0 := hb.ne'
  have habne : a + b ≠ 0 := hab.ne'
  have hpre : (Real.sqrt (4 * Real.pi * a))⁻¹ * (Real.sqrt (4 * Real.pi * b))⁻¹
      = (Real.sqrt (4 * Real.pi * (a + b)))⁻¹ * (Real.sqrt (4 * Real.pi * (a * b / (a + b))))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(z - x) ^ 2 / (4 * a) + -(z - y) ^ 2 / (4 * b)
      = -(x - y) ^ 2 / (4 * (a + b))
        + -(z - (b * x + a * y) / (a + b)) ^ 2 / (4 * (a * b / (a + b))) := by
    field_simp
    ring
  simp only [heatKernel1D]
  rw [show (Real.sqrt (4 * Real.pi * a))⁻¹ * Real.exp (-(z - x) ^ 2 / (4 * a))
        * ((Real.sqrt (4 * Real.pi * b))⁻¹ * Real.exp (-(z - y) ^ 2 / (4 * b)))
      = ((Real.sqrt (4 * Real.pi * a))⁻¹ * (Real.sqrt (4 * Real.pi * b))⁻¹)
          * (Real.exp (-(z - x) ^ 2 / (4 * a)) * Real.exp (-(z - y) ^ 2 / (4 * b))) from by ring]
  rw [← Real.exp_add, hexp, Real.exp_add, hpre]
  ring

/-! ###############################################################################
    ### ★ `gaussDdim_prod_to_single` — the `n`-D product-to-single identity.
    ############################################################################### -/

/-- **★ `gaussDdim_prod_to_single` — THE `n`-D PRODUCT-TO-SINGLE.**  Coordinate-wise lift of the 1-D
    completed square: `G_a(z−x)·G_b(z−y) = G_{a+b}(x−y)·G_h(z−c)` on `Point n`, `h = ab/(a+b)`, `c`
    the weighted mean `k ↦ (b·x_k+a·y_k)/(a+b)`.  Each `Fin n` factor is closed by
    `heatKernel1D_prod_to_single`.  ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_prod_to_single (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x y z : Point n) :
    gaussDdim a (z - x) * gaussDdim b (z - y)
      = gaussDdim (a + b) (x - y)
        * gaussDdim (a * b / (a + b)) (z - fun k => (b * x k + a * y k) / (a + b)) := by
  simp only [gaussDdim]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [Pi.sub_apply]
  exact heatKernel1D_prod_to_single a b (x k) (y k) (z k) ha hb

/-- **`gaussDdim_sq_pairing` — the equal-center (`x = y = 0`) specialization.**
    `G_a(z)·G_b(z) = G_{a+b}(0)·G_h(z)`, `h = ab/(a+b)` (the pointwise core of
    `gaussDdim_pairing_integral`).  ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_sq_pairing (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : Point n) :
    gaussDdim a z * gaussDdim b z
      = gaussDdim (a + b) (0 : Point n) * gaussDdim (a * b / (a + b)) z := by
  simp only [gaussDdim]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have hk := heatKernel1D_prod_to_single a b 0 0 (z k) ha hb
  simp only [sub_zero, mul_zero, add_zero, zero_div, Pi.zero_apply] at hk ⊢
  exact hk

/-! ###############################################################################
    ### ★★ `weighted_pairing_helper` — the Sol #21 helper (general centers).
    ############################################################################### -/

/-- **★★ `weighted_pairing_helper` — THE SOL #21 HELPER.**  For `a, b > 0`, centers `x, y : Point n`
    and coordinate `i`,
      `∫z |z_i − x_i|·(G_a(z−x)·G_b(z−y)) ≤ G_{a+b}(x−y)·((3/2)·√(ab/(a+b)) + (a/(a+b))·|y_i − x_i|)`.
    Route: the product-to-single identity `gaussDdim_prod_to_single` pulls out the `z`-independent
    factor `G_{a+b}(x−y)` and leaves `G_h(z−c)`, `c` the weighted mean; the coordinate triangle
    `|z_i − x_i| ≤ |z_i − c_i| + |c_i − x_i|` with `c_i − x_i = (a/(a+b))(y_i − x_i)`; translation
    invariance (`integral_sub_right_eq_self`) turns `∫|z_i − c_i|·G_h(z−c)` into `∫|w_i|·G_h(w) ≤
    (3/2)√h` (`absCoord_gaussDdim_integral_le`) and `∫G_h(z−c)` into mass one
    (`gaussDdim_integral_eq_one`).  ⚠ NOT `a₁ = R/6`. -/
theorem weighted_pairing_helper (i : Fin n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x y : Point n) :
    (∫ z : Point n, |z i - x i| * (gaussDdim a (z - x) * gaussDdim b (z - y)))
      ≤ gaussDdim (a + b) (x - y)
          * (3 / 2 * Real.sqrt (a * b / (a + b)) + a / (a + b) * |y i - x i|) := by
  have hab : 0 < a + b := by linarith
  have hh : 0 < a * b / (a + b) := by positivity
  set c : Point n := fun k => (b * x k + a * y k) / (a + b) with hc_def
  set h : ℝ := a * b / (a + b) with hh_def
  -- the center coordinate: c_i − x_i = (a/(a+b))·(y_i − x_i)
  have hci : c i - x i = a / (a + b) * (y i - x i) := by
    simp only [hc_def]
    field_simp
    ring
  -- integrand pointwise identity: pull out G_{a+b}(x−y)
  have hrw : ∀ z : Point n, |z i - x i| * (gaussDdim a (z - x) * gaussDdim b (z - y))
      = gaussDdim (a + b) (x - y) * (|z i - x i| * gaussDdim h (z - c)) := by
    intro z
    rw [gaussDdim_prod_to_single a b ha hb x y z, ← hc_def, ← hh_def]
    ring
  -- the shifted moment / mass integrands (translations of banked integrable functions)
  have hInt1 : Integrable (fun z : Point n => |z i - c i| * gaussDdim h (z - c)) volume := by
    have hb0 := (QIQTH.HeatResidualBound.absCoord_gaussDdim_integrable h hh i).comp_sub_right c
    refine hb0.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Pi.sub_apply]
  have hInt2 : Integrable (fun z : Point n => gaussDdim h (z - c)) volume :=
    (QIQTH.HeatResidualBound.gaussDdim_integrable h hh).comp_sub_right c
  -- ∫ |z_i − c_i|·G_h(z−c) = ∫ |w_i|·G_h(w) ≤ (3/2)√h
  have hmom : (∫ z : Point n, |z i - c i| * gaussDdim h (z - c)) ≤ 3 / 2 * Real.sqrt h := by
    have htr : (∫ z : Point n, |z i - c i| * gaussDdim h (z - c))
        = ∫ z : Point n, |z i| * gaussDdim h z := by
      have := integral_sub_right_eq_self (μ := (volume : Measure (Point n)))
        (fun z : Point n => |z i| * gaussDdim h z) c
      simpa only [Pi.sub_apply] using this
    rw [htr]
    exact QIQTH.HeatResidualBound.absCoord_gaussDdim_integral_le h hh i
  -- ∫ G_h(z−c) = 1
  have hmass : (∫ z : Point n, gaussDdim h (z - c)) = 1 := by
    have := integral_sub_right_eq_self (μ := (volume : Measure (Point n)))
      (fun z : Point n => gaussDdim h z) c
    rw [this]
    exact QIQTH.HeatResidualBound.gaussDdim_integral_eq_one h hh
  -- bound the inner moment integral
  have hInner : (∫ z : Point n, |z i - x i| * gaussDdim h (z - c))
      ≤ 3 / 2 * Real.sqrt h + a / (a + b) * |y i - x i| := by
    have hg_int : Integrable (fun z : Point n =>
        |z i - c i| * gaussDdim h (z - c)
          + a / (a + b) * |y i - x i| * gaussDdim h (z - c)) volume :=
      hInt1.add (hInt2.const_mul (a / (a + b) * |y i - x i|))
    have hle : (∫ z : Point n, |z i - x i| * gaussDdim h (z - c))
        ≤ ∫ z : Point n, |z i - c i| * gaussDdim h (z - c)
            + a / (a + b) * |y i - x i| * gaussDdim h (z - c) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_)) hg_int
        (Filter.Eventually.of_forall (fun z => ?_))
      · exact mul_nonneg (abs_nonneg _) (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
      · have hgnn : 0 ≤ gaussDdim h (z - c) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
        have htri : |z i - x i| ≤ |z i - c i| + a / (a + b) * |y i - x i| := by
          have : z i - x i = (z i - c i) + (c i - x i) := by ring
          rw [this, hci]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_div]
          have : |a| / |a + b| = a / (a + b) := by
            rw [abs_of_pos ha, abs_of_pos hab]
          rw [this]
        calc |z i - x i| * gaussDdim h (z - c)
            ≤ (|z i - c i| + a / (a + b) * |y i - x i|) * gaussDdim h (z - c) :=
              mul_le_mul_of_nonneg_right htri hgnn
          _ = |z i - c i| * gaussDdim h (z - c)
              + a / (a + b) * |y i - x i| * gaussDdim h (z - c) := by ring
    calc (∫ z : Point n, |z i - x i| * gaussDdim h (z - c))
        ≤ ∫ z : Point n, |z i - c i| * gaussDdim h (z - c)
            + a / (a + b) * |y i - x i| * gaussDdim h (z - c) := hle
      _ = (∫ z : Point n, |z i - c i| * gaussDdim h (z - c))
            + ∫ z : Point n, a / (a + b) * |y i - x i| * gaussDdim h (z - c) :=
          integral_add hInt1 (hInt2.const_mul _)
      _ = (∫ z : Point n, |z i - c i| * gaussDdim h (z - c))
            + a / (a + b) * |y i - x i| * ∫ z : Point n, gaussDdim h (z - c) := by
          rw [integral_const_mul]
      _ ≤ 3 / 2 * Real.sqrt h + a / (a + b) * |y i - x i| := by
          rw [hmass, mul_one]
          exact add_le_add hmom le_rfl
  -- assemble: ∫ original = G_{a+b}(x−y) · inner ≤ G_{a+b}(x−y) · bound
  rw [show (fun z : Point n => |z i - x i| * (gaussDdim a (z - x) * gaussDdim b (z - y)))
      = fun z => gaussDdim (a + b) (x - y) * (|z i - x i| * gaussDdim h (z - c)) from funext hrw]
  rw [integral_const_mul, hh_def]
  exact mul_le_mul_of_nonneg_left hInner (QIQTH.ResidueBound.gaussDdim_nonneg _ _)

/-- **`pairing_moment_zero` — the CENTERED moment bound (the `x = y = 0` corollary).**
    `∫z |z_i|·(G_a(z)·G_b(z)) ≤ G_{a+b}(0)·(3/2)·√(ab/(a+b))` — the cross term vanishes because both
    Gaussians are centered at `0` (the census centering; see the CENTERING GATE).  ⚠ NOT `a₁ = R/6`. -/
theorem pairing_moment_zero (i : Fin n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ z : Point n, |z i| * (gaussDdim a z * gaussDdim b z))
      ≤ gaussDdim (a + b) (0 : Point n) * (3 / 2 * Real.sqrt (a * b / (a + b))) := by
  have hh : 0 < a * b / (a + b) := by positivity
  rw [show (fun z : Point n => |z i| * (gaussDdim a z * gaussDdim b z))
      = fun z => gaussDdim (a + b) (0 : Point n) * (|z i| * gaussDdim (a * b / (a + b)) z) from
    funext (fun z => by rw [gaussDdim_sq_pairing a b ha hb z]; ring)]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (QIQTH.HeatResidualBound.absCoord_gaussDdim_integral_le _ hh i)
    (QIQTH.ResidueBound.gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### ★ `profRate_inner_bound` — the abstract two-envelope lever ⟹ `Q·τ^{−1/2}`.
    ############################################################################### -/

/-- **★ `profRate_inner_bound` — THE ABSTRACT LEVER (two centered envelopes ⟹ the `τ^{−1/2}` rate).**
    For `τ = u − s`, `0 < s < u`, widths `wA, wF > 0`, amplitudes `CA, CF ≥ 0`, two integrands
    `dH Lev : Point n → ℝ` with product `AEStronglyMeasurable` (`hmeas`), the a.e. CENTERED
    slope-moment envelope `|dH z| ≤ CA/(2τ)·(|z_i|·G_{wA·τ}(z))` (`hdH`) and the pointwise CENTERED
    Levi Gaussian envelope `|Lev z| ≤ CF·G_{wF·s}(z)` (`hLev`), the absolute product integral obeys
      `|∫z dH·Lev| ≤ (3·CA·CF·G_{min(wA,wF)·u}(0)·√wA/4)·τ^{−1/2}`.
    Route: dominate `‖dH·Lev‖` by `CA·CF/(2τ)·|z_i|·G_{wA τ}·G_{wF s}`, integrate via the centered
    pairing `pairing_moment_zero` (`≤ G_{a+b}(0)·(3/2)√h`), bound `G_{a+b}(0) ≤ G_{min·u}(0)`
    (antitone, `min(wA,wF)·u ≤ a+b`) and `√h ≤ √(wA τ) = √wA·√τ`, then `τ⁻¹·√τ = τ^{−1/2}`.  m-FREE.
    ⚠ NOT `a₁ = R/6`. -/
theorem profRate_inner_bound (i : Fin n) (u s wA CA wF CF : ℝ)
    (hs0 : 0 < s) (hsu : s < u) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (dH Lev : Point n → ℝ)
    (hmeas : AEStronglyMeasurable (fun z => dH z * Lev z) volume)
    (hdH : ∀ᵐ z ∂(volume : Measure (Point n)),
      |dH z| ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hLev : ∀ z : Point n, |Lev z| ≤ CF * gaussDdim (wF * s) z) :
    |∫ z, dH z * Lev z|
      ≤ (3 * (CA * CF) * gaussDdim (min wA wF * u) (0 : Point n) * Real.sqrt wA / 4)
          * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hτ : 0 < u - s := by linarith
  have hu : 0 < u := by linarith
  set τ : ℝ := u - s with hτ_def
  set a : ℝ := wA * τ with ha_def
  set bb : ℝ := wF * s with hbb_def
  have ha : 0 < a := mul_pos hwA hτ
  have hbb : 0 < bb := mul_pos hwF hs0
  have hab : 0 < a + bb := by linarith
  set K : ℝ := gaussDdim (min wA wF * u) (0 : Point n) with hK_def
  have hKnn : 0 ≤ K := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  -- the dominator
  set D : ℝ → Point n → ℝ := fun _ z =>
    CA * CF / (2 * τ) * (|z i| * (gaussDdim a z * gaussDdim bb z)) with hD_def
  -- a.e. domination ‖dH·Lev‖ ≤ D
  have hdom : ∀ᵐ z ∂(volume : Measure (Point n)),
      ‖dH z * Lev z‖ ≤ CA * CF / (2 * τ) * (|z i| * (gaussDdim a z * gaussDdim bb z)) := by
    filter_upwards [hdH] with z h1
    have h2 := hLev z
    rw [Real.norm_eq_abs, abs_mul]
    calc |dH z| * |Lev z|
        ≤ (CA / (2 * τ) * (|z i| * gaussDdim a z)) * (CF * gaussDdim bb z) :=
          mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
      _ = CA * CF / (2 * τ) * (|z i| * (gaussDdim a z * gaussDdim bb z)) := by ring
  -- the dominator is integrable
  have hDint : Integrable
      (fun z : Point n => CA * CF / (2 * τ) * (|z i| * (gaussDdim a z * gaussDdim bb z)))
      volume := by
    have hpt : (fun z : Point n => CA * CF / (2 * τ) * (|z i| * (gaussDdim a z * gaussDdim bb z)))
        = fun z => (CA * CF / (2 * τ) * gaussDdim (a + bb) (0 : Point n))
            * (|z i| * gaussDdim (a * bb / (a + bb)) z) := by
      funext z; rw [gaussDdim_sq_pairing a bb ha hbb z]; ring
    rw [hpt]
    exact (QIQTH.HeatResidualBound.absCoord_gaussDdim_integrable (a * bb / (a + bb))
      (by positivity) i).const_mul _
  -- integrability of the product
  have hfint : Integrable (fun z : Point n => dH z * Lev z) volume :=
    hDint.mono' hmeas hdom
  -- ∫ D ≤ the target
  have hQ : CA * CF / (2 * τ) * (∫ z : Point n, |z i| * (gaussDdim a z * gaussDdim bb z))
      ≤ (3 * (CA * CF) * K * Real.sqrt wA / 4) * τ ^ (-(1 : ℝ) / 2) := by
    have hc0 : 0 ≤ CA * CF / (2 * τ) := by positivity
    have hpm := pairing_moment_zero i a bb ha hbb
    -- G_{a+bb}(0) ≤ K
    have hGle : gaussDdim (a + bb) (0 : Point n) ≤ K := by
      rw [hK_def]
      refine QIQTH.CConvV2GaussianPairing.gaussDdim_zero_antitone (min wA wF * u) (a + bb) ?_ ?_
      · exact mul_pos (lt_min hwA hwF) hu
      · have h1 : min wA wF * τ ≤ a := by
          rw [ha_def]; exact mul_le_mul_of_nonneg_right (min_le_left _ _) hτ.le
        have h2 : min wA wF * s ≤ bb := by
          rw [hbb_def]; exact mul_le_mul_of_nonneg_right (min_le_right _ _) hs0.le
        have hus : u = τ + s := by rw [hτ_def]; ring
        nlinarith [h1, h2]
    -- √h ≤ √a = √wA·√τ
    have hsqrt : Real.sqrt (a * bb / (a + bb)) ≤ Real.sqrt wA * Real.sqrt τ := by
      have hha : a * bb / (a + bb) ≤ a := by
        rw [div_le_iff₀ hab]; nlinarith [ha, hbb]
      calc Real.sqrt (a * bb / (a + bb)) ≤ Real.sqrt a := Real.sqrt_le_sqrt hha
        _ = Real.sqrt wA * Real.sqrt τ := by rw [ha_def, Real.sqrt_mul hwA.le]
    -- chain
    have hstep : gaussDdim (a + bb) (0 : Point n) * (3 / 2 * Real.sqrt (a * bb / (a + bb)))
        ≤ K * (3 / 2 * (Real.sqrt wA * Real.sqrt τ)) := by
      apply mul_le_mul hGle _ _ hKnn
      · exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    calc CA * CF / (2 * τ) * (∫ z : Point n, |z i| * (gaussDdim a z * gaussDdim bb z))
        ≤ CA * CF / (2 * τ)
            * (gaussDdim (a + bb) (0 : Point n) * (3 / 2 * Real.sqrt (a * bb / (a + bb)))) :=
          mul_le_mul_of_nonneg_left hpm hc0
      _ ≤ CA * CF / (2 * τ) * (K * (3 / 2 * (Real.sqrt wA * Real.sqrt τ))) :=
          mul_le_mul_of_nonneg_left hstep hc0
      _ = (3 * (CA * CF) * K * Real.sqrt wA / 4) * τ ^ (-(1 : ℝ) / 2) := by
          rw [← QIQTH.HeatResidualBound.inv_sqrt_eq_rpow τ hτ]
          have h2τ : (2 : ℝ) * τ = 2 * (Real.sqrt τ * Real.sqrt τ) := by
            rw [Real.mul_self_sqrt hτ.le]
          have hτs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
          rw [h2τ]; field_simp; ring
  -- assemble via the banked dominated-integral bound
  have hbound := QIQTH.GpowClosure.abs_integral_le_of_dom (fun z => dH z * Lev z)
    (fun z => CA * CF / (2 * τ) * (|z i| * (gaussDdim a z * gaussDdim bb z)))
    ((3 * (CA * CF) * K * Real.sqrt wA / 4) * τ ^ (-(1 : ℝ) / 2)) hfint hDint hdom ?_
  · exact hbound
  · rw [integral_const_mul]; exact hQ

/-! ###############################################################################
    ### ★★ `profRate_integral` — the EXACT census hProfRate shape, re-grounded.
    ############################################################################### -/

/-- **★★ `profRate_integral` — THE `hProfRate` CARRY, RE-GROUNDED (Sol #21).**  The EXACT `hProfRate`
    binder consumed by `ProfFacWitness.hGint_grounded` / `perUCensus_phase4` (identical shape to
    `ProfRateTheorem.profRate_theorem`'s conclusion): per `(u,i,x)`, a `Q ≥ 0` with the moment-gained
    inner rate `|∫z witnessFieldDeriv i (u−s) x z · leviSeries s z 0| ≤ Q·(u−s)^{−1/2}` on `0 < s < u`.
    Supplied from the STANDING centered census carries — the refined field-derivative envelope
    `hDHrefined` and the every-ceiling Levi Gaussian envelope `hFdomEvery` (Tc := u) — plus product
    measurability `hProdMeas`, fed through `profRate_inner_bound`.  The RETRACTED atoms
    `{hProdMoment, hProdPtwise, hLeviCap}` are GONE.  `Q := 3·CA·CF·G_{min(wA,wF)·u}(0)·√wA/4`.  m-FREE.
    ⚠ NOT `a₁ = R/6`. -/
theorem profRate_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hDHrefined : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ Q : ℝ, 0 ≤ Q ∧
        ∀ s, 0 < s → s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ Q * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro u hu i x
  obtain ⟨wA, CA, hwA, hCA, hdH⟩ := hDHrefined u hu i x
  obtain ⟨wF, CF, hwF, hCF, hLev⟩ := hFdomEvery u
  refine ⟨3 * (CA * CF) * gaussDdim (min wA wF * u) (0 : Point n) * Real.sqrt wA / 4, ?_, ?_⟩
  · have hKnn : 0 ≤ gaussDdim (min wA wF * u) (0 : Point n) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCA hCF)) hKnn)
      (Real.sqrt_nonneg _)
  · intro s hs0 hsu
    refine profRate_inner_bound i u s wA CA wF CF hs0 hsu hwA hCA hwF hCF _ _
      (hProdMeas u hu i x s hs0 hsu) (hdH s hs0 hsu) (fun z => hLev s hs0 hsu.le z)

/-! ###############################################################################
    ### ★★ `hGint_regrounded` — the census hGint, hProfRate re-grounded.
    ############################################################################### -/

/-- **★★ `hGint_regrounded` — THE CENSUS `hGint`, `hProfRate` RE-GROUNDED (Sol #21).**  The EXACT
    `hGint` conclusion of `ProfFacWitness.hGint_grounded`, with the last substantive sliver carry
    `hProfRate` supplied by `profRate_integral` (the INTEGRAL-level pairing on the STANDING centered
    carries `{hDHrefined, hFdomEvery, hProdMeas}`) instead of the RETRACTED pointwise
    `{hProdMoment, hProdPtwise, hLeviCap}`.  Every OTHER carry is threaded exactly as `hGint_grounded`.
    Honest carries: {`hFzero`, `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hWFDjoint`, `hLeviJoint`,
    `hDHrefined`, `hProdMeas`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_regrounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hDHrefined : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.ProfFacWitness.hGint_grounded g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery
    hGintMeas hWFDjoint hLeviJoint
    (profRate_integral g gi hC hK S a b U hDHrefined hFdomEvery hProdMeas)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase8` — the fired per-`u` census, hProfRate re-grounded.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase8`.**  `ProfFacWitness.perUCensus_phase4` with the last substantive sliver
    carry `hProfRate` supplied by `profRate_integral` — the Sol #21 INTEGRAL-level re-grounding on the
    STANDING centered carries `{hDHrefined, hFdomEvery, hProdMeas}` (the RETRACTED pointwise
    `{hProdMoment, hProdPtwise, hLeviCap}` GONE).  Every OTHER census field is threaded exactly as
    `perUCensus_phase4`.  Pure composition; each carry satisfiable, non-vacuous, strictly lower-level
    than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase8 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hWFDjoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (u - p.1) x p.2)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((volume.restrict (Set.uIoc (u - epsSeq m) u)).prod (volume : Measure (Point n))))
    (hDHrefined : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ CA / (2 * (u - s)) * (|z i| * gaussDdim (wA * (u - s)) z))
    (hProdMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.ProfFacWitness.perUCensus_phase4 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint
    (profRate_integral g gi hC hK S a b U hDHrefined hFdomEvery hProdMeas)
    hbulkderiv hsliver hcont hQ1

end QIQTH.WeightedPairingHelper

/-! ## THE RE-GROUNDING LEDGER — the `hGint`/`hProfRate` surface after J4-451.

  ── ★★★ THE CENTERING GATE (binding).  The Sol #21 trap ("the moment must be `|z_i − x_i|` relative to
  the `dH`-Gaussian's OWN center; a raw `|z_i|` with off-center `G_a` gives `O((u−s)^{−1})` as `s ↑ u`")
  is VOID for this census: BOTH standing envelopes are CENTERED AT `0` —
    · `hDHrefined` : `|dH i (u−s) x z| ≤ CA/(2(u−s))·(|z_i|·gaussDdim (wA(u−s)) z)` — Gaussian arg `z`,
      moment `|z_i| = |z_i − 0|`, both centered at `0`;
    · `hFdomEvery` : `|leviSeries s z 0| ≤ CF·gaussDdim (wF·s) z` — Gaussian arg `z`, centered at `0`.
  Hence the weighted mean `c = 0`, the cross term `(a/(a+b))·|(y−x)_i| = 0`, and NO corrected shape
  `hDHrefined'` is needed.  The general `weighted_pairing_helper` carries the cross term for
  completeness/reuse, but `profRate_integral` uses only the `x = y = 0` corollary `pairing_moment_zero`.

  ── THE RE-GROUNDING (what replaces the RETRACTED pointwise chain).

    RETRACTED (J4-449/450)            →   RE-GROUNDED (J4-451, integral-level)
    ───────────────────────────────      ─────────────────────────────────────────────────────────
    `hLeviCap` (const Levi cap)       →   GONE — never used; `hFdomEvery` Gaussian used UNDER the ∫.
    `hProdPtwise` (single-Gaussian    →   GONE — the two-Gaussian product is NEVER collapsed pointwise;
       pointwise product-moment)           it is paired UNDER the integral by `pairing_moment_zero`
                                           (`gaussDdim_sq_pairing` + `absCoord_gaussDdim_integral_le`).
    `hProdMoment` (bundled)           →   GONE — replaced by `{hDHrefined, hFdomEvery, hProdMeas}`.

  ── AFTER J4-451, the `hGint`/`hProfRate` sub-chain rests on ONLY:

    supplier carry     role                                          provenance / satisfiability
    ────────────────   ──────────────────────────────────────────   ─────────────────────────────────
    `hFzero`           Levi-source vanishing (`s ≤ 0 ⟹ F = 0`)      banked `hFzero_concrete` shape
    `hWFDdomCapped`    CAPPED field-derivative Gaussian domination   banked bulk engine (`εₘ ≤ τ`)
    `hFdomEvery`       every-ceiling Levi Gaussian envelope          banked F2-style Levi domination —
                       `|Lev s z 0| ≤ CF·G_{wF s}(z)`, CENTERED 0    NOW ALSO the `hProfRate` supplier
    `hGintMeas`        `s`-profile aesm on the BULK window            banked Fubini (`hF'meas_concrete`)
    `hWFDjoint`        `(s,z)` witnessFieldDeriv joint aesm, SLIVER   banked joint-meas (`hWFDjointY`)
    `hLeviJoint`       `(s,z)` Levi joint aesm, SLIVER window         banked joint-meas (`hLeviJoint`)
    `hDHrefined`       ★ refined field-deriv slope-moment envelope    parametrix-pd `z_i/(2(u−s))·G`
                       `|dH| ≤ CA/(2(u−s))·(|z_i|·G_{wA(u−s)})`,      slope (J4-443 chain rule);
                       CENTERED at 0                                  refined tier of `hWFDdomCapped`
    `hProdMeas`        per-`s` product `AEStronglyMeasurable`         standing joint-measurability family

  ── THE INTEGRAL-LEVEL ENGINE (fully PROVED in this brick, no new carry).
    • `heatKernel1D_prod_to_single` / `gaussDdim_prod_to_single` — the completed-square product-to-
      single identity `G_a(z−x)·G_b(z−y) = G_{a+b}(x−y)·G_h(z−c)` (`h = ab/(a+b)`, `c` the weighted
      mean), coordinate-wise from the 1-D exp algebra.  PROVED, std-3.
    • `weighted_pairing_helper` — the Sol #21 inequality (general centers, with cross term), PROVED via
      the identity + coordinate triangle around `c` + translation invariance + banked moment/mass.
    • `pairing_moment_zero` — the centered corollary `∫|z_i|·G_a·G_b ≤ G_{a+b}(0)·(3/2)√h`.
    • `profRate_inner_bound` — the abstract lever: dominate `‖dH·Lev‖` by `CA·CF/(2τ)·|z_i|·G_a·G_b`,
      integrate by the centered pairing, bound `G_{a+b}(0) ≤ G_{min(wA,wF)·u}(0)` (antitone,
      `a+b ≥ min·u`) and `√h ≤ √(wA τ)`, count `τ⁻¹·√τ = τ^{−1/2}`.  m-FREE, `Q` s-uniform.
    • `profRate_integral` — the EXACT census `hProfRate` shape, re-grounded on the standing carries.

  ── DONT-UNDERCREDIT FINDINGS.
    • The two-Gaussian product-to-single at the INTEGRAL level was already partly banked
      (`CConvV2GaussianPairing.gaussDdim_pairing_integral` : `∫ G_a·G_b = G_{a+b}(0)`, from the banked
      convolution semigroup `GaussianConvolution.gaussDdim_conv`).  This brick adds the POINTWISE
      identity (with the `z`-dependent `G_h(z−c)` factor and general centers) needed to carry the
      `|z_i|`-moment, re-using the SAME completed-square algebra as `heatKernel1D_conv`.
    • The `√τ` gain is the banked `absCoord_gaussDdim_integral_le` (`∫|z_i|·G_{wτ} ≤ (3/2)√(wτ)`) and
      the count `τ⁻¹·√τ = τ^{−1/2}` the banked `inv_sqrt_eq_rpow`; the dominated-integral assembly is
      the banked `GpowClosure.abs_integral_le_of_dom`.  The lever needed only their assembly with the
      new pairing identity — no new moment analysis.
    • The `s`-uniform lower bound `a+b = wA(u−s)+wF·s ≥ min(wA,wF)·u` (the exact `abLower` shape) makes
      `G_{a+b}(0)` bounded `s`-uniformly by `G_{min(wA,wF)·u}(0)` (antitone) — this is what absorbs the
      `s→0` peak-divergence that KILLED the pointwise route, precisely because it is taken UNDER the ∫.

  ⚠  J4-451 = census `hProfRate` RE-GROUNDED on the INTEGRAL-level pairing (the RETRACTED pointwise
  `{hProdMoment, hProdPtwise, hLeviCap}` GONE), resting on the STANDING centered carries
  `{hDHrefined, hFdomEvery, hProdMeas}`.  This brick does NOT prove `a₁ = R/6`, and makes NO claim of
  unconditionality.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring
  stack AND on the surviving enumerated carries.
-/

section AxiomChecks
open QIQTH.WeightedPairingHelper
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms heatKernel1D_prod_to_single
#print axioms gaussDdim_prod_to_single
#print axioms weighted_pairing_helper
#print axioms profRate_inner_bound
#print axioms profRate_integral
#print axioms hGint_regrounded
#print axioms perUCensus_phase8
end AxiomChecks
