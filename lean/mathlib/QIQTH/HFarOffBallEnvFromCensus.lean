/-
  HFarOffBallEnvFromCensus — the OFF-BALL Gaussian ENVELOPE of `H_far` for the CONCRETE census/rate
  integrand, DISCHARGED from the already-banked concrete witness time-derivative envelope
  (`witnessTimeDeriv_domination_global_anyS`, J4-950) via a genuinely-new OFF-BALL `τ⁻¹`-ABSORPTION lemma.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable /
  conclusion-in-disguise hypothesis (satisfiability EXHIBITED below), no existing banked file edited.

  ## THE GAP THIS FILLS (from J4-968 `HFarOffBallDischarge.lean`).  `hfar_of_ballrate_offBallEnv_ftc`
  produces `H_far` from {FTC-in-`c` bridge, on-ball `hballrate`, integrability, and an OFF-BALL single-
  Gaussian envelope `henv` on the concrete rate integrand `g c s z`}.  J4-968 CARRIED `henv` abstractly.
  J4-968's own firewall was explicit that the concrete-kernel off-ball envelope was a GENUINELY SEPARATE
  carried hypothesis.  THIS FILE DISCHARGES that `henv` for the concrete census integrand
      `g c s z := deriv (fun r ↦ vanVleckGatedWitness g gi hC hK S a b r 0 z) (c−s) · F s z 0`
  modulo ONLY {the accepted amplitude data (`hAmp0`,`hCfield`,`hSupp`) already carried by the census
  envelope, and a G3 uniform F-factor sup-bound `|F s z 0| ≤ M_F`}.

  ## WHY THE CENSUS ENVELOPE DOES NOT DIRECTLY SUPPLY `henv` (gpt-5.6-sol high, 2026-08-22, CONFIRMED).
  The banked `witnessTimeDeriv_domination_global_anyS` gives, for τ = c−s,
      `|deriv (Wit) τ| ≤ Ccen · τ⁻¹ · gaussDdim (4·D.lam·τ) z`   (∀ z).
  `henv` needs a **FIXED** constant `Cenv` (independent of c,s,z).  Multiplying by `|F| ≤ M_F` still leaves
  the extra `τ⁻¹` prefactor and a τ-DEPENDENT NARROW width `4·D.lam·τ → 0`.  At EQUAL widths a fixed `Cenv`
  is impossible (`Cenv ≥ Ccen·M_F·(c−s)⁻¹` blows up as `c−s ↓ 0`).  This is NOT a defeq match — it needs
  genuinely-new analysis:

  ## THE NEW OFF-BALL `τ⁻¹`-ABSORPTION (§C, `invTau_gaussDdim_offBall_absorb`).  WIDEN the Gaussian to
  `q'·τ` with `q' > q = 4·D.lam`; on the off-ball region `ρ ≤ ‖z‖` the extra exponential slack gives
      `τ⁻¹ · gaussDdim (q·τ) z  ≤  K · gaussDdim (q'·τ) z`   (∀ τ>0, ρ ≤ ‖z‖),
  with a FIXED `K`.  Mechanism: the width ratio (banked `gaussDdim_width_ratio_le`) is
  `(√(q'/q))ⁿ·exp(−d·r²(z)/τ)` with `d = (1/q−1/q')/4 > 0`; off-ball `r²(z) ≥ ρ²` and the scalar bound
  `τ⁻¹·exp(−b/τ) ≤ (b·e)⁻¹` (from `x·e^{−x} ≤ e^{−1}`, i.e. `Real.add_one_le_exp`) with `b = d·ρ² > 0`
  absorb the `τ⁻¹` into `K = (√(q'/q))ⁿ·(d·ρ²·e)⁻¹`.  ρ>0 is GENUINELY REQUIRED (at z=0 the `τ⁻¹` is
  unbounded).  This is real analysis, not wiring.

  ## WHAT LANDS.
    • `norm_le_rncRadial`, `sq_norm_le_rncRadialSq` — the sup-norm → Euclidean-radius bridge
        (`‖z‖ ≤ √(r²(z))`, `‖z‖² ≤ r²(z)`), giving `ρ ≤ ‖z‖ ⟹ ρ² ≤ r²(z)`.
    • `invTau_exp_neg_le` — the scalar sup bound `τ⁻¹·exp(−b/τ) ≤ (b·e)⁻¹` (`b,τ > 0`).
    • `invTau_gaussDdim_offBall_absorb` (★★) — THE OFF-BALL `τ⁻¹`-ABSORPTION.
    • `offBall_env_of_derivEnv_Fbound` (★★) — the abstract adapter: a census-shaped deriv envelope + a
        uniform F-bound + the absorption ⟹ the `henv` shape for `g c s z := Dfun(c−s) z · Ffun s z`.
    • `hfar_offBall_concrete_of_data` (★★★) — THE HEADLINE: wires `witnessTimeDeriv_domination_global_anyS`
        through the adapter into `hfar_of_ballrate_offBallEnv_ftc` (J4-968) to yield `H_far` for the concrete
        convolution, with the OFF-BALL ENVELOPE DISCHARGED (no longer a separate carry).
    • `invTau_gaussDdim_offBall_absorb_teeth`, `offBall_env_of_derivEnv_Fbound_satisfiable` — non-vacuity
        with TEETH (genuine nonzero data; the absorption constant genuinely enters).

  ## HONEST STATUS (blunt; Sol-audited).  This DISCHARGES the concrete off-ball ENVELOPE `henv` that J4-968
  carried — reducing it to {the accepted census amplitude data, a G3 F-factor sup-bound}.  It does NOT
  supply the FTC-in-`c` bridge (`{hDuhamel, hDConv}`), the on-ball `hballrate` (mod-G2), integrability, or
  the G3 F-factor bound itself — all remain carried.  So `hfar_offBall_concrete_of_data` produces `H_far`
  from {hFTC, hballrate, hgint, F-bound, amplitude data, `h+ε ≤ τ₀`}, with the off-ball spatial estimate no
  longer among the carries.  Per Sol: this closes ONLY the envelope premise, NOT `H_far`/`hCross` outright.
  Discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusTauDerivAnySEnvelope
import QIQTH.HFarOffBallDischarge
import QIQTH.GaussianWidthTransfer

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianWidthTransfer
open QIQTH.CensusTauDerivAnySEnvelope QIQTH.HFarOffBallDischarge
open QIQTH.CensusTauDerivGateSplit QIQTH.InverseChartNormalJets
open scoped Topology BigOperators

namespace QIQTH.HFarOffBallEnvFromCensus

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the sup-norm → Euclidean-radius bridge (`ρ ≤ ‖z‖ ⟹ ρ² ≤ r²(z)`).
    ############################################################################### -/

/-- **`norm_le_rncRadial` — `‖z‖ ≤ √(r²(z))`.**  For the sup norm on `Point n = Fin n → ℝ`, each
    coordinate obeys `|zᵢ| = √(zᵢ²) ≤ √(∑ₖ zₖ²) = √(r²(z))` (single-term ≤ sum, `Finset.single_le_sum`),
    so the sup is `≤ √(r²(z))` (`pi_norm_le_iff_of_nonneg`).  NOT `a₁ = R/6`. -/
theorem norm_le_rncRadial (z : Point n) : ‖z‖ ≤ Real.sqrt (rncRadialSq z) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun k => (z k) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

/-- **`sq_norm_le_rncRadialSq` — `‖z‖² ≤ r²(z)`.**  Square `norm_le_rncRadial` (both sides nonneg).
    NOT `a₁ = R/6`. -/
theorem sq_norm_le_rncRadialSq (z : Point n) : ‖z‖ ^ 2 ≤ rncRadialSq z := by
  have h := norm_le_rncRadial z
  have h2 : ‖z‖ ^ 2 ≤ (Real.sqrt (rncRadialSq z)) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg z) h
  rwa [Real.sq_sqrt (rncRadialSq_nonneg z)] at h2

/-! ###############################################################################
    ### §B — the scalar sup bound `τ⁻¹·exp(−b/τ) ≤ (b·e)⁻¹`.
    ############################################################################### -/

/-- **`invTau_exp_neg_le` — `τ⁻¹·exp(−b/τ) ≤ (b·e)⁻¹`** for `b,τ > 0`.  Setting `x = b/τ`, the bound is
    `(1/b)·x·e^{−x} ≤ (1/b)·e^{−1}` from `x ≤ e^{x−1}` (`Real.add_one_le_exp`) times `e^{−x}`.  This is
    the sole calculus fact behind the off-ball `τ⁻¹`-absorption.  NOT `a₁ = R/6`. -/
theorem invTau_exp_neg_le {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) :
    τ⁻¹ * Real.exp (-(b / τ)) ≤ (b * Real.exp 1)⁻¹ := by
  set x := b / τ with hxdef
  have hxpos : 0 < x := div_pos hb hτ
  have hx1 : x ≤ Real.exp (x - 1) := by
    have h := Real.add_one_le_exp (x - 1); linarith
  have hstep : x * Real.exp (-x) ≤ Real.exp (-1) := by
    have hmul := mul_le_mul_of_nonneg_right hx1 (Real.exp_pos (-x)).le
    rw [← Real.exp_add, show (x - 1) + (-x) = -1 by ring] at hmul
    exact hmul
  have hτinv : τ⁻¹ = x / b := by rw [hxdef]; field_simp
  rw [show -(b / τ) = -x by rw [hxdef], hτinv,
      show x / b * Real.exp (-x) = (1 / b) * (x * Real.exp (-x)) by ring]
  calc (1 / b) * (x * Real.exp (-x))
      ≤ (1 / b) * Real.exp (-1) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (b * Real.exp 1)⁻¹ := by rw [Real.exp_neg]; field_simp

/-! ###############################################################################
    ### §C — the OFF-BALL `τ⁻¹`-ABSORPTION (the genuinely-new analytic core).
    ############################################################################### -/

/-- **★★ `invTau_gaussDdim_offBall_absorb` — the OFF-BALL `τ⁻¹`-ABSORPTION.**  For `0 < q < q'` and
    `ρ > 0`, there is a FIXED `K > 0` with, uniformly over `τ > 0` and every OFF-BALL `z` (`ρ ≤ ‖z‖`),
        `τ⁻¹ · gaussDdim (q·τ) z  ≤  K · gaussDdim (q'·τ) z`.
    Route: the banked width-ratio `gaussDdim_width_ratio_le` (η=0, lam=q'/q, w=z) gives
    `gaussDdim (q·τ) z ≤ (√(q'/q))ⁿ·exp(−d·r²(z)/τ)·gaussDdim (q'·τ) z` with `d=(1/q−1/q')/4>0`; off-ball
    `r²(z) ≥ ρ²` and the scalar bound `invTau_exp_neg_le` (`b=d·ρ²`) absorb the `τ⁻¹`.  ρ>0 is REQUIRED.
    NOT `a₁ = R/6`. -/
theorem invTau_gaussDdim_offBall_absorb {q q' ρ : ℝ}
    (hq : 0 < q) (hqq' : q < q') (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 0 < τ → ∀ z : Point n, ρ ≤ ‖z‖ →
      τ⁻¹ * gaussDdim (q * τ) z ≤ K * gaussDdim (q' * τ) z := by
  have hq' : 0 < q' := lt_trans hq hqq'
  set lam : ℝ := q' / q with hlamdef
  have hlam : 0 < lam := div_pos hq' hq
  set d : ℝ := (1 / q - 1 / q') / 4 with hddef
  have hd : 0 < d := by
    rw [hddef]
    have : 1 / q' < 1 / q := one_div_lt_one_div_of_lt hq hqq'
    linarith
  refine ⟨(Real.sqrt lam) ^ n * (d * ρ ^ 2 * Real.exp 1)⁻¹, by positivity, ?_⟩
  intro τ hτ z hzρ
  have hqτ : 0 < q * τ := mul_pos hq hτ
  -- off-ball radial bound `ρ² ≤ r²(z)`.
  have hρ2 : ρ ^ 2 ≤ rncRadialSq z :=
    le_trans (pow_le_pow_left₀ hρ.le hzρ 2) (sq_norm_le_rncRadialSq z)
  -- the width-ratio bound at `η = 0`, `w = z`.
  have hgate : (1 - (0 : ℝ)) * rncRadialSq z ≤ rncRadialSq z := by rw [sub_zero, one_mul]
  have hratio := gaussDdim_width_ratio_le (n := n) (τ := q * τ) (η := 0) (lam := lam)
    hqτ hlam (w := z) (z := z) hgate
  have hwidth : lam * (q * τ) = q' * τ := by rw [hlamdef]; field_simp
  rw [hwidth] at hratio
  simp only [sub_zero] at hratio
  -- name the exponential factor and bound it off-ball.
  set E : ℝ := Real.exp (-((1 - 1 / lam) / 4) * rncRadialSq z / (q * τ)) with hEdef
  have hEle : E ≤ Real.exp (-(d * ρ ^ 2 / τ)) := by
    rw [hEdef]
    apply Real.exp_le_exp.mpr
    have heq : -((1 - 1 / lam) / 4) * rncRadialSq z / (q * τ) = -(d * rncRadialSq z / τ) := by
      rw [hlamdef, hddef]; field_simp
    rw [heq]
    have hle2 : d * ρ ^ 2 / τ ≤ d * rncRadialSq z / τ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ2 hd.le) (inv_nonneg.mpr hτ.le)
    linarith [hle2]
  -- the scalar absorption of `τ⁻¹`.
  have hscal : τ⁻¹ * Real.exp (-(d * ρ ^ 2 / τ)) ≤ (d * ρ ^ 2 * Real.exp 1)⁻¹ :=
    invTau_exp_neg_le (by positivity) hτ
  have hslamn : (0 : ℝ) ≤ (Real.sqrt lam) ^ n := by positivity
  have hgnn : (0 : ℝ) ≤ gaussDdim (q' * τ) z := gaussDdim_nonneg _ _
  have hτinvnn : (0 : ℝ) ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  calc τ⁻¹ * gaussDdim (q * τ) z
      ≤ τ⁻¹ * ((Real.sqrt lam) ^ n * E * gaussDdim (q' * τ) z) :=
        mul_le_mul_of_nonneg_left hratio hτinvnn
    _ = (Real.sqrt lam) ^ n * (τ⁻¹ * E) * gaussDdim (q' * τ) z := by ring
    _ ≤ (Real.sqrt lam) ^ n * (τ⁻¹ * Real.exp (-(d * ρ ^ 2 / τ))) * gaussDdim (q' * τ) z := by
        apply mul_le_mul_of_nonneg_right _ hgnn
        apply mul_le_mul_of_nonneg_left _ hslamn
        exact mul_le_mul_of_nonneg_left hEle hτinvnn
    _ ≤ (Real.sqrt lam) ^ n * (d * ρ ^ 2 * Real.exp 1)⁻¹ * gaussDdim (q' * τ) z := by
        apply mul_le_mul_of_nonneg_right _ hgnn
        exact mul_le_mul_of_nonneg_left hscal hslamn
    _ = (Real.sqrt lam) ^ n * (d * ρ ^ 2 * Real.exp 1)⁻¹ * gaussDdim (q' * τ) z := by ring

/-! ###############################################################################
    ### §D — the abstract adapter: census-shaped deriv envelope + F-bound ⟹ `henv` shape.
    ############################################################################### -/

/-- **★★ `offBall_env_of_derivEnv_Fbound` — the `henv` shape for `g c s z := Dfun(c−s) z · Ffun s z`.**
    From a census-shaped deriv envelope `hderiv` (`|Dfun τ z| ≤ Ccen·τ⁻¹·gaussDdim(q·τ) z` on `0<τ≤τ₀`),
    a uniform F-bound `hF` (`|Ffun s z| ≤ M_F`), and an off-ball `τ⁻¹`-absorption `habs` (widen `q ↦ q'`),
    the OFF-BALL Gaussian envelope holds with the FIXED constant `Ccen·M_F·Kabs`:
        `∀ s ∈ Ioo(u−ε)u, ∀ c ∈ Icc u (u+h), ∀ z, ρ ≤ ‖z‖ →
            |Dfun(c−s) z · Ffun s z| ≤ (Ccen·M_F·Kabs)·gaussDdim (q'·(c−s)) z` .
    `h+ε ≤ τ₀` places `c−s ≤ τ₀` (with `c−s > 0`) so `hderiv` fires.  NOT `a₁ = R/6`. -/
theorem offBall_env_of_derivEnv_Fbound
    (Dfun : ℝ → Point n → ℝ) (Ffun : ℝ → Point n → ℝ)
    (u ε h ρ τ₀ q q' Ccen MF Kabs : ℝ)
    (hCcen : 0 ≤ Ccen) (hMF : 0 ≤ MF)
    (hcap : h + ε ≤ τ₀)
    (hderiv : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |Dfun τ z| ≤ Ccen * τ⁻¹ * gaussDdim (q * τ) z)
    (hF : ∀ s z, |Ffun s z| ≤ MF)
    (habs : ∀ τ, 0 < τ → ∀ z : Point n, ρ ≤ ‖z‖ →
        τ⁻¹ * gaussDdim (q * τ) z ≤ Kabs * gaussDdim (q' * τ) z) :
    ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h), ∀ z : Point n, ρ ≤ ‖z‖ →
      |Dfun (c - s) z * Ffun s z| ≤ (Ccen * MF * Kabs) * gaussDdim (q' * (c - s)) z := by
  intro s hs c hc z hzρ
  have hcs : 0 < c - s := by have h1 := hs.2; have h2 := hc.1; linarith
  have hcsτ : c - s ≤ τ₀ := by
    have h1 : c ≤ u + h := hc.2
    have h2 : u - ε < s := hs.1
    linarith
  have hb1 : |Dfun (c - s) z| ≤ Ccen * (c - s)⁻¹ * gaussDdim (q * (c - s)) z :=
    hderiv (c - s) hcs hcsτ z
  have hb2 : |Ffun s z| ≤ MF := hF s z
  have habsz : (c - s)⁻¹ * gaussDdim (q * (c - s)) z ≤ Kabs * gaussDdim (q' * (c - s)) z :=
    habs (c - s) hcs z hzρ
  have hnn : (0 : ℝ) ≤ Ccen * (c - s)⁻¹ * gaussDdim (q * (c - s)) z :=
    mul_nonneg (mul_nonneg hCcen (inv_nonneg.mpr hcs.le)) (gaussDdim_nonneg _ _)
  calc |Dfun (c - s) z * Ffun s z|
      = |Dfun (c - s) z| * |Ffun s z| := abs_mul _ _
    _ ≤ (Ccen * (c - s)⁻¹ * gaussDdim (q * (c - s)) z) * MF :=
        mul_le_mul hb1 hb2 (abs_nonneg _) hnn
    _ = Ccen * MF * ((c - s)⁻¹ * gaussDdim (q * (c - s)) z) := by ring
    _ ≤ Ccen * MF * (Kabs * gaussDdim (q' * (c - s)) z) :=
        mul_le_mul_of_nonneg_left habsz (mul_nonneg hCcen hMF)
    _ = (Ccen * MF * Kabs) * gaussDdim (q' * (c - s)) z := by ring

/-! ###############################################################################
    ### §E — THE HEADLINE: `H_far` for the concrete convolution, off-ball envelope DISCHARGED.
    ############################################################################### -/

/-- **★★★ `hfar_offBall_concrete_of_data` — `H_far` with the concrete off-ball envelope DISCHARGED.**
    For the concrete census integrand `g c s z := deriv (fun r ↦ vanVleckGatedWitness … r 0 z)(c−s)·F s z 0`
    and outer function `Φouter`, given
      • the accepted census amplitude data (`hAmp0`, `hCfield`, `hSupp`) feeding
        `witnessTimeDeriv_domination_global_anyS` (J4-950),
      • a G3 uniform F-factor sup-bound `hF : |F s z 0| ≤ M_F`,
      • the FTC-in-`c` bridge `hFTC` (the `{hDuhamel, hDConv}` carry),
      • integrability `hgint` and the on-ball trace rate `hball` (the `hballrate`/G2 carry),
      • `ρ > 0` and the time cap `h + ε ≤ τ₀`,
    there is `Cfar ≥ 0` with the far-envelope `H_far`:
        `∀ s ∈ Ioo(u−ε)u, |Φouter(u+h) s − Φouter u s| ≤ Cfar·h·(u−s)^{−1/2}` .
    The OFF-BALL Gaussian envelope is SUPPLIED (via §C+§D from the banked census envelope), not carried.
    Route: `witnessTimeDeriv_domination_global_anyS` → `offBall_env_of_derivEnv_Fbound` →
    `hfar_of_ballrate_offBallEnv_ftc` (J4-968).  NOT `a₁ = R/6`. -/
theorem hfar_offBall_concrete_of_data (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK) (F : ℝ → Point n → Point n → ℝ) (Φouter : ℝ → ℝ → ℝ)
    (u ε h ρ τ₀ M M' MF Cpair : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hρ : 0 < ρ) (hCpair : 0 ≤ Cpair)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hMF : 0 ≤ MF)
    (hcap : h + ε ≤ τ₀)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hF : ∀ s z, |F s z 0| ≤ MF)
    (hFTC : ∀ s ∈ Set.Ioo (u - ε) u,
        Φouter (u + h) s - Φouter u s
          = ∫ c in u..(u + h),
              ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0)
    (hgint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        Integrable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0)
          volume)
    (hball : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |∫ z in Metric.ball (0 : Point n) ρ,
            deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0|
          ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) :
    ∃ Cfar : ℝ, 0 ≤ Cfar ∧ ∀ s ∈ Set.Ioo (u - ε) u,
      |Φouter (u + h) s - Φouter u s| ≤ Cfar * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  -- the banked concrete census time-derivative envelope (any S).
  obtain ⟨Ccen, hCcenpos, hcensus⟩ :=
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK S a b D τ₀ M M'
      hτ₀ hM hM' hAmp0 hCfield hSupp
  -- the off-ball `τ⁻¹`-absorption at `q = 4·D.lam`, `q' = 8·D.lam`.
  obtain ⟨Kabs, hKabspos, habs⟩ :=
    invTau_gaussDdim_offBall_absorb (n := n) (q := 4 * D.lam) (q' := 8 * D.lam) (ρ := ρ)
      (by positivity) (by linarith) hρ
  -- the concrete off-ball envelope from the adapter.
  have henv := offBall_env_of_derivEnv_Fbound
    (Dfun := fun τ z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ)
    (Ffun := fun s z => F s z 0)
    u ε h ρ τ₀ (4 * D.lam) (8 * D.lam) Ccen MF Kabs hCcenpos.le hMF hcap
    hcensus (fun s z => hF s z) habs
  have hCenv_nn : (0 : ℝ) ≤ Ccen * MF * Kabs :=
    mul_nonneg (mul_nonneg hCcenpos.le hMF) hKabspos.le
  refine ⟨Cpair + (Ccen * MF * Kabs) * (Real.sqrt 2 ^ n * Real.sqrt (h + ε)),
    add_nonneg hCpair (mul_nonneg hCenv_nn (by positivity)), ?_⟩
  exact hfar_of_ballrate_offBallEnv_ftc Φouter
    (fun c s z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0)
    (fun c s => 8 * D.lam * (c - s))
    u ε h ρ Cpair (Ccen * MF * Kabs)
    hε hh hρ.le hCpair hCenv_nn hFTC hgint
    (fun s hs c hc => by
      have hcs : 0 < c - s := by have h1 := hs.2; have h2 := hc.1; linarith
      exact mul_pos (mul_pos (by norm_num) hlampos) hcs)
    henv hball

/-! ###############################################################################
    ### §F — non-vacuity (TEETH).
    ############################################################################### -/

/-- **Non-vacuity of `invTau_gaussDdim_offBall_absorb` — TEETH.**  At `q=1, q'=2, ρ=1` the absorption
    genuinely fires and BOTH sides are strictly positive at `τ=1`, `z := fun _ ↦ 1` (`‖z‖ = 1 ≥ ρ`,
    provided `0 < n`): `τ⁻¹·gaussDdim (1·1) z > 0`, so the inequality is a GENUINE nonzero constraint,
    NOT `0 ≤ 0`.  NOT `a₁ = R/6`. -/
theorem invTau_gaussDdim_offBall_absorb_teeth :
    ∃ K : ℝ, 0 < K ∧
      (∀ τ : ℝ, 0 < τ → ∀ z : Point n, (1 : ℝ) ≤ ‖z‖ →
          τ⁻¹ * gaussDdim (1 * τ) z ≤ K * gaussDdim (2 * τ) z) ∧
      (0 : ℝ) < (1 : ℝ)⁻¹ * gaussDdim ((1 : ℝ) * 1) (fun _ => (1 : ℝ) : Point n) := by
  obtain ⟨K, hKpos, hb⟩ :=
    invTau_gaussDdim_offBall_absorb (n := n) (q := 1) (q' := 2) (ρ := 1)
      one_pos (by norm_num) one_pos
  refine ⟨K, hKpos, hb, ?_⟩
  rw [inv_one, one_mul, one_mul]
  exact QIQTH.LeviSeries.gaussDdim_pos 1 one_pos _

/-- **Non-vacuity of `offBall_env_of_derivEnv_Fbound` — TEETH.**  The abstract adapter's hypothesis
    bundle is jointly satisfiable with GENUINE nonzero data: `Dfun τ z := τ⁻¹·gaussDdim (τ) z` (so the
    census-shape holds with `Ccen=1`, `q=1`), `Ffun s z := 1` (so `M_F=1`), and `habs` from
    `invTau_gaussDdim_offBall_absorb` (`q=1, q'=2, ρ=1`).  Hence the envelope fires on genuine
    `Ioo/Icc` positions; the constant `Ccen·M_F·Kabs = Kabs > 0` genuinely enters.  NOT `a₁ = R/6`. -/
theorem offBall_env_of_derivEnv_Fbound_satisfiable :
    ∃ (Dfun Ffun : ℝ → Point n → ℝ) (u ε h ρ τ₀ q q' Ccen MF Kabs : ℝ),
      0 ≤ Ccen ∧ 0 ≤ MF ∧ 0 < Kabs ∧ 0 < ρ ∧ h + ε ≤ τ₀ ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, |Dfun τ z| ≤ Ccen * τ⁻¹ * gaussDdim (q * τ) z) ∧
      (∀ s z, |Ffun s z| ≤ MF) ∧
      (∀ τ, 0 < τ → ∀ z : Point n, ρ ≤ ‖z‖ →
          τ⁻¹ * gaussDdim (q * τ) z ≤ Kabs * gaussDdim (q' * τ) z) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h), ∀ z : Point n, ρ ≤ ‖z‖ →
          |Dfun (c - s) z * Ffun s z| ≤ (Ccen * MF * Kabs) * gaussDdim (q' * (c - s)) z) := by
  obtain ⟨Kabs, hKabspos, habs⟩ :=
    invTau_gaussDdim_offBall_absorb (n := n) (q := 1) (q' := 2) (ρ := 1)
      one_pos (by norm_num) one_pos
  refine ⟨fun τ z => τ⁻¹ * gaussDdim (1 * τ) z, fun _ _ => 1,
    0, 1, 1, 1, 2, 1, 2, 1, 1, Kabs,
    zero_le_one, zero_le_one, hKabspos, one_pos, by norm_num, ?_, ?_, habs, ?_⟩
  · -- census shape: `|τ⁻¹·gaussDdim (1·τ) z| ≤ 1·τ⁻¹·gaussDdim (1·τ) z` (nonneg, `Ccen=1`).
    intro τ hτ _ z
    rw [one_mul, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hτ.le) (gaussDdim_nonneg _ _))]
  · -- F-bound: `|1| ≤ 1`.
    intro _ _; rw [abs_one]
  · -- the produced envelope, from the adapter itself.
    exact offBall_env_of_derivEnv_Fbound
      (fun τ z => τ⁻¹ * gaussDdim (1 * τ) z) (fun _ _ => 1)
      0 1 1 1 2 1 2 1 1 Kabs zero_le_one zero_le_one (by norm_num)
      (by intro τ hτ _ z;
          rw [one_mul, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hτ.le) (gaussDdim_nonneg _ _))])
      (by intro _ _; rw [abs_one]) habs

end QIQTH.HFarOffBallEnvFromCensus

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFarOffBallEnvFromCensus
#print axioms norm_le_rncRadial
#print axioms sq_norm_le_rncRadialSq
#print axioms invTau_exp_neg_le
#print axioms invTau_gaussDdim_offBall_absorb
#print axioms offBall_env_of_derivEnv_Fbound
#print axioms hfar_offBall_concrete_of_data
#print axioms invTau_gaussDdim_offBall_absorb_teeth
#print axioms offBall_env_of_derivEnv_Fbound_satisfiable
end AxiomChecks
