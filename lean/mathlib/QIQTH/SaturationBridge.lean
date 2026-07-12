/-
  SATURATION BRIDGE — the Planck entropy's log-divergence and the non-commuting saturation
  diagram: the β → 0 corner of the record/gravity correspondence (duality campaign, brick D3e/f).

  The DY7 conjecture (`QIQTH.Conjectures.FlatSpaceRecordGravityCorrespondence`) equates the
  finite SATURATED area law `S = Σ log D_k = A/4G` — the `β → 0`-first corner, in which each
  link's occupation saturates its capacity `D_k` — with the CONTINUUM thermal entropy — the
  `D → ∞`-first corner, the positive-temperature free-boson result of `ContinuumEntropy`
  (`integral_sInf_scaled`).  These two limits provably DON'T commute: BOTH diverge as
  `(D → ∞, β → 0)`, and the STRUCTURE differs in the `O(1)` remainder.  THIS brick makes the
  diagram precise.

  What is proved (all axiom-free):

  PART 1 — THE CORE PLANCK BRIDGE (about the held `QIQTH.ContinuumEntropy.sInf`):
  • `tendsto_self_div_exp_sub_one`  — `x/(eˣ−1) → 1` as `x → 0⁺` (derivative of `exp` at 0);
  • `tendsto_one_sub_exp_neg_div_self` — `(1−e^{−x})/x → 1`;
  • `tendsto_neg_log_one_sub_exp_neg_div_self` — `−log((1−e^{−x})/x) → 0`;
  • `sInf_add_log_eventuallyEq` — the algebraic rewrite of `s_∞(x) + log x`;
  • ★★ `tendsto_sInf_add_log` — THE CORE BRIDGE: `s_∞(x) = −log x + 1 + o(1)`, i.e.
    `s_∞(x) + log x → 1` as `x → 0⁺` (equivalently `tendsto_sInf_sub_log_inv`);
  • `sInf_logCutoff_bridge` — THE CUTOFF-MATCHING BRIDGE: if `D_eff·x → C` then
    `s_∞(x) − log D_eff → 1 − log C` — the continuum per-mode log-divergence matches the
    finite saturated `log D`; `D_eff ~ 1/x` gives offset `1`, and EXACT additive matching
    (offset `0`) is `C = e`, the physical cutoff identification `D_eff ~ e/x`.

  PART 2 — THE NON-COMMUTING THREE-REGIME DIAGRAM (built on the held DS3
  `QIQTH.Decoupling.thermalEntropy`, `tendsto_thermalEntropy_saturation`,
  `tendsto_thermalEntropy_planck`):
  • `thermalEntropy_closed` — the closed form
    `S_D(x) = log((1−e^{−Dx})/(1−e^{−x})) + x/(eˣ−1) − Dx/(e^{Dx}−1)`;
  • `saturation_regime` (`D·x → 0`)  — `S_D(x) − log D → 0`;
  • `crossover_regime`  (`D·x → c`)  — `S_D(x) − log D → truncCrossoverPhi c`, the
    boundary-layer constant;
  • `continuum_regime`  (`D·x → ∞`)  — `S_D(x) + log x → 1` (matching Part 1);
  • ★★ `saturation_diagram_noncommuting` — THE GUARD: the renormalized finite part
    `S_D(x) − log D` is SCHEDULE-DEPENDENT (`→ 0` along `x_D = 1/D²`, but
    `→ truncCrossoverPhi 10 ≠ 0` along `x_D = 10/D`).

  ────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (honest scope, binding).  This rung does NOT prove the DY7 conjecture:
  • the theorem PROVES the analytic log-matching `s_∞(x) = log(1/x) + 1 + o(1)` and the
    schedule-dependence of the renormalized finite part;
  • the cutoff / temperature-frequency IDENTIFICATION `D_eff ~ 1/x` (and the exact constant
    `C`, e.g. `C = e` for offset `0`) is a MODELING CHOICE, not derived here;
  • the raw per-mode entropy DIVERGES in both orders of the double limit — this is a matching
    of DIVERGENCES, not a finite equality;
  • `β → 0` with the finite-model area law is the finite-truncated corner; `D → ∞` at fixed
    `β` is the continuum corner — the conjecture's full equality needs the physical cutoff
    identification joining them;
  • 1D massless field only.
  This is NOT the conjecture (its fifth/final continuum rung), NOT the strong holographic
  principle, and NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.ContinuumEntropy

namespace QIQTH.SaturationBridge

open Filter
open scoped Topology

/-! ### PART 1 — the core Planck bridge -/

/-- `x/(eˣ−1) → 1` as `x → 0⁺` — the reciprocal of the difference quotient of `exp` at `0`. -/
theorem tendsto_self_div_exp_sub_one :
    Tendsto (fun x => x / (Real.exp x - 1)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hderiv : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hslope : Tendsto (slope Real.exp 0) (𝓝[≠] (0:ℝ)) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hderiv
  have hEq : slope Real.exp 0 =ᶠ[𝓝[≠] (0:ℝ)] fun y => (Real.exp y - 1) / y := by
    filter_upwards [self_mem_nhdsWithin] with y _hy
    rw [slope_def_field, Real.exp_zero, sub_zero]
  have hne0 : Tendsto (fun y : ℝ => (Real.exp y - 1) / y) (𝓝[≠] (0:ℝ)) (𝓝 1) :=
    hslope.congr' hEq
  have hpos : Tendsto (fun y : ℝ => (Real.exp y - 1) / y) (𝓝[>] (0:ℝ)) (𝓝 1) :=
    hne0.mono_left (nhdsWithin_mono 0 (fun y hy => hy.ne'))
  have hinv := hpos.inv₀ (one_ne_zero)
  simpa [inv_div] using hinv

/-- `(1−e^{−x})/x → 1` as `x → 0⁺` — the difference quotient of `1 − e^{−·}` at `0`. -/
theorem tendsto_one_sub_exp_neg_div_self :
    Tendsto (fun x => (1 - Real.exp (-x)) / x) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1) 0 := by
      have h := (hasDerivAt_neg (0:ℝ)).exp
      simpa using h
    have h2 := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub h1
    simpa using h2
  have hslope : Tendsto (slope (fun x : ℝ => 1 - Real.exp (-x)) 0) (𝓝[≠] (0:ℝ)) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have hEq : slope (fun x : ℝ => 1 - Real.exp (-x)) 0
      =ᶠ[𝓝[≠] (0:ℝ)] fun y => (1 - Real.exp (-y)) / y := by
    filter_upwards [self_mem_nhdsWithin] with y _hy
    rw [slope_def_field]
    simp only [neg_zero, Real.exp_zero, sub_self, sub_zero]
  have hne0 : Tendsto (fun y : ℝ => (1 - Real.exp (-y)) / y) (𝓝[≠] (0:ℝ)) (𝓝 1) :=
    hslope.congr' hEq
  exact hne0.mono_left (nhdsWithin_mono 0 (fun y hy => hy.ne'))

/-- `−log((1−e^{−x})/x) → 0` as `x → 0⁺` (continuity of `log` at `1`). -/
theorem tendsto_neg_log_one_sub_exp_neg_div_self :
    Tendsto (fun x => -Real.log ((1 - Real.exp (-x)) / x)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlog : Tendsto (fun x => Real.log ((1 - Real.exp (-x)) / x)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num)
    have h := hc.tendsto.comp tendsto_one_sub_exp_neg_div_self
    simpa [Real.log_one] using h
  simpa using hlog.neg

/-- The algebraic rewrite valid for `x > 0`:
    `s_∞(x) + log x = x/(eˣ−1) − log((1−e^{−x})/x)`. -/
theorem sInf_add_log_eventuallyEq :
    (fun x => QIQTH.ContinuumEntropy.sInf x + Real.log x)
      =ᶠ[𝓝[>] (0:ℝ)] fun x => x / (Real.exp x - 1) - Real.log ((1 - Real.exp (-x)) / x) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0:ℝ) < x := hx
  rw [QIQTH.ContinuumEntropy.sInf_of_pos hx0]
  have hexp : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hnum : (0:ℝ) < 1 - Real.exp (-x) := by linarith
  rw [Real.log_div hnum.ne' hx0.ne']
  ring

/-- **★★ THE CORE BRIDGE**: `s_∞(x) = −log x + 1 + o(1)` — precisely `s_∞(x) + log x → 1`
    as `x → 0⁺`.  The continuum per-mode entropy's log-divergence has universal constant `1`;
    this is the quantitative matching point for the finite saturated `log D`. -/
theorem tendsto_sInf_add_log :
    Tendsto (fun x => QIQTH.ContinuumEntropy.sInf x + Real.log x) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hrhs : Tendsto (fun x => x / (Real.exp x - 1) - Real.log ((1 - Real.exp (-x)) / x))
      (𝓝[>] (0:ℝ)) (𝓝 (1 - 0)) := by
    have h2 : Tendsto (fun x => Real.log ((1 - Real.exp (-x)) / x)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using tendsto_neg_log_one_sub_exp_neg_div_self.neg
    exact tendsto_self_div_exp_sub_one.sub h2
  have h := hrhs.congr' sInf_add_log_eventuallyEq.symm
  simpa using h

/-- The equivalent form: `s_∞(x) − log(1/x) → 1` (since `log x⁻¹ = −log x`). -/
theorem tendsto_sInf_sub_log_inv :
    Tendsto (fun x => QIQTH.ContinuumEntropy.sInf x - Real.log x⁻¹) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  refine tendsto_sInf_add_log.congr' ?_
  filter_upwards with x
  rw [Real.log_inv]; ring

/-- **THE CUTOFF-MATCHING BRIDGE**: if the effective dimension matches the frequency,
    `D_eff·x → C`, then the continuum per-mode entropy's log-divergence matches the finite
    saturated `log D_eff` up to `1 − log C`:  `s_∞(x) − log D_eff → 1 − log C`.

    `D_eff ~ 1/x` (i.e. `C = 1`) gives offset `1`; EXACT additive matching (offset `0`) is
    `C = e`, the physical cutoff identification `D_eff ~ e/x` — a MODELING CHOICE, not
    derived (see the header firewall). -/
theorem sInf_logCutoff_bridge {ι : Type*} {l : Filter ι} [l.NeBot]
    {x Deff : ι → ℝ} {C : ℝ} (hx : Tendsto x l (𝓝[>] (0:ℝ))) (hC : 0 < C)
    (hDpos : ∀ᶠ i in l, 0 < Deff i)
    (hmatch : Tendsto (fun i => Deff i * x i) l (𝓝 C)) :
    Tendsto (fun i => QIQTH.ContinuumEntropy.sInf (x i) - Real.log (Deff i)) l
      (𝓝 (1 - Real.log C)) := by
  have hxpos : ∀ᶠ i in l, 0 < x i :=
    hx.eventually (eventually_mem_nhdsWithin.mono fun _y hy => hy)
  have heq : (fun i => QIQTH.ContinuumEntropy.sInf (x i) - Real.log (Deff i))
      =ᶠ[l] (fun i => (QIQTH.ContinuumEntropy.sInf (x i) + Real.log (x i))
        - Real.log (Deff i * x i)) := by
    filter_upwards [hDpos, hxpos] with i hDi hxi
    rw [Real.log_mul hDi.ne' hxi.ne']
    ring
  have hmain : Tendsto (fun i => (QIQTH.ContinuumEntropy.sInf (x i) + Real.log (x i))
      - Real.log (Deff i * x i)) l (𝓝 (1 - Real.log C)) :=
    (tendsto_sInf_add_log.comp hx).sub ((Real.continuousAt_log hC.ne').tendsto.comp hmatch)
  exact hmain.congr' heq.symm

/-! ### PART 2 — the closed form and the non-commuting three-regime diagram -/

/-- The boundary-layer term `g(t) = log((1−e^{−t})/t)`, with `g(t) → 0` as `t → 0⁺`. -/
noncomputable def truncG (t : ℝ) : ℝ := Real.log ((1 - Real.exp (-t)) / t)

/-- The crossover (boundary-layer) constant of the `D·x → c` regime:
    `truncCrossoverPhi c = log((1−e^{−c})/c) + 1 − c/(eᶜ−1)`. -/
noncomputable def truncCrossoverPhi (c : ℝ) : ℝ :=
  Real.log ((1 - Real.exp (-c)) / c) + 1 - c / (Real.exp c - 1)

/-- The weighted geometric sum identity `(1−q)²·Σ_{n<D} n·qⁿ = q(1−q^D) − D·q^D·(1−q)`. -/
private theorem sum_range_mul_pow (q : ℝ) (D : ℕ) :
    (1 - q) ^ 2 * ∑ n ∈ Finset.range D, (n : ℝ) * q ^ n
      = q * (1 - q ^ D) - (D : ℝ) * q ^ D * (1 - q) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The closed form of the truncated occupation `⟨N⟩_D = q/(1−q) − D·q^D/(1−q^D)`. -/
private theorem meanN_closed {D : ℕ} (hD : 1 ≤ D) {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    QIQTH.Decoupling.meanN D q = q / (1 - q) - (D : ℝ) * q ^ D / (1 - q ^ D) := by
  have hq1 : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  have hDne : D ≠ 0 := by omega
  have hqDlt : q ^ D < 1 := pow_lt_one₀ h0.le h1 hDne
  have hqD1 : (1 : ℝ) - q ^ D ≠ 0 := sub_ne_zero.mpr (ne_of_lt hqDlt).symm
  have hZ : QIQTH.Decoupling.Zgeom D q = (1 - q ^ D) / (1 - q) := by
    rw [QIQTH.Decoupling.Zgeom, geom_sum_eq (ne_of_lt h1),
      div_eq_div_iff (sub_ne_zero.mpr (ne_of_lt h1)) hq1]
    ring
  have hsum : ∑ n ∈ Finset.range D, (n : ℝ) * q ^ n
      = (q * (1 - q ^ D) - (D : ℝ) * q ^ D * (1 - q)) / (1 - q) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hq1), mul_comm]
    exact sum_range_mul_pow q D
  rw [QIQTH.Decoupling.meanN, hZ, hsum]
  field_simp

/-- The closed form of `x·⟨N⟩_D` at `q = e^{−x}`:
    `x·⟨N⟩_D = x/(eˣ−1) − Dx/(e^{Dx}−1)`. -/
private theorem x_meanN_closed {D : ℕ} (hD : 1 ≤ D) {x : ℝ} (hx : 0 < x) :
    x * QIQTH.Decoupling.meanN D (Real.exp (-x))
      = x / (Real.exp x - 1) - (D : ℝ) * x / (Real.exp ((D : ℝ) * x) - 1) := by
  have hq0 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hq1 : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hqD : Real.exp (-x) ^ D = Real.exp (-((D : ℝ) * x)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [meanN_closed hD hq0 hq1, hqD, mul_sub]
  congr 1
  · exact QIQTH.Decoupling.planck_form hx
  · have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hDx : (0 : ℝ) < (D : ℝ) * x := mul_pos hDpos hx
    rw [← QIQTH.Decoupling.planck_form hDx]
    ring

/-- **THE CLOSED FORM** of the DS3 truncated thermal entropy for `D ≥ 1`, `x > 0`:
    `S_D(x) = log((1−e^{−Dx})/(1−e^{−x})) + x/(eˣ−1) − Dx/(e^{Dx}−1)`. -/
theorem thermalEntropy_closed {D : ℕ} (hD : 1 ≤ D) {x : ℝ} (hx : 0 < x) :
    QIQTH.Decoupling.thermalEntropy D x
      = Real.log ((1 - Real.exp (-((D : ℝ) * x))) / (1 - Real.exp (-x)))
        + x / (Real.exp x - 1) - (D : ℝ) * x / (Real.exp ((D : ℝ) * x) - 1) := by
  have hq1ne : Real.exp (-x) ≠ 1 := by
    have : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    exact ne_of_lt this
  have hqD : Real.exp (-x) ^ D = Real.exp (-((D : ℝ) * x)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hZ : QIQTH.Decoupling.Zgeom D (Real.exp (-x))
      = (1 - Real.exp (-((D : ℝ) * x))) / (1 - Real.exp (-x)) := by
    rw [QIQTH.Decoupling.Zgeom, geom_sum_eq hq1ne, hqD,
      div_eq_div_iff (sub_ne_zero.mpr hq1ne) (sub_ne_zero.mpr hq1ne.symm)]
    ring
  rw [QIQTH.Decoupling.thermalEntropy, hZ, x_meanN_closed hD hx]
  ring

/-- The renormalized (subtract `log D`) form:
    `S_D(x) − log D = g(Dx) − g(x) + x/(eˣ−1) − Dx/(e^{Dx}−1)`. -/
theorem thermalEntropy_sub_log_eq {D : ℕ} (hD : 1 ≤ D) {x : ℝ} (hx : 0 < x) :
    QIQTH.Decoupling.thermalEntropy D x - Real.log D
      = truncG ((D : ℝ) * x) - truncG x + x / (Real.exp x - 1)
        - (D : ℝ) * x / (Real.exp ((D : ℝ) * x) - 1) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDx : (0 : ℝ) < (D : ℝ) * x := mul_pos hDpos hx
  have e1 : (0 : ℝ) < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have e2 : (0 : ℝ) < 1 - Real.exp (-((D : ℝ) * x)) := by
    have : Real.exp (-((D : ℝ) * x)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  rw [thermalEntropy_closed hD hx]
  simp only [truncG]
  rw [Real.log_div e2.ne' e1.ne', Real.log_div e2.ne' hDx.ne',
    Real.log_div e1.ne' hx.ne', Real.log_mul hDpos.ne' hx.ne']
  ring

/-- The continuum (add `log x`) form:
    `S_D(x) + log x = log(1−e^{−Dx}) − g(x) + x/(eˣ−1) − Dx/(e^{Dx}−1)`. -/
theorem thermalEntropy_add_log_eq {D : ℕ} (hD : 1 ≤ D) {x : ℝ} (hx : 0 < x) :
    QIQTH.Decoupling.thermalEntropy D x + Real.log x
      = Real.log (1 - Real.exp (-((D : ℝ) * x))) - truncG x + x / (Real.exp x - 1)
        - (D : ℝ) * x / (Real.exp ((D : ℝ) * x) - 1) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hDx : (0 : ℝ) < (D : ℝ) * x := mul_pos hDpos hx
  have e1 : (0 : ℝ) < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have e2 : (0 : ℝ) < 1 - Real.exp (-((D : ℝ) * x)) := by
    have : Real.exp (-((D : ℝ) * x)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  rw [thermalEntropy_closed hD hx]
  simp only [truncG]
  rw [Real.log_div e2.ne' e1.ne', Real.log_div e1.ne' hx.ne']
  ring

/-! ### The sub-limits feeding the three regimes -/

/-- `g(t) = log((1−e^{−t})/t) → 0` as `t → 0⁺`. -/
theorem truncG_tendsto_zero : Tendsto truncG (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := tendsto_neg_log_one_sub_exp_neg_div_self.neg
  simpa [truncG] using h

/-- `g` is continuous at each `c > 0`. -/
theorem truncG_continuousAt {c : ℝ} (hc : 0 < c) : ContinuousAt truncG c := by
  have hexp : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hnum : (0 : ℝ) < 1 - Real.exp (-c) := by linarith
  have hinner : ContinuousAt (fun t : ℝ => (1 - Real.exp (-t)) / t) c :=
    (continuousAt_const.sub ((Real.continuous_exp.comp continuous_neg).continuousAt)).div
      continuousAt_id hc.ne'
  simpa [truncG] using hinner.log (div_pos hnum hc).ne'

/-- `t/(eᵗ−1)` is continuous at each `c > 0`. -/
theorem qfun_continuousAt {c : ℝ} (hc : 0 < c) :
    ContinuousAt (fun t : ℝ => t / (Real.exp t - 1)) c := by
  have hd : Real.exp c - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hc).ne'
  exact continuousAt_id.div (Real.continuous_exp.continuousAt.sub continuousAt_const) hd

/-- `t/(eᵗ−1) → 0` as `t → ∞`. -/
theorem qfun_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => t / (Real.exp t - 1)) atTop (𝓝 0) := by
  have hnum : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-t)) atTop (𝓝 1) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using tendsto_const_nhds.sub h
  have hcomb : Tendsto (fun t : ℝ => (t * Real.exp (-t)) / (1 - Real.exp (-t))) atTop (𝓝 (0 / 1)) :=
    hnum.div hden one_ne_zero
  rw [zero_div] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have h1 : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h2 : (1 : ℝ) - Real.exp (-t) ≠ 0 := by
    have : (0 : ℝ) < 1 - Real.exp (-t) := by linarith
    exact this.ne'
  have h3 : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr ht).ne'
  rw [Real.exp_neg]
  field_simp

/-- `log(1−e^{−y}) → 0` as `y → ∞`. -/
theorem log_one_sub_exp_neg_tendsto_atTop :
    Tendsto (fun y : ℝ => Real.log (1 - Real.exp (-y))) atTop (𝓝 0) := by
  have harg : Tendsto (fun y : ℝ => 1 - Real.exp (-y)) atTop (𝓝 1) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using tendsto_const_nhds.sub h
  have hc : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num)
  have h := hc.tendsto.comp harg
  simpa [Real.log_one] using h

/-! ### The three regimes -/

/-- **SATURATION REGIME** (`D·x → 0`, the finite/equipartition corner): the renormalized
    truncated entropy `S_D(x) − log D → 0`. -/
theorem saturation_regime {ι : Type*} {l : Filter ι} [l.NeBot] {D : ι → ℕ} {x : ι → ℝ}
    (hx : Tendsto x l (𝓝[>] (0:ℝ))) (hD : Tendsto (fun i => (D i : ℝ)) l atTop)
    (hy : Tendsto (fun i => (D i : ℝ) * x i) l (𝓝 0)) :
    Tendsto (fun i => QIQTH.Decoupling.thermalEntropy (D i) (x i) - Real.log (D i)) l (𝓝 0) := by
  have hxpos : ∀ᶠ i in l, 0 < x i :=
    hx.eventually (eventually_mem_nhdsWithin.mono fun _y hy => hy)
  have hDge1 : ∀ᶠ i in l, 1 ≤ D i := by
    filter_upwards [hD.eventually_ge_atTop 1] with i hi; exact_mod_cast hi
  have hy_pos : Tendsto (fun i => (D i : ℝ) * x i) l (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hy, ?_⟩
    filter_upwards [hDge1, hxpos] with i hDi hxi
    have hDp : (0 : ℝ) < (D i : ℝ) := by
      have : 0 < D i := hDi
      exact_mod_cast this
    exact mul_pos hDp hxi
  have hcomb := (((truncG_tendsto_zero.comp hy_pos).sub (truncG_tendsto_zero.comp hx)).add
    (tendsto_self_div_exp_sub_one.comp hx)).sub (tendsto_self_div_exp_sub_one.comp hy_pos)
  have hval : (0 : ℝ) - 0 + 1 - 1 = 0 := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [hDge1, hxpos] with i hDi hxi
  exact (thermalEntropy_sub_log_eq hDi hxi).symm

/-- **CROSSOVER REGIME** (`D·x → c`, `0 < c`, the boundary layer): the renormalized truncated
    entropy `S_D(x) − log D → truncCrossoverPhi c` — the schedule-dependent finite part. -/
theorem crossover_regime {ι : Type*} {l : Filter ι} [l.NeBot] {D : ι → ℕ} {x : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hx : Tendsto x l (𝓝[>] (0:ℝ))) (hD : Tendsto (fun i => (D i : ℝ)) l atTop)
    (hy : Tendsto (fun i => (D i : ℝ) * x i) l (𝓝 c)) :
    Tendsto (fun i => QIQTH.Decoupling.thermalEntropy (D i) (x i) - Real.log (D i)) l
      (𝓝 (truncCrossoverPhi c)) := by
  have hxpos : ∀ᶠ i in l, 0 < x i :=
    hx.eventually (eventually_mem_nhdsWithin.mono fun _y hy => hy)
  have hDge1 : ∀ᶠ i in l, 1 ≤ D i := by
    filter_upwards [hD.eventually_ge_atTop 1] with i hi; exact_mod_cast hi
  have ht1 : Tendsto (fun i => truncG ((D i : ℝ) * x i)) l (𝓝 (truncG c)) :=
    (truncG_continuousAt hc).tendsto.comp hy
  have ht2 : Tendsto (fun i => truncG (x i)) l (𝓝 0) := truncG_tendsto_zero.comp hx
  have ht3 : Tendsto (fun i => (x i) / (Real.exp (x i) - 1)) l (𝓝 1) :=
    tendsto_self_div_exp_sub_one.comp hx
  have ht4 : Tendsto (fun i => ((D i : ℝ) * x i) / (Real.exp ((D i : ℝ) * x i) - 1)) l
      (𝓝 (c / (Real.exp c - 1))) := (qfun_continuousAt hc).tendsto.comp hy
  have hcomb := ((ht1.sub ht2).add ht3).sub ht4
  have hval : truncG c - 0 + 1 - c / (Real.exp c - 1) = truncCrossoverPhi c := by
    simp only [truncG, truncCrossoverPhi]; ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [hDge1, hxpos] with i hDi hxi
  exact (thermalEntropy_sub_log_eq hDi hxi).symm

/-- **CONTINUUM REGIME** (`D·x → ∞`, the positive-temperature corner): the entropy plus
    `log x` has the universal limit `S_D(x) + log x → 1` (matching Part 1's core bridge —
    only HERE is the answer the universal `1`). -/
theorem continuum_regime {ι : Type*} {l : Filter ι} [l.NeBot] {D : ι → ℕ} {x : ι → ℝ}
    (hx : Tendsto x l (𝓝[>] (0:ℝ))) (hD : Tendsto (fun i => (D i : ℝ)) l atTop)
    (hy : Tendsto (fun i => (D i : ℝ) * x i) l atTop) :
    Tendsto (fun i => QIQTH.Decoupling.thermalEntropy (D i) (x i) + Real.log (x i)) l (𝓝 1) := by
  have hxpos : ∀ᶠ i in l, 0 < x i :=
    hx.eventually (eventually_mem_nhdsWithin.mono fun _y hy => hy)
  have hDge1 : ∀ᶠ i in l, 1 ≤ D i := by
    filter_upwards [hD.eventually_ge_atTop 1] with i hi; exact_mod_cast hi
  have ht1 : Tendsto (fun i => Real.log (1 - Real.exp (-((D i : ℝ) * x i)))) l (𝓝 0) :=
    log_one_sub_exp_neg_tendsto_atTop.comp hy
  have ht2 : Tendsto (fun i => truncG (x i)) l (𝓝 0) := truncG_tendsto_zero.comp hx
  have ht3 : Tendsto (fun i => (x i) / (Real.exp (x i) - 1)) l (𝓝 1) :=
    tendsto_self_div_exp_sub_one.comp hx
  have ht4 : Tendsto (fun i => ((D i : ℝ) * x i) / (Real.exp ((D i : ℝ) * x i) - 1)) l (𝓝 0) :=
    qfun_tendsto_atTop_zero.comp hy
  have hcomb := ((ht1.sub ht2).add ht3).sub ht4
  have hval : (0 : ℝ) - 0 + 1 - 0 = 1 := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [hDge1, hxpos] with i hDi hxi
  exact (thermalEntropy_add_log_eq hDi hxi).symm

/-! ### ★★ THE GUARD — the non-commuting saturation diagram -/

/-- **★★ THE GUARD — THE `(D → ∞, β → 0)` LIMITS DON'T COMMUTE.**  The finite `A/4G`
    saturation (`log D`) and the continuum thermal entropy (`−log x + 1`) are the two
    order-of-limits ENDPOINTS of ONE double sequence whose renormalized finite part
    `S_D(x) − log D` is SCHEDULE-DEPENDENT: along `x_D = 1/D²` (`D·x → 0`) it tends to `0`,
    but along `x_D = 10/D` (`D·x → 10`) it tends to `truncCrossoverPhi 10 ≠ 0`.  The raw
    entropy diverges in both orders; the STRUCTURE differs in the `O(1)` remainder.  This is
    the honest bridge — the conjecture's `S = Σ log D_k = A/4G` (finite, `β → 0`-first) and
    `S = continuum thermal entropy` (`D → ∞`-first) are the two corners of the non-commuting
    diagram, quantitatively linked by `log D_eff ↔ −log x + O(1)` (see `sInf_logCutoff_bridge`).

    FIREWALL: this proves the analytic schedule-dependence, NOT the conjecture — the cutoff
    identification joining the corners is a modeling choice; see the header. -/
theorem saturation_diagram_noncommuting :
    Tendsto (fun D : ℕ => QIQTH.Decoupling.thermalEntropy D (1 / (D : ℝ) ^ 2) - Real.log D)
        atTop (𝓝 0)
    ∧ Tendsto (fun D : ℕ => QIQTH.Decoupling.thermalEntropy D (10 / (D : ℝ)) - Real.log D)
        atTop (𝓝 (truncCrossoverPhi 10))
    ∧ truncCrossoverPhi 10 ≠ 0 := by
  have hD_id : Tendsto (fun D : ℕ => (D : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨?_, ?_, ?_⟩
  · -- saturation schedule x_D = 1/D²
    have hx_sat : Tendsto (fun D : ℕ => 1 / (D : ℝ) ^ 2) atTop (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hsq : Tendsto (fun D : ℕ => (1 / (D : ℝ)) * (1 / (D : ℝ))) atTop (𝓝 (0 * 0)) :=
          (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).mul
            (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
        rw [mul_zero] at hsq
        refine hsq.congr' ?_
        filter_upwards with D
        ring
      · filter_upwards [eventually_gt_atTop 0] with D hD
        have hDp : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
        exact div_pos one_pos (pow_pos hDp 2)
    have hy_sat : Tendsto (fun D : ℕ => (D : ℝ) * (1 / (D : ℝ) ^ 2)) atTop (𝓝 0) := by
      refine (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with D hD
      have hDp : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    exact saturation_regime (D := fun i => i) hx_sat hD_id hy_sat
  · -- crossover schedule x_D = 10/D, c = 10
    have hx_cross : Tendsto (fun D : ℕ => 10 / (D : ℝ)) atTop (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h10 : Tendsto (fun D : ℕ => (10 : ℝ) * (1 / (D : ℝ))) atTop (𝓝 (10 * 0)) :=
          (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10
        rw [mul_zero] at h10
        refine h10.congr' ?_
        filter_upwards with D
        rw [mul_one_div]
      · filter_upwards [eventually_gt_atTop 0] with D hD
        have hDp : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
        exact div_pos (by norm_num) hDp
    have hy_cross : Tendsto (fun D : ℕ => (D : ℝ) * (10 / (D : ℝ))) atTop (𝓝 10) := by
      refine (tendsto_const_nhds (x := (10 : ℝ))).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with D hD
      have hDp : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    exact crossover_regime (D := fun i => i) (by norm_num) hx_cross hD_id hy_cross
  · -- truncCrossoverPhi 10 ≠ 0  (in fact < 0, via e² < 10)
    have hnum : (0 : ℝ) < 1 - Real.exp (-(10:ℝ)) := by
      have : Real.exp (-(10:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
      linarith
    have hlt1 : (1 : ℝ) - Real.exp (-(10:ℝ)) < 1 := by
      have := Real.exp_pos (-(10:ℝ)); linarith
    have h_split : Real.log ((1 - Real.exp (-(10:ℝ))) / 10)
        = Real.log (1 - Real.exp (-(10:ℝ))) - Real.log 10 :=
      Real.log_div hnum.ne' (by norm_num)
    have hlogneg : Real.log (1 - Real.exp (-(10:ℝ))) < 0 := Real.log_neg hnum hlt1
    have hlog10 : (2 : ℝ) < Real.log 10 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 10)]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2]
      have hb : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hmul := mul_lt_mul' hb.le hb hpos.le (by norm_num : (0:ℝ) < 2.7182818286)
      have hnum2 : (2.7182818286 : ℝ) * 2.7182818286 < 10 := by norm_num
      linarith [hmul, hnum2]
    have hAlt : Real.log ((1 - Real.exp (-(10:ℝ))) / 10) < -2 := by rw [h_split]; linarith
    have hexp10 : (1 : ℝ) < Real.exp 10 := by rw [Real.one_lt_exp_iff]; norm_num
    have hB : (0 : ℝ) < 10 / (Real.exp 10 - 1) := div_pos (by norm_num) (by linarith)
    have hlt : truncCrossoverPhi 10 < 0 := by
      unfold truncCrossoverPhi
      linarith [hAlt, hB]
    exact ne_of_lt hlt

end QIQTH.SaturationBridge
