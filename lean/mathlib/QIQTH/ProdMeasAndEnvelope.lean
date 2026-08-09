/-
  ProdMeasAndEnvelope — J4-453: (A) the census `hProdMeas` z-slice discharge, and (B) the REFINED
  (two-term) on-gate field-derivative envelope grounding the satisfiable `hDHrefined₂` shape, with the
  D₀/(2τ) mass-scaling GATE run and reconciled.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ★★★ THE PART-B GATE (run BEFORE the lemma; the verdict is BINDING) — the D₀/(2τ) reconciliation.

  J4-452 corrected the census envelope to the SATISFIABLE two-term shape
    `hDHrefined₂ :  |dH i (u−s) x z| ≤ (CA/(2(u−s))·‖z‖ + CB)·G_{wA(u−s)}(z)`   a.e. `z`,
  matching the honest slope structure: the contraction `sc = −⟨W z p, ∂ᵢW⟩/(2τ)` (Cauchy–Schwarz gives
  the `‖·‖`-moment) + the amplitude-derivative mass `Bd`.  The GATE it left open (flagged by three prior
  scaling gates): the near-isometry `‖W z p‖ ≤ L·‖z‖ + D₀` seems to feed `D₀·L'/(2τ)` into the MASS
  coefficient `CB`, i.e. `CB ~ 1/(2τ)` — which under the mass pairing would give `τ⁻¹·τ⁰ = τ⁻¹`, TOO
  SINGULAR.  So: does a `1/(2τ)` sneak into the mass?

  ── ★★★ THE GATE VERDICT (BINDING): **`D₀ = 0` at the witness — NO `1/(2τ)` in the mass.**
    The inverse chart is CENTERED at the witness field point.  The banked displacement bound
    (`InverseChartDisplacement.chartW0_displacement`) is
      `‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W·‖z‖²`   (sign: `W z 0 = −z + O(‖z‖²)`),
    hence the near-isometry has **NO additive displacement constant**: `W (z=0) 0 = 0`, and on the
    near-isometry ball the bootstrap gives the PURELY LINEAR `‖W z 0‖ ≤ 2·‖z‖` (proved inside
    `chartW0_displacement`).  Thus the honest slope obeys, by Cauchy–Schwarz (here Hölder ℓ∞–ℓ¹ on the
    sup-normed `Point n = Fin n → ℝ`) + the linear near-isometry,
      `|sc| = |∑ₖ (W z p)ₖ·Pₖ|/(2τ) ≤ (∑ₖ|Pₖ|)·‖W z p‖/(2τ) ≤ (∑ₖ|Pₖ|)·Lz/(2τ)·‖z‖`,
    a PURE `‖z‖`-moment with the `1/(2τ)` sitting ONLY on the moment (→ `CA/(2τ)`, `CA` τ-free).  The
    ONLY mass is the amplitude derivative `Bd`, giving `CB = C₁·Bd` — carrying NO `1/(2τ)`.  The feared
    `D₀·L'/(2τ)` term is ABSENT because `D₀ = 0` (the chart is centered where the census evaluates).
    Even the residual quadratic correction `C_W‖z‖²` (if one kept `‖W z 0‖ ≤ ‖z‖ + C_W‖z‖²` rather than
    `≤ 2‖z‖`) would pair as a SECOND moment `τ⁻¹·∫‖z‖²·G_a·G_b ~ τ⁻¹·O(τ) = O(1)` — a bounded `τ⁰`
    mass, still NO `τ⁻¹`.  Either way the J4-452 count STANDS: the mass has no net `1/(2τ)` power.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.ProdMeasAndEnvelope`).
    • `slopeContraction_holder`             — ★ the Hölder ℓ∞–ℓ¹ contraction bound
        `|∑ₖ Wₖ·Pₖ| ≤ ‖W‖·∑ₖ|Pₖ|` on the sup-normed `Point n` (the Cauchy–Schwarz surrogate).
    • `witnessFieldDeriv_refined_gate_envelope` — ★★ THE PART-B SUBSTANTIVE LEVER: the REFINED on-gate
        two-term pointwise bound `|dH i τ p z| ≤ (CA/(2τ)·‖z‖ + CB)·G_σ(z)` with
        `CA = (∑ₖ|Pₖ|)·Lz·Ba·C₁` and `CB = Bd·C₁` — CB carries NO `1/(2τ)` (THE GATE, discharged).
        The one refinement UP from `WitnessDerivDomination.witnessFieldDeriv_gate_envelope` (which
        crudified the slope to a constant `Bs`): here the `‖z‖`-moment is KEPT via Hölder + the centered
        near-isometry carry `hiso`.
    • `prodMeas_at_witness`                 — ★★ PART A: the EXACT census `hProdMeas` z-slice shape,
        discharged to the two z-slice factor measurabilities via `AEStronglyMeasurable.mul`.
    • `perUCensus_phase10`                  — ★★★ the fired per-`u` census (= `perUCensus_phase9`) with
        `hProdMeas` now SUPPLIED internally by `prodMeas_at_witness` (Part A integrated).

  ⚠  HONESTY FIREWALL.  `witnessFieldDeriv_refined_gate_envelope` is ON-GATE and pointwise: it grounds
  the SHAPE and SCALING of `hDHrefined₂` (the crux gate: `CB` has no `1/(2τ)`), reducing it to strictly
  lower-level carries {the amplitude sup-bounds `Ba`,`Bd`, the centered near-isometry `hiso`, the
  chart-Gaussian envelope `hgauss_env`}.  The full ∀`z` `hDHrefined₂` (off-gate vanishing + uniform
  constant selection over `(u,i,x)`) is NOT assembled here and stays a labelled carry into
  `profRate_integral₂`/`perUCensus_phase10`.  NONE of this proves `a₁ = R/6`.  No `sorry` (header prose
  excepted), no `:= True`, no new axioms, std-3 only.  `a₁ = R/6` remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.DHrefinedWitness
import QIQTH.WitnessDerivDomination

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.FlatHeatEquation QIQTH.HeatKernelA1 QIQTH.VanVleck QIQTH.ResidueBound
open scoped Topology Interval BigOperators

namespace QIQTH.ProdMeasAndEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `slopeContraction_holder` — the Hölder ℓ∞–ℓ¹ contraction bound.
    ############################################################################### -/

/-- **★ `slopeContraction_holder` — THE CONTRACTION (CAUCHY–SCHWARZ SURROGATE).**  On the sup-normed
    `Point n = Fin n → ℝ`, the field-jet contraction is bounded by the Hölder ℓ∞–ℓ¹ pairing
      `|∑ₖ Wₖ·Pₖ| ≤ ‖W‖·(∑ₖ|Pₖ|)`.
    Route: `|∑| ≤ ∑|Wₖ·Pₖ| = ∑|Wₖ||Pₖ| ≤ ∑‖W‖·|Pₖ| = ‖W‖·∑|Pₖ|` (`|Wₖ| ≤ ‖W‖` via `norm_le_pi_norm`).
    This is the honest slope factor the J4-452 gate demands (the `‖·‖`-moment), replacing the crude
    constant `Bs`.  ⚠ NOT `a₁ = R/6`. -/
theorem slopeContraction_holder (W Pval : Fin n → ℝ) :
    |∑ k, W k * Pval k| ≤ ‖(W : Point n)‖ * ∑ k, |Pval k| := by
  calc |∑ k, W k * Pval k|
      ≤ ∑ k, |W k * Pval k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |W k| * |Pval k| := by simp_rw [abs_mul]
    _ ≤ ∑ k, ‖(W : Point n)‖ * |Pval k| := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hWk : |W k| ≤ ‖(W : Point n)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm W k
        exact mul_le_mul_of_nonneg_right hWk (abs_nonneg _)
    _ = ‖(W : Point n)‖ * ∑ k, |Pval k| := by rw [← Finset.mul_sum]

/-! ###############################################################################
    ### ★★ `witnessFieldDeriv_refined_gate_envelope` — the REFINED two-term on-gate bound.
    ############################################################################### -/

/-- **★★ `witnessFieldDeriv_refined_gate_envelope` — THE PART-B SUBSTANTIVE LEVER (J4-453).**  The
    REFINED on-gate pointwise TWO-TERM bound for the concrete first-derivative kernel `dH`.  Starting
    from the E1 formula (`witnessFieldDeriv_gate_eq`: `dH = G·sc·A + G·∂ᵢA`, `sc = −⟨W z p, P⟩/(2τ)`),
    the slope is bounded NOT by a crude constant but by the honest `‖z‖`-moment:
      `|sc| ≤ (∑ₖ|Pₖ|)·‖W z p‖/(2τ) ≤ (∑ₖ|Pₖ|)·Lz/(2τ)·‖z‖`
    (Hölder `slopeContraction_holder` + the CENTERED near-isometry carry `hiso : ‖W z p‖ ≤ Lz·‖z‖`).
    With the amplitude sup-bounds `|A|≤Ba`, `|∂ᵢA|≤Bd` and the chart-Gaussian envelope
    `hgauss_env : G_τ(W z p) ≤ C₁·G_σ(z)`, this yields
      `|dH i τ p z| ≤ ((∑ₖ|Pₖ|)·Lz·Ba·C₁/(2τ)·‖z‖ + Bd·C₁)·G_σ(z)`,
    i.e. exactly the `hDHrefined₂` shape with `CA = (∑ₖ|Pₖ|)·Lz·Ba·C₁` and **`CB = Bd·C₁` — carrying NO
    `1/(2τ)`** (THE GATE, discharged: the mass term has no `τ`-singularity because `D₀ = 0` at the
    centered witness).  The one refinement up from `WitnessDerivDomination.witnessFieldDeriv_gate_envelope`.
    ⚠ NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_refined_gate_envelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (Ba Bd Lz σ C₁ : ℝ)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd)
    (hiso : ‖uniformInverseChart g gi hC hK z p‖ ≤ Lz * ‖z‖)
    (hgauss_env : gaussDdim τ (uniformInverseChart g gi hC hK z p) ≤ C₁ * gaussDdim σ z) :
    |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ (((∑ k, |Pval k|) * Lz * Ba * C₁) / (2 * τ) * ‖z‖ + Bd * C₁) * gaussDdim σ z := by
  rw [witnessFieldDeriv_gate_eq g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV hAmp1]
  set W : Point n := uniformInverseChart g gi hC hK z p with hWdef
  set G := gaussDdim τ W with hGdef
  set A := chartFieldAmp g gi hC hK a b τ z p with hAdef
  set dA := pd (chartFieldAmp g gi hC hK a b τ z) i p with hdAdef
  set Mp := ∑ k, |Pval k| with hMpdef
  have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
  have hMp : 0 ≤ Mp := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hBa' : 0 ≤ Ba := le_trans (abs_nonneg _) hBa
  have hBd' : 0 ≤ Bd := le_trans (abs_nonneg _) hBd
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  -- the honest slope: `|sc| ≤ Mp·Lz·‖z‖/(2τ)` (Hölder + centered near-isometry).
  have hnum : |∑ k, W k * Pval k| ≤ Mp * Lz * ‖z‖ := by
    calc |∑ k, W k * Pval k|
        ≤ ‖W‖ * Mp := slopeContraction_holder W Pval
      _ ≤ (Lz * ‖z‖) * Mp := mul_le_mul_of_nonneg_right hiso hMp
      _ = Mp * Lz * ‖z‖ := by ring
  have hsc : |(-(∑ k, W k * Pval k) / (2 * τ))| ≤ Mp * Lz * ‖z‖ / (2 * τ) := by
    rw [abs_div, abs_neg, abs_of_pos h2τ]
    exact div_le_div_of_nonneg_right hnum h2τ.le
  -- the nonnegative combined coefficient.
  set coef := Mp * Lz * Ba / (2 * τ) * ‖z‖ + Bd with hcoefdef
  have hslope_nn : 0 ≤ Mp * Lz * ‖z‖ / (2 * τ) := le_trans (abs_nonneg _) hsc
  have hcoef_nn : 0 ≤ coef := by
    refine add_nonneg ?_ hBd'
    have : Mp * Lz * Ba / (2 * τ) * ‖z‖ = (Mp * Lz * ‖z‖ / (2 * τ)) * Ba := by ring
    rw [this]; exact mul_nonneg hslope_nn hBa'
  -- STEP 1: `|dH| ≤ G · coef`.
  have hstep1 : |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A + G * dA| ≤ G * coef := by
    calc |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A + G * dA|
        ≤ |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A| + |G * dA| := abs_add_le _ _
      _ = G * |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + G * |dA| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hGnn]
      _ ≤ G * (Mp * Lz * ‖z‖ / (2 * τ)) * Ba + G * Bd := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hBd hGnn)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hsc hGnn) hBa (abs_nonneg _)
            (mul_nonneg hGnn hslope_nn)
      _ = G * coef := by rw [hcoefdef]; ring
  -- STEP 2: `G · coef ≤ (C₁ · G_σ z) · coef`, then rearrange to the stated RHS.
  calc |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A + G * dA|
      ≤ G * coef := hstep1
    _ ≤ (C₁ * gaussDdim σ z) * coef := mul_le_mul_of_nonneg_right hgauss_env hcoef_nn
    _ = (((∑ k, |Pval k|) * Lz * Ba * C₁) / (2 * τ) * ‖z‖ + Bd * C₁) * gaussDdim σ z := by
        rw [hcoefdef, hMpdef]; ring

/-! ###############################################################################
    ### ★★ PART A — `prodMeas_at_witness` — the census hProdMeas z-slice discharge.
    ############################################################################### -/

/-- **★★ PART A — `prodMeas_at_witness` — THE `hProdMeas` CARRY, DISCHARGED.**  The EXACT `hProdMeas`
    binder consumed by `DHrefinedWitness.profRate_integral₂`/`perUCensus_phase9`: per `(u,i,x,s)` with
    `0 < s < u`, the z-slice product `z ↦ witnessFieldDeriv i (u−s) x z · leviSeries s z 0` is
    `AEStronglyMeasurable`.  Discharged to the two z-slice factor measurabilities via
    `AEStronglyMeasurable.mul` — the per-`s` slice analogue of `ProfFacWitness.profMeas_at_witness`
    (which used the joint `(s,z)` family + `innerIntegral_aesm`; here the per-`s`, ∀-`s` shape forces
    the honest z-slice suppliers).  Honest carries: {`hWFDslice`, `hLeviSlice`} — each a genuine
    single-variable measurability (satisfiable via `WitnessMeasDeriv.hKmeas_concrete`-style slice facts
    + the Levi-series z-measurability), strictly lower-level, never the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem prodMeas_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hWFDslice : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z)
          (volume : Measure (Point n)))
    (hLeviSlice : ∀ u ∈ U, ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume : Measure (Point n)) := by
  intro u hu i x s hs0 hsu
  exact (hWFDslice u hu i x s hs0 hsu).mul (hLeviSlice u hu s hs0 hsu)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase10` — the fired per-`u` census, hProdMeas SUPPLIED (Part A).
    ############################################################################### -/

/-- **★★★ `perUCensus_phase10`.**  `DHrefinedWitness.perUCensus_phase9` with `hProdMeas` no longer a raw
    carry but SUPPLIED internally by `prodMeas_at_witness` from the two z-slice factor measurabilities
    {`hWFDslice`, `hLeviSlice`} (Part A integrated).  Every OTHER census field is threaded exactly as
    `perUCensus_phase9`.  Pure composition; each carry satisfiable, non-vacuous, strictly lower-level
    than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase10 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hDHrefined₂ : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z)
    (hWFDslice : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) x z)
          (volume : Measure (Point n)))
    (hLeviSlice : ∀ u ∈ U, ∀ s, 0 < s → s < u →
        AEStronglyMeasurable
          (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
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
  QIQTH.DHrefinedWitness.perUCensus_phase9 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint hDHrefined₂
    (prodMeas_at_witness g gi hC hK S a b U hWFDslice hLeviSlice)
    hbulkderiv hsliver hcont hQ1

end QIQTH.ProdMeasAndEnvelope

/-! ## THE J4-453 LEDGER — (A) hProdMeas discharge + (B) refined envelope / D₀/(2τ) gate.

  ── ★★★ THE PART-B GATE VERDICT (binding): `D₀ = 0` at the witness — the mass has NO `1/(2τ)`.
    The inverse chart is CENTERED at the witness field point: `chartW0_displacement` gives
    `‖W z 0 + z‖ ≤ C_W·‖z‖²` (i.e. `W z 0 = −z + O(‖z‖²)`, and the bootstrap `‖W z 0‖ ≤ 2‖z‖`).  So the
    near-isometry is PURELY LINEAR (no additive constant `D₀`), and by Hölder + linearity the slope
    `|sc| ≤ (∑ₖ|Pₖ|)·Lz/(2τ)·‖z‖` is a PURE `‖z‖`-moment — the `1/(2τ)` sits ONLY on the moment
    (→ `CA/(2τ)`, `CA` τ-free), NOT on the mass.  The only mass is `CB = C₁·Bd` (amplitude derivative),
    carrying NO `1/(2τ)`.  The feared `D₀·L'/(2τ)` singular mass term is ABSENT (`D₀ = 0`).  Residual
    quadratic `C_W‖z‖²`, if kept, pairs as `τ⁻¹·O(τ) = O(1)` — a bounded `τ⁰` mass, still no `τ⁻¹`.
    The J4-452 count STANDS.

  ── WHAT LANDED.
    • `slopeContraction_holder` — `|∑ₖ Wₖ·Pₖ| ≤ ‖W‖·∑ₖ|Pₖ|` (Hölder ℓ∞–ℓ¹ on sup-normed `Point n`).
      PROVED, std-3.
    • `witnessFieldDeriv_refined_gate_envelope` — the refined on-gate two-term bound
      `|dH| ≤ (CA/(2τ)·‖z‖ + CB)·G_σ(z)`, `CA = (∑|Pₖ|)·Lz·Ba·C₁`, `CB = Bd·C₁`; the exact `hDHrefined₂`
      shape at a point, grounding its scaling (CB no `1/(2τ)`).  ONE refinement up from
      `witnessFieldDeriv_gate_envelope`.  PROVED, std-3.
    • `prodMeas_at_witness` (PART A) — the exact `hProdMeas` z-slice shape, from {`hWFDslice`,
      `hLeviSlice`} via `AEStronglyMeasurable.mul`.  PROVED, std-3.
    • `perUCensus_phase10` — `perUCensus_phase9` with `hProdMeas` supplied by `prodMeas_at_witness`.

  ── WHAT REMAINS CARRIED (labelled, satisfiable, never the conclusion).
    • For `witnessFieldDeriv_refined_gate_envelope`: {`Ba`,`Bd` amplitude sup-bounds (E1/E2 gate data);
      `hiso : ‖W z p‖ ≤ Lz·‖z‖` the CENTERED near-isometry (satisfiable at `p = 0` via
      `chartW0_displacement`, D₀ = 0); `hgauss_env` the x-free chart-Gaussian envelope}.
    • The full ∀`z` `hDHrefined₂` (off-gate vanishing `witnessFieldDeriv_offGate_eq_zero` +
      uniform `(u,i,x)`-constant selection wA/CA/CB) is NOT assembled; it stays a labelled carry into
      `profRate_integral₂`/`perUCensus_phase10`.  This is the honest wall to the next brick.
    • PART A slice carries {`hWFDslice`,`hLeviSlice`}: single-variable z-measurabilities, satisfiable
      from `WitnessMeasDeriv.hKmeas_concrete`-style slice facts + Levi z-measurability.

  ── DONT-UNDERCREDIT FINDINGS.
    • The centered displacement bound `chartW0_displacement` (`W z 0 = −z + O(‖z‖²)`, and the internal
      bootstrap `‖W z 0‖ ≤ 2‖z‖`) was ALREADY banked in `InverseChartDisplacement` — the D₀ = 0 gate
      resolution needed no new geometry, only its READING (the near-isometry has no additive constant).
    • The E1 on-gate formula `witnessFieldDeriv_gate_eq` (`dH = G·sc·A + G·∂ᵢA`) and the crude one-term
      `witnessFieldDeriv_gate_envelope` were banked; the refined lever is a two-term REFINEMENT keeping
      the `‖z‖`-moment via `slopeContraction_holder` + `hiso` instead of crudifying to `Bs`.
    • The Hölder step uses banked `norm_le_pi_norm` / `Finset.abs_sum_le_sum_abs` (the same pattern as
      `AmplitudeDataOnCollar`); the sup-norm ℓ∞–ℓ¹ pairing is the correct Cauchy–Schwarz surrogate on
      `Point n = Fin n → ℝ` (NOT the Euclidean inner product — `Point n` is Pi-sup-normed).

  ⚠  J4-453 = Part A (hProdMeas discharged) + Part B (the D₀/(2τ) GATE run: `D₀ = 0`, mass has no
  `1/(2τ)`; the refined on-gate two-term envelope PROVED, grounding `hDHrefined₂`'s scaling).  This
  brick does NOT prove `a₁ = R/6` and makes NO claim of unconditionality.
-/

section AxiomChecks
open QIQTH.ProdMeasAndEnvelope
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms slopeContraction_holder
#print axioms witnessFieldDeriv_refined_gate_envelope
#print axioms prodMeas_at_witness
#print axioms perUCensus_phase10
end AxiomChecks
