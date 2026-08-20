/-
  HZMassLeviBaseEnvelope — J4-882: the CONCRETE Levi-base Gaussian envelope for `BL`, and the
  WIDTH-`2s` companion of the `hzmass` peak/Gaussian split — plus the HONEST verdict on whether the
  banked parametrix Levi bound closes the deep `hzmass` `z`-mass wall of
  `MixedDirectionsFieldHessianEnvelope`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick (i) specializes the banked
  J4-114 whole-gate Levi-series domination `leviSeries_gatedWitnessN1_dominated` to the `hzmass`
  base-density slice `(τ,p,q) := (s,z,0)`, delivering the CONCRETE base-`z` Gaussian envelope on the
  Levi factor `BL`, and (ii) supplies the WIDTH-`2s` companion of the J4-881 split reduction.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## FINDING A — the banked Levi bound DOES supply a base-`z` Gaussian envelope for `BL`, but at
  ##             WIDTH `2s`, NOT width `t−s`.

  The J4-114 domination (`HeatResidualBound.leviSeries_gatedWitnessN1_dominated`) gives, for the
  CONCRETE gated van-Vleck residual `E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)` and given
  the single M1 base joint strong-measurability `hEmeas`,
      `|leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q`.
  Since `baseKernelW 2 0 τ p q = τ^0 · gaussDdim (2·τ) (p − q) = gaussDdim (2·τ) (p − q)`
  (`baseKernelW_zero_apply`), specializing `(τ,p,q) := (s,z,0)` gives EXACTLY the `hzmass` Levi factor
      `|leviSeries E s z 0| ≤ C_L · gaussDdim (2·s) z`   (`leviBase_gaussDdim2s_envelope`).
  This is a genuine BASE-`z` Gaussian envelope — the object `HZMassPeakGaussianSplit`'s `hBLgauss` slot
  wants — BUT its width is `2·s` (time-since-start), whereas the J4-881 split reduction
  `hzmass_of_peak_BF_gaussian_BL` hard-codes the width `t − s` (time-to-endpoint).  The two Gaussians are
  NOT inter-dominable uniformly in `z`: `gaussDdim (2s) z ≤ κ · gaussDdim (t−s) z` for all `z` forces
  `2s ≤ t − s`, i.e. `s ≤ t/3`, which FAILS on the upper part of the window `uIoc 0 (t − εₘ)` (`s → t`).
  So the banked bound does NOT feed the J4-881 split `hBLgauss` slot directly.

  ## FINDING B — the WIDTH is IRRELEVANT to the `(t−s)⁻¹` target; the split works at width `2s`.

  The `(t−s)⁻¹` in `hzmass`'s target `∫z BL·BF ≤ C·(t−s)⁻¹` is carried ENTIRELY by the matched power
  `Ppk·CB ≤ C·(t−s)⁻¹` — NOT by the Gaussian width, because `gaussDdim w` has total mass `1` for EVERY
  `w > 0` (`gaussDdim_mass_one`).  `hzmass_of_peak_BF_gaussian2s_BL` PROVES the width-`2s` companion of
  the J4-881 split: from
    • `hspos` — `0 < s` on the window (a genuine window fact when `t − εₘ > 0`),
    • `hBFpeak` — `BF s z ≤ Ppk s`  (`z`-UNIFORM peak; the ONLY bound J4-868 allows for `BF`),
    • `hBLgauss` — `BL s z ≤ CB s · gaussDdim (2·s) z`  (the CONCRETE Levi envelope of FINDING A),
    • `hpow` — `Ppk s · CB s ≤ C · (t−s)⁻¹`  (the matched time-power bookkeeping),
    • nonnegativity + integrability,
  the mass-one reduction at width `2s` closes `∫z BL·BF ≤ C·(t−s)⁻¹`.  This is the correct-width
  companion to `HZMassPeakGaussianSplit.hzmass_of_peak_BF_gaussian_BL`; the two differ ONLY in the
  Gaussian width the Levi factor is bounded by, and BOTH reduce `hzmass` to the SAME residual triple
  {peak `BF`, matched power `hpow`, integrability}.

  ## FINDING C — the SOLE remaining wall is the matched power `Ppk · CB ≤ C·(t−s)⁻¹`, and it is NOT
  ##             met by the CURRENT ingredients for `n ≥ 3`.  (RIGOROUS PROSE; not formalized here.)

  With FINDING A the Levi coefficient is `CB s := C_L`, a CONSTANT (no `(t−s)`-decay: the whole-gate
  parametrix estimate carries no endpoint-time gain).  The J4-868 peak is
  `Ppk s = gaussDdim (t−s) 0 · Poly_sup`, and `gaussDdim (t−s) 0 = ((√(4π(t−s)))⁻¹)^n ≍ (t−s)^{−n/2}`
  (`ResidueBound.gaussDdim_eq_exp` at `v = 0`).  Hence `Ppk s · CB s ≍ (t−s)^{−n/2}`, and the target
  requires `(t−s)^{−n/2} ≤ C·(t−s)⁻¹` UNIFORMLY as `s → t` — i.e. `(t−s)^{1 − n/2} ≤ C`, which HOLDS
  for `n ≤ 2` (bounded near `s = t`, closing `hzmass` there) but FAILS for `n ≥ 3` (`1 − n/2 < 0`,
  `(t−s)^{1−n/2} → ∞` as `s → t`).  CONSEQUENCE: `hzmass` does NOT close through the peak route with the
  current whole-gate Levi coefficient for physical `n = 4`.  The honest remaining analytic content is a
  SHARP field-Hessian peak bound `Ppk s ≤ C·(t−s)^{n/2−1}·(t−s)⁻¹` (i.e. control of the ACTUAL
  field-Hessian magnitude, not its `(t−s)^{−n/2}` chart-Gaussian DOMINATOR), OR an endpoint-time gain
  `CB s ≍ (t−s)^{n/2−1}` in the Levi coefficient.  Neither is currently banked.  This is recorded as
  rigorous prose (an unformalized `r ↓ 0` divergence of `r^{1−n/2}`); the file ships only the two clean
  reductions above so that no `sorry`/asymptotic-limit lemma enters the axiom surface.  NOT `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.HZMassLeviBaseEnvelope`).
    • `leviBase_gaussDdim2s_envelope` — ★★★ the CONCRETE base-`z` Gaussian envelope on `BL` from the
      banked J4-114 domination (conditional on the SAME single M1 `hEmeas`), at width `2s`.
    • `hzmass_of_peak_BF_gaussian2s_BL` — ★★ the WIDTH-`2s` companion of the J4-881 split reduction.
    • `hzmass_gaussian2s_split_nonvacuous` — the split-companion antecedents are jointly inhabited
      (zero envelopes), no J4-548/847-style unsatisfiable hypothesis.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HZMassIntegrabilityAttempt
import QIQTH.GatedWitnessPackage
import QIQTH.ParametrixHEboundWiring
import QIQTH.ConvApproximants

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.ChartJetXUniformBound
open scoped Topology BigOperators ContDiff

namespace QIQTH.HZMassLeviBaseEnvelope

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the CONCRETE base-`z` Gaussian envelope on the Levi factor `BL`.
    ############################################################################### -/

/-- **★★★ `leviBase_gaussDdim2s_envelope`.**  The CONCRETE base-`z` Gaussian envelope on the `hzmass`
    Levi factor.  Specializing the banked J4-114 whole-gate Levi-series domination
    `HeatResidualBound.leviSeries_gatedWitnessN1_dominated` to the base-density slice `(τ,p,q) :=
    (s,z,0)` and rewriting `baseKernelW 2 0 s z 0 = gaussDdim (2·s) z` (`baseKernelW_zero_apply`,
    `sub_zero`), we obtain — for the CONCRETE gated van-Vleck witness `vanVleckGatedWitness g gi hC hK
    S a b` (which is DEFINITIONALLY `gatedKernel K S (globalCutoffParametrixWitnessN 1 …)`, the
    dominated bound's kernel) and given the single M1 base joint strong-measurability `hEmeas` — the
    envelope
      `|leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0| ≤ C_L · gaussDdim (2·s) z`.
    This is the EXACT shape of the `hzmass` Levi factor `BL`, at Gaussian width `2·s`.  The ONLY
    conditional input is `hEmeas` — the same M1 wall the J4-114 bound carries (its concrete supplier is
    `GatedRepSFix.tripleHEmeas_concrete_v4`, modulo the strong-measurability interface bridge).  NOT
    `a₁ = R/6`. -/
theorem leviBase_gaussDdim2s_envelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n),
      StronglyMeasurable (fun w : ℝ × Point n × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) w.1 w.2.1 w.2.2) →
        ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T →
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ C_L * gaussDdim (2 * s) z := by
  obtain ⟨a, b, C, ha, hab, hC0, S, _hheat, hlevi⟩ :=
    leviSeries_gatedWitnessN1_dominated g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0 hn T hT
  refine ⟨a, b, ha, hab, S, ?_⟩
  intro hEmeas
  obtain ⟨C_L, hCL0, hbound⟩ := hlevi hEmeas
  refine ⟨C_L, hCL0, ?_⟩
  intro s z hs hsT
  have hb := hbound s z 0 hs hsT
  rw [baseKernelW_zero_apply] at hb
  simpa [sub_zero] using hb

/-! ###############################################################################
    ### §B — the WIDTH-`2s` companion of the J4-881 split reduction.
    ############################################################################### -/

/-- **★★ `hzmass_of_peak_BF_gaussian2s_BL`.**  The WIDTH-`2s` companion of
    `HZMassPeakGaussianSplit.hzmass_of_peak_BF_gaussian_BL`.  The `(t−s)⁻¹` target is carried by the
    matched power `Ppk·CB`, NOT by the Gaussian width (mass-one holds for EVERY positive width), so the
    split closes with the CONCRETE width-`2s` Levi envelope of §A.  Given, a.e. `s` in the window:
      • `hspos` — `0 < s`  (a genuine window fact when `t − εₘ > 0`; needed for `gaussDdim (2s)`
                  mass-one);
      • `hBFpeak` — `BF s z ≤ Ppk s`  (the `z`-CONSTANT peak from J4-868);
      • `hBLnn` — `0 ≤ BL s z`;
      • `hBLgauss` — `BL s z ≤ CB s · gaussDdim (2·s) z`  (the §A Levi envelope);
      • `hPpknn` — `0 ≤ Ppk s`;
      • `hpow` — `Ppk s · CB s ≤ C · (t−s)⁻¹`  (matched time-power bookkeeping),
      • window positivity `hpos` and product integrability `hint`,
    the mass-one reduction at width `2s` gives `∫z BL·BF ≤ C·(t−s)⁻¹`.  NOT `a₁ = R/6`. -/
theorem hzmass_of_peak_BF_gaussian2s_BL
    (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ) (Ppk CB : ℝ → ℝ)
    (hCnn : 0 ≤ C)
    (hspos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < s)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BF s z ≤ Ppk s)
    (hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, 0 ≤ BL s z)
    (hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z ≤ CB s * gaussDdim (2 * s) z)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        0 ≤ Ppk s)
    (hpow : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Ppk s * CB s ≤ C * (t - s)⁻¹) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ C * (t - s)⁻¹ := by
  filter_upwards [hspos, hpos, hint, hBFpeak, hBLnn, hBLgauss, hPpknn, hpow]
    with s hsp hpp hii hpk hbn hbg hpn hpw hs
  have hs2 : 0 < 2 * s := by have := hsp hs; linarith
  have hii := hii hs
  -- pointwise product envelope `BL·BF ≤ (Ppk·CB)·gaussDdim (2s) z`.
  have henv : ∀ z : Point n,
      BL s z * BF s z ≤ (Ppk s * CB s) * gaussDdim (2 * s) z := by
    intro z
    have hpks := hpk hs z
    have hbns := hbn hs z
    have hbgs := hbg hs z
    have hpns := hpn hs
    have step1 : BL s z * BF s z ≤ BL s z * Ppk s :=
      mul_le_mul_of_nonneg_left hpks hbns
    have step2 : BL s z * Ppk s ≤ (CB s * gaussDdim (2 * s) z) * Ppk s :=
      mul_le_mul_of_nonneg_right hbgs hpns
    have step3 : (CB s * gaussDdim (2 * s) z) * Ppk s
        = (Ppk s * CB s) * gaussDdim (2 * s) z := by ring
    calc BL s z * BF s z
        ≤ BL s z * Ppk s := step1
      _ ≤ (CB s * gaussDdim (2 * s) z) * Ppk s := step2
      _ = (Ppk s * CB s) * gaussDdim (2 * s) z := step3
  -- integrate the envelope; the Gaussian has total mass `1` at width `2s`.
  have hgint : Integrable (fun z : Point n => gaussDdim (2 * s) z) volume :=
    gaussDdim_integrable' (2 * s) hs2
  have henvint : Integrable (fun z : Point n => (Ppk s * CB s) * gaussDdim (2 * s) z) volume :=
    hgint.const_mul (Ppk s * CB s)
  have hmono : (∫ z, BL s z * BF s z)
      ≤ ∫ z : Point n, (Ppk s * CB s) * gaussDdim (2 * s) z :=
    integral_mono hii henvint henv
  have hval : (∫ z : Point n, (Ppk s * CB s) * gaussDdim (2 * s) z) = Ppk s * CB s := by
    rw [integral_const_mul, gaussDdim_mass_one (2 * s) hs2, mul_one]
  rw [hval] at hmono
  exact le_trans hmono (hpw hs)

/-! ###############################################################################
    ### §C — NON-VACUITY of the width-`2s` split companion.
    ############################################################################### -/

/-- **Non-vacuity of the width-`2s` split companion.**  The genuinely-chosen antecedents are jointly
    inhabited at the zero envelopes `BL ≡ 0`, `BF ≡ 0`, `Ppk ≡ 0`, `CB ≡ 0`: the product is integrable
    (`0`), `BF ≤ 0`, `0 ≤ BL`, `BL ≤ 0·gaussDdim (2s) = 0`, `0 ≤ Ppk`, and `Ppk·CB = 0 ≤ C·(t−s)⁻¹` on
    the positive window (`C ≥ 0`, `(t−s)⁻¹ > 0`), yielding `∫z 0 = 0 ≤ C·(t−s)⁻¹`.  Window facts
    `hspos`/`hpos` are properties of `(t,m)` (carried, not asserted false).  No J4-548/847-style
    unsatisfiable antecedent. -/
theorem hzmass_gaussian2s_split_nonvacuous {n : ℕ} (t : ℝ) (m : ℕ) (C : ℝ) (hCnn : 0 ≤ C)
    (hspos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < s)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ _z : Point n, (0 : ℝ) * 0) ≤ C * (t - s)⁻¹ := by
  have hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n =>
        (fun _ _ => (0 : ℝ)) s z * (fun _ _ => (0 : ℝ)) s z) volume := by
    refine ae_of_all _ (fun s _ => ?_)
    simp only [mul_zero]
    exact integrable_zero _ _ _
  have hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ z => le_refl 0)
  have hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, 0 ≤ (fun _ _ => (0 : ℝ)) s z :=
    ae_of_all _ (fun s _ z => le_refl 0)
  have hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z
        ≤ (fun _ => (0 : ℝ)) s * gaussDdim (2 * s) z := by
    refine ae_of_all _ (fun s _ z => ?_)
    simp
  have hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      0 ≤ (fun _ => (0 : ℝ)) s :=
    ae_of_all _ (fun s _ => le_refl 0)
  have hpow : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (fun _ => (0 : ℝ)) s * (fun _ => (0 : ℝ)) s ≤ C * (t - s)⁻¹ := by
    filter_upwards [hpos] with s hposs hs
    have hts : 0 < t - s := hposs hs
    have : (0 : ℝ) ≤ C * (t - s)⁻¹ := mul_nonneg hCnn (le_of_lt (inv_pos.mpr hts))
    simpa using this
  have h := hzmass_of_peak_BF_gaussian2s_BL (n := n) t m C
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    hCnn hspos hpos hint hBFpeak hBLnn hBLgauss hPpknn hpow
  filter_upwards [h] with s hs hsU
  exact hs hsU

end QIQTH.HZMassLeviBaseEnvelope

section AxiomChecks
open QIQTH.HZMassLeviBaseEnvelope
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms leviBase_gaussDdim2s_envelope
#print axioms hzmass_of_peak_BF_gaussian2s_BL
#print axioms hzmass_gaussian2s_split_nonvacuous
end AxiomChecks
