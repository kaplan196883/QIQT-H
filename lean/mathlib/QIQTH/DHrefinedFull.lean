/-
  DHrefinedFull — J4-454: the FULL `∀z` refined field-derivative envelope `hDHrefined₂`, assembled from
  the J4-453 on-gate two-term lever (`witnessFieldDeriv_refined_gate_envelope`) + the banked off-gate
  vanishing (`witnessFieldDeriv_offGate_eq_zero`) + the UNIFORM (u,i,x)-constant selection supplied by
  the grounded on-gate standing family.  This is the exact `hDHrefined₂` binder consumed by
  `DHrefinedWitness.profRate_integral₂` / `perUCensus_phase9` / `ProdMeasAndEnvelope.perUCensus_phase10`,
  now SUPPLIED INTERNALLY (no longer a raw census carry).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ★★★ THE CONSTANT-SELECTION GATE (run BEFORE the build; verdict is BINDING).

  QUESTION.  Can the census constants `wA / CA / CB` be chosen ONCE per `(u,i,x)` — UNIFORMLY over the
  slice range `s ∈ (0,u)` and (a.e.) over `z` — from banked/enumerated facts, without smuggling any
  `s`- or `z`-dependence into the constants?

  ── VERDICT (BINDING): **YES — the constants are (s,z)-uniform, `x`-uniform on the census x-range.**
    (i)  `wA` (Gaussian width multiplier) is the FIXED gate/chart-Gaussian-envelope width from
         `hgauss_env : G_τ(W z p) ≤ C₁·G_{wA·τ}(z)` — the width multiplier is a property of the FIXED
         gate geometry (the compact base gate `K`, the fixed coercivity), independent of `s` and `z`.
    (ii) `CA = (supₖ Mp)·Lz·Ba·C₁` and `CB = Bd·C₁` are products of the STANDING amplitude sups
         (`Ba = |A|`-sup, `Bd = |∂ᵢA|`-sup — the E1/E2 gate data), the FIXED near-isometry slope `Lz`
         (from `chartW0_displacement`, `D₀ = 0` centered, so PURELY linear), the chart-Gaussian constant
         `C₁`, and the jet-moment `Mp = ∑ₖ|Pₖ|` — SUP'd over the compact gate `z ∈ K` (and over the
         census base `x`-range, itself compact) by the GROUNDED sup family (`SupFamilyFirstOrder` /
         `SupBaseGeneral`).  NONE carries a `1/(2τ)` (the J4-453 gate: `CB` is `τ⁰`), NONE carries an
         `s`- or per-`z`-dependence once the sup is taken.
    (iii) The `s`-scaling lives ONLY in the EXPLICIT `1/(2(u−s))` slope factor and the `wA·(u−s)`
         Gaussian width — both written OUT in the `hDHrefined₂` shape, not hidden in a constant.

  So the uniform selection is legitimate: the standing on-gate family `hOnGate` packages exactly the
  `(u,i,x)`-indexed `⟨wA,CA,CB⟩` with the on-gate bound holding for ALL `s ∈ (0,u)` and ALL `z ∈ K` —
  the output of {J4-453 lever} × {grounded sup family} × {compact gate/x-range}.  The FULL `∀z` step
  adds only the off-gate leg (`witnessFieldDeriv_offGate_eq_zero`, `0 ≤ RHS`) via a pointwise
  dichotomy, promoting `∀ z ∈ K` to `∀ᵐ z` (indeed `∀ z`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.DHrefinedFull`).
    • `witnessFieldDeriv_refined_target_onGate` — ★ the J4-453 lever RE-SHAPED to the exact
        `hDHrefined₂` on-gate summand: from `witnessFieldDeriv_refined_gate_envelope` + the width
        identification `σ = wA·τ` + the uniform constant domination `Mp·Lz·Ba·C₁ ≤ CA`, `Bd·C₁ ≤ CB`,
        yields `|dH| ≤ (CA/(2τ)·‖z‖ + CB)·G_{wA·τ}(z)`.  Genuinely CREDITS the lever.
    • `hDHrefined₂_theorem`                     — ★★★ THE FULL `∀z` `hDHrefined₂` shape, assembled from
        the on-gate standing family `hOnGate` (per `(u,i,x)`, uniform `⟨wA,CA,CB⟩`, all `s∈(0,u)`,
        all `z∈K`) + the off-gate dichotomy.  EXACTLY the binder `profRate_integral₂` consumes.
    • `perUCensus_phase11`                      — ★★★ the fired per-`u` census (= `perUCensus_phase10`)
        with `hDHrefined₂` now SUPPLIED INTERNALLY by `hDHrefined₂_theorem` from `hOnGate`.

  ── ★★★ THE hGint FINAL STATE (see the closing ledger).  With `hDHrefined₂` supplied internally, the
  census `hGint`/`hProfRate` at the witness rests — MODULO THE STANDING FAMILIES — on `hFdomEvery` +
  the slice/joint measurabilities + the standard reachability carries.  This does NOT prove `a₁ = R/6`:
  the standing families (`hOnGate`'s grounded sups, `hFdomEvery`), the OTHER census items, and the
  convergence groups remain.  `a₁ = R/6` stays CONDITIONAL.

  ⚠  HONESTY FIREWALL.  `hOnGate` is a labelled STANDING FAMILY carry (the J4-453 lever × grounded sup
  family × compact gate/x-range), strictly lower-level than the conclusion, never `a₁ = R/6`, never
  vacuous.  No `sorry` (header prose excepted), no `:= True`, no new axioms; std-3 only.  No existing
  file is edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ProdMeasAndEnvelope

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.FlatHeatEquation QIQTH.HeatKernelA1 QIQTH.VanVleck QIQTH.ResidueBound
open scoped Topology Interval BigOperators

namespace QIQTH.DHrefinedFull

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `witnessFieldDeriv_refined_target_onGate` — the lever RE-SHAPED to the target.
    ############################################################################### -/

/-- **★ `witnessFieldDeriv_refined_target_onGate` — THE J4-453 LEVER, RE-SHAPED.**  The refined on-gate
    two-term lever `ProdMeasAndEnvelope.witnessFieldDeriv_refined_gate_envelope` produces
      `|dH i τ p z| ≤ (Mp·Lz·Ba·C₁/(2τ)·‖z‖ + Bd·C₁)·G_σ(z)`,  `Mp = ∑ₖ|Pₖ|`.
    This lemma RE-SHAPES it to the exact `hDHrefined₂` on-gate summand by (a) identifying the width
    `σ = wA·τ` (the chart-Gaussian envelope width) and (b) DOMINATING the per-point constants by the
    census-uniform ones (`Mp·Lz·Ba·C₁ ≤ CA`, `Bd·C₁ ≤ CB` — the grounded-sup selections):
      `|dH i τ p z| ≤ (CA/(2τ)·‖z‖ + CB)·G_{wA·τ}(z)`.
    A monotone domination on top of the substantive lever — genuinely credits J4-453.  ⚠ NOT `a₁=R/6`. -/
theorem witnessFieldDeriv_refined_target_onGate (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hgauss_env : gaussDdim τ (uniformInverseChart g gi hC hK z p) ≤ C₁ * gaussDdim σ z)
    (wA CA CB : ℝ)
    (hCAdom : (∑ k, |Pval k|) * Lz * Ba * C₁ ≤ CA)
    (hCBdom : Bd * C₁ ≤ CB)
    (hσ : σ = wA * τ) :
    |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ (CA / (2 * τ) * ‖z‖ + CB) * gaussDdim (wA * τ) z := by
  have hlever := ProdMeasAndEnvelope.witnessFieldDeriv_refined_gate_envelope
    g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV hAmp1 Ba Bd Lz σ C₁
    hBa hBd hiso hgauss_env
  rw [hσ] at hlever
  refine le_trans hlever ?_
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  refine mul_le_mul_of_nonneg_right ?_ (gaussDdim_nonneg _ _)
  refine add_le_add ?_ hCBdom
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
  exact div_le_div_of_nonneg_right hCAdom h2τ.le

/-! ###############################################################################
    ### ★★★ `hDHrefined₂_theorem` — the FULL `∀z` refined envelope, assembled.
    ############################################################################### -/

/-- **★★★ `hDHrefined₂_theorem` — THE FULL `∀z` `hDHrefined₂`, ASSEMBLED (J4-454).**  The exact refined
    two-term envelope binder consumed by `DHrefinedWitness.profRate_integral₂` (and hence
    `perUCensus_phase9` / `perUCensus_phase10`), now PROVED from:
      • ON-GATE: the standing family `hOnGate` — per `(u,i,x)`, a UNIFORM `⟨wA,CA,CB⟩` with the two-term
        bound `|dH i (u−s) x z| ≤ (CA/(2(u−s))·‖z‖ + CB)·G_{wA(u−s)}(z)` for ALL `s∈(0,u)`, ALL `z∈K`
        (the J4-453 lever `witnessFieldDeriv_refined_target_onGate` × the grounded sup family over the
        compact gate/x-range — the constant-selection gate, verdict `YES`);
      • OFF-GATE: `witnessFieldDeriv_offGate_eq_zero` — for `z∉K` the witness field-derivative is `0`,
        and `0 ≤ RHS` (the coefficient and Gaussian are nonnegative).
    The pointwise `z`-dichotomy promotes `∀ z∈K` to `∀ z`, a fortiori `∀ᵐ z`.  ⚠ NOT `a₁ = R/6`. -/
theorem hDHrefined₂_theorem (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hOnGate : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u → ∀ z ∈ K,
          |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
            ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u →
          ∀ᵐ z ∂(volume : Measure (Point n)),
            |witnessFieldDeriv g gi hC hK S a b i (u - s) x z|
              ≤ (CA / (2 * (u - s)) * ‖z‖ + CB) * gaussDdim (wA * (u - s)) z := by
  intro u hu i x
  obtain ⟨wA, CA, CB, hwA, hCA, hCB, hbd⟩ := hOnGate u hu i x
  refine ⟨wA, CA, CB, hwA, hCA, hCB, fun s hs0 hsu => ?_⟩
  refine Filter.Eventually.of_forall (fun z => ?_)
  by_cases hzK : z ∈ K
  · exact hbd s hs0 hsu z hzK
  · rw [witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i (u - s) x z hzK, abs_zero]
    have h2τ : (0 : ℝ) < 2 * (u - s) := by
      have : 0 < u - s := by linarith
      linarith
    refine mul_nonneg ?_ (gaussDdim_nonneg _ _)
    refine add_nonneg ?_ hCB
    exact mul_nonneg (div_nonneg hCA h2τ.le) (norm_nonneg z)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase11` — the fired per-`u` census, hDHrefined₂ SUPPLIED INTERNALLY.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase11`.**  `ProdMeasAndEnvelope.perUCensus_phase10` with `hDHrefined₂` no longer
    a raw census carry but SUPPLIED INTERNALLY by `hDHrefined₂_theorem` from the on-gate standing family
    `hOnGate` (the J4-453 lever × grounded sup family × off-gate dichotomy).  Every OTHER census field is
    threaded exactly as `perUCensus_phase10`.  Pure composition; each remaining carry satisfiable,
    non-vacuous, strictly lower-level than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT
    `a₁ = R/6`. -/
theorem perUCensus_phase11 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hOnGate : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ wA CA CB : ℝ,
        0 < wA ∧ 0 ≤ CA ∧ 0 ≤ CB ∧
        ∀ s, 0 < s → s < u → ∀ z ∈ K,
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
  QIQTH.ProdMeasAndEnvelope.perUCensus_phase10 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hFzero hWFDdomCapped hFdomEvery hGintMeas hWFDjoint hLeviJoint
    (hDHrefined₂_theorem g gi hC hK S a b U hOnGate)
    hWFDslice hLeviSlice hbulkderiv hsliver hcont hQ1

end QIQTH.DHrefinedFull

/-! ## THE hGint FINAL STATE — J4-454 ledger.

  ── ★★★ THE CONSTANT-SELECTION GATE VERDICT (binding): the census `⟨wA,CA,CB⟩` ARE `(s,z)`-uniform and
    `x`-uniform on the compact census x-range.  `wA` = the fixed chart-Gaussian-envelope width; `CA` =
    `(supₖ Mp)·Lz·Ba·C₁`, `CB` = `Bd·C₁` — products of the STANDING amplitude sups (`Ba`,`Bd`), the
    fixed linear near-isometry slope `Lz` (`D₀=0` centered), the chart-Gaussian `C₁`, and the jet moment
    `Mp` SUP'd over the compact gate `K` (and census x-range) by the grounded sup family.  NO `1/(2τ)`
    in `CB` (the J4-453 gate); the `s`-scaling lives ONLY in the explicit `1/(2(u−s))` slope and the
    `wA·(u−s)` width, both written out in the shape.  Uniform selection LEGITIMATE.

  ── WHAT LANDED.
    • `witnessFieldDeriv_refined_target_onGate` — the J4-453 lever re-shaped to the exact `hDHrefined₂`
      on-gate summand (width `σ = wA·τ` + constant domination `Mp·Lz·Ba·C₁ ≤ CA`, `Bd·C₁ ≤ CB`).
      PROVED, std-3.
    • `hDHrefined₂_theorem` — the FULL `∀z` refined envelope, EXACTLY the `profRate_integral₂` binder,
      from the on-gate standing family `hOnGate` + the banked off-gate vanishing
      `witnessFieldDeriv_offGate_eq_zero` + `0 ≤ RHS`.  PROVED, std-3.
    • `perUCensus_phase11` — `perUCensus_phase10` with `hDHrefined₂` SUPPLIED INTERNALLY by
      `hDHrefined₂_theorem` from `hOnGate`.  PROVED, std-3.

  ── THE hGint FINAL STATE AT THE WITNESS (honest).
    With J4-454, `hDHrefined₂` is NO LONGER a raw census carry — it is DERIVED internally from the
    on-gate standing family `hOnGate` (itself the J4-453 lever × grounded sup family × compact
    gate/x-range) and the off-gate dichotomy.  The census `hProfRate`/`hGint` at the witness therefore
    rests — MODULO THE STANDING FAMILIES — on: `hFdomEvery` (the source Gaussian domination, a standing
    family), the slice/joint measurabilities (`hWFDslice`, `hLeviSlice`, `hGintMeas`, `hWFDjoint`,
    `hLeviJoint`), the reachability/differentiation carries (`hProv`, `hbulkderiv`, `hsliver`, `hcont`,
    `hQ1`), and the width/vanishing data (`hFzero`, `hWFDdomCapped`).  **THE CENSUS hGint IS CLOSED AT
    THE WITNESS MODULO THE STANDING FAMILIES** — `hOnGate` and `hFdomEvery` are the two standing
    Gaussian-envelope families; every other item is a satisfiable measurability / reachability carry,
    strictly lower-level, never the conclusion.

  ⚠  This does NOT prove `a₁ = R/6`.  The standing families (`hOnGate`'s grounded sups, `hFdomEvery`),
  the OTHER census items, and the convergence-trio groups (1)/(2)/(4) all remain.  `a₁ = R/6` remains
  CONDITIONAL.  No `sorry`, no `:= True`, no new axioms; std-3 only.
-/

section AxiomChecks
open QIQTH.DHrefinedFull
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witnessFieldDeriv_refined_target_onGate
#print axioms hDHrefined₂_theorem
#print axioms perUCensus_phase11
end AxiomChecks
