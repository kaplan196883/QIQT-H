/-
  DaLimHardTranche — J4-333: the HARD TRANCHE (items 4 + 5) of the `hDaLimLU_concrete` remainder
  (the dependency-ordered `X2` remainder classified by J4-331 `DaLimCensusRecon`, whose items 1–3
  were discharged in J4-332 `DaLimEasyTranche`).  Attacks item 4 (the √ε sliver amplitude `hbnd`)
  and item 5 (the width-3/2 residual domination `hEdom`), at the concrete `N = 1` van-Vleck gate
  `H_G := vanVleckGatedWitness g gi hChr hK S a b`, source `F := leviSeries (heatOp g gi H_G)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Every
  theorem's docstring restates this.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited, nothing committed.  `hDaLimLU_concrete` remains the concrete-gate `Da`-limit
  and is NOT the `a₁ = R/6` diagonal.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## A0 — THE RECON (exact binders + inventory + the item-5 width-entry map).

  ── ITEM 4 — `hbnd` (the √ε sliver amplitude; companions `D0`,`D1`,`hD0`,`hD1`) ─────────────────────
     BINDERS (verbatim from `DaLimLUConcreteDischarge.hDaLimLU_concrete`, lines 159–163):
       `D0 D1 : Fin n → ℝ`,  `hD0 : ∀ i, 0 ≤ D0 i`,  `hD1 : ∀ i, 0 ≤ D1 i`,
       `hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
           |∫ s in (u − ε_m)..u, ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u − s) z · F s z 0|
             ≤ D0 i · (2·√ε_m) + D1 i · ε_m`.
     `hD2Hexpand` INVENTORY.  The census names `AmplitudeDerivativeData.hD2Hexpand` as the missing
     input.  It is banked as a STRUCTURE FIELD (`AmplitudePackage.AmplitudeDerivativeData`, J4-126):
     the bundle carries `Aamp/A1amp/A2amp` (the three amplitude components), the Leibniz–Gaussian
     3-term identity `hD2Hexpand` for the CONCRETE `witnessSecondXDeriv` (the ONE hard geometric input,
     isolated — see the `AmplitudePackage` header BLOCKER: the chart-image Gaussian argument `W z 0`),
     the sup-bounds `hAampBdd/hA1ampBdd/hA2ampBdd`, the Levi width-2 domination `hFdom`, the base
     measurabilities and the term-1 Lipschitz carry `hqLip`.  The DELIVERABLE
     `amplitudePackage_sliver_bound` (banked) consumes the bundle and yields EXACTLY the `hbnd` RHS
     with
       `D0 i = L·(15/2·n) + (3/4)·(M₁·(C_L·gaussDdim aa 0))`,   `D1 i = M₂·(C_L·gaussDdim aa 0)`.
     VERDICT — DISCHARGED (A1 `hbnd_concrete`) from a PER-COORDINATE bundle `∀ i, AmplitudeDerivativeData
     … i T τ₀` plus the SATISFIABLE window/short-time carries `aa ≤ u ≤ T` and `ε_m < aa/2`, `ε_m ≤ τ₀`.
     SAT: the sliver window conditions are a genuine short-time budget (`ε_m → 0`, so `ε_m < aa/2`
     holds for a large-enough uniform time floor `aa`); NO uniform-in-s singularity — the `√ε` rate is
     the vanishing sliver's measure.  The one hard input `hD2Hexpand` is CARRIED (bundle field), never
     fabricated; it is the derivative-layer geometry, not the conclusion.

  ── ITEM 5 — `hEdom` (the width-3/2 residual domination) ────────────────────────────────────────────
     BINDER (verbatim, `DaLimLUConcreteDischarge` line 166–168):
       `hEdom : ∀ τ, 0 < τ → ∀ p q,
           |heatOp g gi H_G τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p − q)`.
     ⚠ THE DIRECTION.  `gaussDdim ((3/2)·τ)` decays FASTER than `gaussDdim (2·τ)` (`3/2 < 2`), so a
     NAKED width-2 bound does NOT imply width-3/2:  pointwise `gaussDdim(2τ)(z) = (3/4)^{n/2}·
     exp(+‖z‖²/(24τ))·gaussDdim((3/2)τ)(z)`, whose extra factor is UNBOUNDED in the tail.  Narrowing
     is only possible when an EXPOSED polynomial prefactor (`r²/τ`-shaped, from a derivative hit)
     supplies the width slack.

     THE WIDTH-ENTRY MAP of the banked `hEbound`/residual derivation.
       • CONCRETE GATED, width **2**, GLOBAL (∀ p q): `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final`
         (≡ `DataPileWitnessAudit.hEboundFull_from_geometry_existentialGate`) gives, for the
         provider-chosen `(a,b,S)`, `|heatOp g gi H_G τ p q| ≤ C·(1+t)·baseKernelW 2 0 τ p q`
         (`= C·(1+t)·gaussDdim (2τ)(p−q)`, `τ ≤ t`).  This has NO exposed polynomial (the polynomial
         was ABSORBED into width 2 already, deep in the `_lin` / L3–L4 coefficient chain in
         `CoeffU1Fix.lean`), so it CANNOT be narrowed to 3/2 pointwise.  The width `2` is PINNED here.
       • UNGATED IN-CHART, width **3/2**, PER-BASE-POINT: `WidthMarginEngine.globalWitness_residual_
         bound_inChart_final_narrow` (the M2 engine RE-RUN at the narrow target) already delivers
         `|heatOp g gi (globalCutoffParametrixWitness … Vmap) τ (φ_q v) q| ≤ B·gaussDdim ((3/2)·τ) v`.
         The width-3/2 residual bound is thus REACHABLE — but only in the ungated, per-base-point,
         chart-recentered form, and its assembly to the GLOBAL GATED shape (all `p,q`) is the C4c
         far-field / gate-compatibility wall, UNSOLVED at BOTH widths (only the width-2 gated-global
         `_final` is banked, via the `_lin` chain that is width-2-pinned).
     THE RE-RUNNABLE ABSORPTION STEP IS BANKED at the Gaussian level:
       `WidthMarginEngine.gaussDdim_le_gaussDdim_narrow`   : `G_τ v ≤ √(3/2)ⁿ·G_{(3/2)τ} v`;
       `WidthMarginEngine.rncRadialSq_mul_gaussDdim_le_narrow` : `r²·G_τ v ≤ √(3/2)ⁿ·12·τ·G_{(3/2)τ} v`.
     VERDICT — CONDITIONAL BRIDGE (A2 `hEdom_of_gaussPoly_residual`) + reusable engine
     (`gaussian_beats_power`).  `hEdom_concrete` is NOT bank-dischargeable as stated: the global gated
     width-3/2 residual bound would require a `_narrow` sibling of the width-2 `_final` (a re-run of the
     `_lin`/L4 coefficient chain at the narrow target, inside `CoeffU1Fix.lean` — a READ-ONLY file).
     What IS provable NOW and reusable: the bound-level width-narrowing bridge — from the honest
     PRE-COLLAPSE exposed-polynomial residual shape `|heatOp| ≤ P·((r²/τ + 1)·G_τ)` (the natural
     width-1 residual of the `N=1` parametrix, ONE derivative hit ⟹ one `r²/τ` factor) the width-3/2
     `hEdom` FOLLOWS, via the banked narrow absorption family.  The named residue is exactly that
     exposed-polynomial residual bound (which the banked chain collapses to width 2 instead of
     exposing).  Plus the reusable exp-absorption engine `gaussian_beats_power`
     (`(r²/s)^k·e^{−a r²/s} ≤ (k!/(a−a')^k)·e^{−a' r²/s}`), the `∀ k` generalization of the bank's
     `gaussian_beats_linear/quadratic` (β1/β2), proved from the crude single-term exp-series bound
     `GaussianPolyBound.pow_mul_exp_neg_le_factorial`.

  ## SUMMARY of the updated `Da`-limit remainder (post J4-333).
     1–3 DONE (J4-332).  4 `hbnd` DONE (A1, modulo the carried `AmplitudeDerivativeData` bundle whose
     ONE hard field is `hD2Hexpand`).  5 `hEdom` REDUCED to the honest named residue (the exposed-
     polynomial residual bound `hraw`) via the conditional bridge; the reusable absorption engine
     landed.  6 `hLapFull` (the Laplacian-comparison wall) remains — the deepest, out of scope here.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLUConcreteDischarge
import QIQTH.AmplitudePackage
import QIQTH.WidthMarginEngine

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel QIQTH.RadialDistance
open QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimHardTranche

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### A1 — ITEM 4: the √ε sliver amplitude `hbnd`, discharged via the amplitude package.
    ############################################################################### -/

/-- **★ A1 (ITEM 4) — `hbnd_concrete`.**  The concrete-gate `hbnd` binder (with its `D0`/`D1`/`hD0`/
    `hD1` companions produced as a package): the second-`x`-derivative sliver of the `N = 1` van-Vleck
    witness obeys the `√ε` amplitude bound
      `|∫ s in (u−ε_m)..u, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0| ≤ D0 i·(2√ε_m) + D1 i·ε_m`
    for every coordinate `i`, truncation index `m`, and window time `u ∈ U`, with
      `D0 i = L·(15/2·n) + (3/4)·(M₁·(C_L·gaussDdim aa 0))`,   `D1 i = M₂·(C_L·gaussDdim aa 0)`
    the amplitude moduli of the per-coordinate `AmplitudeDerivativeData` bundle.  Route: the banked
    `HeatResidualBound.amplitudePackage_sliver_bound` (which discharges the sliver interface for the
    concrete witness modulo the bundle), applied at each `i` with `ε := ε_m`, the fixed uniform time
    floor `aa`, and the SATISFIABLE short-time carries `ε_m < aa/2` (`hεaa`) and `ε_m ≤ τ₀` (`hετ₀`).

    Carried (each genuine, none the conclusion, none vacuous):
      • `data i` — the amplitude bundle for coordinate `i` (its ONE hard field is `hD2Hexpand`, the
        Leibniz–Gaussian identity for the concrete second `x`-derivative — the derivative-layer
        geometry, CARRIED not fabricated);
      • the window `aa ≤ u ≤ T` (`hau`/`hUT`) and short-time budget `hεaa`/`hετ₀` — a genuine
        vanishing-sliver window (`ε_m → 0`), no uniform-in-s singularity.
    ⚠ NOT `a₁ = R/6`. -/
theorem hbnd_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T τ₀ aa : ℝ) (haa : 0 < aa)
    (data : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b F i T τ₀)
    (hau : ∀ u ∈ U, aa ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2)
    (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀) :
    ∃ D0 D1 : Fin n → ℝ, (∀ i, 0 ≤ D0 i) ∧ (∀ i, 0 ≤ D1 i) ∧
      ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m := by
  refine ⟨fun i => (data i).L * (15 / 2 * (n : ℝ))
            + 3 / 4 * ((data i).M₁ * ((data i).C_L * gaussDdim aa (0 : Point n))),
          fun i => (data i).M₂ * ((data i).C_L * gaussDdim aa (0 : Point n)),
          ?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg (data i).hL (by positivity))
      (mul_nonneg (by norm_num)
        (mul_nonneg (data i).hM₁
          (mul_nonneg (data i).hC_L (QIQTH.ResidueBound.gaussDdim_nonneg _ _))))
  · intro i
    exact mul_nonneg (data i).hM₂
      (mul_nonneg (data i).hC_L (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
  · intro i m u hu
    exact amplitudePackage_sliver_bound g gi hChr hK S a b F i T τ₀ (data i)
      u (epsSeq m) aa haa (hau u hu) (hUT u hu)
      (epsSeq_pos m).le (hεaa m) (hετ₀ m)

/-! ###############################################################################
    ### A2 — ITEM 5: the reusable exp-absorption engine and the width-3/2 conditional bridge.
    ############################################################################### -/

/-- **★ A2 (ITEM 5, engine) — `gaussian_beats_power`.**  The `∀ k` generalization of the bank's
    `GaussianJetTheorem.gaussian_beats_linear/quadratic` (β1/β2): for `a′ < a`, `s > 0`, every real
    `r`, every `k : ℕ`,
      `(r²·s⁻¹)^k · exp(−a r²/s)  ≤  (k! / (a−a')^k) · exp(−a' r²/s)`.
    Each `r²/s` factor (a derivative hit on the Gaussian) is absorbed against the exponent gap `a−a'`
    at the crude cost `k!/(a−a')^k`.  Proof: split `exp(−a r²/s) = exp(−a' r²/s)·exp(−v)` with
    `v := (a−a')·(r²/s) ≥ 0`, rewrite `(r²·s⁻¹)^k = v^k/(a−a')^k`, and absorb the single term
    `v^k·exp(−v) ≤ k!` via `GaussianPolyBound.pow_mul_exp_neg_le_factorial` (the crude single-term
    exp-series bound, itself from Mathlib's `Real.pow_div_factorial_le_exp`).  The reusable engine a
    width-narrowing re-run of the residual chain consumes.  ⚠ NOT `a₁ = R/6`. -/
theorem gaussian_beats_power (a a' : ℝ) (haa' : a' < a) {s : ℝ} (hs : 0 < s) (r : ℝ) (k : ℕ) :
    (r ^ 2 * s⁻¹) ^ k * Real.exp (-(a * r ^ 2 / s))
      ≤ ((k.factorial : ℝ) / (a - a') ^ k) * Real.exp (-(a' * r ^ 2 / s)) := by
  have hd : (0 : ℝ) < a - a' := by linarith
  have hcpos : (0 : ℝ) < (a - a') ^ k := pow_pos hd k
  have hrs : (0 : ℝ) ≤ r ^ 2 / s := by positivity
  set v : ℝ := (a - a') * (r ^ 2 / s) with hvdef
  have hv0 : 0 ≤ v := mul_nonneg hd.le hrs
  -- the single-term exp-series absorption
  have hkey : v ^ k * Real.exp (-v) ≤ (k.factorial : ℝ) :=
    QIQTH.GaussianPolyBound.pow_mul_exp_neg_le_factorial hv0 k
  -- split the exponent
  have hexp : Real.exp (-(a * r ^ 2 / s)) = Real.exp (-(a' * r ^ 2 / s)) * Real.exp (-v) := by
    rw [← Real.exp_add]; congr 1; rw [hvdef]; field_simp; ring
  -- express the power
  have hpk : (r ^ 2 * s⁻¹) ^ k = v ^ k / (a - a') ^ k := by
    have hvk : v ^ k = (a - a') ^ k * (r ^ 2 * s⁻¹) ^ k := by
      rw [hvdef, show (r : ℝ) ^ 2 / s = r ^ 2 * s⁻¹ from div_eq_mul_inv _ _, mul_pow]
    rw [hvk, mul_div_cancel_left₀ _ (pow_ne_zero k hd.ne')]
  -- the reduced inequality after dividing by `(a−a')^k`
  have hstep : v ^ k / (a - a') ^ k * Real.exp (-v) ≤ (k.factorial : ℝ) / (a - a') ^ k := by
    rw [div_mul_eq_mul_div, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hcpos.le)
  rw [hexp, hpk]
  calc v ^ k / (a - a') ^ k * (Real.exp (-(a' * r ^ 2 / s)) * Real.exp (-v))
      = (v ^ k / (a - a') ^ k * Real.exp (-v)) * Real.exp (-(a' * r ^ 2 / s)) := by ring
    _ ≤ ((k.factorial : ℝ) / (a - a') ^ k) * Real.exp (-(a' * r ^ 2 / s)) :=
        mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le

/-- **★ A2 (ITEM 5, bridge) — `hEdom_of_gaussPoly_residual`.**  THE HONEST CONDITIONAL BRIDGE for the
    width-3/2 residual domination `hEdom`.  From the PRE-COLLAPSE exposed-polynomial residual bound
      `hraw : ∀ τ>0, ∀ p q, |heatOp g gi H τ p q| ≤ P·((r²/τ + 1)·gaussDdim τ (p−q))`,   `r² := rncRadialSq (p−q)`
    (the natural width-1 residual shape of the `N=1` parametrix: ONE derivative hit ⟹ one `r²/τ`
    factor plus the `τ⁰` coefficient term), the width-3/2 `hEdom` FOLLOWS with `E₀ = 13·P`, `E₁ = 0`:
      `|heatOp g gi H τ p q| ≤ (13P + 0·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`.
    Route: absorb the exposed polynomial via the banked narrow family
    (`WidthMarginEngine.rncRadialSq_mul_gaussDdim_le_narrow`, `…gaussDdim_le_gaussDdim_narrow`):
      `(r²/τ)·G_τ ≤ √(3/2)ⁿ·12·G_{(3/2)τ}`  and  `G_τ ≤ √(3/2)ⁿ·G_{(3/2)τ}`,  sum `≤ 13·√(3/2)ⁿ·G_{(3/2)τ}`.

    HONESTY.  `hraw` is the NAMED, SATISFIABLE residue: the banked coefficient chain
    (`gatedWitnessN1_hEboundW_le_vanVleck_final`) COLLAPSES this exposed form into a width-2 bound
    (absorbing the `r²/τ` into the width), so `hraw` is not itself bankable at the global gated level
    without a `_narrow` re-run of that chain (a READ-ONLY file).  `hraw` is NON-vacuous and NOT the
    conclusion (it is a width-1 bound; the conclusion is width-3/2 with an affine prefactor).  The
    output is EXACTLY the `hEdom` binder shape of `DaLimLUConcreteDischarge.hDaLimLU_concrete`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hEdom_of_gaussPoly_residual (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (hraw : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q|
          ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim τ (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  refine ⟨13 * P, 0, by positivity, le_rfl, fun τ hτ p q => ?_⟩
  set z : Point n := p - q with hz
  set Sc : ℝ := Real.sqrt (3 / 2) ^ n with hSc
  -- the two banked narrow-absorption facts
  have h2 : gaussDdim τ z ≤ Sc * gaussDdim (3 / 2 * τ) z :=
    gaussDdim_le_gaussDdim_narrow hτ z
  have hR : rncRadialSq z * gaussDdim τ z ≤ Sc * 12 * τ * gaussDdim (3 / 2 * τ) z :=
    rncRadialSq_mul_gaussDdim_le_narrow hτ z
  -- divide the polynomial absorption by `τ`
  have hdiv : rncRadialSq z * gaussDdim τ z / τ ≤ Sc * 12 * gaussDdim (3 / 2 * τ) z := by
    rw [div_le_iff₀ hτ]
    calc rncRadialSq z * gaussDdim τ z
        ≤ Sc * 12 * τ * gaussDdim (3 / 2 * τ) z := hR
      _ = Sc * 12 * gaussDdim (3 / 2 * τ) z * τ := by ring
  -- expand the exposed-polynomial factor
  have hexpand : (rncRadialSq z / τ + 1) * gaussDdim τ z
      = rncRadialSq z * gaussDdim τ z / τ + gaussDdim τ z := by
    rw [add_mul, one_mul, div_mul_eq_mul_div]
  -- assemble
  calc |heatOp g gi H τ p q|
      ≤ P * ((rncRadialSq z / τ + 1) * gaussDdim τ z) := hraw τ hτ p q
    _ = P * (rncRadialSq z * gaussDdim τ z / τ + gaussDdim τ z) := by rw [hexpand]
    _ ≤ P * (Sc * 12 * gaussDdim (3 / 2 * τ) z + Sc * gaussDdim (3 / 2 * τ) z) :=
        mul_le_mul_of_nonneg_left (add_le_add hdiv h2) hP
    _ = (13 * P + 0 * τ) * Sc * gaussDdim (3 / 2 * τ) z := by ring

end QIQTH.DaLimHardTranche

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimHardTranche.hbnd_concrete
#print axioms QIQTH.DaLimHardTranche.gaussian_beats_power
#print axioms QIQTH.DaLimHardTranche.hEdom_of_gaussPoly_residual
