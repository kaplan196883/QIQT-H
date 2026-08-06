/-
  DaLimCensusRecon — J4-331: the CLASSIFIED per-item census of the `hDaLimLU` data pile
  (the hypothesis list of `DaLimLUConcreteDischarge.hDaLimLU_concrete`, the banked loc-unif
  `Da`-limit provider feeding the capstone's `hDuhamel`/`hDConv` slots via J4-310/311/312),
  plus the DERIVABLE-NOW tranche DISCHARGED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  CENSUS + COMPOSITION brick over the `hDaLimLU_concrete` hypothesis pile.  No `sorry` (header prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited.  `hDaLimLU_concrete` remains the
  concrete-gate `Da`-limit and is **not** the `a₁ = R/6` diagonal statement.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## X0 — THE COMPLETE CLASSIFIED CENSUS of `hDaLimLU_concrete`'s hypotheses.
  Verdict legend:  BANKED (cited exact lemma) · DERIVABLE-NOW (small composition, discharged in THIS
  file) · DERIVABLE-with-carries (banked provider + satisfiable geometry/analytic carries) ·
  NEW-BRICK (needs a genuine new analytic lemma; nature stated) · DATA (trivial satisfiable window /
  positivity binder).  `pdpdH := witnessSecondXDeriv g gi hChr hK S a b`, `H_G := vanVleckGatedWitness
  g gi hChr hK S a b`, and — at the endgame gate — `F := leviSeries (heatOp g gi H_G)`.

  ── (A) GAUGE (RNC normalization at the centre) ───────────────────────────────────────────────────
    • `hgi : MemGaugeGi gi`      (= `∀ i j, gi 0 i j = δ_{ij}`)
        VERDICT **DERIVABLE-NOW** → discharged here `memGaugeGi_of_geometry`
        (⇐ `OuterCarryRecon.hgi_of_geometry`; carries `hK0`,`hframeK`,`hinvF` — RNC frame + inverse
        relation).  SAT: flat metric satisfies all three; no vacuity.
    • `hΓ : MemGaugeGamma g gi`  (= `∀ k i j, christoffel g gi k i j 0 = 0`)
        VERDICT **DERIVABLE-NOW** → discharged here `memGaugeGamma_of_hdg0`
        (⇐ `OuterCarryRecon.hGamma_of_hdg0`; carry `hdg0 = ∂_e g_{ab}(0)=0`).  SAT: flat; no vacuity.

  ── (B) THE W2 differentiation-under-∫∫ family (INTERNALLY consumed → `hInterchange`) ───────────────
    `V,hVopen,hV0,snb,hsnb,hQ1,hFmeas,hFint,hF'meas,bnd,hbdd,hbound,hdiff`
        VERDICT **BANKED engine** — `SecondOrderInterchangeConcrete.witness_MemInterchange` (J4-256)
        already consumes this family inside `hDaLimLU_concrete`, producing
        `MemInterchange … witnessSecondXDeriv`.  The family members ARE the honest W2 remainder
        (`hasFDerivAt_integral_of_dominated`-shaped diff-under-∫ facts on `witnessFieldDeriv/Deriv2`).
        SAT AUDIT: the majorant `bnd m i s` in `hbound`/`hbdd`/`hdiff` is s-DEPENDENT and interval-
        integrable — NOT a uniform-in-s singular prefactor; the `∀ w ∈ snb` window is a derivative
        neighbourhood, not an ∀-z blow-up.  No ∀S artefact (S is fixed by the witness).  SATISFIABLE,
        no over-quantification (contrast the retired hFbd/hGateData/∀S-hEmeas facade poisons — NONE
        recur in the `Da`-limit pile).  → X2 (already threaded; content = the concrete W2 engine).

  ── (C) LAPLACIAN COMPARISON ───────────────────────────────────────────────────────────────────────
    • `hLapFull : MemLapFull g gi H_G F U pdpdH`
        (= `∀ u ∈ U, Δ_g(H_G*F)(0) = ∑ᵢ ∫₀ᵘ ∫ pdpdH·F`)
        VERDICT **NEW-BRICK** (the Laplacian-comparison wall).  Provider
        `InterchangeThreading.hLapFull_of_lims` is per-`u`, abstract in `H F`, and RELOCATES content
        to its C²-limit carry `hLHSlim` (an F2 derivative-of-limit fact); NO concrete-witness builder
        banked.  Nature: exchange of `Δ_g` with the double `∫∫` at the concrete kernel via a C²
        dominated-limit.  SAT: honest analytic fact about `H_G` (no singular quantifier).

  ── (D) ADJACENCY interval-integrabilities ─────────────────────────────────────────────────────────
    • `hII_lo : MemAdjLo F U pdpdH` / `hII_hi : MemAdjHi F U pdpdH`
        (= interval-integrability of `s ↦ ∫ pdpdH·F` on `[0,u−ε_m]` / `[u−ε_m,u]`)
        VERDICT **NEW-BRICK (routine)**.  Gaussian-domination of `pdpdH·F` (both `pdpdH =
        witnessSecondXDeriv` and `F = leviSeries` are Gaussian-dominated) + `IntervalIntegrable` of a
        Beta-type `s`-power; the J4-323 pairing seeds (`gaussDdim_pairing_integral`,
        `betaPow_integrableOn`) feed this but NO concrete `MemAdj*` builder is banked.  SAT: routine,
        no singular prefactor.

  ── (E) THE √ε SLIVER amplitudes ───────────────────────────────────────────────────────────────────
    • `D0 D1 : Fin n → ℝ`, `hD0`,`hD1` (nonneg — trivial), `hbnd`
        (= `|∫_{u−ε_m}^u ∫ pdpdH·F| ≤ D0 i·2√ε_m + D1 i·ε_m`, ∀ i m, ∀ u ∈ U)
        VERDICT **NEW-BRICK** — the sliver amplitude.  Dischargeable via
        `AmplitudePackage.amplitudePackage_sliver_bound` ONCE the `AmplitudeDerivativeData` bundle
        (`hD2Hexpand`, the Leibniz–Gaussian 2nd-derivative identity at `pdpdH := witnessSecondXDeriv`)
        is supplied — NOT built.  SAT: the `√ε` rate is a genuine width-2 short-time amplitude; no
        uniform-in-s singularity (the `[u−ε_m,u]` strip is the vanishing sliver, √ε is its measure).

  ── (F) RESIDUAL heat-operator domination ──────────────────────────────────────────────────────────
    • window/positivity `E₀ E₁ C_L aT`,`hE₀`,`hE₁`,`hC_L`,`haT`,`hUlb`,`hUT` — **DATA** (trivial).
    • `hEdom : ∀ τ>0, ∀ p q, |heatOp g gi H_G τ p q| ≤ (E₀+E₁τ)·√(3/2)^n·gaussDdim(3/2·τ)(p−q)`
        VERDICT **NEW-BRICK (width-narrowing)**.  ⚠ SAT AUDIT (the flagged item): the domination is at
        width **3/2**, whereas the banked witness bound `gatedWitnessN1_hEboundW_le_vanVleck_final`
        gives width **2** (`baseKernelW 2 0 τ = gaussDdim(2τ)`).  Since `3/2 < 2`, `gaussDdim(3/2·τ)`
        DECAYS FASTER (narrower) — dominating BY it is STRICTLY STRONGER in the tail than the banked
        width-2 bound.  This is NOT unsatisfiable: the standard Gaussian-slack absorption
        `gaussDdim(2τ)·poly(r) ≤ C·gaussDdim(3/2·τ)` (steal the exponent gap
        `exp(−r²(1/6−1/8)/τ)=exp(−r²/24τ)` to beat the polynomial prefactor) makes width-3/2 REACHABLE;
        the bank's `gaussian_beats_linear/quadratic` (J4-322 β-bricks) are exactly this seed.  So the
        witness DOES satisfy it — but only via a genuine new width-narrowing brick, not a rewrite.
        VERDICT stands: satisfiable, NEW-BRICK.  (Header note that `hEdom` "only consumed elsewhere"
        confirms it is a carried domination, not the `Da`-limit's own consumer.)

  ── (G) SOURCE domination / vanishing (at `F := leviSeries (heatOp g gi H_G)`) ─────────────────────
    • `hFdom : ∀ s>0, s≤T, ∀ z y, |F s z y| ≤ C_L·gaussDdim(2s)(z−y)`
        VERDICT **DERIVABLE-with-carries** — the WIDTH MATCHES (2s = banked width-2).  Route:
        `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated` (∃C_L, `|leviSeries| ≤
        C_L·baseKernelW 2 0 s`) + `ParametrixHEboundWiring.baseKernelW_zero_apply`
        (`baseKernelW 2 0 s = gaussDdim(2s)`).  Carries: the full RNC geometry pile
        (`hg/hC/hK/hgnd/hgsymm/hinvF/hframeK/hw/hdg0/hg0/hn/hT`) + the base strong-measurability
        `hEmeas`.  SAT: this is the LANDED Levi domination (J4-324 `leviSeries_dominatedW_le` +
        `baseKernelW_zero_apply`, γ = 0, no s-singularity); satisfiable at the concrete gate.  Not
        discharged here only because it re-exports a large geometry pile (kept in the endgame
        assembly, not this census file).
    • `hFzero : ∀ s≤0, ∀ z y, F s z y = 0`
        VERDICT **NEW-BRICK (small)**.  `leviSeries E` with `E = heatOp g gi H_G` vanishing at `τ≤0`
        (`CoeffBoundsN1.heatOp_gatedWitnessN1_eq_zero_of_nonpos`) is itself `0` at `τ≤0` — each `iterE`
        integrates over the degenerate interval `[0,τ]`.  No banked `leviSeries_eq_zero_of_nonpos`;
        one short lemma (empty-interval iterate ⇒ tsum 0).  SAT: honest, trivial content.

  ── (H) STRIP interval-integrabilities of the `E·F` inner pairing ──────────────────────────────────
    • `hIlo`/`hIhi : IntervalIntegrable (fun s => ∫ heatOp g gi H_G (u−s) 0 z · F s z 0)` on
        `[0,u−ε_m]` / `[u−ε_m,u]`, ∀ m, ∀ u ∈ U.
        VERDICT **NEW-BRICK (routine)**.  Both factors Gaussian-dominated ⇒ the `z`-pairing is a
        `gaussDdim`-convolution (`gaussDdim_pairing_integral`, J4-323) whose `s`-profile is a Beta
        `s`-power (`betaPow_integrableOn`, γ>−1); the `IntervalIntegrable` follows.  NO concrete strip
        builder banked.  SAT: routine, no singular prefactor.

  ── (I) THE E-COMBINATION ──────────────────────────────────────────────────────────────────────────
    • `hEcomb : MemECombine g gi H_G F`   (= `∀ m u, DaTrunc = LapTrunc + Etrunc`)
        VERDICT **DERIVABLE-NOW** → discharged here `memECombine_of_data`
        (⇐ `HeatResidualBound.hE_combination`, per `(m,u)`; carries the 6 representation/integrability
        sub-facts `hDa`/`hLap`/`hLapZ`/`hEZ`/`hLapS`/`hES`).  SAT: each carry is a genuine
        Fubini/representation fact about `H_G`,`F`; no vacuity, no singular quantifier.

  ── (J) SCALAR window/geometry binders ─────────────────────────────────────────────────────────────
    `T,U,hUopen`,`hn : 1 ≤ n` — **DATA** (geometry/window; `hn` feeds the internally-discharged
    `hEzero` via `hEzeroE_concrete`).  Trivially satisfiable.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SATISFIABILITY AUDIT — SUMMARY (per feedback_axiom_budget_blind_spot).
  EVERY census item is SATISFIABLE by the concrete `N=1` van-Vleck witness / `leviSeries` source; NO
  over-quantified or unsatisfiable artefact appears in the `Da`-limit pile.  The three known facade
  poisons — the capstone `∀S`-`hEmeas`, `hFbd` (`s^{−n/2}` singular at `(0,0)`), and `hGateData`
  (constant-`Bs` naked quotient) — live in the SEPARATE `hCConv` boundary/facade pile and DO NOT recur
  here (the `Da`-limit is W1-free, see `DaLimLUConcreteDischarge` header).  The ONE item warranting
  scrutiny, `hEdom`, was audited (F above): its width-3/2 (< the banked width-2) is REACHABLE via
  Gaussian-slack polynomial absorption — satisfiable, needing a new width-narrowing brick, not a poison.
  No uniform-in-s or ∀-z bound in the pile demands a singular prefactor: `bnd`/`hbound` use s-dependent
  interval-integrable majorants; `hFdom`/`hEdom` carry constant `C_L`/`E₀,E₁` with genuine Gaussian
  cores.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## X1 — DERIVABLE-NOW discharges (THIS FILE).
    • `memGaugeGi_of_geometry`   : `MemGaugeGi gi`        ⇐ `hgi_of_geometry` (hK0,hframeK,hinvF).
    • `memGaugeGamma_of_hdg0`     : `MemGaugeGamma g gi`  ⇐ `hGamma_of_hdg0` (hdg0).
    • `memECombine_of_data`       : `MemECombine g gi H F` ⇐ `hE_combination` (per-(m,u) ×6 carries).

  ## X2 — THE HONEST REMAINDER (dependency order; each a genuine new analytic brick).
    1. `hFzero`  (small — leviSeries empty-interval vanishing at `τ≤0`).
    2. `hFdom`   (re-export of the LANDED Levi domination + `baseKernelW_zero_apply`; geometry pile).
    3. `hIlo`/`hIhi`, `hII_lo`/`hII_hi`  (Gaussian-pairing + Beta `s`-power interval-integrability).
    4. `hbnd`    (the √ε sliver amplitude — needs `AmplitudeDerivativeData.hD2Hexpand`).
    5. `hEdom`   (width-3/2 residual domination — the Gaussian-slack width-narrowing brick).
    6. `hLapFull` (the Laplacian-comparison wall — Δ_g ↔ ∫∫ interchange at the concrete kernel; the
        deepest, relocates to the F2 C²-limit `hLHSlim`).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLUConcreteDischarge
import QIQTH.OuterCarryRecon
import QIQTH.TruncatedDuhamel

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimCensusRecon

variable {n : ℕ}

/-! ###############################################################################
    ### X1 — the DERIVABLE-NOW tranche of the `hDaLimLU_concrete` census.
    ############################################################################### -/

/-- **X1 (A·hgi) — `memGaugeGi_of_geometry`.**  The RNC inverse-metric normalization census item
    `MemGaugeGi gi` (= `∀ i j, gi 0 i j = δ_{ij}`) DISCHARGED from the RNC frame condition `hframeK`
    (with `0 ∈ K`) and the inverse relation `hinvF`, via `OuterCarryRecon.hgi_of_geometry`.  Every
    carry is a satisfiable RNC-geometry fact (the flat metric satisfies all three), NONE the
    conclusion.  NOT `a₁ = R/6`. -/
theorem memGaugeGi_of_geometry (g gi : Point n → Fin n → Fin n → ℝ) {K : Set (Point n)}
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    MemGaugeGi (n := n) gi :=
  fun i j => QIQTH.OuterCarryRecon.hgi_of_geometry g gi hK0 hframeK hinvF i j

/-- **X1 (A·hΓ) — `memGaugeGamma_of_hdg0`.**  The RNC Christoffel-vanishing census item
    `MemGaugeGamma g gi` (= `∀ k i j, christoffel g gi k i j 0 = 0`) DISCHARGED from the first-derivative
    gauge `hdg0` (`∂_e g_{ab}(0) = 0`), via `OuterCarryRecon.hGamma_of_hdg0`.  The carry is a satisfiable
    RNC fact (flat metric), not the conclusion.  NOT `a₁ = R/6`. -/
theorem memGaugeGamma_of_hdg0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0) :
    MemGaugeGamma (n := n) g gi :=
  fun k i j => QIQTH.OuterCarryRecon.hGamma_of_hdg0 g gi hdg0 k i j

/-- **X1 (I·hEcomb) — `memECombine_of_data`.**  The `E`-combination census item
    `MemECombine g gi H F` (= `∀ m u, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u`)
    DISCHARGED from the six per-`(m,u)` representation/integrability sub-facts, via
    `HeatResidualBound.hE_combination` applied pointwise in `(m,u)`.  Each carry is a genuine
    Fubini/representation fact about `H`,`F` (the two `Da`/`Lap` representations, the two fibrewise
    `Integrable`s, the two `IntervalIntegrable`s); NONE is the conclusion, none vacuous.  NOT
    `a₁ = R/6`. -/
theorem memECombine_of_data (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ)
    (hDa : ∀ (m : ℕ) (u : ℝ), DaTrunc H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ), LapTrunc g gi H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi H (u - s) 0 z * F s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m)) :
    MemECombine g gi H F :=
  fun m u => HeatResidualBound.hE_combination g gi H F m u
    (hDa m u) (hLap m u) (hLapZ u) (hEZ u) (hLapS m u) (hES m u)

end QIQTH.DaLimCensusRecon

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimCensusRecon.memGaugeGi_of_geometry
#print axioms QIQTH.DaLimCensusRecon.memGaugeGamma_of_hdg0
#print axioms QIQTH.DaLimCensusRecon.memECombine_of_data
