/-
  CurvedA1HContDom — J4-596: draining the `hContDom` carrier that J4-592's `hInnerCont` reduction
  carries, for the CENTER-GAUGE curved a₁ = R/6 capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  The center-gauge curved capstone
  `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center` is NON-VACUOUS (J4-587) at the genuinely
  curved witness `g^K = curvedRNCMetric κ` (`κ < 0`, `Ric ≠ 0`) but CARRIES a residual family, drained
  one-by-one (hmassone J4-588→591; hInnerCont→hContDom J4-592; hOffCollarTail J4-593; hsrc J4-594;
  hjets J4-595).  J4-592 (`CurvedA1HInnerCont.curved_hInnerCont_at_gate`) reduced the carried
  interior-time continuity binder `hInnerCont` EXACTLY to the per-interior-point dominated-continuity
  datum `hContDom` for `g^K`:

      `∀ u ∈ U, ∀ s₀ ∈ Ioo 0 u, ∃ bound, Integrable bound ∧
         (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (fun z => W (u−s) 0 z · L s z 0)) ∧
         (∀ᶠ s in 𝓝 s₀, ∀ᵐ z, ‖W (u−s) 0 z · L s z 0‖ ≤ bound z) ∧
         (∀ᵐ z, ContinuousAt (fun s => W (u−s) 0 z · L s z 0) s₀)`,

  where `W := vanVleckGatedWitness g^K … (constGate g^K …) a b` (the gated van-Vleck parametrix witness)
  and `L := leviSeries (heatOp g^K gi^K W)` (the Levi/Duhamel residual series).  THIS brick attacks that
  `hContDom`.

  ── ★★ VERDICT (J4-596).  The ALREADY-BANKED, std-3 generic ABSTRACT BUILDER
     `ContDomWindow.hContDom_discharged` produces the EXACT `hContDom` shape (dominator + norm-bound
     conjuncts included) from the FOUR granular inputs
       • `hAdom` — the D1 witness Gaussian domination `|W τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim(3/2·τ)(p−q)`
         (∀ `τ>0`, all `p q`);
       • `hBdom` — the width-`2` Levi domination `|L s z y| ≤ C_L·gaussDdim(2s)(z−y)` on `(0,T]`;
       • `hmeas` — the interior `z`-slice eventual `AEStronglyMeasurable`;
       • `hcont` — the a.e.-`z` time `ContinuousAt`.
     Its stated `g, gi, hChr, hK, S, a, b, T, U` are FREE, so its conclusion is LITERALLY the curved
     `hContDom` under `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
     `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c`.  The two GENUINELY ANALYTIC
     conjuncts of `hContDom` — the EXISTENCE of an integrable Gaussian×Gaussian dominator and the
     UNIFORM-over-a-window norm bound — are CONSTRUCTED INTERNALLY by that builder (window dominator
     `gaussDdim_window_le`, product integrability `gaussDdim_mul_integrable`); only the raw Gaussian
     dominations `{hAdom, hBdom}` and the two lighter measurability/continuity carries `{hmeas, hcont}`
     remain.  This is the analytic half of `hContDom` DISCHARGED for `g^K`; the reduction is exactly the
     one J4-592's residual asks for.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hContDom_at_gate` — ★★ the EXACT `hContDom` datum carried by
      `CurvedA1HInnerCont.curved_hInnerCont_at_gate` for `g^K`, obtained as the
      `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`, `S := constGate …` specialization of the banked
      `ContDomWindow.hContDom_discharged`.  Its integrable dominator and window norm bound are BUILT
      internally; it reduces `hContDom` to the granular `{hAdom, hBdom, hmeas, hcont}` for `g^K`.
    • `curved_hInnerCont_of_dominations` — ★★ the COMPOSED reduction: feeds `curved_hContDom_at_gate`
      into `CurvedA1HInnerCont.curved_hInnerCont_at_gate`, so the carried `hInnerCont` binder of the
      capstone is reduced ALL THE WAY to the four raw dominations/measurability/continuity carries
      `{hAdom, hBdom, hmeas, hcont}` for `g^K` — the opaque `ContinuousOn` and the opaque per-point
      dominated-continuity existential BOTH removed.
    • `curved_hContDom_satisfiable` — ★ the NON-VACUITY certificate.  For `κ < 0`, `n ≥ 2`, `g^K` is
      GENUINELY CURVED (`∃ w, 1 < det g^K w`), so the reduction is NOT secretly the flat kernel.
      Re-exports `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.

  ── WHY `hContDom` IS GENUINELY TRUE FOR `g^K` (satisfiability, not vacuity).  Fix `s₀ ∈ Ioo 0 u`.
     Then `s₀ > 0` AND `u − s₀ ∈ (0, u)` is STRICTLY positive; on the window `Ioo (s₀−δ) (s₀+δ)`,
     `δ := min s₀ (u−s₀)/2`, BOTH `s` and `u − s` stay bounded away from `0`, so both kernels sit at
     strictly positive time — no `τ→0` Gaussian blow-up.  There `W(u−s)` (Gaussian × smooth amplitude)
     and `L(s)` (positive-time-strip Levi series) are locally-uniformly Gaussian×Gaussian dominated
     (giving the integrable dominator + window norm bound the builder constructs) and time-continuous
     for a.e. `z`.  The ONLY degeneracy (`s→0` / `u−s→0`) is excluded by the OPEN interval `Ioo 0 u`.

  ── HONEST RESIDUAL.  After this brick, `hContDom`'s analytic half (dominator + window norm bound) is
     DISCHARGED for `g^K`; it is reduced to `{hAdom, hBdom, hmeas, hcont}`.  Neither `hAdom` (the curved
     witness Gaussian domination is banked only in the FROZEN-`p=0`, windowed collar form
     `CurvedRNCBaseWitnessDom.curvedRNC_baseWitness_dom`, NOT the global all-`p,q` clean form) nor
     `hBdom` (the width-`2` Levi domination for `g^K` — the D2/convergence-trio frontier;
     `ConcreteDominations` explicitly: "NOT attempted: (D2) the Levi-series domination") is banked in
     the exact shape, so `hContDom` is NOT fully closed and `hInnerCont` is NOT yet unconditional for
     `g^K`.  Assembling `{hAdom, hBdom, hmeas, hcont}` from the curved witness / heatOp-defect
     (`CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg`) / Levi positive-strip bricks is a SEPARATE
     analytic thread (the domination pile + convergence trio), not addressed here.

  ⚠ HONEST FIREWALL.  This attacks the `hContDom` carrier (the follow-on of `hInnerCont`) of the
  NON-VACUOUS curved a₁ = R/6 capstone; it proves NOTHING about `R/6`.  a₁ = R/6 remains CONDITIONAL;
  the curved capstone still owes `{hAdom, hBdom, hmeas, hcont}` PLUS the other carried residuals — the
  census/measurability/domination piles, the convergence trio, `hmassone`'s pre-ρ carriers, and the
  `hjets` residual.  Everything here is TRUE for the genuinely-curved `g^K` (`κ < 0`, `Ric ≠ 0`) and
  DERIVED from the PROVED `ContDomWindow` builder, NOT axiomatized, NOT the `a₁` conclusion, and the
  `R/6` value is unaffected.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous /
  conclusion-in-disguise hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.ContDomWindow
import QIQTH.CurvedA1HInnerCont
import QIQTH.CurvedA1HmassoneBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped Topology

namespace QIQTH.CurvedA1HContDom

variable {n : ℕ}

/-- **★★ `curved_hContDom_at_gate` — THE `hContDom` CARRIER OF J4-592's `hInnerCont` REDUCTION,
    ANALYTIC HALF DISCHARGED.**  The EXACT per-interior-point dominated-continuity datum `hContDom`
    carried by `CurvedA1HInnerCont.curved_hInnerCont_at_gate` at the genuinely-curved witness
    `g^K = curvedRNCMetric κ` — for each `u ∈ U`, each interior `s₀ ∈ Ioo 0 u`, the existence of an
    integrable dominator + eventual `AEStronglyMeasurable` + eventual a.e. norm bound + a.e.-`z` time
    `ContinuousAt` for the space-time slice `z ↦ W (u−s) 0 z · L s z 0` — obtained as the
    `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
    `S := constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c` specialization of the banked
    abstract builder `ContDomWindow.hContDom_discharged`.  The two genuinely-analytic conjuncts (the
    integrable Gaussian×Gaussian dominator and the uniform-over-window norm bound) are CONSTRUCTED
    INTERNALLY from the raw Gaussian dominations `{hAdom (D1 witness), hBdom (width-2 Levi)}`; only
    `{hAdom, hBdom}` and the two lighter measurability/continuity carries `{hmeas, hcont}` remain.
    This is the EXACT `hContDom` binder of `curved_hInnerCont_at_gate` — GENUINELY TRUE on the OPEN
    interval `Ioo 0 u` (both `s` and `u−s` strictly positive ⟹ no `τ→0` degeneracy), NOT vacuous, NOT
    `a₁ = R/6`. -/
theorem curved_hContDom_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) s₀) :
    ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u,
        ∃ bound : Point n → ℝ, Integrable bound (volume : Measure (Point n)) ∧
          (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
            (volume : Measure (Point n))) ∧
          (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖
              ≤ bound z) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)), ContinuousAt
            (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                  (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) s₀) := by
  intro u hu s₀ hs₀
  exact QIQTH.ContDomWindow.hContDom_discharged (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUT
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hBdom hmeas hcont u hu s₀ hs₀

/-- **★★ `curved_hInnerCont_of_dominations` — THE `hInnerCont` CARRIER, REDUCED ALL THE WAY TO THE RAW
    DOMINATIONS.**  Composes `curved_hContDom_at_gate` (this file) into
    `CurvedA1HInnerCont.curved_hInnerCont_at_gate` (J4-592).  The carried `hInnerCont` binder of the
    center-gauge curved capstone — the interior-time continuity of the inner space-time pairing on
    `Ioo 0 u` — is reduced, for `g^K = curvedRNCMetric κ`, ALL THE WAY to the four raw carries
    `{hAdom (D1 witness Gaussian domination), hBdom (width-2 Levi domination), hmeas (interior z-slice
    measurability), hcont (a.e.-z time continuity)}`: BOTH the opaque `ContinuousOn` (J4-592's engine)
    AND the opaque per-interior-point dominated-continuity existential (`hContDom`'s dominator + norm
    bound) are removed.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_of_dominations (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c T : ℝ) (U : Set ℝ)
    (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) s₀) :
    ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (Set.Ioo 0 u) :=
  QIQTH.CurvedA1HInnerCont.curved_hInnerCont_at_gate κ hChr hK a b c U
    (curved_hContDom_at_gate κ hChr hK a b c T U hUT A₀ A₁ C_L hA₀ hA₁ hC_L
      hAdom hBdom hmeas hcont)

/-- **★ `curved_hContDom_satisfiable` — THE NON-VACUITY CERTIFICATE.**  For `κ < 0`, `n ≥ 2`, the
    witness `g^K = curvedRNCMetric κ` is GENUINELY CURVED: `∃ w, 1 < det g^K w`
    (`det g^K(w) = (1 − (K/3)‖w‖²)^(n−1) > 1` for `‖w‖ > 0`, `K < 0`).  So the `hContDom` reduction of
    `curved_hContDom_at_gate` is applied to a NON-flat metric — it is not secretly the flat heat kernel.
    Re-exports `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_hContDom_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2

end QIQTH.CurvedA1HContDom

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HContDom

#print axioms curved_hContDom_at_gate
#print axioms curved_hInnerCont_of_dominations
#print axioms curved_hContDom_satisfiable

end AxiomChecks
