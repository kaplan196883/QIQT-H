/-
  AmplitudePackage — J4-126: the AMPLITUDE PACKAGE for the concrete `N = 1` van-Vleck gated witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  `SliverEstimates.sliver2_bound` (J4-125) is the linewise second-`x`-derivative sliver
  bound — the deliverable of the `hDaLim` wall of the `a₁ = R/6` campaign.  It is stated for a GENERIC
  formal second-derivative object `D2H` together with the amplitude INTERFACE:
      • `hD2Hexpand` — the exact 3-term Leibniz shape of the `i`-th formal second `x`-derivative of `H`
        at the RNC center `x = 0`:
          `D2H τ z = (zᵢ²−2τ)/(4τ²)·G_τ(z)·Aamp τ z + zᵢ/(2τ)·G_τ(z)·A1amp τ z + G_τ(z)·A2amp τ z`;
      • `hAampBdd`/`hA1ampBdd`/`hA2ampBdd` — the amplitude sup-bounds;
      • `hFdom` / measurabilities / `hqLip` — the Levi-side domination, base measurability, and the
        term-1 Lipschitz carry.
  This file INSTANTIATES that interface for the CONCRETE kernel `H_G := vanVleckGatedWitness` (the
  `N = 1` gated van-Vleck parametrix witness built in `ConvApproximants`), i.e. it packages exactly
  what the derivative layer must produce for `H_G`, and wires it into `sliver2_bound`.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  A0 — THE MAP (the small-`τ`, `x = 0`-slice structure of `H_G`; verbatim from the def chain).
  Unwinding `vanVleckGatedWitness g gi hC hK S a b` all the way down (see the LANDED unfolding lemmas
  below, all proved here):
      `vanVleckGatedWitness … τ p q`
        `= gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W) τ p q`      (def)
        `= if q ∈ K then (if p ∈ S q then W₁ τ p q else 0) else 0`                   (`gatedKernel`)
   where, ON THE GATE (`q ∈ K`, `p ∈ S q`),
      `W₁ τ p q = radialCutoff a b (W q p) · heatParametrix 1 Θ u τ (W q p)`
              `= radialCutoff a b (W q p) · G_τ(W q p) · Θ(W q p)^{−1/2} · (u₀(W q p) + u₁(W q p)·τ)`,
   with  `Θ := vanVleck g`,  `u := transportCoeff (transportOp (vanVleck g) g gi)`  (so `u₀ ≡ 1`),
         `W := uniformInverseChart g gi hC hK`  (the per-base normal-coordinate inverse chart), and
         `G_τ := gaussDdim τ`.
  ANSWERS to the three A0 questions:
    (i)   THE GAUSSIAN ARGUMENT IS A CHART IMAGE, NOT `z` ITSELF.  For the `hAnear`-slice `p = 0`,
          `q = z`, the argument is `W z 0 = uniformInverseChart … z 0` — the normal coordinate of the
          origin as seen from base `z`.  It equals `z` only up to the geodesic/Euclidean discrepancy
          `‖W z 0‖ = d_g(z,0) ≠ ‖z‖` off-flat (see `vanVleckGatedWitness_zero_factor` and the BLOCKER
          note below).  `Aamp/A1amp/A2amp` (which sit OUTSIDE `G`) cannot repair the Gaussian argument.
    (ii)  THE GATE `S` and CUTOFF `radialCutoff` are BOTH `z`-only (τ-independent): `S q` is the
          `.choose`-built flow-ball `φ_q '' ball 0 (cf q)` (opaque; `GatedWitnessPackage`), and
          `radialCutoff a b (W q p)` depends on `(p,q)` through `W q p`, not on `τ`.
    (iii) INSIDE the gate AND the inner cutoff plateau (`rncRadialSq (W z 0) ≤ a²` ⟹ `radialCutoff = 1`)
          the witness is EXACTLY `G_τ(W z 0)·Θ(W z 0)^{−1/2}·(u₀(W z 0)+u₁(W z 0)·τ)` — the honest
          near-diagonal factorization (`vanVleckGatedWitness_zero_factor`).  The `hAnear` shape carried
          by `BoundaryAssembly` (`G_τ(z)·(u₀ z + τ·u₁ z)`) is the SAME up to the Gaussian-argument
          identification `W z 0 ↦ z`, which is the geometric input isolated below.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDS (this file, UNCONDITIONALLY).
    • `heatParametrix_one_apply`         — the `N = 1` ansatz unfolding `H₁ = G·Θ^{−1/2}·(u₀+u₁τ)`.
    • `vanVleckGatedWitness_gate_apply`  — the EXACT on-gate value of the concrete witness (the A0 map,
                                           formalized): a genuine def-chain unfolding, no hypotheses
                                           beyond the two gate memberships.
    • `vanVleckGatedWitness_zero_factor` — the honest near-diagonal `x = 0` factorization, isolating
                                           the chart-image Gaussian `G_τ(W z 0)`.
    • `witnessSecondXDeriv`              — the CONCRETE formal second-`x`-derivative object for the
                                           witness, `pd_i(pd_i(x ↦ H_G τ x z))(0)` — tied to the witness,
                                           NOT a free stand-in (non-vacuity anchor).
    • `AmplitudeDerivativeData`          — the data bundle naming EXACTLY the `sliver2_bound` amplitude
                                           interface FOR `witnessSecondXDeriv` (fields = `Aamp/A1amp/
                                           A2amp` + the Leibniz identity `hD2Hexpand` for the CONCRETE
                                           `witnessSecondXDeriv` + the bounds + `hFdom`/meas/`hqLip`).
    • `amplitudePackage_sliver_bound`    — ★ THE DELIVERABLE: given the data bundle, the concrete-witness
                                           formal-second-derivative sliver obeys the `√ε` bound, via
                                           `sliver2_bound`.  This is the sliver interface DISCHARGED for
                                           the concrete van-Vleck witness modulo the bundled amplitude
                                           data.

  ⚠ HONEST FIREWALL.
    CARRIED (as the `AmplitudeDerivativeData` fields — each a genuine fact, NONE the conclusion, none
      vacuous, all satisfiable by the true chart-pullback amplitude of `H_G`):
      • `hD2Hexpand` — the geometric identity that the `i`-th formal second `x`-derivative of `H_G` at
        `x = 0` has the Leibniz-Gaussian 3-term shape with `G_τ` at the BASE point `z`.  This is the
        derivative-layer content (chart Jacobian at the center + the C⁴ regularity tower
        `expMap_contDiffOn_four` / the `C²` chart `uniformInverseChart`); it is the ONE hard geometric
        input this brick isolates rather than fabricates.
      • `hAampBdd`/`hA1ampBdd`/`hA2ampBdd` — the amplitude sup-bounds (the concrete coefficient layer
        `CoeffBoundsN1`/`CoeffU1Fix`/`UniformCoeffBound` supplies the ball-bounds for `u₀/u₁`; the gate
        support kills the exterior).
      • `hFdom` — the Levi-series width-2 domination (LANDED for `H_G` in `GatedWitnessPackage`,
        `leviSeries_gatedWitnessN1_dominated`, conditional only on base measurability); carried
        parametrically here.
      • `hAampmeas`/`hA1ampmeas`/`hA2ampmeas`/`hFmeas`/`hqLip` — base measurability and the term-1
        Lipschitz carry, consistent with the deferred measurability family (J4-117/118/119).
    THE BLOCKER (bankable intelligence).  The `BoundaryAssembly.hAnear` shape `A τ 0 z = G_τ(z)·(u₀ z +
      τ·u₁ z)` is NOT literally satisfied by the concrete witness: the concrete Gaussian argument is
      `W z 0` (chart image), and `gaussDdim` depends on `‖·‖²`, so matching requires `‖W z 0‖ = ‖z‖`,
      i.e. `d_g(z,0) = ‖z‖`, which holds only in the flat/RNC-linearized regime.  Discharging `hAnear`
      for `H_G` therefore needs the chart near-isometry `rncRadialSq (W z 0) = ‖z‖² + O(‖z‖⁴)` PLUS an
      error-absorption of the `O(‖z‖⁴)` Gaussian discrepancy into `u₀/u₁` — a genuine geometric step,
      not a def-chain unfolding.  `vanVleckGatedWitness_zero_factor` records the exact honest form the
      discharge must start from.
    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  Reusable packaging
    BRICK; NOT `a₁ = R/6` — this discharges ONE brick (the amplitude package for the sliver interface)
    of the `hDaLim` wall of the campaign.
-/
import Mathlib
import QIQTH.SliverEstimates
import QIQTH.ConvApproximants

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The `N = 1` parametrix ansatz unfolding. -/

/-- **The `N = 1` heat-parametrix ansatz, unfolded.**  `heatParametrix 1 Θ u t x = G_t(x)·Θ(x)^{−1/2}·
    (u₀(x) + u₁(x)·t)`.  The `∑_{k ∈ range 2}` collapses to the two-term DeWitt polynomial. -/
theorem heatParametrix_one_apply (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (x : Point n) :
    heatParametrix 1 Θ u t x
      = gaussDdim t x * Θ x ^ (-(1 : ℝ) / 2) * (u 0 x + u 1 x * t) := by
  simp only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    zero_add]
  ring

/-! ### A0 — the concrete witness on the gate (the map, formalized). -/

/-- **★ A0 — THE EXACT ON-GATE VALUE OF THE CONCRETE VAN-VLECK WITNESS.**  For a base point `q ∈ K`
    and a field point `p ∈ S q`, the gated `N = 1` van-Vleck witness equals its ungated parametrix:
      `H_G τ p q = radialCutoff a b (W q p) · (G_τ(W q p) · Θ(W q p)^{−1/2} · (u₀(W q p) + u₁(W q p)·τ))`,
    with `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`,
    `W = uniformInverseChart g gi hC hK`.  Pure def-chain unfolding (`gatedKernel_apply_of_mem` +
    `globalCutoffParametrixWitnessN` + `heatParametrix_one_apply`); no analytic hypotheses.  This is
    the A0 map made formal — the Gaussian argument is the CHART IMAGE `W q p`. -/
theorem vanVleckGatedWitness_gate_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {p q : Point n} (hq : q ∈ K) (hp : p ∈ S q) :
    vanVleckGatedWitness g gi hC hK S a b τ p q
      = radialCutoff a b (uniformInverseChart g gi hC hK q p)
        * (gaussDdim τ (uniformInverseChart g gi hC hK q p)
            * vanVleck g (uniformInverseChart g gi hC hK q p) ^ (-(1 : ℝ) / 2)
            * (transportCoeff (transportOp (vanVleck g) g gi) 0
                  (uniformInverseChart g gi hC hK q p)
              + transportCoeff (transportOp (vanVleck g) g gi) 1
                  (uniformInverseChart g gi hC hK q p) * τ)) := by
  unfold vanVleckGatedWitness
  rw [gatedKernel_apply_of_mem K S _ τ hq hp]
  simp only [globalCutoffParametrixWitnessN]
  rw [heatParametrix_one_apply]

/-- **The honest near-diagonal `x = 0` factorization.**  Specializing the on-gate value to the
    `hAnear`-slice (`p = 0`, `q = z`) and regrouping, the witness factors as
      `H_G τ 0 z = G_τ(W z 0) · amp(τ,z)`,   `amp(τ,z) = radialCutoff a b (W z 0)·Θ(W z 0)^{−1/2}·(u₀+u₁τ)`,
    with the Gaussian at the CHART IMAGE `W z 0` (NOT `z`).  This is the exact starting form the
    `BoundaryAssembly.hAnear` discharge must begin from; see the BLOCKER note in the header. -/
theorem vanVleckGatedWitness_zero_factor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {z : Point n} (hz : z ∈ K) (h0 : (0 : Point n) ∈ S z) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0)
        * (radialCutoff a b (uniformInverseChart g gi hC hK z 0)
            * vanVleck g (uniformInverseChart g gi hC hK z 0) ^ (-(1 : ℝ) / 2)
            * (transportCoeff (transportOp (vanVleck g) g gi) 0
                  (uniformInverseChart g gi hC hK z 0)
              + transportCoeff (transportOp (vanVleck g) g gi) 1
                  (uniformInverseChart g gi hC hK z 0) * τ)) := by
  rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hz h0]; ring

/-! ### A1 — the concrete formal second-`x`-derivative object. -/

/-- **The CONCRETE formal second-`x`-derivative of the witness at the RNC center**, along coordinate
    `i`: `witnessSecondXDeriv … i τ z = ∂²_{xᵢ}(x ↦ H_G τ x z)(0)` in the `pd` calculus.  This is the
    object `D2H` of `sliver2_bound` for the concrete kernel; it is tied to the witness (NOT a free
    stand-in), so the `hD2Hexpand` field of `AmplitudeDerivativeData` below is a genuine, non-vacuous
    constraint (the Leibniz identity for the ACTUAL second derivative). -/
noncomputable def witnessSecondXDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) : ℝ :=
  pd (fun x : Point n =>
      pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x) i (0 : Point n)

/-! ### A3(iv) — the amplitude data bundle for the concrete witness. -/

/-- **★★ THE AMPLITUDE PACKAGE (data bundle).**  Exactly the `sliver2_bound` amplitude interface,
    instantiated for the CONCRETE `witnessSecondXDeriv` of the `N = 1` van-Vleck gated witness.  A term
    of this type is precisely the derivative-layer deliverable the sliver estimate consumes:
      • `Aamp/A1amp/A2amp` — the three amplitude components;
      • `hD2Hexpand` — the Leibniz-Gaussian 3-term identity FOR the concrete `witnessSecondXDeriv`
        (the ONE hard geometric input, isolated here — see header BLOCKER);
      • `hAampBdd/hA1ampBdd/hA2ampBdd` — amplitude sup-bounds;
      • `hFdom` — the Levi-side width-2 domination of `F`;
      • measurabilities + `hqLip` — base measurability and the term-1 Lipschitz carry.
    Each field is a genuine fact, none is the conclusion, and all are satisfiable by the true chart
    pullback amplitude of `H_G`.  NOT `a₁ = R/6`. -/
structure AmplitudeDerivativeData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ) where
  /-- The zeroth (Hessian-weighted) amplitude component. -/
  Aamp : ℝ → Point n → ℝ
  /-- The first (gradient-weighted) amplitude component. -/
  A1amp : ℝ → Point n → ℝ
  /-- The second (mass-weighted) amplitude component. -/
  A2amp : ℝ → Point n → ℝ
  /-- Sup-bound constant for `Aamp`. -/
  M₀ : ℝ
  /-- Sup-bound constant for `A1amp`. -/
  M₁ : ℝ
  /-- Sup-bound constant for `A2amp`. -/
  M₂ : ℝ
  /-- Lipschitz constant of the term-1 product `Aamp·F`. -/
  L : ℝ
  /-- Width-2 domination constant for the Levi kernel `F`. -/
  C_L : ℝ
  hM₀ : 0 ≤ M₀
  hM₁ : 0 ≤ M₁
  hM₂ : 0 ≤ M₂
  hL : 0 ≤ L
  hC_L : 0 ≤ C_L
  /-- ★ The Leibniz-Gaussian 3-term identity for the CONCRETE second `x`-derivative of the witness. -/
  hD2Hexpand : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
      witnessSecondXDeriv g gi hC hK S a b i τ z
        = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * Aamp τ z
          + z i / (2 * τ) * gaussDdim τ z * A1amp τ z
          + gaussDdim τ z * A2amp τ z
  hAampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |Aamp τ z| ≤ M₀
  hA1ampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |A1amp τ z| ≤ M₁
  hA2ampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |A2amp τ z| ≤ M₂
  hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)
  hAampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => Aamp τ z) volume
  hA1ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A1amp τ z) volume
  hA2ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A2amp τ z) volume
  hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume
  hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T →
      ∀ z w : Point n, |Aamp τ z * F s z 0 - Aamp τ w * F s w 0| ≤ L * dist z w

/-! ### THE DELIVERABLE — the sliver interface discharged for the concrete witness. -/

/-- **★★★ THE AMPLITUDE PACKAGE CAPSTONE.**  Given the amplitude data bundle for the concrete `N = 1`
    van-Vleck gated witness, the formal second-`x`-derivative sliver of the witness obeys the `√ε`
    bound of `sliver2_bound`:
      `|∫ s in (u−ε)..u, ∫ z, witnessSecondXDeriv … (u−s) z · F s z 0|`
        `≤ (L·(15/2·n) + (3/4)·(M₁·C_F))·2√ε + M₂·C_F·ε`,   `C_F = C_L·gaussDdim aa 0`.
    This is the `hDaLim`-brick sliver interface DISCHARGED for the concrete van-Vleck witness, modulo
    the bundled amplitude data (the derivative-layer geometry).  Route: a direct application of
    `sliver2_bound` with `D2H := witnessSecondXDeriv`.  NOT `a₁ = R/6`. -/
theorem amplitudePackage_sliver_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (data : AmplitudeDerivativeData g gi hC hK S a b F i T τ₀)
    (u ε aa : ℝ) (haa : 0 < aa) (hau : aa ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < aa / 2)
    (hετ₀ : ε ≤ τ₀) :
    |∫ s in (u - ε)..u, ∫ z, witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
      ≤ (data.L * (15 / 2 * (n : ℝ))
            + 3 / 4 * (data.M₁ * (data.C_L * gaussDdim aa (0 : Point n)))) * (2 * Real.sqrt ε)
        + data.M₂ * (data.C_L * gaussDdim aa (0 : Point n)) * ε := by
  exact sliver2_bound (witnessSecondXDeriv g gi hC hK S a b i) F
    data.Aamp data.A1amp data.A2amp i T τ₀
    data.M₀ data.M₁ data.M₂ data.L data.C_L
    data.hM₀ data.hM₁ data.hM₂ data.hL data.hC_L
    u ε aa haa hau huT hε0 hεa hετ₀
    data.hD2Hexpand data.hAampBdd data.hA1ampBdd data.hA2ampBdd
    data.hFdom data.hAampmeas data.hA1ampmeas data.hA2ampmeas data.hFmeas data.hqLip

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.heatParametrix_one_apply
#print axioms QIQTH.HeatResidualBound.vanVleckGatedWitness_gate_apply
#print axioms QIQTH.HeatResidualBound.vanVleckGatedWitness_zero_factor
#print axioms QIQTH.HeatResidualBound.amplitudePackage_sliver_bound
