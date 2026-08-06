/-
  QIQTH / HeatResidualBound — D2HExpandRecon.lean   (J4-350)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer recon/discharge brick of the a₁ = R/6
  heat-kernel campaign.  It proves NOTHING about R/6; a₁ = R/6 remains CONDITIONAL.  It reduces the
  hard `hD2Hexpand` field of `AmplitudeDerivativeData` to a CLEANER, SATISFIABLE, NON-VACUOUS residue
  (a germ-level factored representation of the concrete witness plus four chart-jet identities), via
  the banked Leibniz–Gaussian second-`x`-derivative normal form `gaussComp_amp_center_decomp`
  (J4-130, `QIQTH/ChartJetHessian.lean`).  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  D0 — THE COMPLETE CLASSIFIED CENSUS of `AmplitudeDerivativeData` (QIQTH/AmplitudePackage.lean, J4-126).

  The bundle (over `g gi hC {K} hK S a b F i T τ₀`) carries the sliver2_bound amplitude interface for
  the CONCRETE object

      witnessSecondXDeriv g gi hC hK S a b i τ z
        := pd (fun x => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x) i 0

  the `i`-th formal second `x`-derivative of the gated van-Vleck witness at the RNC center `x = 0`.
  The 24 fields, classified:

    DATA (3) — the amplitude components (functions `ℝ → Point n → ℝ`):
      • `Aamp`   : the zeroth (Hessian-weighted) amplitude
      • `A1amp`  : the first (gradient-weighted) amplitude
      • `A2amp`  : the second (mass-weighted) amplitude
    DATA (5) — the moduli constants (`ℝ`):  `M₀ M₁ M₂ L C_L`.
    TRIVIAL nonnegativity (5):  `hM₀ hM₁ hM₂ hL hC_L : 0 ≤ (·)` — pure sign facts on the chosen moduli.
    ★ HARD — the ONE geometric field (1):
      • `hD2Hexpand : ∀ τ ∈ Ioo 0 τ₀, ∀ z,
             witnessSecondXDeriv … i τ z
               = (z i^2 − 2τ)/(4τ²)·gaussDdim τ z·Aamp τ z
                 + z i/(2τ)·gaussDdim τ z·A1amp τ z
                 + gaussDdim τ z·A2amp τ z`
        — the Leibniz–Gaussian 3-term identity: the SECOND `x`-derivative of the amplitude·Gaussian
        product expanded into a Hessian-weighted (`(z i²−2τ)/(4τ²)·G`), a gradient-weighted
        (`z i/(2τ)·G`), and a mass-weighted (`G`) term.  THIS is the census-named
        "Leibniz–Gaussian derivative layer".  It is the derivative-layer geometry of the concrete
        witness (see the DISCHARGE MAP below).
    ANALYTIC bounds (3):  `hAampBdd hA1ampBdd hA2ampBdd` — sup-bounds `|A·amp τ z| ≤ M·` (the concrete
        coefficient layer `CoeffBoundsN1`/`UniformCoeffBound` supplies these off-file).
    LEVI-side (1):  `hFdom : ∀ s, 0<s → s≤T → ∀ z y, |F s z y| ≤ C_L·gaussDdim (2s) (z−y)` — width-2
        domination of the Levi kernel `F` (independent of the `hD2Hexpand` layer).
    MEASURABILITY (4):  `hAampmeas hA1ampmeas hA2ampmeas hFmeas` — `AEStronglyMeasurable` carries.
    LIPSCHITZ (1):  `hqLip` — the term-1 product `Aamp·F` Lipschitz carry.

  SATISFIABILITY AUDIT (per feedback_axiom_budget_blind_spot).  The bundle is CLEAN: NO over-quantified
  field, NO singular prefactor, NO vacuous `:= True`.  Concretely:
    • the trivial nonneg fields are satisfiable by any nonneg modulus choice;
    • the analytic bounds / measurability / Lipschitz / Levi fields are all satisfiable by the true
      chart-pullback amplitude of `H_G` (banked coefficient + measurability layers);
    • the ONE hard field `hD2Hexpand` is satisfiable by the true amplitude — this file EXHIBITS the
      exact factored source (the on-gate `G_τ(W z x')·amp` shape, `vanVleckGatedWitness_gate_apply`)
      and, in `residueJets_satisfiable`, MACHINE-CHECKS that the residue chart-jet bundle the discharge
      reduces `hD2Hexpand` to is jointly satisfiable (an explicit `V = z + ·`, `A ≡ 1`, `P = eᵢ`,
      `Q = 0` model), so the reduction introduces NO vacuity.
    No facade artefact detected (contrast the three caught earlier in the campaign; like the Da-limit
    pile, this bundle is clean).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE DISCHARGE MAP for `hD2Hexpand`.

  The on-gate value of the witness (banked, `vanVleckGatedWitness_gate_apply`, J4-126) is
      H_G τ x' z = radialCutoff a b (W z x') · G_τ(W z x') · Θ(W z x')^{−1/2} · (u₀+u₁τ),
      W := uniformInverseChart g gi hC hK,   G_τ := gaussDdim τ,
  i.e. near `x' = 0` the witness FACTORS as `G_τ(V x')·A x'` with

      V x' := W z x'  (the per-base inverse chart, field slot `x'`, base `z`),
      A x' := radialCutoff a b (W z x')·Θ(W z x')^{−1/2}·(u₀(W z x')+u₁(W z x')·τ).

  Feeding this factorization into the banked SECOND-`x`-derivative normal form
  `gaussComp_amp_center_decomp` (J4-130) gives EXACTLY the 3-term Leibniz–Gaussian shape, provided the
  chart jets at the center reduce the coefficients:
      gaussDdim τ (V 0) = gaussDdim τ z,   ∑ₖ V0ₖ·P0ₖ = z i,   ∑ₖ P0ₖ² = 1,   ∑ₖ V0ₖ·Qₖ = 0,
  with `P`, `Q` the first/second `i`-jets of `V`.  Under those, one reads off the amplitudes:
      Aamp = A 0,   A1amp = −2·∂ᵢA(0),   A2amp = ∂ᵢ²A(0).

  The FIRST jet identity `gaussDdim τ (V 0) = gaussDdim τ z` is precisely the ONE genuine geometric
  wall this brick isolates — the "chart-image Gaussian" fact `‖W z 0‖ = d_g(z,0) = ‖z‖` (RNC
  near-isometry, off-flat an `O(‖z‖⁴)` discrepancy absorbed into the amplitude).  It is NOT fabricated
  and NOT the conclusion; it is the derivative-layer geometry, CARRIED.

  WHAT LANDS here (unconditionally, no `sorry`, no new axioms):
    • `pd_congr_of_eventuallyEq`  / `pd_pd_congr_of_eventuallyEq` — germ-congruence for the coordinate
      partial and its iterate (so a NEAR-`0` factorization suffices; the global-equality form would be
      FALSE off-gate, hence UNSATISFIABLE — the germ form keeps every hypothesis satisfiable).
    • `witnessSecondXDeriv_expand_bridge` — ★ THE D2 REDUCTION: from the germ representation + chart
      jets, the concrete `witnessSecondXDeriv` equals the exact `hD2Hexpand` RHS (with the amplitudes
      identified as above).  The Leibniz algebra is DISCHARGED via the banked `gaussComp_amp_center_decomp`.
    • `residueJets_satisfiable` — the satisfiability audit, machine-checked: the residue chart-jet
      bundle (everything the reduction needs EXCEPT the germ representation) is jointly satisfiable.

  REMAINING WALL (isolated, named, NOT closed here): the germ representation `hrep` of the concrete
  witness as `G_τ(V ·)·A ·` near `0` on the gate interior — i.e. the chart-image Gaussian identity
  `gaussDdim τ (W z 0) = gaussDdim τ z`.  This is the residue the bridge reduces `hD2Hexpand` to.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmplitudePackage
import QIQTH.ChartJetHessian

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation

namespace QIQTH.D2HExpandRecon

open QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    S1 — germ congruence for the coordinate partial `pd` and its iterate.
    ############################################################################### -/

/-- **Germ congruence for `pd`.**  If `f =ᶠ[𝓝 x] g` then `∂ᵢf(x) = ∂ᵢg(x)`.  `pd` reads only the
    germ at `x`: the line map `s ↦ update x i s` is continuous with value `x` at `s = x i`, so the two
    composed lines agree near `x i`, and `deriv` is germ-local. -/
theorem pd_congr_of_eventuallyEq (f g : Point n → ℝ) (i : Fin n) (x : Point n)
    (hfg : f =ᶠ[nhds x] g) : pd f i x = pd g i x := by
  simp only [pd]
  apply Filter.EventuallyEq.deriv_eq
  have hcont : Continuous (fun s : ℝ => Function.update x i s) :=
    continuous_const.update i continuous_id
  have hpt : Function.update x i (x i) = x := Function.update_eq_self i x
  have hmem : (fun s : ℝ => Function.update x i s) ⁻¹' {y | f y = g y} ∈ nhds (x i) := by
    apply ContinuousAt.preimage_mem_nhds hcont.continuousAt
    show {y | f y = g y} ∈ nhds (Function.update x i (x i))
    rw [hpt]; exact hfg
  exact hmem

/-- **Germ congruence for the second coordinate partial.**  If `f =ᶠ[𝓝 x₀] g` then
    `∂ᵢ(∂ᵢf)(x₀) = ∂ᵢ(∂ᵢg)(x₀)`.  On the open set where `f = g`, every point has `f =ᶠ g` in its own
    neighbourhood, so the first partials agree there, and germ congruence closes the outer partial. -/
theorem pd_pd_congr_of_eventuallyEq (f g : Point n → ℝ) (i : Fin n) (x₀ : Point n)
    (hfg : f =ᶠ[nhds x₀] g) :
    pd (fun y => pd f i y) i x₀ = pd (fun y => pd g i y) i x₀ := by
  apply pd_congr_of_eventuallyEq
  have h2 : ∀ᶠ y in nhds x₀, f =ᶠ[nhds y] g := eventually_eventually_nhds.mpr hfg
  filter_upwards [h2] with y hy
  exact pd_congr_of_eventuallyEq f g i y hy

/-! ###############################################################################
    S2 — the D2 reduction of `hD2Hexpand` (the Leibniz–Gaussian derivative layer).
    ############################################################################### -/

/-- **★ THE D2 BRIDGE — `witnessSecondXDeriv_expand_bridge`.**  From
      • `hrep` : the concrete witness factors as `G_τ(V ·)·A ·` in a NEIGHBOURHOOD of the RNC center
        `x' = 0` (the on-gate factorization germ; the isolated geometric residue),
      • the chart first/second `i`-jets `hV1`/`hP1` of `V` and the amplitude jets `hA1`/`hA2` of `A`,
      • the four center chart-jet identities `hV0`/`hVP`/`hPsq`/`hVQ`,
    the concrete `witnessSecondXDeriv` obeys the EXACT `AmplitudeDerivativeData.hD2Hexpand` 3-term shape
      `= (z i²−2τ)/(4τ²)·gaussDdim τ z·(A 0)
         + z i/(2τ)·gaussDdim τ z·(−2·∂ᵢA(0))
         + gaussDdim τ z·(∂ᵢ²A(0))`,
    i.e. with `Aamp = A 0`, `A1amp = −2·∂ᵢA(0)`, `A2amp = ∂ᵢ²A(0)`.  The Leibniz algebra is discharged
    by the banked normal form `gaussComp_amp_center_decomp` (J4-130); the germ suffices via
    `pd_pd_congr_of_eventuallyEq`.  This REDUCES `hD2Hexpand` to `hrep` + the (satisfiable) chart jets.
    ⚠ NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_expand_bridge
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (z : Point n)
    (V : Point n → Point n) (A : Point n → ℝ) (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hrep : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
              =ᶠ[nhds (0 : Point n)] (fun x' => gaussDdim τ (V x') * A x'))
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i (0 : Point n))
    (hV0 : gaussDdim τ (V 0) = gaussDdim τ z)
    (hVP : ∑ k, V 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, V 0 k * Q k = 0) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * A 0
        + z i / (2 * τ) * gaussDdim τ z * (-2 * pd A i 0)
        + gaussDdim τ z * pd (fun y => pd A i y) i 0 := by
  unfold witnessSecondXDeriv
  rw [pd_pd_congr_of_eventuallyEq
        (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
        (fun x' => gaussDdim τ (V x') * A x') i (0 : Point n) hrep,
      gaussComp_amp_center_decomp V A P Q τ hτ i hV1 hP1 hA1 hA2,
      hV0, hVP, hPsq, hVQ]
  have hτ' : τ ≠ 0 := hτ.ne'
  have h2τ : (2 : ℝ) * τ ≠ 0 := by positivity
  have h4τ : (4 : ℝ) * τ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ###############################################################################
    S3 — the satisfiability audit (machine-checked non-vacuity of the residue jets).
    ############################################################################### -/

/-- **★ SATISFIABILITY AUDIT — `residueJets_satisfiable`.**  The residue chart-jet bundle that
    `witnessSecondXDeriv_expand_bridge` reduces `hD2Hexpand` to — EVERYTHING the reduction consumes
    EXCEPT the germ representation `hrep` — is JOINTLY SATISFIABLE, exhibited by the explicit RNC model
      `V := z + ·`,   `A ≡ 1`,   `P := eᵢ` (`k ↦ if k = i then 1 else 0`),   `Q := 0`.
    Under this model all four center identities hold: `gaussDdim τ (V 0) = gaussDdim τ z`,
    `∑ V0·P0 = z i`, `∑ P0² = 1`, `∑ V0·Q = 0`, together with the first/second `i`-jets and amplitude
    differentiabilities.  This PROVES the discharge introduces NO vacuity: none of the carried residue
    hypotheses is contradictory or over-quantified.  (The isolated `hrep` germ — the chart-image
    Gaussian identity — is the ONE genuine geometric residue, not covered by this toy model and NOT
    claimed here.)  ⚠ NOT `a₁ = R/6`. -/
theorem residueJets_satisfiable (τ : ℝ) (z : Point n) (i : Fin n) :
    ∃ (V : Point n → Point n) (A : Point n → ℝ) (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
      (∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i)) ∧
      (∀ k, HasDerivAt
        (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) ∧
      (∀ x, PdiffAt A i x) ∧
      PdiffAt (fun y => pd A i y) i (0 : Point n) ∧
      gaussDdim τ (V 0) = gaussDdim τ z ∧
      (∑ k, V 0 k * P 0 k) = z i ∧
      (∑ k, P 0 k ^ 2) = 1 ∧
      (∑ k, V 0 k * Q k) = 0 := by
  refine ⟨fun y k => z k + y k, fun _ => (1 : ℝ), fun _ k => if k = i then (1 : ℝ) else 0,
    fun _ => (0 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hV1: first `i`-jet of `V = z + ·`
    intro x k
    dsimp only
    rcases eq_or_ne k i with hk | hk
    · subst hk
      rw [if_pos rfl]
      have hfun : (fun s : ℝ => z k + Function.update x k s k) = (fun s => z k + s) := by
        funext s; rw [Function.update_self]
      rw [hfun]
      exact (hasDerivAt_const_add_iff (z k)).mpr (hasDerivAt_id (x k))
    · rw [if_neg hk]
      have hfun : (fun s : ℝ => z k + Function.update x i s k) = (fun _ => z k + x k) := by
        funext s; rw [Function.update_of_ne hk]
      rw [hfun]
      exact hasDerivAt_const (x i) (z k + x k)
  · -- hP1: the second `i`-jet of the constant field `P = eᵢ` is `0`
    intro k
    dsimp only
    exact hasDerivAt_const _ _
  · -- hA1: `A ≡ 1` is `pd`-differentiable everywhere
    intro x
    exact differentiableAt_const 1
  · -- hA2: `∂ᵢ(A) ≡ 0` is `pd`-differentiable at `0`
    have hc : (fun y : Point n => pd (fun _ => (1 : ℝ)) i y) = fun _ => (0 : ℝ) := by
      funext y; exact pd_const 1 i y
    rw [hc]
    exact differentiableAt_const 0
  · -- hV0: `V 0 = z`
    have hV0eq : (fun y k => z k + y k) (0 : Point n) = z := by
      funext k; simp
    rw [hV0eq]
  · -- hVP: `∑ V0·P0 = z i`
    dsimp only
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  · -- hPsq: `∑ P0² = 1`
    dsimp only
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  · -- hVQ: `∑ V0·Q = 0`
    dsimp only
    simp

end QIQTH.D2HExpandRecon

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq
#print axioms QIQTH.D2HExpandRecon.pd_pd_congr_of_eventuallyEq
#print axioms QIQTH.D2HExpandRecon.witnessSecondXDeriv_expand_bridge
#print axioms QIQTH.D2HExpandRecon.residueJets_satisfiable
