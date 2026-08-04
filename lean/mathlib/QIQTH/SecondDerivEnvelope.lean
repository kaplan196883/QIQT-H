/-
  SecondDerivEnvelope — J4-198: the ORDER-2 `hD1` feed of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It supplies three
  order-2 analogues of the banked order-1 `EngineInstantiation` / `GatedDInstantiation` bricks (the
  E1/E2 on-gate formula & envelope, the J4-185 measurable-representative measurability) for the SECOND
  field-derivative kernel `witnessFieldDeriv2` of the concrete `N = 1` van-Vleck gated witness, and it
  states — with rigorous Lean support — the honest INTEGRABILITY VERDICT for the `hD1` route.

  ── WHAT THIS FEEDS.  `SpatialC2.hCConv_reduction` reduces the `∞`-capstone's `hCConv` (`C²`) slot to
     `hD1 : ContDiffAt ℝ 1 D 0`, the `C¹`-regularity of the first-derivative field `D` whose components
     are the `gcoef` double integrals `gcoef i x = ∫₀ᵗ∫ dH·F`.  The `hD1` route mirrors the L1
     architecture ONE ORDER UP via `EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated` (J4-197),
     applied with `K := witnessFieldDeriv·F` and `K' := witnessFieldDeriv2·F`.  That abstract lever
     needs (a) the order-2 gate ENVELOPE and (b) the order-2 joint MEASURABILITY — supplied here — plus
     an `s`-integrable outer dominator `B` in its `hBint` slot.  §C settles whether that slot is even
     satisfiable at the honest order-2 rate.

  ── WHAT LANDS (this file, ns `QIQTH.SecondDerivEnvelope`).

    §A — THE ORDER-2 ON-GATE FORMULA + ENVELOPE (the E1/E2 pattern one order up).
      • `witnessFieldDeriv2_gate_eq` — on the OPEN gate (base `z ∈ K`, field point `p ∈ S z`), the
        second field-derivative kernel is the 3-term Leibniz–Gaussian normal form (`gaussComp_amp_pd_pd`
        at the GENERAL field point `p`, not just the centre `0` of `hNormalForm_concrete`):
          `dHH i τ p z = G·(⟨V,P⟩²/(4τ²) − (⟨P,P⟩+⟨V,Q⟩)/(2τ))·A`
                      ` + 2·(G·(−⟨V,P⟩/(2τ)))·∂ᵢA + G·∂ᵢ∂ᵢA`,
        `G := gaussDdim τ (W z p)`, `V := W z p`, `A := chartFieldAmp`, `P`/`Q` the carried first/second
        field jets of `W z` at `p`.
      • `witnessFieldDeriv2_gate_abs_le` — ★ THE ORDER-2 GATE ENVELOPE (E2 one order up): triangle
        inequality on the 3-term form, `|dHH| ≤ G·(Bs2·Ba + 2·Bs1·Bd + Bdd)` from the carried scalar /
        amplitude sup-bounds.  The `1/τ²` (Hessian) and `1/τ` (gradient) singular powers live INSIDE
        the carried scalar bounds `Bs2`/`Bs1` — the source of the §C integrability wall.
      • `witnessFieldDeriv2_envelope_coercive` — the `x`-free-Gaussian form: compose with the coercivity
        `gaussDdim_halfcoer_le` ⟹ `|dHH| ≤ (√2)ⁿ·G_{2τ}(z)·(Bs2·Ba + 2·Bs1·Bd + Bdd)`.

    §B — THE ORDER-2 MEASURABILITY (the J4-185 `GatedDInstantiation` mirror one order up).
      • `gatedDeriv2Rep` — the `z ∈ K`-indicator of the order-2 on-gate closed form (carrying first/second
        jet fields `Pfield`/`Qfield`).
      • `gatedDeriv2Rep_measurable` — its joint `(s,z)`-Borel measurability.
      • `witnessFieldDeriv2_eq_zero_of_nonpos` — for `τ ≤ 0` (`0 < n`) the kernel vanishes.
      • `witnessFieldDeriv2_eq_gatedDeriv2Rep` — the EVERYWHERE identity via the three-way dichotomy
        (`z ∉ K` / `z ∈ K, τ ≤ 0` / `z ∈ K, τ > 0`).
      • `witnessFieldDeriv2_measurable_of_gateEq` — ★★ the joint `(s,z)`-measurability of the raw
        second-derivative kernel.  THE minimum-bankable deliverable (the order-2 `hD1` measurability).

    §C — THE INTEGRABILITY VERDICT (rigorous Lean facts + the honest route statement).
      • `order2_naive_dominator_not_intervalIntegrable` — ★ for `0 < t`, `0 < C`, the honest order-2
        `s`-dominator `s ↦ C·(t−s)⁻¹` is NOT interval-integrable on `(0,t)`.  After the `z`-integral the
        order-2 envelope's LEADING term is `(1/τ²)·⟨V,P⟩²·G_{2τ}` with `V ≈ z`, whose `z`-mass is
        `(1/τ²)·(2nd moment ≈ τ) = 1/τ = (t−s)⁻¹`; the `hBint` slot of the J4-197 naive lever therefore
        has NO admissible dominator.  ⟹ **hD1 does NOT go through the naive lever.**
      • `sliver_rate_intervalIntegrable` — the sliver route's `(t−s)^{−1/2}` rate IS interval-integrable
        (`∫₀ᵗ(t−s)^{−1/2} = 2√t`), the `√ε` gain of `witness_sliver2_grand`/`witness_sliver2_concrete`.
        ⟹ **hD1 must use the SLIVER-TRUNCATION route** (the √ε machinery mirrored one order up):
        split `(0,t) = (0,t−ε] [bulk: τ bounded below, the `1/τ`-powers are fine, naive lever works]`
        `∪ (t−ε,t] [sliver: the cancellation `G_τ(Wz)−G_τ(z)` upgrades `τ^{−1}` to `τ^{−1/2}`, giving
        the `2√ε` bound]` — EXACTLY as the banked hDaLimLU chain (`witness_sliver2_concrete`) did.

  No conclusion-in-disguise; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.
  All mains std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EngineInstantiation
import QIQTH.GatedDInstantiation

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SecondDerivEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the order-2 on-gate formula, envelope, and coercive envelope.
    ############################################################################### -/

/-- **General-base second-order germ congruence of `pd∘pd`.**  The `pd_pd_congr_of_eventuallyEq`
    (`NormalFormDischarge`, stated at the centre `0`) at an arbitrary base point `p`: if `f =ᶠ[𝓝 p] f'`
    then `pd (pd f i) i p = pd (pd f' i) i p`.  Same route (pick an open `V ∋ p`, apply the first-order
    germ-locality `pd_congr_of_eventuallyEq` on `V`, then once more on the outer `pd`). -/
theorem pd_pd_congr_at (f f' : Point n → ℝ) (i : Fin n) (p : Point n)
    (h : ∀ᶠ x in 𝓝 p, f x = f' x) :
    pd (fun y => pd f i y) i p = pd (fun y => pd f' i y) i p := by
  apply pd_congr_of_eventuallyEq
  obtain ⟨V, hVeq, hVopen, hVp⟩ := eventually_nhds_iff.mp h
  refine eventually_nhds_iff.mpr ⟨V, ?_, hVopen, hVp⟩
  intro y hyV
  exact pd_congr_of_eventuallyEq f f' i y (eventually_nhds_iff.mpr ⟨V, hVeq, hVopen, hyV⟩)

/-- **★ §A — `witnessFieldDeriv2_gate_eq` — THE ON-GATE ORDER-2 FORMULA (at a general field point).**
    On the OPEN gate (base `z ∈ K`, field point `p ∈ S z`), with the carried chart field jets `P`/`Q`
    and amplitude differentiabilities, the second field-derivative kernel of the gated `N = 1` van-Vleck
    witness equals the 3-term Leibniz–Gaussian normal form (`ChartJetHessian.gaussComp_amp_pd_pd` at
    `x₀ = p`).  The `p = 0` specialisation is `hNormalForm_concrete` (up to the `sTerm` regrouping); this
    keeps the raw `gaussComp` form and holds at every gate-interior field point `p`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_gate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetV : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hJetP : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update p i s) k) (Q k) (p i))
    (hAmp1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p) :
    witnessFieldDeriv2 g gi hC hK S a b i τ p z
      = gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * ((∑ k, uniformInverseChart g gi hC hK z p k * P p k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P p k ^ 2)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ))
          * chartFieldAmp g gi hC hK a b τ z p
        + 2 * (gaussDdim τ (uniformInverseChart g gi hC hK z p)
              * (-(∑ k, uniformInverseChart g gi hC hK z p k * P p k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) i p
        + gaussDdim τ (uniformInverseChart g gi hC hK z p)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p := by
  -- on-gate nbhd factorisation of the witness in the field slot (same as the order-1 gate-eq).
  have hev : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      =ᶠ[𝓝 p]
      (fun x' : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z x')
          * chartFieldAmp g gi hC hK a b τ z x') := by
    refine eventually_nhds_iff.mpr ⟨S z, ?_, hSopen, hp⟩
    intro x' hx'
    show vanVleckGatedWitness g gi hC hK S a b τ x' z
        = gaussDdim τ (uniformInverseChart g gi hC hK z x') * chartFieldAmp g gi hC hK a b τ z x'
    rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hz hx']
    simp only [chartFieldAmp]
    ring
  -- transfer the local `pd∘pd` off the factored form, then apply the Leibniz–Gaussian normal form.
  have hstep : witnessFieldDeriv2 g gi hC hK S a b i τ p z
      = pd (fun y => pd (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
            * chartFieldAmp g gi hC hK a b τ z x') i y) i p := by
    unfold witnessFieldDeriv2
    exact pd_pd_congr_at
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
        * chartFieldAmp g gi hC hK a b τ z x') i p hev
  rw [hstep, gaussComp_amp_pd_pd (uniformInverseChart g gi hC hK z)
      (chartFieldAmp g gi hC hK a b τ z) P Q τ hτ i p hJetV hJetP hAmp1 hAmp2]

/-- **★★ §A — `witnessFieldDeriv2_gate_abs_le` — THE ORDER-2 GATE ENVELOPE.**  From the on-gate 3-term
    order-2 formula (`witnessFieldDeriv2_gate_eq`) and the carried factor sup-bounds
      `|hessScalar| ≤ Bs2`,  `|gradScalar| ≤ Bs1`,  `|A| ≤ Ba`,  `|∂ᵢA| ≤ Bd`,  `|∂ᵢ∂ᵢA| ≤ Bdd`,
    where `hessScalar := ⟨V,P⟩²/(4τ²) − (⟨P,P⟩+⟨V,Q⟩)/(2τ)`, `gradScalar := −⟨V,P⟩/(2τ)`, the second
    field-derivative kernel obeys the Gaussian-envelope pointwise bound
      `|dHH i τ p z| ≤ G_τ(W z p)·(Bs2·Ba + 2·Bs1·Bd + Bdd)`.
    The `1/τ²`/`1/τ` singular powers of `witnessFieldDeriv2` sit INSIDE the carried scalar bounds
    `Bs2`/`Bs1` (whose sources are `GaussianPolyBound.heatKernel1D_deriv_x_abs_le` one order up).  Pure
    triangle inequality on the on-gate formula (the E2 pattern one order up).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_gate_abs_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetV : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hJetP : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update p i s) k) (Q k) (p i))
    (hAmp1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p)
    (Bs2 Bs1 Ba Bd Bdd : ℝ)
    (hSc2 : |(∑ k, uniformInverseChart g gi hC hK z p k * P p k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P p k ^ 2)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ)| ≤ Bs2)
    (hSc1 : |(-(∑ k, uniformInverseChart g gi hC hK z p k * P p k) / (2 * τ))| ≤ Bs1)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd)
    (hBdd : |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p| ≤ Bdd) :
    |witnessFieldDeriv2 g gi hC hK S a b i τ p z|
      ≤ gaussDdim τ (uniformInverseChart g gi hC hK z p) * (Bs2 * Ba + 2 * Bs1 * Bd + Bdd) := by
  rw [witnessFieldDeriv2_gate_eq g gi hC hK S a b i τ hτ z hz hSopen p hp P Q hJetV hJetP hAmp1 hAmp2]
  set G := gaussDdim τ (uniformInverseChart g gi hC hK z p) with hGdef
  set hs := (∑ k, uniformInverseChart g gi hC hK z p k * P p k) ^ 2 / (4 * τ ^ 2)
      - ((∑ k, P p k ^ 2) + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ) with hsdef
  set gr := -(∑ k, uniformInverseChart g gi hC hK z p k * P p k) / (2 * τ) with grdef
  set A := chartFieldAmp g gi hC hK a b τ z p with hAdef
  set dA := pd (chartFieldAmp g gi hC hK a b τ z) i p with hdAdef
  set ddA := pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p with hddAdef
  have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
  have hBs2nn : 0 ≤ Bs2 := le_trans (abs_nonneg _) hSc2
  have hBs1nn : 0 ≤ Bs1 := le_trans (abs_nonneg _) hSc1
  have hBdnn : 0 ≤ Bd := le_trans (abs_nonneg _) hBd
  calc |G * hs * A + 2 * (G * gr) * dA + G * ddA|
      ≤ |G * hs * A| + |2 * (G * gr) * dA| + |G * ddA| := by
        have h1 := abs_add_le (G * hs * A + 2 * (G * gr) * dA) (G * ddA)
        have h2 := abs_add_le (G * hs * A) (2 * (G * gr) * dA)
        linarith
    _ = G * |hs| * |A| + 2 * (G * |gr|) * |dA| + G * |ddA| := by
        simp only [abs_mul, abs_of_nonneg hGnn, abs_two]
    _ ≤ G * Bs2 * Ba + 2 * (G * Bs1) * Bd + G * Bdd := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hSc2 hGnn) hBa (abs_nonneg _)
            (mul_nonneg hGnn hBs2nn)
        · refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hBd (abs_nonneg _)
            (by positivity)
          exact mul_le_mul_of_nonneg_left hSc1 hGnn
        · exact mul_le_mul_of_nonneg_left hBdd hGnn
    _ = G * (Bs2 * Ba + 2 * Bs1 * Bd + Bdd) := by ring

/-- **★ §A — `witnessFieldDeriv2_envelope_coercive` — THE `x`-FREE-GAUSSIAN ORDER-2 ENVELOPE.**
    Composing the order-2 gate envelope (`witnessFieldDeriv2_gate_abs_le`) with the ℓ²-coercivity
    argument-substitution `gaussDdim_halfcoer_le` (`G_τ(W z p) ≤ (√2)ⁿ·G_{2τ}(z)` under the carried
    near-isometry lower bound `hco : ½·r²_z ≤ r²_{W z p}`) replaces the entangled chart Gaussian by a
    width-doubled PLAIN Gaussian in the base `z`:
      `|dHH i τ p z| ≤ (√2)ⁿ·G_{2τ}(z)·(Bs2·Ba + 2·Bs1·Bd + Bdd)`.
    ⚠  This is the POINTWISE `z`-dominator; the `1/τ²`/`1/τ` powers still reside in `Bs2`/`Bs1`, so its
    `z`-integral (∫ carries `⟨V,P⟩²` ≈ 2nd `z`-moment ≈ `τ`) leaves the LEADING `s`-rate `(t−s)⁻¹` — the
    §C non-integrability.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_envelope_coercive (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetV : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hJetP : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update p i s) k) (Q k) (p i))
    (hAmp1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p)
    (Bs2 Bs1 Ba Bd Bdd : ℝ)
    (hSc2 : |(∑ k, uniformInverseChart g gi hC hK z p k * P p k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P p k ^ 2)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ)| ≤ Bs2)
    (hSc1 : |(-(∑ k, uniformInverseChart g gi hC hK z p k * P p k) / (2 * τ))| ≤ Bs1)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd)
    (hBdd : |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i p| ≤ Bdd)
    (hBenv : 0 ≤ Bs2 * Ba + 2 * Bs1 * Bd + Bdd)
    (hco : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z p)) :
    |witnessFieldDeriv2 g gi hC hK S a b i τ p z|
      ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z * (Bs2 * Ba + 2 * Bs1 * Bd + Bdd) := by
  refine le_trans (witnessFieldDeriv2_gate_abs_le g gi hC hK S a b i τ hτ z hz hSopen p hp
    P Q hJetV hJetP hAmp1 hAmp2 Bs2 Bs1 Ba Bd Bdd hSc2 hSc1 hBa hBd hBdd) ?_
  refine mul_le_mul_of_nonneg_right ?_ hBenv
  exact gaussDdim_halfcoer_le τ hτ (uniformInverseChart g gi hC hK z p) z hco

/-! ###############################################################################
    ### §B — the order-2 measurability (the J4-185 `GatedDInstantiation` mirror).
    ############################################################################### -/

/-- **`gatedDeriv2Rep` — the measurable explicit representative of `witnessFieldDeriv2`.**  For a fixed
    field point `x` and carried first/second jet fields `Pfield`/`Qfield`, the `z ∈ K`-indicator of the
    order-2 on-gate closed form (`witnessFieldDeriv2_gate_eq`), `τ := t − p.1`, `V := W p.2 x`:
      `p ↦ 𝟙_{p.2 ∈ K}·( G·(⟨V,P⟩²/(4τ²) − (⟨P,P⟩+⟨V,Q⟩)/(2τ))·A`
                     `+ 2·(G·(−⟨V,P⟩/(2τ)))·∂ᵢA + G·∂ᵢ∂ᵢA )`.
    `witnessFieldDeriv2` will be shown to EQUAL this everywhere, so its joint `(s,z)`-measurability rides
    the representative.  NOT `a₁ = R/6`. -/
noncomputable def gatedDeriv2Rep (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Fin n → ℝ) : ℝ × Point n → ℝ :=
  Set.indicator (Prod.snd ⁻¹' K)
    (fun p : ℝ × Point n =>
      gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)
          * ((∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 x k) ^ 2 / (4 * (t - p.1) ^ 2)
              - ((∑ k, Pfield p.2 x k ^ 2)
                  + (∑ k, uniformInverseChart g gi hC hK p.2 x k * Qfield p.2 k)) / (2 * (t - p.1)))
          * chartFieldAmp g gi hC hK a b (t - p.1) p.2 x
        + 2 * (gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)
              * (-(∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 x k) / (2 * (t - p.1))))
            * pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x
        + gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x)

/-- **★ `gatedDeriv2Rep_measurable`.**  The joint `(s,z)`-Borel measurability of the order-2 explicit
    representative, from `hKmeasSet` (`MeasurableSet K`), `hChartMeas` (Borel chart-in-`z`), `hPmeas`
    /`hQmeas` (first/second jet fields), `hAmpMeas`/`hAmpDerivMeas`/`hAmpDeriv2Meas` (amplitude and its
    first/second field-`pd`).  The `gaussDdim` factor is jointly measurable via
    `gaussDdim_uncurry_measurable`; the `1/τ²`/`1/τ` denominators are `measurable_const.sub
    measurable_fst`-built (no singularity issue: measurability, not integrability).  NOT `a₁ = R/6`. -/
theorem gatedDeriv2Rep_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x))
    (hPmeas : ∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 x k))
    (hQmeas : ∀ k, Measurable (fun p : ℝ × Point n => Qfield p.2 k))
    (hAmpMeas : Measurable
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x))
    (hAmpDerivMeas : Measurable
      (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hAmpDeriv2Meas : Measurable
      (fun p : ℝ × Point n => pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x)) :
    Measurable (gatedDeriv2Rep g gi hC hK a b i t x Pfield Qfield) := by
  unfold gatedDeriv2Rep
  have hG : Measurable
      (fun p : ℝ × Point n => gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)) :=
    gaussDdim_uncurry_measurable.comp ((measurable_const.sub measurable_fst).prodMk hChartMeas)
  have hVP : Measurable
      (fun p : ℝ × Point n => ∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 x k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hPmeas k)
  have hPP : Measurable
      (fun p : ℝ × Point n => ∑ k, Pfield p.2 x k ^ 2) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact (hPmeas k).pow_const 2
  have hVQ : Measurable
      (fun p : ℝ × Point n => ∑ k, uniformInverseChart g gi hC hK p.2 x k * Qfield p.2 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hQmeas k)
  have hden2 : Measurable (fun p : ℝ × Point n => 4 * (t - p.1) ^ 2) :=
    measurable_const.mul ((measurable_const.sub measurable_fst).pow_const 2)
  have hden1 : Measurable (fun p : ℝ × Point n => 2 * (t - p.1)) :=
    measurable_const.mul (measurable_const.sub measurable_fst)
  have hHess : Measurable
      (fun p : ℝ × Point n =>
        (∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 x k) ^ 2 / (4 * (t - p.1) ^ 2)
          - ((∑ k, Pfield p.2 x k ^ 2)
              + (∑ k, uniformInverseChart g gi hC hK p.2 x k * Qfield p.2 k)) / (2 * (t - p.1))) :=
    ((hVP.pow_const 2).div hden2).sub ((hPP.add hVQ).div hden1)
  have hGrad : Measurable
      (fun p : ℝ × Point n =>
        -(∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 x k) / (2 * (t - p.1))) :=
    hVP.neg.div hden1
  refine Measurable.indicator ?_ (measurable_snd hKmeasSet)
  exact (((hG.mul hHess).mul hAmpMeas).add
      ((measurable_const.mul (hG.mul hGrad)).mul hAmpDerivMeas)).add (hG.mul hAmpDeriv2Meas)

/-- **`witnessFieldDeriv2_eq_zero_of_nonpos`.**  For `τ ≤ 0` (`0 < n`) the whole gated witness slot
    vanishes (`GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos` for its field-`pd`), so the
    SECOND field-`pd` — being the field-`pd` of the identically-`0` first — also vanishes.  The leg that
    makes the representative identity hold everywhere.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_eq_zero_of_nonpos (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (hτ : τ ≤ 0) :
    witnessFieldDeriv2 g gi hC hK S a b i τ p z = 0 := by
  rw [witnessFieldDeriv2_eq_pd_witnessFieldDeriv]
  have hz0 : (fun x : Point n => witnessFieldDeriv g gi hC hK S a b i τ x z) = fun _ => (0 : ℝ) := by
    funext x
    exact QIQTH.GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos hn g gi hC hK S a b i τ x z hτ
  rw [hz0]
  exact pd_const 0 i p

/-- **★ `witnessFieldDeriv2_eq_gatedDeriv2Rep` — THE EVERYWHERE IDENTITY.**  The raw second-derivative
    kernel EQUALS the explicit representative at every `p = (s,z)`, via the three-way dichotomy:
      • `z ∉ K` — both `0` (`witnessFieldDeriv2_offGate_eq_zero`, `Set.indicator_of_notMem`);
      • `z ∈ K`, `τ = t−s ≤ 0` — LHS `0` (`witnessFieldDeriv2_eq_zero_of_nonpos`), RHS `0` (the shared
        `gaussDdim (t−s)` factor vanishes, `gaussDdim_eq_zero_of_nonpos`, killing all 3 terms);
      • `z ∈ K`, `τ > 0` — the order-2 on-gate formula (`witnessFieldDeriv2_gate_eq`) with the carried
        jet/openness data `hgate`.
    NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_eq_gatedDeriv2Rep (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Fin n → ℝ)
    (hgate : ∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
        IsOpen (S p.2) ∧ x ∈ S p.2 ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update y i s) k)
          (Pfield p.2 y k) (y i)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pfield p.2 (Function.update x i s) k) (Qfield p.2 k) (x i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x) :
    ∀ p : ℝ × Point n,
      witnessFieldDeriv2 g gi hC hK S a b i (t - p.1) x p.2
        = gatedDeriv2Rep g gi hC hK a b i t x Pfield Qfield p := by
  intro p
  simp only [gatedDeriv2Rep]
  by_cases hzK : p.2 ∈ K
  · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' K from hzK)]
    by_cases hτ : 0 < t - p.1
    · obtain ⟨hSopen, hxS, hjetV, hjetP, hamp1, hamp2⟩ := hgate p hzK hτ
      exact witnessFieldDeriv2_gate_eq g gi hC hK S a b i (t - p.1) hτ p.2 hzK hSopen x hxS
        (Pfield p.2) (Qfield p.2) hjetV hjetP hamp1 hamp2
    · rw [not_lt] at hτ
      rw [witnessFieldDeriv2_eq_zero_of_nonpos hn g gi hC hK S a b i (t - p.1) x p.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn (t - p.1) (uniformInverseChart g gi hC hK p.2 x) hτ]
      ring
  · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' K from hzK)]
    exact witnessFieldDeriv2_offGate_eq_zero g gi hC hK S a b i (t - p.1) x p.2 hzK

/-- **★★ `witnessFieldDeriv2_measurable_of_gateEq` — THE ORDER-2 `hD1` MEASURABILITY.**  The joint
    `(s,z)`-Borel measurability of the raw concrete SECOND field-derivative van-Vleck witness kernel
    `(s,z) ↦ witnessFieldDeriv2 … i (t−s) x z` at a fixed field point `x`, obtained by rewriting it —
    via the everywhere identity (`witnessFieldDeriv2_eq_gatedDeriv2Rep`) — as the manifestly measurable
    explicit representative `gatedDeriv2Rep` (`gatedDeriv2Rep_measurable`).  The order-2 analogue of
    `GatedDInstantiation.witnessFieldDeriv_measurable_of_gateEq` (J4-185); THE minimum-bankable feed for
    the `hD1` dominated-differentiation lever's `hK'meas`/`hG'meas` slots.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_measurable_of_gateEq (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x))
    (hPmeas : ∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 x k))
    (hQmeas : ∀ k, Measurable (fun p : ℝ × Point n => Qfield p.2 k))
    (hAmpMeas : Measurable
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x))
    (hAmpDerivMeas : Measurable
      (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hAmpDeriv2Meas : Measurable
      (fun p : ℝ × Point n => pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x))
    (hgate : ∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
        IsOpen (S p.2) ∧ x ∈ S p.2 ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update y i s) k)
          (Pfield p.2 y k) (y i)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pfield p.2 (Function.update x i s) k) (Qfield p.2 k) (x i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i y) i x) :
    Measurable (fun p : ℝ × Point n =>
      witnessFieldDeriv2 g gi hC hK S a b i (t - p.1) x p.2) := by
  have hrw : (fun p : ℝ × Point n => witnessFieldDeriv2 g gi hC hK S a b i (t - p.1) x p.2)
      = gatedDeriv2Rep g gi hC hK a b i t x Pfield Qfield := by
    funext p
    exact witnessFieldDeriv2_eq_gatedDeriv2Rep hn g gi hC hK S a b i t x Pfield Qfield hgate p
  rw [hrw]
  exact gatedDeriv2Rep_measurable g gi hC hK a b i t x Pfield Qfield hKmeasSet hChartMeas hPmeas
    hQmeas hAmpMeas hAmpDerivMeas hAmpDeriv2Meas

/-! ###############################################################################
    ### §C — the integrability verdict (rigorous facts + the honest route statement).
    ############################################################################### -/

/-- **★ §C — `order2_naive_dominator_not_intervalIntegrable` — THE NAIVE-LEVER WALL.**  For `0 < t` and
    `0 < C`, the honest order-2 outer `s`-dominator `s ↦ C·(t−s)⁻¹` is NOT interval-integrable on
    `(0,t)`.  RATIONALE: after the `z`-integral, the leading term of the order-2 envelope
    (`witnessFieldDeriv2_envelope_coercive`) is `(1/τ²)·⟨V,P⟩²·G_{2τ}(z)` with `V ≈ z`, whose `z`-mass
    `= (1/τ²)·(2nd `z`-moment ≈ τ) = 1/τ = (t−s)⁻¹`; so the `hBint : IntervalIntegrable B volume 0 t`
    slot of the J4-197 lever (`hasFDerivAt_doubleIntegral_of_dominated`) has NO admissible dominator at
    this rate.  ⟹ **the naive dominated-Leibniz route does NOT close `hD1`.**  Via
    `not_intervalIntegrable_of_sub_inv_isBigO_punctured` at `c = t`.  NOT `a₁ = R/6`. -/
theorem order2_naive_dominator_not_intervalIntegrable (t C : ℝ) (ht : 0 < t) (hC : 0 < C) :
    ¬ IntervalIntegrable (fun s : ℝ => C * (t - s)⁻¹) volume 0 t := by
  -- reduce to the standard `fun s => (s − t)⁻¹` non-integrability at `c = t`.
  have hBigO : (fun s : ℝ => (s - t)⁻¹) =O[𝓝[≠] t] (fun s : ℝ => C * (t - s)⁻¹) := by
    refine Asymptotics.IsBigO.of_bound C⁻¹ (Filter.Eventually.of_forall (fun s => ?_))
    have heq : ‖(s - t)⁻¹‖ = C⁻¹ * ‖C * (t - s)⁻¹‖ := by
      rw [norm_mul, norm_inv, norm_inv, Real.norm_eq_abs C, abs_of_pos hC,
          ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC), one_mul, norm_sub_rev]
    exact le_of_eq heq
  exact not_intervalIntegrable_of_sub_inv_isBigO_punctured hBigO (ne_of_lt ht)
    (by simp [Set.uIcc_of_le ht.le, ht.le])

/-- **★ §C — `sliver_rate_intervalIntegrable` — THE SLIVER ROUTE SURVIVES.**  The sliver route's
    `(t−s)^{−1/2}` rate IS interval-integrable on `(0,t)` (`∫₀ᵗ(t−s)^{−1/2} = 2√t`).  This is the rate
    the `√ε` cancellation of `witness_sliver2_grand`/`witness_sliver2_concrete` produces: the sliver
    replacement `G_τ(Wz) − G_τ(z)` (`gaussDdim_replace_bound`) upgrades the non-integrable `τ^{−1}` to
    the integrable `τ^{−1/2}`.  ⟹ **`hD1` closes via the SLIVER-TRUNCATION route, NOT the naive lever**:
    split `(0,t) = (0,t−ε] ∪ (t−ε,t]`, bulk by the naive lever (`τ` bounded below), sliver by the
    concrete `√ε` bound.  Via `intervalIntegrable_rpow'` (`−1 < −1/2`) reflected through `t − s`.  NOT
    `a₁ = R/6`. -/
theorem sliver_rate_intervalIntegrable (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)) volume 0 t := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hcomp := hbase.comp_sub_left t
  -- `comp_sub_left` yields `volume (t − 0) (t − t) = volume t 0`; symmetrise to `0 t`.
  simpa only [sub_zero, sub_self] using hcomp.symm

end QIQTH.SecondDerivEnvelope

section AxiomChecks
open QIQTH.SecondDerivEnvelope
#print axioms pd_pd_congr_at
#print axioms witnessFieldDeriv2_gate_eq
#print axioms witnessFieldDeriv2_gate_abs_le
#print axioms witnessFieldDeriv2_envelope_coercive
#print axioms gatedDeriv2Rep_measurable
#print axioms witnessFieldDeriv2_eq_zero_of_nonpos
#print axioms witnessFieldDeriv2_eq_gatedDeriv2Rep
#print axioms witnessFieldDeriv2_measurable_of_gateEq
#print axioms order2_naive_dominator_not_intervalIntegrable
#print axioms sliver_rate_intervalIntegrable
end AxiomChecks
