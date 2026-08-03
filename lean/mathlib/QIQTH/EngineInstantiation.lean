/-
  EngineInstantiation — J4-152: the DOMINATED-ENGINE-FAMILY concrete instantiation.  Supplying the
  `dH`/`dHH` derivative-kernel DATA (and the on-gate factorized bounds) for the concrete `N = 1`
  van-Vleck gated witness `H_G := vanVleckGatedWitness`, and threading the concrete kernels through
  the abstract second-order interchange engine (`SecondOrderInterchange`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and
  proves NOTHING about `R/6`.  The abstract interchange engine (`pd_pd_heatConvFrozen_interchange`,
  `SecondOrderInterchange`) differentiates the frozen double convolution
      `heatConvFrozen H F u b x 0 = ∫ s in (0)..b, ∫ z, H (u−s) x z · F s z 0`
  TWICE in the FIELD slot `x` (base slot `z` is the outer integration variable), producing the
  interchange
      `pd (fun y => pd (fun x => heatConvFrozen H F u b x 0) i y) i 0 = ∫∫ dHH (u−s) 0 z · F`
  provided it is fed the CONCRETE first/second field-derivative kernels `dH`/`dHH`, their
  dominations, and the `HasDerivAt` families.  This file supplies those kernels for the witness and
  proves their DATA facts (on-gate factorization, off-gate vanishing, on-gate factorized bound).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  SLOT CONVENTION (traps).  In `H_G τ p q` the FIELD point is `p`, the BASE point is `q`.  The
  engine differentiates the field slot `x` and integrates over the base slot `z`.  So the concrete
  derivative kernels are field-slot partials at the field point, base slot the integration variable:
      `dH  i τ p z := pd_i (x' ↦ H_G τ x' z)     at p`   (`witnessFieldDeriv`),
      `dHH i τ p z := pd_i (pd_i (x' ↦ H_G τ x' z))  at p`   (`witnessFieldDeriv2`),
  and at the field center `p = 0` the second kernel is EXACTLY the banked `witnessSecondXDeriv`.
  The gate condition is `z ∈ K` (base) ∧ `p ∈ S z` (field); the off-gate leg `z ∉ K` kills the whole
  witness in the field slot, so both kernels VANISH there — the leg that splits the `z`-integral.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDS (this file, ns `QIQTH.HeatResidualBound`).

    (E1)  `witnessFieldDeriv` / `witnessFieldDeriv2` — the concrete first/second FIELD-derivative
          kernels of the gated witness (tied to `H_G`, NOT free stand-ins).
          `witnessFieldDeriv2_center` — `dHH i τ 0 z = witnessSecondXDeriv … i τ z` (`rfl`).
          `witnessFieldDeriv_gate_eq` — ★ THE ON-GATE FIRST-DERIVATIVE FORMULA: on the OPEN gate the
            witness factors as `G_τ(W z ·)·chartFieldAmp`, so
              `dH i τ p z = G_τ(W z p)·(−(∑ₖ (W z p)ₖ·Pₖ)/(2τ))·A(p) + G_τ(W z p)·∂A(p)`
            (the product rule with the carried chart jet `P` and amplitude `A = chartFieldAmp`);
            the first-order analogue of `hNormalForm_concrete`.
          `witnessFieldDeriv_offGate_eq_zero` / `witnessFieldDeriv2_offGate_eq_zero` — off the base
            gate (`z ∉ K`) both kernels are `0` (first-order analogue of
            `witnessSecondXDeriv_offGate_eq_zero`).

    (E2)  `witnessFieldDeriv_gate_abs_le` — ★ THE ON-GATE FACTORIZED DOMINATION.  From the on-gate
          formula (E1) plus the carried factor bounds (`|scalar| ≤ Bs`, `|A| ≤ Ba`, `|∂A| ≤ Bd`),
              `|dH i τ p z| ≤ G_τ(W z p)·(Bs·Ba + Bd)`
          — the Gaussian-envelope pointwise dominator the `innerZ`/`line_pd_double_integral` engine
          consumes (the τ-power lives in the carried scalar bound `Bs`; the `heatKernel1D` derivative
          bounds `GaussianPolyBound.heatKernel1D_deriv_x_abs_le` are the source of `Bs`).

    (E3)  ★★ `witness_secondOrder_interchange` — THE ENGINE INSTANTIATION.  Feeding the concrete
          `dH := witnessFieldDeriv`, `dHH := witnessFieldDeriv2` into
          `pd_pd_heatConvFrozen_interchange`, the second-order interchange holds for the CONCRETE
          witness at any gap `b`:
              `pd (fun y => pd (fun x => heatConvFrozen H_G F u b x 0) i y) i 0
                 = ∫ s in (0)..b, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`.
          The analytic family (first-order interchange `hQ1`, the `∫z`/`∫s` dominations,
          `HasDerivAt` family, measurabilities) is carried — each a genuine differentiation-under-∫
          fact about the concrete witness, satisfiable via E1/E2 + the C4b Gaussian-derivative bounds
          and the strictly-positive gap, NONE the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL.
    CARRIED (each genuine, satisfiable, non-vacuous, never the conclusion):
      • `hJetV` — the first FIELD jet of the inverse chart `W z` on the `i`-line at the field point
        (PROVEN unconditionally at the assembly point `z = 0` via `chartField_firstJet_center`; the
        honest `C²` carry `chartField_firstJet_of_contDiffAt` for a general base).
      • `hAmp1` — field partial-differentiability of the smooth chart amplitude `chartFieldAmp`.
      • the gate memberships `z ∈ K`, `p ∈ S z`, `IsOpen (S z)` — the honest on-gate hypotheses
        (`vanVleckGatedWitness` equals its ungated parametrix exactly here).
      • the E2 factor bounds `Bs`/`Ba`/`Bd` — the pointwise scalar/amplitude/derivative sup-bounds.
      • (E3) `hQ1` + the `∫z`/`∫s` dominations, `HasDerivAt` family, measurabilities — the
        differentiation-under-∫ carries of the engine, at the concrete `dH`/`dHH`.
    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NormalFormDischarge
import QIQTH.SecondOrderInterchange
import QIQTH.GeometricModuliThreading

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### E1 — the concrete first/second FIELD-derivative kernels of the witness.
    ############################################################################### -/

/-- **E1 — the concrete FIRST field-derivative kernel `dH`.**  The `i`-th field-slot partial of the
    gated `N = 1` van-Vleck witness at the field point `p`, base `z` (the outer integration variable):
      `witnessFieldDeriv … i τ p z = pd_i (x' ↦ H_G τ x' z) (p)`.
    This is the `dK := dH` the `SecondOrderInterchange` engine differentiates; it is tied to the
    concrete witness (NOT a free stand-in). -/
noncomputable def witnessFieldDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) : ℝ :=
  pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i p

/-- **E1 — the concrete SECOND field-derivative kernel `dHH`.**  The `i`-th iterated field-slot
    partial of the witness at the field point `p`, base `z`:
      `witnessFieldDeriv2 … i τ p z = pd_i (pd_i (x' ↦ H_G τ x' z)) (p)`.
    This is the `dK := dHH` the engine's SECOND differentiation produces; at the field center it is
    exactly the banked `witnessSecondXDeriv` (see `witnessFieldDeriv2_center`). -/
noncomputable def witnessFieldDeriv2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) : ℝ :=
  pd (fun x : Point n =>
      pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x) i p

/-- **E1 — `dHH` at the field center IS `witnessSecondXDeriv`.**  Definitional identity connecting
    the second field-derivative kernel at `p = 0` to the banked formal second `x`-derivative object
    (`AmplitudePackage.witnessSecondXDeriv`), the `pdpdH` the engine's conclusion is stated with. -/
theorem witnessFieldDeriv2_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) :
    witnessFieldDeriv2 g gi hC hK S a b i τ (0 : Point n) z
      = witnessSecondXDeriv g gi hC hK S a b i τ z := rfl

/-- **E1 — `dHH` is the field-`pd` of `dH`.**  `witnessFieldDeriv2 … i τ p z
    = pd_i (x ↦ witnessFieldDeriv … i τ x z) (p)` (`rfl`); the engine's second differentiation
    stacks on the first. -/
theorem witnessFieldDeriv2_eq_pd_witnessFieldDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) :
    witnessFieldDeriv2 g gi hC hK S a b i τ p z
      = pd (fun x : Point n => witnessFieldDeriv g gi hC hK S a b i τ x z) i p := rfl

/-! ### E1 — the on-gate first-derivative formula. -/

/-- **★ E1 — `witnessFieldDeriv_gate_eq` — THE ON-GATE FIRST-DERIVATIVE FORMULA.**  On the OPEN gate
    (base `z ∈ K`, field point `p ∈ S z`), the witness factors as `H_G τ x' z = G_τ(W z x')·A(x')`
    on a neighbourhood of `p` (`A = chartFieldAmp`), so germ-congruence of `pd`
    (`pd_congr_of_eventuallyEq`) plus the first-order Leibniz–Gaussian product rule (`gaussComp_pd`)
    give
      `dH i τ p z = G_τ(W z p)·(−(∑ₖ (W z p)ₖ·Pₖ)/(2τ))·A(p) + G_τ(W z p)·∂ᵢA(p)`,
    with `W z := uniformInverseChart g gi hC hK z` and `P` the carried first FIELD jet of `W z` at
    `p`.  The first-order analogue of `hNormalForm_concrete`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_gate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p) :
    witnessFieldDeriv g gi hC hK S a b i τ p z
      = gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * (-(∑ k, uniformInverseChart g gi hC hK z p k * Pval k) / (2 * τ))
          * chartFieldAmp g gi hC hK a b τ z p
        + gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * pd (chartFieldAmp g gi hC hK a b τ z) i p := by
  -- (1) on-gate nbhd factorisation of the witness in the field slot.
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
  -- (2) transfer the local `pd` off the factored form.
  unfold witnessFieldDeriv
  rw [pd_congr_of_eventuallyEq _ _ i p hev]
  -- (3) first-order Leibniz + the `gaussComp_pd` normal form.
  have hGf : PdiffAt (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')) i p :=
    (gaussComp_hasDerivAt_line (uniformInverseChart g gi hC hK z) Pval τ hτ i p hJetV).differentiableAt
  rw [pd_mul (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x'))
        (chartFieldAmp g gi hC hK a b τ z) i p hGf hAmp1,
      gaussComp_pd (uniformInverseChart g gi hC hK z) Pval τ hτ i p hJetV]

/-! ### E1 — the off-gate vanishing of both kernels. -/

/-- **E1 — `witnessFieldDeriv_offGate_eq_zero`.**  Off the BASE gate (`z ∉ K`) the witness is
    identically `0` in the field slot, so its field-`pd` (the first-derivative kernel) is `0`.  The
    first-order analogue of `witnessSecondXDeriv_offGate_eq_zero`; the off-gate leg that splits the
    full-space `z`-integral. -/
theorem witnessFieldDeriv_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (hz : z ∉ K) :
    witnessFieldDeriv g gi hC hK S a b i τ p z = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDeriv
  simp only [hzero]
  exact pd_const 0 i p

/-- **E1 — `witnessFieldDeriv2_offGate_eq_zero`.**  Off the base gate the second field-derivative
    kernel vanishes too (the inner `pd` is `pd` of the identically-`0` witness, hence `0`, so the
    outer `pd` is `0`).  Off-gate leg for the SECOND kernel. -/
theorem witnessFieldDeriv2_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (hz : z ∉ K) :
    witnessFieldDeriv2 g gi hC hK S a b i τ p z = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDeriv2
  have hin : (fun x : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x
    simp only [hzero]
    exact pd_const 0 i x
  rw [hin]
  exact pd_const 0 i p

/-! ###############################################################################
    ### E2 — the on-gate factorized domination of `dH`.
    ############################################################################### -/

/-- **★ E2 — `witnessFieldDeriv_gate_abs_le` — THE ON-GATE FACTORIZED DOMINATION.**  From the on-gate
    first-derivative formula (E1) and the carried factor sup-bounds
      `|scalar| ≤ Bs`,   `|A(p)| ≤ Ba`,   `|∂ᵢA(p)| ≤ Bd`
    (`scalar := −(∑ₖ (W z p)ₖ·Pₖ)/(2τ)`, `A := chartFieldAmp`), the first-derivative kernel obeys the
    Gaussian-envelope pointwise bound
      `|dH i τ p z| ≤ G_τ(W z p)·(Bs·Ba + Bd)`.
    This is the pointwise dominator the `innerZ_line_hasDerivAt` / `line_pd_double_integral` engine
    consumes: `G_τ(W z p) = gaussDdim τ (W z p)` is the integrable Gaussian envelope in the base slot,
    and the τ-power sits inside the carried scalar bound `Bs` (whose source is the C4b derivative
    bounds `GaussianPolyBound.heatKernel1D_deriv_x_abs_le`).  Pure triangle inequality on the on-gate
    formula.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_gate_abs_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (Bs Ba Bd : ℝ)
    (hSc : |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pval k) / (2 * τ))| ≤ Bs)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd) :
    |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ gaussDdim τ (uniformInverseChart g gi hC hK z p) * (Bs * Ba + Bd) := by
  rw [witnessFieldDeriv_gate_eq g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV hAmp1]
  set G := gaussDdim τ (uniformInverseChart g gi hC hK z p) with hGdef
  set sc := -(∑ k, uniformInverseChart g gi hC hK z p k * Pval k) / (2 * τ) with hscdef
  set A := chartFieldAmp g gi hC hK a b τ z p with hAdef
  set dA := pd (chartFieldAmp g gi hC hK a b τ z) i p with hdAdef
  have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
  have hBsnn : 0 ≤ Bs := le_trans (abs_nonneg _) hSc
  calc |G * sc * A + G * dA|
      ≤ |G * sc * A| + |G * dA| := abs_add_le _ _
    _ = G * |sc| * |A| + G * |dA| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hGnn]
    _ ≤ G * Bs * Ba + G * Bd := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left hBd hGnn)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hSc hGnn) hBa (abs_nonneg _)
          (mul_nonneg hGnn hBsnn)
    _ = G * (Bs * Ba + Bd) := by ring

/-! ###############################################################################
    ### E3 — the engine instantiation for the concrete witness.
    ############################################################################### -/

/-- **★★ E3 — `witness_secondOrder_interchange` — THE ENGINE INSTANTIATION.**  Feeding the CONCRETE
    first/second field-derivative kernels `dH := witnessFieldDeriv`, `dHH := witnessFieldDeriv2` into
    the abstract second-order interchange engine `pd_pd_heatConvFrozen_interchange`
    (`SecondOrderInterchange`), the second-order coordinate differentiation passes under the double
    space-time integral for the concrete `N = 1` van-Vleck gated witness, at any gap `b`:
      `pd (fun y => pd (fun x => heatConvFrozen H_G F u b x 0) i y) i 0
         = ∫ s in (0)..b, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`,
    where `H_G := vanVleckGatedWitness g gi hC hK S acut bcut`.  The analytic family is carried:
      • `hQ1` — the first-order interchange on the open field nbhd `V ∋ 0`, at the concrete `dH`
        (`= pd_heatConvFrozen_interchange` for the witness);
      • the `∫z`-derivative `HasDerivAt` family `hdiff` (each an `innerZ_line_hasDerivAt` for the
        `dH`→`dHH` step), the `∫z`/`∫s` measurabilities `hFmeas`/`hFint`/`hF'meas`, and the
        interval-integrable `s`-dominator `bound`/`hbdd`/`hbound`.
    Each is a genuine differentiation-under-∫ fact about the concrete witness (satisfiable via
    E1/E2 + the C4b Gaussian-derivative bounds and the strictly-positive gap), NONE the conclusion.
    Pure threading through `pd_pd_heatConvFrozen_interchange` + the `dHH`-center identification
    (`witnessFieldDeriv2_center`).  NOT `a₁ = R/6`. -/
theorem witness_secondOrder_interchange (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u b : ℝ) (i : Fin n)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (hQ1 : ∀ y ∈ V,
      pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u b x 0) i y
        = ∫ s in (0)..b, ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) y z * F s z 0)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 ((0 : Point n) i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
      volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) (0 : Point n) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0)
        (∫ z, witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0) w) :
    pd (fun y => pd
        (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S acut bcut) F u b x 0) i y) i 0
      = ∫ s in (0)..b, ∫ z, witnessSecondXDeriv g gi hC hK S acut bcut i (u - s) z * F s z 0 := by
  have h := pd_pd_heatConvFrozen_interchange (vanVleckGatedWitness g gi hC hK S acut bcut)
    (witnessFieldDeriv g gi hC hK S acut bcut i) (witnessFieldDeriv2 g gi hC hK S acut bcut i) F
    u b i V hVopen hV0 hQ1 snb hsnb hFmeas hFint hF'meas bound hbdd hbound hdiff
  rw [h]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show witnessFieldDeriv2 g gi hC hK S acut bcut i (u - s) 0 z * F s z 0
      = witnessSecondXDeriv g gi hC hK S acut bcut i (u - s) z * F s z 0
  rw [witnessFieldDeriv2_center]

/-! ###############################################################################
    ### E4 — the ε-pinning: eventual side-conditions + the `hbnd` slot supply.
    ############################################################################### -/

/-- **E4 — `epsSeq_eventually_lt`.**  For any positive threshold `c`, the concrete gap sequence
    `ε_m = 1/(m+1)` is eventually below `c` (from `epsSeq_tendsto : ε_m → 0`).  The atomic
    eventual-smallness fact behind the sliver side conditions. -/
theorem epsSeq_eventually_lt (c : ℝ) (hc : 0 < c) : ∀ᶠ m in Filter.atTop, epsSeq m < c :=
  epsSeq_tendsto.eventually (Iio_mem_nhds hc)

/-- **★ E4 — `epsSeq_sliver_side_conditions`.**  The three `m`-dependent side conditions that
    `witness_sliver2_concrete` / `witness_sliver2_grand` require of the gap `ε := ε_m` — `ε_m ≤ u`,
    `ε_m < aT/2`, `ε_m ≤ τ₀` — hold FOR ALL LARGE `m` (`∃ M₀, ∀ m ≥ M₀`), because `ε_m → 0` and the
    thresholds `u`, `aT/2`, `τ₀` are all strictly positive.  This is the eventual-window brick that
    lets the concrete-witness sliver bound fire for every `m ≥ M₀`, feeding the ε-free per-`m`
    √ε-bound that `hbnd_from_eventual` then extends to ALL `m`.  NOT `a₁ = R/6`. -/
theorem epsSeq_sliver_side_conditions (u aT τ₀ : ℝ) (hu : 0 < u) (haT : 0 < aT) (hτ₀ : 0 < τ₀) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
      epsSeq m ≤ u ∧ epsSeq m < aT / 2 ∧ epsSeq m ≤ τ₀ := by
  have h1 : ∀ᶠ m in Filter.atTop, epsSeq m < u := epsSeq_eventually_lt u hu
  have h2 : ∀ᶠ m in Filter.atTop, epsSeq m < aT / 2 := epsSeq_eventually_lt (aT / 2) (by linarith)
  have h3 : ∀ᶠ m in Filter.atTop, epsSeq m < τ₀ := epsSeq_eventually_lt τ₀ hτ₀
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨M₀, fun m hm => ?_⟩
  obtain ⟨hu', haT', hτ'⟩ := hM₀ m hm
  exact ⟨hu'.le, haT', hτ'.le⟩

/-- **★ E4 — `hbnd_witness_supplied`.**  THE `hbnd` SLOT SUPPLIED.  Given the eventual per-coordinate
    √ε sliver bound with FIXED ε-free amplitudes `D0`/`D1` (the shape `witness_sliver2_concrete`
    delivers for the concrete witness at every `m ≥ M₀` once `epsSeq_sliver_side_conditions` fires),
    the finite-max extension `hbnd_from_eventual` closes the ∀`m` form — EXACTLY the per-`i`,`m`
    hypothesis `hbnd` consumed by `SliverSumPlumbing.sliver_sum_bound` / `hDuhamel_semifinal`.  The
    ε-free amplitude `D0'` absorbs the exceptional window `m < M₀`; `D1` is unchanged.  Pure forward
    to `hbnd_from_eventual`; the eventual carry is the genuine, non-vacuous input.  NOT `a₁ = R/6`. -/
theorem hbnd_witness_supplied (slivInt : Fin n → ℕ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i) (M₀ : ℕ)
    (heventual : ∀ (i : Fin n) (m : ℕ), M₀ ≤ m →
        |slivInt i m| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ D0' : Fin n → ℝ, (∀ i, 0 ≤ D0' i) ∧
      ∀ (i : Fin n) (m : ℕ),
        |slivInt i m| ≤ D0' i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m :=
  hbnd_from_eventual slivInt D0 D1 hD0 hD1 M₀ heventual

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.witnessFieldDeriv2_center
#print axioms QIQTH.HeatResidualBound.witnessFieldDeriv2_eq_pd_witnessFieldDeriv
#print axioms QIQTH.HeatResidualBound.witnessFieldDeriv_gate_eq
#print axioms QIQTH.HeatResidualBound.witnessFieldDeriv_offGate_eq_zero
#print axioms QIQTH.HeatResidualBound.witnessFieldDeriv2_offGate_eq_zero
#print axioms QIQTH.HeatResidualBound.witnessFieldDeriv_gate_abs_le
#print axioms QIQTH.HeatResidualBound.witness_secondOrder_interchange
#print axioms QIQTH.HeatResidualBound.epsSeq_eventually_lt
#print axioms QIQTH.HeatResidualBound.epsSeq_sliver_side_conditions
#print axioms QIQTH.HeatResidualBound.hbnd_witness_supplied
