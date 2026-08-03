/-
  NormalFormDischarge — J4-138: the `hNormalForm` discharge — connecting the ABSTRACT 3-term
  slice decomposition of the sliver-2 program (`GaussReplaceSlice.witness_sliver2_grand`) to the
  CONCRETE van-Vleck witness second `x`-derivative (`AmplitudePackage.witnessSecondXDeriv`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and
  proves NOTHING about `R/6`.  `witness_sliver2_grand` proves the terminal formal-Hessian sliver
  `√ε` bound for an ABSTRACT `D2H` carrying the 3-term normal form
      `hNormalForm : ∀ τ ∈ Ioo 0 τ₀, ∀ z, D2H τ z = sTerm0 Y P Q A0 τ z + sTerm1 Y P A1 τ z
                                                    + sTerm2 Y A2 τ z`.
  This file DISCHARGES that interface for the CONCRETE witness: it shows the actual
  `witnessSecondXDeriv` of `vanVleckGatedWitness` (the `pd∘pd` of the gated `N = 1` van-Vleck
  parametrix in the field slot) equals the 3-term normal form with CONCRETE, defined chart jets and
  amplitude jets, and then feeds that concrete `D2H` through the grand sliver bound.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE CONCRETE OBJECTS (verbatim from the def chain, `AmplitudePackage.vanVleckGatedWitness_gate_apply`).
  For a fixed base `z ∈ K` and field slot `x'`, on the gate (`x' ∈ S z`) the witness factors as
      `H_G τ x' z = gaussDdim τ (W z x') · chartFieldAmp τ z x'`,
      `chartFieldAmp τ z x' = radialCutoff a b (W z x') · Θ(W z x')^{−1/2} · (u₀(W z x') + u₁(W z x')·τ)`,
  `W z := uniformInverseChart g gi hC hK z` (field-slot inverse chart), `Θ := vanVleck g`,
  `u := transportCoeff (transportOp (vanVleck g) g gi)`.  Since the gate `S z` is OPEN and `0 ∈ S z`,
  this factorisation holds on a NEIGHBOURHOOD of the field center `x' = 0`, so the LOCAL `pd∘pd`
  operator sees only the smooth factored form, and `ChartJetHessian.gaussComp_amp_pd_pd` applies.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDS.
    • `pd_congr_of_eventuallyEq`      — `pd` is a LOCAL operator: `f =ᶠ[𝓝 x] f' ⟹ pd f i x = pd f' i x`.
    • `pd_pd_congr_of_eventuallyEq`   — its second-order corollary: `f =ᶠ[𝓝 0] f'`
        `⟹ pd (pd f i) i 0 = pd (pd f' i) i 0` (via the open-set germ, congruence at every nearby base).
    • `chartFieldAmp`                 — the concrete on-gate amplitude of `H_G` as a function of the
        field slot `x'` (the smooth chart-pullback amplitude).
    • `hNormalForm_concrete` (N1)     — ★★ THE DISCHARGE: for the CONCRETE witness, on the gate,
        `witnessSecondXDeriv … i τ z = sTerm0 Yc Pc Qc A0c τ z + sTerm1 Yc Pc A1c τ z + sTerm2 Yc A2c τ z`
        with `Yc z = W z 0`, `Pc/Qc = the carried field jets at `x'=0`, and `A0c/A1c/A2c = chartFieldAmp`
        and its first/second field-`pd`s at `x'=0` — all CONCRETE.  Route: the on-gate nbhd
        factorisation ⟹ `pd∘pd` congruence ⟹ `gaussComp_amp_pd_pd`.
    • `witnessSecondXDeriv_offGate_eq_zero` (N3) — off the base gate (`z ∉ K`) the witness is
        identically `0` in the field slot, so its `pd∘pd` is `0` (the off-gate normal form is the
        trivial one).
    • `witness_sliver2_concrete` (N2) — ★★★ THE PRIZE: the grand sliver bound
        (`witness_sliver2_grand`) specialised to `D2H := witnessSecondXDeriv`, giving the terminal
        `√ε` bound for the ACTUAL concrete witness second `x`-derivative.

  ⚠ HONEST FIREWALL — the carry list (each a genuine fact, NONE the conclusion, none vacuous).
    N1 carries the exact `gaussComp_amp_pd_pd` jet interface for the CONCRETE chart / amplitude:
      • `hJetV : ∀ x k, HasDerivAt (fun s ↦ W z (update x i s) k) (P x k) (x i)` — the first FIELD jet
        of the inverse chart (SATISFIABLE: at `z = 0` PROVEN unconditionally, `ChartJetBounds`
        `chartField_firstJet_center` via `chartField_contDiffAt_center`; the general base is the honest
        `C²`-carry `chartField_firstJet_of_contDiffAt`).  `hJetP` — the second field jet `Q` (the J1b
        carry).  `hAmp1`/`hAmp2` — field partial-differentiability of the smooth chart amplitude.
      • the gate is OPEN and `0 ∈ S z`, `z ∈ K` — the honest on-gate hypotheses (`vanVleckGatedWitness`
        equals its ungated parametrix exactly here); never the conclusion.
    N2 carries `hNormalForm` (discharged on the gate by N1), the geometric moduli
    `hco`/`hYdisp`/`hJ3`/`hJ3Q` (about the concrete `Yc = W₀`/`Pc`/`Qc` — the `J4-129` near-isometry
    inputs; carried), the amplitude bounds, `hFdom`, `hqLip`, and the split integrabilities — exactly
    the carry list of `witness_sliver2_grand`.
    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessian
import QIQTH.ChartJetBounds
import QIQTH.SliverAssembly
import QIQTH.GaussReplaceSlice
import QIQTH.AmplitudePackage

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    Locality of `pd` — germ congruence (first and second order).
    ############################################################################### -/

/-- **`pd` is a LOCAL operator.**  If `f =ᶠ[𝓝 x] f'` then `pd f i x = pd f' i x`.
    Route: `pd f i x = deriv (fun t ↦ f (update x i t)) (x i)`, the coordinate line
    `t ↦ update x i t` is continuous and tends to `x` at `t = x i` (`Function.update_eq_self`), so the
    eventual equality pulls back along it (`EventuallyEq.comp_tendsto`), and `deriv` respects germs
    (`EventuallyEq.deriv_eq`). -/
theorem pd_congr_of_eventuallyEq (f f' : Point n → ℝ) (i : Fin n) (x : Point n)
    (h : f =ᶠ[𝓝 x] f') : pd f i x = pd f' i x := by
  have hcont : Continuous (fun t : ℝ => Function.update x i t) := by
    refine continuous_pi (fun j => ?_)
    simp only [Function.update_apply]
    by_cases h' : j = i
    · simp only [if_pos h']; exact continuous_id
    · simp only [if_neg h']; exact continuous_const
  have hg : Filter.Tendsto (fun t : ℝ => Function.update x i t) (𝓝 (x i)) (𝓝 x) := by
    have ht := hcont.tendsto (x i)
    rwa [Function.update_eq_self i x] at ht
  simp only [pd]
  exact (h.comp_tendsto hg).deriv_eq

/-- **Second-order germ congruence.**  If `f =ᶠ[𝓝 0] f'` then `pd (pd f i) i 0 = pd (pd f' i) i 0`.
    From the eventual equality pick an OPEN `V ∋ 0` on which `f = f'`; at every `y ∈ V`, `V` is a
    nbhd, so `f =ᶠ[𝓝 y] f'` and `pd f i y = pd f' i y` (`pd_congr_of_eventuallyEq`); thus the inner
    `pd`-functions agree on `V`, i.e. `=ᶠ[𝓝 0]`, and the outer `pd` closes by the same lemma. -/
theorem pd_pd_congr_of_eventuallyEq (f f' : Point n → ℝ) (i : Fin n)
    (h : ∀ᶠ x in 𝓝 (0 : Point n), f x = f' x) :
    pd (fun y => pd f i y) i 0 = pd (fun y => pd f' i y) i 0 := by
  apply pd_congr_of_eventuallyEq
  obtain ⟨V, hVeq, hVopen, hV0⟩ := eventually_nhds_iff.mp h
  refine eventually_nhds_iff.mpr ⟨V, ?_, hVopen, hV0⟩
  intro y hyV
  exact pd_congr_of_eventuallyEq f f' i y (eventually_nhds_iff.mpr ⟨V, hVeq, hVopen, hyV⟩)

/-! ###############################################################################
    The concrete on-gate amplitude of `H_G` as a function of the field slot `x'`.
    ############################################################################### -/

/-- **The concrete on-gate field amplitude `chartFieldAmp τ z`.**  For fixed base `z` and time `τ`,
    the smooth amplitude of the gated `N = 1` van-Vleck witness as a function of the FIELD slot `x'`,
    so that on the gate `H_G τ x' z = gaussDdim τ (W z x') · chartFieldAmp τ z x'`
    (`AmplitudePackage.vanVleckGatedWitness_gate_apply`).  The Gaussian argument is the CHART IMAGE
    `W z x' = uniformInverseChart g gi hC hK z x'`. -/
noncomputable def chartFieldAmp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z : Point n) (x' : Point n) : ℝ :=
  radialCutoff a b (uniformInverseChart g gi hC hK z x')
    * (vanVleck g (uniformInverseChart g gi hC hK z x') ^ (-(1 : ℝ) / 2)
        * (transportCoeff (transportOp (vanVleck g) g gi) 0 (uniformInverseChart g gi hC hK z x')
          + transportCoeff (transportOp (vanVleck g) g gi) 1
              (uniformInverseChart g gi hC hK z x') * τ))

/-! ###############################################################################
    ★★ N1 — the `hNormalForm` discharge for the CONCRETE witness (on the gate).
    ############################################################################### -/

/-- **★★ N1 — `hNormalForm_concrete`.**  For the CONCRETE van-Vleck gated witness, on the gate
    (base `z ∈ K`, field center `0` in the OPEN gate `S z`), with the carried chart/amplitude field
    jets, the second `x`-derivative equals the 3-term Leibniz-Gaussian normal form with CONCRETE
    coefficients:
      `witnessSecondXDeriv … i τ z`
        `= sTerm0 (W · 0) (P 0) Q (chartFieldAmp · · 0) τ z`
        `+ sTerm1 (W · 0) (P 0) (pd (chartFieldAmp · ·) i 0) τ z`
        `+ sTerm2 (W · 0) (pd (pd (chartFieldAmp · ·) i) i 0) τ z`,
    where `W w := uniformInverseChart g gi hC hK w` (so `Yc z = W z 0 = W₀ z`), `P`/`Q` are the carried
    first/second FIELD jets of `W z`, and `A0c/A1c/A2c` are `chartFieldAmp` and its first/second field
    `pd`s at `x' = 0`.  Route: the on-gate nbhd factorisation `H_G = G_τ(W z ·)·chartFieldAmp` (open
    gate) ⟹ `pd∘pd` germ congruence (`pd_pd_congr_of_eventuallyEq`) ⟹ `gaussComp_amp_pd_pd`.
    NOT `a₁ = R/6`. -/
theorem hNormalForm_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetV : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hJetP : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hAmp1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i (0 : Point n)) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = sTerm0 (fun w : Point n => uniformInverseChart g gi hC hK w 0)
          (fun _w : Point n => P (0 : Point n)) (fun _w : Point n => (Q : Point n))
          (fun (τ' : ℝ) (z' : Point n) => chartFieldAmp g gi hC hK a b τ' z' 0) τ z
        + sTerm1 (fun w : Point n => uniformInverseChart g gi hC hK w 0)
          (fun _w : Point n => P (0 : Point n))
          (fun (τ' : ℝ) (z' : Point n) => pd (chartFieldAmp g gi hC hK a b τ' z') i 0) τ z
        + sTerm2 (fun w : Point n => uniformInverseChart g gi hC hK w 0)
          (fun (τ' : ℝ) (z' : Point n) =>
            pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z') i y) i 0) τ z := by
  -- the on-gate nbhd factorisation of the witness in the field slot.
  have hev : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      =ᶠ[𝓝 (0 : Point n)]
      (fun x' : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z x')
          * chartFieldAmp g gi hC hK a b τ z x') := by
    refine eventually_nhds_iff.mpr ⟨S z, ?_, hSopen, h0⟩
    intro x' hx'
    show vanVleckGatedWitness g gi hC hK S a b τ x' z
        = gaussDdim τ (uniformInverseChart g gi hC hK z x') * chartFieldAmp g gi hC hK a b τ z x'
    rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hz hx']
    simp only [chartFieldAmp]
    ring
  -- transfer the local `pd∘pd` off the factored form.
  have hstep : witnessSecondXDeriv g gi hC hK S a b i τ z
      = pd (fun y => pd (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
            * chartFieldAmp g gi hC hK a b τ z x') i y) i (0 : Point n) := by
    unfold witnessSecondXDeriv
    exact pd_pd_congr_of_eventuallyEq
      (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
        * chartFieldAmp g gi hC hK a b τ z x') i hev
  rw [hstep, gaussComp_amp_pd_pd (uniformInverseChart g gi hC hK z)
      (chartFieldAmp g gi hC hK a b τ z) P Q τ hτ i (0 : Point n) hJetV hJetP hAmp1 hAmp2]
  simp only [sTerm0, sTerm1, sTerm2]
  have hPP : (∑ k, P (0 : Point n) k * P (0 : Point n) k) = ∑ k, P (0 : Point n) k ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [hPP]

/-! ###############################################################################
    N3 — the off-gate (base `z ∉ K`) trivial normal form.
    ############################################################################### -/

/-- **N3 — the off-gate witness derivative vanishes.**  When the BASE point `z ∉ K`, the gated
    witness is identically `0` in the field slot (`gatedKernel_apply_of_notMem`), so its `pd∘pd` (the
    formal second `x`-derivative) is `0` — the trivial off-gate normal form.  This is the off-gate
    leg used to split the full-space `z`-integral: the off-gate integrand is exactly `0`. -/
theorem witnessSecondXDeriv_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (hz : z ∉ K) :
    witnessSecondXDeriv g gi hC hK S a b i τ z = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessSecondXDeriv
  have hin : (fun x : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x
    simp only [hzero]
    exact pd_const 0 i x
  rw [hin]
  exact pd_const 0 i 0

/-! ###############################################################################
    ★★★ N2 — the grand sliver bound, discharged for the CONCRETE witness.
    ############################################################################### -/

/-- **★★★ N2 — `witness_sliver2_concrete`.**  The terminal formal-Hessian sliver `√ε` bound of
    `GaussReplaceSlice.witness_sliver2_grand`, specialised to `D2H := witnessSecondXDeriv` — the
    ACTUAL concrete second `x`-derivative of the gated `N = 1` van-Vleck witness.  Given the concrete
    normal form `hNormalForm` (DISCHARGED on the gate by `hNormalForm_concrete`), the geometric moduli
    `hco`/`hYdisp`/`hJ3`/`hJ3Q` of the concrete chart jets `Yc = W₀`/`Pc`/`Qc`, the amplitude bounds,
    the Levi domination `hFdom`, the term-1 Lipschitz carry `hqLip`, and the split integrabilities,
    the witness sliver obeys
      `|∫ s in (u−ε)..u, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0|`
        `≤ ((15/2·n·L + C_R) + C₁) · 2√ε + C₂·ε`.
    A direct forwarding to `witness_sliver2_grand` with the concrete `D2H`.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ)
    (iCoord : Fin n) (L M₀ M₁ M₂ C_L T aT τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (u ε : ℝ) (ha : 0 < aT) (hau : aT ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < aT / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec iCoord‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        witnessSecondXDeriv g gi hC hK S acut bcut iCoord τ z
          = sTerm0 Y P Q A0 τ z + sTerm1 Y P A1 τ z + sTerm2 Y A2 τ z)
    (hIntT1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z 0)) volume)
    (hIntT2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z iCoord) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z 0)) volume)
    (hIntT3 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => ((z iCoord) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z 0)) volume)
    (hqLip : ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z 0| ≤ M)
    (hInt1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm1 Y P A1 (u - s) z * F s z 0) volume)
    (hInt2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 Y A2 (u - s) z * F s z 0) volume) :
    ∃ C_R : ℝ, 0 ≤ C_R ∧
      |∫ s in (u - ε)..u, ∫ z, witnessSecondXDeriv g gi hC hK S acut bcut iCoord (u - s) z * F s z 0|
        ≤ ((15 / 2 * (n : ℝ) * L + C_R)
            + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim aT (0 : Point n))
                * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                  + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                  + ((n : ℝ) * C_W * C_P)
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))))
            * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim aT (0 : Point n)) * ε :=
  witness_sliver2_grand (witnessSecondXDeriv g gi hC hK S acut bcut iCoord) F Y P Q A0 A1 A2
    iCoord L M₀ M₁ M₂ C_L T aT τ₀ C_W C_P C_Q
    hL hM₀ hM₁ hM₂ hC_L hC_W hC_P hC_Q u ε ha hau huT hε0 hεu hεa hετ₀
    hco hYdisp hJ3 hJ3Q hA0bdd hA1bdd hA2bdd hFdom hNormalForm
    hIntT1 hIntT2 hIntT3 hqLip hInt1 hInt2

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.pd_congr_of_eventuallyEq
#print axioms QIQTH.HeatResidualBound.pd_pd_congr_of_eventuallyEq
#print axioms QIQTH.HeatResidualBound.hNormalForm_concrete
#print axioms QIQTH.HeatResidualBound.witnessSecondXDeriv_offGate_eq_zero
#print axioms QIQTH.HeatResidualBound.witness_sliver2_concrete
