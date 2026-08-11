/-
  WhiteWitness — J4-621: (1) the FORMAL DIAGONAL NO-GO PIN for the as-built flat-phase witness
  (upgrading the J4-620 assessment to a theorem), (2) the WHITENED witness definitions
  (`whiteVel`/`whiteExp`/`whiteW`/`whitePullbackMetric`) with their zeroth/first jets, and
  (3) the confinement/composition adapters for the J4-622 whitened replay.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: the whitened replay (J4-622) + whitened `hpkgBound` + `hEbound`/`hInt` at the transport
  kernel + the `K1TransportBudget` + the fat-`K` carrier piles + the capstone co-instantiation at
  the whitened witness + the prior analytic piles.

  ── ITEM 1: THE FORMAL NO-GO PIN (the J4-620 "assessed FALSE" upgraded to a theorem).

  ⚠ HONEST SCOPE OF THE PIN.  The pin is proved for the MODEL kernel `flatPhaseModel τ x y :=
  gaussDdim τ (x − y)` — the flat Euclidean-phase Gaussian in the ambient coordinate — against the
  genuinely curved operator `heatOp g^κ gi^κ`.  This is the PRINCIPAL ON-GATE FORM of the as-built
  witness in the chart coordinate: the as-built `vanVleckGatedWitness` is
  `gatedKernel K S (globalCutoffParametrixWitnessN 1 … (uniformInverseChart …))`, whose parametrix
  factor `heatParametrix N Θ u τ (W_q p)` carries EXACTLY the flat `gaussDdim` phase in the chart
  velocity `W_q p` (formal connection witnessed at trivial amplitude by
  `flatPhaseModel_eq_trivialParametrix` below).  The IDENTIFICATION of the full gated witness with
  `amplitude × flatPhaseModel ∘ chart` — the gate/amplitude/chart bookkeeping — is NOT formalized
  here and is the labelled residue of the pin:
      ⚠ LABELLED GAP (pin scope): the no-go is proved for the flat-phase representative kernel
      (trivial amplitude, identity chart), i.e. for the PHASE mechanism itself; the transport of
      the failure through the amplitude/gate layers of the literal `vanVleckGatedWitness` is
      assessed (J4-620 item 3: the phase is the witness's own) but not formalized.
  What IS exact and unconditional here:
    • `flatPhaseModel_heatOp_diag` — the EXACT diagonal defect identity (no asymptotics):
          `heatOp g gi (flatPhaseModel) τ q q = ((tr gi(q) − n)/(2τ)) · (4πτ)^{−n/2}`
      for ANY metric pair and ANY `τ > 0` — the `1/τ` diagonal floor in closed form.
    • ★★ `flatPhase_hpkgBound_fails` — THE PIN: for `κ < 0`, `n ≥ 2` there is NO constant `C` with
          `|heatOp g^κ gi^κ (flatPhaseModel) τ p q| ≤ C·gaussDdim (2τ) (p−q)`
      uniformly on `τ ∈ (0,1]`, `p, q` — the exact (hpkgBound)-shape bound FAILS for the
      flat-phase kernel at the genuinely curved witness (via the diagonal identity at any
      off-center row + the banked scalar route gate `centerShape_no_uniform_majorant`).
    • `flatPhaseModel_heatOp_diag_ne_zero` — non-vacuity: the diagonal defect is GENUINELY
      nonzero at every off-center row (`κ < 0`, `n ≥ 2`, `q ≠ 0`, `τ > 0`).

  ── ITEM 2: THE WHITENED WITNESS DEFINITIONS + JETS (route (c), J4-620 item 4).
    • `whiteVel κ q w := E_q w` — the whitened chart velocity through the banked closed-form frame
      `E_q = curvedWhitening κ q` (J4-620); `curvedWhitening_zero` shows the closed form extends
      CONTINUOUSLY through `q = 0` with `E_0 = δ` (no piecewise definition needed: the `b`-term
      carries the factor `q i · q j = 0`).
    • `whiteExp κ hκ hKc q := uniformFlowExp g^κ gi^κ … q ∘ whiteVel κ q` — the whitened chart:
      the SAME banked uniform-flow machinery, pre-composed with the linear frame change.
    • `whitePullbackMetric` — the whitened pullback metric `ĝ_q(w) = E_qᵀ · g̃_q(E_q w) · E_q`
      (the pullback of `whiteExp` under the chain rule `D(φ∘E) = (Dφ∘E)·E`; the DEFINITION here is
      the matrix transport formula — the chart-level `fderiv` identification is a J4-622 item).
    • ★★ `whitePullbackMetric_zero` — THE POINT OF WHITENING: `ĝ_q(0) = δ` at EVERY `q` in the
      base compact (via the banked value jet `uniformFlowPullbackMetric_zero_center` + the
      whitening identity, extended through `q = 0` by `curvedRNC_whitening_all`) — the zeroth-jet
      δ-frame requirement of the SOLE `hframeK` consumer now HOLDS at every row (contrast the
      as-built failure `uniformFlow_perq_chart_frame_defect`, EquivProbe).
    • ★★ `whitePullbackMetric_pd_zero` — the first jet `∂ĝ_q(0) = 0` — the banked frame-free
      pd-jet (`uniformFlowPullbackMetric_pd_zero_center` mechanism, through the weld to
      `expPullbackMetric`) survives the linear pre-composition (chain rule `pd_comp_linearVel`).
    • ★ `white_vs_asBuilt_frame_gate` — THE ADVERSARIAL CONTRAST GATE: at the SAME genuinely
      curved off-center witness (`n = 2`, `κ = −1`, `q = (1,1)` in the fat ball), the whitened
      value-jet trace IS `n` while the as-built value-jet trace is NOT `n` — the whitening
      genuinely repairs the exact defect the as-built chart exhibits (non-vacuity both ways).

  ── ITEM 3: THE ADAPTERS (as far as tractable this brick).
    • `whiteVel_radialSq_le` — CONTRACTION: `‖E_q w‖² ≤ ‖w‖²` for ALL `q` (κ ≤ 0) — eigenvalues
      of `E_q` are `a_q ≤ 1` (tangential) and `1` (radial); with `whiteVel_norm_le` (sup-norm
      form, cost `√n`) this is the CONFINEMENT adapter: whitened velocities stay admissible for
      the banked tube machinery (`whiteVel_within_radius`).
    • `whiteVel_radialSq_ge` / `whiteVel_radialSq_ge_uniform` — NON-DEGENERACY, uniform over the
      fat ball: `‖E_q w‖² ≥ ‖w‖²/(1 + (−κ/3)r²)` for `‖q‖² ≤ r²` — the two-sided operator bound
      the whitened chart-radius bookkeeping needs.
    • ★ `quadForm_whiteVel` — THE EXACT PHASE TRANSFER: `Q_{g^κ(q)}(E_q w) = ‖w‖²` — the frozen
      quadratic phase in the whitened velocity IS the flat phase; hence
      `whiteW_eq_det_mul_gaussDdim`: `Γ_{g^κ(q)}(τ, E_q w) = √det g^κ(q) · gaussDdim τ w` — the
      whitened witness Gaussian is EXACTLY the flat Gaussian in the whitened chart velocity
      (Sol's "minimal change = phase e^{−vᵀg(q)v/4τ}", realized through the banked `frozenGauss`).
    • `whiteVel_nondegenerate` — the frame change is genuinely non-identity at the curved witness.

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.EquivProbe
import QIQTH.FrozenGauss
import QIQTH.FrozenDefect
import QIQTH.CurvedA1CenterN1
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.LeviSeries

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterN1 QIQTH.EquivProbe
open QIQTH.CConvV2GaussianPairing QIQTH.GaussianWidthTransfer
open QIQTH.FrozenGauss QIQTH.LeviSeries
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.WhiteWitness

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### 1a. The flat-phase model kernel and its `pd` calculus at the diagonal. -/

/-- **The flat-phase model kernel** `M(τ,x,y) = gaussDdim τ (x − y)` — the Euclidean-phase
    Gaussian in the ambient coordinate: the principal on-gate form of the as-built witness
    (trivial amplitude, identity chart; see the header's labelled scope). -/
noncomputable def flatPhaseModel (τ : ℝ) (x y : Point n) : ℝ :=
  gaussDdim τ (fun i => x i - y i)

/-- The model kernel IS the trivial-amplitude `N = 0` parametrix ansatz (`Θ ≡ 1`, `u ≡ 1`) in the
    identity chart — the formal connection of the representative to the witness's parametrix
    layer. -/
theorem flatPhaseModel_eq_trivialParametrix (τ : ℝ) (x y : Point n) :
    flatPhaseModel τ x y
      = heatParametrix 0 (fun _ => 1) (fun _ _ => 1) τ (fun i => x i - y i) := by
  simp [flatPhaseModel, heatParametrix, Real.one_rpow]

/-- The flat Gaussian is partially differentiable in every coordinate direction (`t > 0`). -/
theorem gaussDdim_pdiffAt (t : ℝ) (ht : 0 < t) (x : Point n) (i : Fin n) :
    PdiffAt (fun y => gaussDdim t y) i x := by
  show DifferentiableAt ℝ (fun s => gaussDdim t (Function.update x i s)) (x i)
  have hfun : (fun s : ℝ => gaussDdim t (Function.update x i s))
      = (fun s : ℝ => heatKernel1D t s * ∏ k ∈ Finset.univ.erase i, heatKernel1D t (x k)) := by
    funext s
    simp only [gaussDdim]
    rw [← Finset.mul_prod_erase Finset.univ
        (fun k => heatKernel1D t (Function.update x i s k)) (Finset.mem_univ i)]
    congr 1
    · rw [Function.update_self]
    · exact Finset.prod_congr rfl (fun k hk => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  rw [hfun]
  exact ((heatKernel1D_hasDerivAt_x t (x i) ht).differentiableAt).mul_const _

/-- First partial of the flat Gaussian at the origin: `∂ᵢ G(0) = 0`. -/
theorem gaussDdim_pd_zero (t : ℝ) (ht : 0 < t) (i : Fin n) :
    pd (fun y => gaussDdim t y) i (0 : Point n) = 0 := by
  rw [gaussDdim_pd_i t ht (0 : Point n) i]
  simp

/-- **Second partials of the flat Gaussian at the origin**:
    `∂ᵢ∂ⱼ G(0) = −δᵢⱼ/(2t) · G(t,0)` — the diagonal Hessian is the pure trace term. -/
theorem gaussDdim_pd_pd_zero (t : ℝ) (ht : 0 < t) (i j : Fin n) :
    pd (fun y => pd (fun z => gaussDdim t z) j y) i (0 : Point n)
      = (if i = j then -(1 / (2 * t)) else 0) * gaussDdim t (0 : Point n) := by
  by_cases hij : i = j
  · subst hij
    rw [gaussDdim_pd_pd_i t ht (0 : Point n) i, if_pos rfl]
    norm_num
  · rw [if_neg hij]
    have hinner : (fun y => pd (fun z => gaussDdim t z) j y)
        = (fun y : Point n => -(y j) / (2 * t) * gaussDdim t y) :=
      funext fun y => gaussDdim_pd_i t ht y j
    rw [hinner]
    have hconst : (fun s : ℝ => -(Function.update (0 : Point n) i s j) / (2 * t))
        = fun _ : ℝ => 0 := by
      funext s
      rw [Function.update_of_ne (Ne.symm hij)]
      simp
    have hf : PdiffAt (fun y : Point n => -(y j) / (2 * t)) i (0 : Point n) := by
      show DifferentiableAt ℝ
        (fun s => -(Function.update (0 : Point n) i s j) / (2 * t)) ((0 : Point n) i)
      rw [hconst]
      exact differentiableAt_const 0
    have hg : PdiffAt (fun y => gaussDdim t y) i (0 : Point n) := gaussDdim_pdiffAt t ht 0 i
    rw [pd_mul _ _ i (0 : Point n) hf hg]
    have h1 : pd (fun y : Point n => -(y j) / (2 * t)) i (0 : Point n) = 0 := by
      simp only [pd]
      rw [hconst]
      exact deriv_const _ _
    rw [h1]
    simp

/-- **Translation invariance of `pd`**: the partial of a `q`-shifted field is the shifted
    partial.  Unconditional (no differentiability needed — `deriv` shift invariance). -/
theorem pd_shift (f : Point n → ℝ) (q : Point n) (i : Fin n) (x : Point n) :
    pd (fun y => f (fun k => y k - q k)) i x = pd f i (fun k => x k - q k) := by
  simp only [pd]
  have hupd : ∀ s : ℝ, (fun k => Function.update x i s k - q k)
      = Function.update (fun k => x k - q k) i (s - q i) := by
    intro s; funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h1 : (fun s : ℝ => f (fun k => Function.update x i s k - q k))
      = (fun s : ℝ => f (Function.update (fun k => x k - q k) i (s - q i))) :=
    funext fun s => by rw [hupd s]
  rw [h1]
  exact deriv_comp_sub_const (f := fun s : ℝ => f (Function.update (fun k => x k - q k) i s))
    (x := x i) (a := q i)

/-! ### 1b. The exact diagonal defect identity. -/

/-- **★ THE EXACT DIAGONAL DEFECT IDENTITY (no asymptotics).**  For ANY metric pair `(g, gi)`,
    ANY `τ > 0` and ANY base point `q`, the heat defect of the flat-phase model kernel at the
    diagonal is EXACTLY the trace defect times the `1/τ`-weighted Gaussian peak:
        `heatOp g gi M τ q q = ((tr gi(q) − n)/(2τ)) · gaussDdim τ 0`.
    Mechanism: `∂_t G(τ,0) = −n/(2τ)·G₀` (flat heat equation at the peak), while
    `Δ_{g,x} M(τ,·,q)|_q = tr gi(q)·(−1/(2τ))·G₀` (the first partials vanish at the diagonal, so
    the Christoffel terms drop; the Hessian is `−δ/(2τ)·G₀`).  NOT `a₁ = R/6`. -/
theorem flatPhaseModel_heatOp_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (q : Point n) :
    heatOp g gi (fun t x y => flatPhaseModel t x y) τ q q
      = ((∑ i, gi q i i) - (n : ℝ)) / (2 * τ) * gaussDdim τ (0 : Point n) := by
  have h0 : (fun k : Fin n => q k - q k) = (0 : Point n) := funext fun k => sub_self _
  -- the time derivative at the diagonal
  have hderiv : deriv (fun u => flatPhaseModel u q q) τ
      = -((n : ℝ) / (2 * τ)) * gaussDdim τ (0 : Point n) := by
    have hfun : (fun u => flatPhaseModel u q q) = (fun u => gaussDdim u (0 : Point n)) := by
      funext u; simp only [flatPhaseModel]; rw [h0]
    rw [hfun, gaussDdim_heat_eqn τ hτ (0 : Point n)]
    have hterm : ∀ i : Fin n,
        pd (fun y => pd (fun z => gaussDdim τ z) i y) i (0 : Point n)
          = -(1 / (2 * τ)) * gaussDdim τ (0 : Point n) := by
      intro i
      rw [gaussDdim_pd_pd_i τ hτ (0 : Point n) i]
      have : ((0 : Point n) i) = 0 := rfl
      rw [this]; ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the first partials at the diagonal
  have hfst : ∀ k : Fin n,
      pd (fun p => flatPhaseModel τ p q) k q = 0 := by
    intro k
    have h1 : pd (fun p => flatPhaseModel τ p q) k q
        = pd (fun z => gaussDdim τ z) k (fun i => q i - q i) :=
      pd_shift (fun z => gaussDdim τ z) q k q
    rw [h1, h0]
    exact gaussDdim_pd_zero τ hτ k
  -- the second partials at the diagonal
  have hmix : ∀ i j : Fin n,
      pd (fun y => pd (fun p => flatPhaseModel τ p q) j y) i q
        = (if i = j then -(1 / (2 * τ)) else 0) * gaussDdim τ (0 : Point n) := by
    intro i j
    have hy : (fun y => pd (fun p => flatPhaseModel τ p q) j y)
        = (fun y => pd (fun z => gaussDdim τ z) j (fun k => y k - q k)) :=
      funext fun y => pd_shift (fun z => gaussDdim τ z) q j y
    rw [hy]
    have h2 : pd (fun y => pd (fun z => gaussDdim τ z) j (fun k => y k - q k)) i q
        = pd (fun v => pd (fun z => gaussDdim τ z) j v) i (fun k => q k - q k) :=
      pd_shift (fun v => pd (fun z => gaussDdim τ z) j v) q i q
    rw [h2, h0]
    exact gaussDdim_pd_pd_zero τ hτ i j
  -- assemble
  simp only [heatOp]
  rw [hderiv]
  have hlap : laplaceBeltrami g gi (fun p => flatPhaseModel τ p q) q
      = -(∑ i, gi q i i) / (2 * τ) * gaussDdim τ (0 : Point n) := by
    simp only [laplaceBeltrami]
    have hij : ∀ i j : Fin n,
        gi q i j * (pd (fun y => pd (fun p => flatPhaseModel τ p q) j y) i q
          - ∑ k, christoffel g gi k i j q * pd (fun p => flatPhaseModel τ p q) k q)
        = gi q i j * ((if i = j then -(1 / (2 * τ)) else 0) * gaussDdim τ (0 : Point n)) := by
      intro i j
      rw [hmix i j]
      have hΓ : (∑ k, christoffel g gi k i j q * pd (fun p => flatPhaseModel τ p q) k q)
          = 0 := Finset.sum_eq_zero fun k _ => by rw [hfst k]; ring
      rw [hΓ, sub_zero]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j]
    have hinner : ∀ i : Fin n,
        (∑ j, gi q i j * ((if i = j then -(1 / (2 * τ)) else 0) * gaussDdim τ (0 : Point n)))
          = gi q i i * (-(1 / (2 * τ)) * gaussDdim τ (0 : Point n)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro j _ hj
        rw [if_neg (fun h : i = j => hj h.symm)]
        ring
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.sum_mul]
    ring
  rw [hlap]
  ring

/-- **Non-vacuity of the diagonal defect**: at every off-center row of the genuinely curved
    witness (`κ < 0`, `n ≥ 2`, `q ≠ 0`, `τ > 0`) the diagonal heat defect is GENUINELY nonzero —
    the no-go pin below is about a genuinely nonvanishing object.  NOT `a₁ = R/6`. -/
theorem flatPhaseModel_heatOp_diag_ne_zero (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n)
    (q : Point n) (hq : q ≠ 0) (τ : ℝ) (hτ : 0 < τ) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (fun t x y => flatPhaseModel t x y) τ q q ≠ 0 := by
  rw [flatPhaseModel_heatOp_diag (curvedRNCMetric κ) (curvedRNCInv κ) τ hτ q]
  have htr : (∑ i, curvedRNCInv κ q i i) ≠ (n : ℝ) :=
    curvedRNCInv_trace_defect_ne κ hκ hn q hq
  have hG : 0 < gaussDdim τ (0 : Point n) := gaussDdim_pos τ hτ (0 : Point n)
  exact mul_ne_zero (div_ne_zero (sub_ne_zero.mpr htr) (by positivity)) hG.ne'

/-! ### 1c. ★★ The formal no-go pin. -/

/-- **★★ J4-621 ITEM 1 — THE FORMAL DIAGONAL NO-GO PIN.**  For the genuinely curved witness
    `g^κ` (`κ < 0`, `n ≥ 2`), the flat-phase kernel — the as-built witness's principal on-gate
    form (see the header's labelled scope) — admits NO `(hpkgBound)`-shape Gaussian domination:
    there is NO constant `C` with
        `|heatOp g^κ gi^κ M τ p q| ≤ C · gaussDdim (2τ) (p − q)`
    uniformly over `τ ∈ (0,1]` and all `p, q`.  Proof: at the diagonal `p = q = q₀` (any
    off-center row, here `q₀ = (1,…,1)`), the EXACT identity `flatPhaseModel_heatOp_diag` gives
    `|E| = ε₀/(2τ)·gaussDdim τ 0` with `ε₀ = |tr gi^κ(q₀) − n| > 0`
    (`curvedRNCInv_trace_defect_ne`), while `gaussDdim (2τ) 0 ≤ gaussDdim τ 0`
    (`gaussDdim_zero_antitone`), so the hypothetical bound forces the uniform scalar majorant
    `ε₀/(2τ) ≤ |C|` on `(0,1]` — contradicting the banked route gate
    `centerShape_no_uniform_majorant` (J4-608).  This upgrades the J4-620 "assessed FALSE
    as-built" to a THEOREM for the flat-phase representative.  NOT `a₁ = R/6`. -/
theorem flatPhase_hpkgBound_fails (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ p q : Point n,
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (fun t x y => flatPhaseModel t x y) τ p q|
        ≤ C * gaussDdim (2 * τ) (fun i => p i - q i) := by
  rintro ⟨C, hC⟩
  -- the off-center row
  set q₀ : Point n := fun _ => 1 with hq₀def
  have hnpos : 0 < n := lt_of_lt_of_le two_pos hn
  have hq₀ : q₀ ≠ 0 := by
    intro h
    have h0 : q₀ ⟨0, hnpos⟩ = 0 := by rw [h]; rfl
    simp [hq₀def] at h0
  -- the strictly positive defect coefficient
  set ε₀ : ℝ := |(∑ i, curvedRNCInv κ q₀ i i) - (n : ℝ)| with hε₀def
  have hε₀ : 0 < ε₀ := by
    rw [hε₀def]
    exact abs_pos.mpr (sub_ne_zero.mpr (curvedRNCInv_trace_defect_ne κ hκ hn q₀ hq₀))
  -- feed the scalar route gate
  refine centerShape_no_uniform_majorant (1 / 2) ε₀ 1 (by norm_num) hε₀ one_pos
    ⟨|C|, fun τ hτ hτ1 => ?_⟩
  have h0 : (fun i : Fin n => q₀ i - q₀ i) = (0 : Point n) := funext fun k => sub_self _
  have hG : 0 < gaussDdim τ (0 : Point n) := gaussDdim_pos τ hτ (0 : Point n)
  -- the diagonal instance of the hypothetical bound
  have hbound := hC τ hτ hτ1 q₀ q₀
  rw [h0] at hbound
  rw [flatPhaseModel_heatOp_diag (curvedRNCMetric κ) (curvedRNCInv κ) τ hτ q₀] at hbound
  have hLHS : |((∑ i, curvedRNCInv κ q₀ i i) - (n : ℝ)) / (2 * τ) * gaussDdim τ (0 : Point n)|
      = ε₀ / (2 * τ) * gaussDdim τ (0 : Point n) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * τ),
      abs_of_pos hG, hε₀def]
  rw [hLHS] at hbound
  -- widen the right side to the same peak
  have hRHS : C * gaussDdim (2 * τ) (0 : Point n) ≤ |C| * gaussDdim τ (0 : Point n) := by
    have h1 : C * gaussDdim (2 * τ) (0 : Point n) ≤ |C| * gaussDdim (2 * τ) (0 : Point n) :=
      mul_le_mul_of_nonneg_right (le_abs_self C)
        (le_of_lt (gaussDdim_pos (2 * τ) (by linarith) (0 : Point n)))
    have h2 : gaussDdim (2 * τ) (0 : Point n) ≤ gaussDdim τ (0 : Point n) :=
      gaussDdim_zero_antitone τ (2 * τ) hτ (by linarith)
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg C))
  have hchain : ε₀ / (2 * τ) * gaussDdim τ (0 : Point n)
      ≤ |C| * gaussDdim τ (0 : Point n) := le_trans hbound hRHS
  have hdiv : ε₀ / (2 * τ) ≤ |C| := le_of_mul_le_mul_right hchain hG
  calc (1 : ℝ) / 2 * ε₀ * (1 / τ) = ε₀ / (2 * τ) := by ring
    _ ≤ |C| := hdiv

/-! ### 2a. The whitening frame through the center; the all-`q` whitening identity. -/

/-- **The closed-form whitening extends continuously through `q = 0`**: `E_0 = δ` — the `b`-term
    of `curvedWhitening` carries the factor `q i · q j = 0`, so no piecewise definition or
    removable-singularity argument is needed. -/
theorem curvedWhitening_zero (K : ℝ) (i j : Fin n) :
    curvedWhitening K (0 : Point n) i j = if i = j then (1 : ℝ) else 0 := by
  have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
  simp only [curvedWhitening, Pi.zero_apply, mul_zero, add_zero, h0]
  norm_num

/-- **The whitening identity at EVERY base point** (including the center):
    `E_qᵀ g^κ(q) E_q = δ` for all `q` (`κ ≤ 0`) — `curvedRNC_whitening` off-center, `E_0 = δ` and
    `g^κ(0) = δ` at the center. -/
theorem curvedRNC_whitening_all (K : ℝ) (hK : K ≤ 0) (q : Point n) (i j : Fin n) :
    (∑ k, ∑ l, curvedWhitening K q i k * curvedRNCMetric K q k l * curvedWhitening K q l j)
      = if i = j then (1 : ℝ) else 0 := by
  by_cases hq : q = 0
  · subst hq
    have hterm : ∀ k l : Fin n,
        curvedWhitening K (0 : Point n) i k * curvedRNCMetric K (0 : Point n) k l
            * curvedWhitening K (0 : Point n) l j
          = (if i = k then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0)
            * (if l = j then (1 : ℝ) else 0) := by
      intro k l
      rw [curvedWhitening_zero K i k, curvedWhitening_zero K l j, curvedRNCMetric_zero K k l]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l]
    have hinner : ∀ k : Fin n,
        (∑ l, (if i = k then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0)
          * (if l = j then (1 : ℝ) else 0))
          = (if i = k then (1 : ℝ) else 0) * (if k = j then (1 : ℝ) else 0) := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl, mul_one]
      · intro l _ hl
        rw [if_neg (fun h : k = l => hl h.symm)]
        ring
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [Finset.sum_congr rfl fun k _ => hinner k]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, one_mul]
    · intro k _ hk
      rw [if_neg (fun h : i = k => hk h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ i) h
  · exact curvedRNC_whitening K hK q hq i j

/-! ### 2b. The whitened witness definitions. -/

/-- **The whitened chart velocity** `w ↦ E_q w` — the linear frame change by the banked
    closed-form whitening `E_q = curvedWhitening κ q` (`E_0 = δ` automatically). -/
noncomputable def whiteVel (K : ℝ) (q w : Point n) : Point n :=
  fun i => ∑ j, curvedWhitening K q i j * w j

@[simp] theorem whiteVel_zero_vel (K : ℝ) (q : Point n) :
    whiteVel K q (0 : Point n) = 0 := by
  funext i; simp [whiteVel]

/-- At the center the whitened velocity is the identity: `whiteVel K 0 w = w`. -/
theorem whiteVel_center (K : ℝ) (w : Point n) : whiteVel K (0 : Point n) w = w := by
  funext i
  simp only [whiteVel]
  rw [Finset.sum_congr rfl fun j _ => by rw [curvedWhitening_zero K i j]]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, one_mul]
  · intro j _ hj
    rw [if_neg (fun h : i = j => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The pointwise closed form** `(E_q w)ᵢ = a·wᵢ + b·⟨q,w⟩·qᵢ` (rank-one structure of the
    whitening frame; valid for all `q` — at `q = 0` both sides carry the junk `b`). -/
theorem whiteVel_apply (K : ℝ) (q w : Point n) (i : Fin n) :
    whiteVel K q w i
      = (1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) * w i
        + ((1 - 1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) / rncRadialSq q)
          * (∑ a, q a * w a) * q i := by
  simp only [whiteVel, curvedWhitening]
  set a : ℝ := 1 / Real.sqrt (1 - K / 3 * rncRadialSq q) with hadef
  set b : ℝ := (1 - a) / rncRadialSq q with hbdef
  have hsplit : ∀ j : Fin n,
      (a * (if i = j then (1 : ℝ) else 0) + b * q i * q j) * w j
        = a * ((if i = j then (1 : ℝ) else 0) * w j) + b * q i * (q j * w j) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  have h1 : (∑ j, a * ((if i = j then (1 : ℝ) else 0) * w j)) = a * w i := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, one_mul]
    · intro j _ hj
      rw [if_neg (fun h : i = j => hj h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h2 : (∑ j, b * q i * (q j * w j)) = b * (∑ a, q a * w a) * q i := by
    rw [← Finset.mul_sum]
    ring
  rw [h1, h2]

/-- **The whitened chart** — the banked uniform-flow endpoint map pre-composed with the linear
    whitening: `whiteExp κ q w = uniformFlowExp g^κ gi^κ q (E_q w)`.  The change against the
    as-built chart is EXACTLY the frame pre-composition `w ↦ E_q w` (J4-620 item 4: the tube
    machinery accepts arbitrary initial velocity). -/
noncomputable def whiteExp (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : Point n → Point n :=
  fun w => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
    (whiteVel κ q w)

@[simp] theorem whiteExp_eq (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q w : Point n) :
    whiteExp κ hκ hKc q w
      = uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
          (whiteVel κ q w) := rfl

/-- **The whitened witness Gaussian** — the banked frozen-metric Gaussian evaluated at the
    whitened velocity: `whiteW κ q τ w = Γ_{g^κ(q)}(τ, E_q w)`.  By `whiteW_eq_det_mul_gaussDdim`
    this carries the EXACT flat phase `‖w‖²/(4τ)` in the whitened chart velocity — Sol's
    "minimal change" whitened phase. -/
noncomputable def whiteW (κ : ℝ) (q : Point n) (τ : ℝ) (w : Point n) : ℝ :=
  frozenGauss (curvedRNCMetric κ q) τ (whiteVel κ q w)

/-- **The whitened pullback metric** `ĝ_q(w) = E_qᵀ · g̃_q(E_q w) · E_q` — the matrix transport
    of the banked per-`q` uniform-flow pullback metric under the whitened chart
    (`D(φ∘E) = (Dφ∘E)·E`; the definition here is the transport formula — the chart-level
    `fderiv` identification is a J4-622 item). -/
noncomputable def whitePullbackMetric (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q w : Point n) (i j : Fin n) : ℝ :=
  ∑ k, ∑ l, curvedWhitening κ q i k
    * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
        (whiteVel κ q w) k l
    * curvedWhitening κ q l j

/-! ### 2c. ★★ The whitened jets. -/

/-- **★★ THE WHITENED VALUE JET — THE POINT OF WHITENING.**  `ĝ_q(0) = δ` at EVERY base point of
    the compact (including the center): the banked frame-free value jet `g̃_q(0) = g^κ(q)`
    (`uniformFlowPullbackMetric_zero_center`) composed with the all-`q` whitening identity
    `E_qᵀ g^κ(q) E_q = δ`.  The zeroth-jet δ-frame requirement of the SOLE `hframeK` consumer of
    the residual chain now HOLDS at every row of the whitened chart — contrast the as-built
    failure `uniformFlow_perq_chart_frame_defect` (EquivProbe).  NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (i j : Fin n) :
    whitePullbackMetric κ hκ hKc q 0 i j = if i = j then (1 : ℝ) else 0 := by
  simp only [whitePullbackMetric, whiteVel_zero_vel]
  have hval : ∀ k l : Fin n,
      uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
          (0 : Point n) k l
        = curvedRNCMetric κ q k l := fun k l =>
    uniformFlowPullbackMetric_zero_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q hq k l
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [hval k l]]
  exact curvedRNC_whitening_all κ hκ q i j

/-- **The chain rule for `pd` through a linear velocity map, at a critical origin**: if `f` is
    differentiable at `0` with all coordinate partials vanishing there, then every coordinate
    partial of `w ↦ f(E w)` vanishes at `0` (the update line maps to the line `t ↦ t·E(eₑ)`
    through `0`, and `Df(0)` kills every direction). -/
theorem pd_comp_linearVel (f : Point n → ℝ) (E : Fin n → Fin n → ℝ) (e : Fin n)
    (hf : DifferentiableAt ℝ f 0)
    (hpd : ∀ s, pd f s 0 = 0) :
    pd (fun w => f (fun i => ∑ j, E i j * w j)) e (0 : Point n) = 0 := by
  classical
  set Ee : Point n := fun i => E i e with hEedef
  have hupd : ∀ s : ℝ, (fun i => ∑ j, E i j * Function.update (0 : Point n) e s j)
      = s • Ee := by
    intro s; funext i
    rw [Finset.sum_eq_single e]
    · rw [Function.update_self]
      simp [hEedef, Pi.smul_apply, smul_eq_mul, mul_comm]
    · intro j _ hj
      rw [Function.update_of_ne hj]
      simp
    · intro h; exact absurd (Finset.mem_univ e) h
  simp only [pd]
  have hcomp : (fun s : ℝ => f (fun i => ∑ j, E i j * Function.update (0 : Point n) e s j))
      = (fun s : ℝ => f (s • Ee)) := funext fun s => by rw [hupd s]
  rw [hcomp]
  have hγ : HasDerivAt (fun s : ℝ => s • Ee) Ee (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Ee
  have hfd : HasFDerivAt f (fderiv ℝ f 0) ((fun s : ℝ => s • Ee) 0) := by
    rw [show (fun s : ℝ => s • Ee) 0 = 0 from by simp]
    exact hf.hasFDerivAt
  have hchain : HasDerivAt (fun s : ℝ => f (s • Ee)) ((fderiv ℝ f 0) Ee) 0 :=
    hfd.comp_hasDerivAt (0 : ℝ) hγ
  have hpt : ((0 : Point n) e) = (0 : ℝ) := rfl
  rw [hpt, hchain.deriv]
  -- decompose the direction over the coordinate basis
  have hEe : Ee = ∑ s : Fin n, E s e • Pi.single s (1 : ℝ) := by
    funext j
    rw [Finset.sum_apply]
    have hterm : ∀ s : Fin n, (E s e • Pi.single s (1 : ℝ)) j
        = if j = s then E s e else 0 := by
      intro s
      by_cases h : j = s
      · subst h; simp [Pi.single_apply]
      · simp [Pi.single_apply, h]
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_ite_eq Finset.univ j fun s => E s e]
    simp [hEedef]
  rw [hEe, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [map_smul, smul_eq_mul, ← pd_eq_fderiv f s 0 hf, hpd s, mul_zero]

/-- **★★ THE WHITENED FIRST JET IS FRAME-FREE ZERO.**  `∂ₑ ĝ_q(0)ᵢⱼ = 0` at every `q` in the
    compact: the banked frame-free pd-jet of the per-`q` chart
    (`pd_expPullbackMetric_at_zero` through the weld
    `uniformFlowPullbackMetric_eq_expPullbackMetric_eventually`) survives the linear whitening
    pre-composition by the chain rule (`pd_comp_linearVel` — the whitening is `w`-constant).
    Together with `whitePullbackMetric_zero`, the whitened chart has the EXACT
    `(value, pd)`-jet pair `(δ, 0)` that the sole `hframeK` consumer requires.
    NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_pd_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (i j e : Fin n) :
    pd (fun w => whitePullbackMetric κ hκ hKc q w i j) e (0 : Point n) = 0 := by
  classical
  -- the weld germ, pulled back through the (continuous linear) whitening
  have hev := uniformFlowPullbackMetric_eq_expPullbackMetric_eventually
    (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q hq
  have hcont : Continuous (fun w : Point n => whiteVel κ q w) := by
    apply continuous_pi
    intro a
    exact continuous_finset_sum _ fun b _ => (continuous_apply b).const_mul _
  have htend : Filter.Tendsto (fun w : Point n => whiteVel κ q w)
      (nhds (0 : Point n)) (nhds (0 : Point n)) := by
    have h := hcont.tendsto (0 : Point n)
    rwa [whiteVel_zero_vel] at h
  have hevE : ∀ᶠ w in nhds (0 : Point n), ∀ k l : Fin n,
      uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
          (whiteVel κ q w) k l
        = expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
            (whiteVel κ q w) k l := htend.eventually hev
  have hfun : (fun w => whitePullbackMetric κ hκ hKc q w i j)
      =ᶠ[nhds (0 : Point n)] (fun w => ∑ k, ∑ l, curvedWhitening κ q i k
          * expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
              (whiteVel κ q w) k l
          * curvedWhitening κ q l j) := by
    filter_upwards [hevE] with w hw
    simp only [whitePullbackMetric]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [hw k l]
  rw [pd_congr_eventuallyEq e hfun]
  -- component regularity + banked pd-jet of the exp chart
  have hgc : ∀ a b : Fin n, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hdiff : ∀ k l : Fin n, DifferentiableAt ℝ
      (fun v => expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
        v k l) 0 := fun k l =>
    (contDiffAt2_expPullbackMetric_zero (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) q hgc k l).differentiableAt (by norm_num)
  have hpdz : ∀ k l s : Fin n, pd
      (fun v => expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
        v k l) s 0 = 0 := fun k l s =>
    pd_expPullbackMetric_at_zero (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
      (curvedRNCMetric_symm κ) (fun a b => curvedRNCMetric_hinvF κ hκ q a b) hgc k l s
  -- the composed components: pd = 0 at the origin
  have hcompPd : ∀ k l : Fin n,
      pd (fun w => expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
        (whiteVel κ q w) k l) e (0 : Point n) = 0 := by
    intro k l
    have h := pd_comp_linearVel
      (fun v => expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
        v k l)
      (curvedWhitening κ q) e (hdiff k l) (hpdz k l)
    simpa only [whiteVel] using h
  -- differentiability of the composed components (for the `pd` sum algebra)
  have hdiffE : DifferentiableAt ℝ (fun w : Point n => whiteVel κ q w) 0 := by
    rw [differentiableAt_pi]
    intro a
    have : (fun w : Point n => whiteVel κ q w a)
        = (fun w : Point n => ∑ b, curvedWhitening κ q a b * w b) := rfl
    rw [this]
    exact DifferentiableAt.fun_sum fun b _ =>
      ((ContinuousLinearMap.proj b : (Fin n → ℝ) →L[ℝ] ℝ).differentiableAt).const_mul _
  have hcompDiff : ∀ k l : Fin n, DifferentiableAt ℝ
      (fun w => expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
        (whiteVel κ q w) k l) 0 := by
    intro k l
    have hpt : DifferentiableAt ℝ
        (fun v => expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
          v k l) (whiteVel κ q (0 : Point n)) := by
      rw [whiteVel_zero_vel]; exact hdiff k l
    exact hpt.comp (0 : Point n) hdiffE
  -- pd through the double sum
  have hPdTerm : ∀ k l : Fin n, PdiffAt
      (fun w => curvedWhitening κ q i k
        * expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
            (whiteVel κ q w) k l
        * curvedWhitening κ q l j) e (0 : Point n) := fun k l =>
    QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ e (0 : Point n)
      (((differentiableAt_const _).mul (hcompDiff k l)).mul (differentiableAt_const _))
  have hPdInner : ∀ k : Fin n, PdiffAt
      (fun w => ∑ l, curvedWhitening κ q i k
        * expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
            (whiteVel κ q w) k l
        * curvedWhitening κ q l j) e (0 : Point n) := fun k =>
    PdiffAt_sum Finset.univ _ e (0 : Point n) fun l _ => hPdTerm k l
  rw [pd_sum Finset.univ _ e (0 : Point n) fun k _ => hPdInner k]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pd_sum Finset.univ _ e (0 : Point n) fun l _ => hPdTerm k l]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hshape : (fun w => curvedWhitening κ q i k
      * expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
          (whiteVel κ q w) k l
      * curvedWhitening κ q l j)
      = (fun w => (curvedWhitening κ q i k * curvedWhitening κ q l j)
        * expPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q
            (whiteVel κ q w) k l) := funext fun w => by ring
  rw [hshape, pd_const_mul _ _ e (0 : Point n)
    (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ e (0 : Point n) (hcompDiff k l)), hcompPd k l, mul_zero]

/-! ### 3a. The two-sided operator bounds of the whitening frame (confinement adapters). -/

/-- The scalar frame data at an off-center `q`: `a ∈ (0,1]`, `b ≥ 0`, `a + b·r² = 1`,
    `a²·(1 − (κ/3)r²) = 1` — the shared endgame facts of the adapters below. -/
theorem whitening_scalar_facts (K : ℝ) (hK : K ≤ 0) (q : Point n) (hq : q ≠ 0) :
    0 < (1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) ∧
    (1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) ≤ 1 ∧
    (1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) ^ 2 * (1 - K / 3 * rncRadialSq q) = 1 ∧
    (1 / Real.sqrt (1 - K / 3 * rncRadialSq q))
      + ((1 - 1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) / rncRadialSq q) * rncRadialSq q
      = 1 := by
  have hr : 0 < rncRadialSq q := rncRadialSq_pos hq
  set α : ℝ := 1 - K / 3 * rncRadialSq q with hαdef
  have hα1 : (1 : ℝ) ≤ α := by
    have h : 0 ≤ -(K / 3) * rncRadialSq q := mul_nonneg (by linarith) hr.le
    simp only [hαdef]; linarith
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα1
  have hsq1 : (1 : ℝ) ≤ Real.sqrt α := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hα1
  have hsq0 : (0 : ℝ) < Real.sqrt α := lt_of_lt_of_le one_pos hsq1
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one hsq0]; exact hsq1
  · rw [div_pow, one_pow, Real.sq_sqrt hα0.le]
    field_simp
  · rw [div_mul_cancel₀ _ hr.ne']
    ring

/-- **CONTRACTION (κ ≤ 0): the whitening never expands the Euclidean length** —
    `‖E_q w‖² ≤ ‖w‖²` for ALL `q, w` (eigenvalues `a_q ≤ 1` and `1`).  The confinement half of
    the adapter pair: whitened velocities stay inside the Euclidean ball of the raw velocity. -/
theorem whiteVel_radialSq_le (K : ℝ) (hK : K ≤ 0) (q w : Point n) :
    rncRadialSq (whiteVel K q w) ≤ rncRadialSq w := by
  by_cases hq : q = 0
  · subst hq
    rw [whiteVel_center]
  · have hr : 0 < rncRadialSq q := rncRadialSq_pos hq
    obtain ⟨ha0, ha1, haα, hsum⟩ := whitening_scalar_facts K hK q hq
    set a : ℝ := 1 / Real.sqrt (1 - K / 3 * rncRadialSq q) with hadef
    set b : ℝ := (1 - a) / rncRadialSq q with hbdef
    set s : ℝ := ∑ i, q i * w i with hsdef
    have hb0 : 0 ≤ b := by
      rw [hbdef]
      exact div_nonneg (by linarith) hr.le
    have hval : ∀ i : Fin n, whiteVel K q w i = a * w i + b * s * q i := by
      intro i
      rw [hbdef, hsdef, hadef]
      exact whiteVel_apply K q w i
    have hsq : ∀ i : Fin n, (whiteVel K q w i) ^ 2
        = a ^ 2 * (w i) ^ 2 + 2 * a * b * s * (q i * w i) + b ^ 2 * s ^ 2 * (q i) ^ 2 := by
      intro i; rw [hval i]; ring
    have hexp : rncRadialSq (whiteVel K q w)
        = a ^ 2 * rncRadialSq w + (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 := by
      calc rncRadialSq (whiteVel K q w)
          = ∑ i, (whiteVel K q w i) ^ 2 := rfl
        _ = ∑ i, (a ^ 2 * (w i) ^ 2 + 2 * a * b * s * (q i * w i)
              + b ^ 2 * s ^ 2 * (q i) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hsq i
        _ = a ^ 2 * (∑ i, (w i) ^ 2) + 2 * a * b * s * (∑ i, q i * w i)
              + b ^ 2 * s ^ 2 * (∑ i, (q i) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum]
        _ = a ^ 2 * rncRadialSq w + (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 := by
            rw [← hsdef, show (∑ i, (w i) ^ 2) = rncRadialSq w from rfl,
              show (∑ i, (q i) ^ 2) = rncRadialSq q from rfl]
            ring
    have hcs : s ^ 2 ≤ rncRadialSq q * rncRadialSq w := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
        (fun i => q i) (fun i => w i)
      rw [hsdef]
      simpa only [rncRadialSq] using h
    have hcoef : 0 ≤ 2 * a * b + b ^ 2 * rncRadialSq q :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0.le) hb0)
        (mul_nonneg (sq_nonneg b) hr.le)
    have hkey : (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2
        ≤ (2 * a * b + b ^ 2 * rncRadialSq q) * (rncRadialSq q * rncRadialSq w) :=
      mul_le_mul_of_nonneg_left hcs hcoef
    have h2 : a ^ 2 * rncRadialSq w
        + (2 * a * b + b ^ 2 * rncRadialSq q) * (rncRadialSq q * rncRadialSq w)
        = ((a + b * rncRadialSq q) ^ 2) * rncRadialSq w := by ring
    have h3 : (a + b * rncRadialSq q) ^ 2 = 1 := by rw [hsum]; norm_num
    have h4 : ((a + b * rncRadialSq q) ^ 2) * rncRadialSq w = rncRadialSq w := by
      rw [h3]; ring
    rw [hexp]
    linarith [hkey, h2, h4]

/-- **NON-DEGENERACY (pointwise)**: `‖E_q w‖² ≥ ‖w‖²/(1 − (κ/3)‖q‖²)` — the whitening is
    boundedly invertible with explicit lower eigenvalue `a_q² = 1/α_q`. -/
theorem whiteVel_radialSq_ge (K : ℝ) (hK : K ≤ 0) (q w : Point n) :
    (1 / (1 - K / 3 * rncRadialSq q)) * rncRadialSq w ≤ rncRadialSq (whiteVel K q w) := by
  by_cases hq : q = 0
  · subst hq
    rw [whiteVel_center]
    have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
    rw [h0]
    norm_num
  · have hr : 0 < rncRadialSq q := rncRadialSq_pos hq
    obtain ⟨ha0, ha1, haα, hsum⟩ := whitening_scalar_facts K hK q hq
    set a : ℝ := 1 / Real.sqrt (1 - K / 3 * rncRadialSq q) with hadef
    set b : ℝ := (1 - a) / rncRadialSq q with hbdef
    set s : ℝ := ∑ i, q i * w i with hsdef
    have hb0 : 0 ≤ b := by
      rw [hbdef]
      exact div_nonneg (by linarith) hr.le
    have hα0 : (0 : ℝ) < 1 - K / 3 * rncRadialSq q := by
      nlinarith [mul_nonneg (neg_nonneg.mpr hK) hr.le]
    have hval : ∀ i : Fin n, whiteVel K q w i = a * w i + b * s * q i := by
      intro i
      rw [hbdef, hsdef, hadef]
      exact whiteVel_apply K q w i
    have hsq : ∀ i : Fin n, (whiteVel K q w i) ^ 2
        = a ^ 2 * (w i) ^ 2 + 2 * a * b * s * (q i * w i) + b ^ 2 * s ^ 2 * (q i) ^ 2 := by
      intro i; rw [hval i]; ring
    have hexp : rncRadialSq (whiteVel K q w)
        = a ^ 2 * rncRadialSq w + (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 := by
      calc rncRadialSq (whiteVel K q w)
          = ∑ i, (whiteVel K q w i) ^ 2 := rfl
        _ = ∑ i, (a ^ 2 * (w i) ^ 2 + 2 * a * b * s * (q i * w i)
              + b ^ 2 * s ^ 2 * (q i) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hsq i
        _ = a ^ 2 * (∑ i, (w i) ^ 2) + 2 * a * b * s * (∑ i, q i * w i)
              + b ^ 2 * s ^ 2 * (∑ i, (q i) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum]
        _ = a ^ 2 * rncRadialSq w + (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 := by
            rw [← hsdef, show (∑ i, (w i) ^ 2) = rncRadialSq w from rfl,
              show (∑ i, (q i) ^ 2) = rncRadialSq q from rfl]
            ring
    have ha2 : a ^ 2 = 1 / (1 - K / 3 * rncRadialSq q) := by
      rw [eq_div_iff hα0.ne']
      exact haα
    have hcoef : 0 ≤ (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 :=
      mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0.le) hb0)
        (mul_nonneg (sq_nonneg b) hr.le)) (sq_nonneg s)
    rw [hexp, ← ha2]
    linarith [hcoef]

/-- **NON-DEGENERACY, uniform over the fat ball**: on `‖q‖² ≤ r²`,
    `‖E_q w‖² ≥ ‖w‖²/(1 + (−κ/3)r²)` — ONE lower constant for the whole compact, as the whitened
    chart-radius bookkeeping requires. -/
theorem whiteVel_radialSq_ge_uniform (K r : ℝ) (hK : K ≤ 0) (q : Point n)
    (hqr : rncRadialSq q ≤ r ^ 2) (w : Point n) :
    (1 / (1 + (-K / 3) * r ^ 2)) * rncRadialSq w ≤ rncRadialSq (whiteVel K q w) := by
  refine le_trans ?_ (whiteVel_radialSq_ge K hK q w)
  have hq0 : 0 ≤ rncRadialSq q := rncRadialSq_nonneg q
  have hden1 : (0 : ℝ) < 1 - K / 3 * rncRadialSq q := by nlinarith
  have hden2 : (0 : ℝ) < 1 + (-K / 3) * r ^ 2 := by nlinarith
  have hle : 1 - K / 3 * rncRadialSq q ≤ 1 + (-K / 3) * r ^ 2 := by nlinarith
  have hfrac : 1 / (1 + (-K / 3) * r ^ 2) ≤ 1 / (1 - K / 3 * rncRadialSq q) :=
    one_div_le_one_div_of_le hden1 hle
  exact mul_le_mul_of_nonneg_right hfrac (rncRadialSq_nonneg w)

/-- **Sup-norm confinement** (the repo's tube machinery is sup-norm-gated): the whitening costs
    at most `√n` in the sup norm, `‖E_q w‖ ≤ √n·‖w‖`. -/
theorem whiteVel_norm_le (K : ℝ) (hK : K ≤ 0) (q w : Point n) :
    ‖whiteVel K q w‖ ≤ Real.sqrt n * ‖w‖ := by
  have h1 : ‖whiteVel K q w‖ ≤ Real.sqrt (rncRadialSq (whiteVel K q w)) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact QIQTH.FrozenDefect.abs_apply_le_sqrt_radialSq (whiteVel K q w) i
  have h2 : Real.sqrt (rncRadialSq (whiteVel K q w)) ≤ Real.sqrt (rncRadialSq w) :=
    Real.sqrt_le_sqrt (whiteVel_radialSq_le K hK q w)
  have h3 : rncRadialSq w ≤ (n : ℝ) * ‖w‖ ^ 2 := by
    refine rncRadialSq_le_of_mem_closedBall (q := w) (r := ‖w‖) ?_
    rw [Metric.mem_closedBall, dist_zero_right]
  have h4 : Real.sqrt (rncRadialSq w) ≤ Real.sqrt ((n : ℝ) * ‖w‖ ^ 2) :=
    Real.sqrt_le_sqrt h3
  have h5 : Real.sqrt ((n : ℝ) * ‖w‖ ^ 2) = Real.sqrt n * ‖w‖ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg w)]
  calc ‖whiteVel K q w‖ ≤ Real.sqrt (rncRadialSq (whiteVel K q w)) := h1
    _ ≤ Real.sqrt (rncRadialSq w) := h2
    _ ≤ Real.sqrt ((n : ℝ) * ‖w‖ ^ 2) := h4
    _ = Real.sqrt n * ‖w‖ := by rw [h5]

/-- **The admissibility adapter**: any raw radius budget `ρ` for the tube machinery is met by
    whitened velocities from the shrunk ball `√n·‖w‖ ≤ ρ`. -/
theorem whiteVel_within_radius (K : ℝ) (hK : K ≤ 0) (q w : Point n) (ρ : ℝ)
    (hw : Real.sqrt n * ‖w‖ ≤ ρ) : ‖whiteVel K q w‖ ≤ ρ :=
  le_trans (whiteVel_norm_le K hK q w) hw

/-! ### 3b. ★ The exact phase transfer. -/

/-- **★ THE EXACT PHASE TRANSFER**: `Q_{g^κ(q)}(E_q w) = ‖w‖²` — the frozen quadratic form at
    the whitened velocity is EXACTLY the flat Euclidean phase.  (This is `E_qᵀ g E_q = δ` read
    through the quadratic form; proved from the closed forms via the same scalar endgame as the
    whitening identity.)  NOT `a₁ = R/6`. -/
theorem quadForm_whiteVel (K : ℝ) (hK : K ≤ 0) (q w : Point n) :
    quadForm (curvedRNCMetric K q) (whiteVel K q w) = rncRadialSq w := by
  by_cases hq : q = 0
  · subst hq
    rw [whiteVel_center]
    have hδ : curvedRNCMetric K (0 : Point n)
        = (fun i j => if i = j then (1 : ℝ) else 0) :=
      funext fun i => funext fun j => curvedRNCMetric_zero K i j
    rw [hδ, quadForm_delta]
  · have hr : 0 < rncRadialSq q := rncRadialSq_pos hq
    obtain ⟨ha0, ha1, haα, hsum⟩ := whitening_scalar_facts K hK q hq
    set a : ℝ := 1 / Real.sqrt (1 - K / 3 * rncRadialSq q) with hadef
    set b : ℝ := (1 - a) / rncRadialSq q with hbdef
    set s : ℝ := ∑ i, q i * w i with hsdef
    -- the key cross-cancellation scalar (as in `curvedRNC_whitening`)
    have hb1 : b * rncRadialSq q = 1 - a := by
      rw [hbdef, div_mul_cancel₀ _ hr.ne']
    have hexp2 : (1 - K / 3 * rncRadialSq q) * (1 - a) * (1 + a)
        = (1 - K / 3 * rncRadialSq q) - 1 := by
      have h : (1 - K / 3 * rncRadialSq q) * (1 - a) * (1 + a)
          = (1 - K / 3 * rncRadialSq q) - a ^ 2 * (1 - K / 3 * rncRadialSq q) := by ring
      rw [h, haα]
    have hkey : (1 - K / 3 * rncRadialSq q) * b * (1 + a) + K / 3 = 0 := by
      have h2 : ((1 - K / 3 * rncRadialSq q) * b * (1 + a)) * rncRadialSq q
          = (-(K / 3)) * rncRadialSq q := by
        calc ((1 - K / 3 * rncRadialSq q) * b * (1 + a)) * rncRadialSq q
            = (1 - K / 3 * rncRadialSq q) * (b * rncRadialSq q) * (1 + a) := by ring
          _ = (1 - K / 3 * rncRadialSq q) * (1 - a) * (1 + a) := by rw [hb1]
          _ = (1 - K / 3 * rncRadialSq q) - 1 := hexp2
          _ = (-(K / 3)) * rncRadialSq q := by ring
      have h3 := mul_right_cancel₀ hr.ne' h2
      linarith
    -- the pointwise closed form and the two sum identities
    have hval : ∀ i : Fin n, whiteVel K q w i = a * w i + b * s * q i := by
      intro i
      rw [hbdef, hsdef, hadef]
      exact whiteVel_apply K q w i
    have hdot : (∑ i, q i * whiteVel K q w i) = s := by
      have hterm : ∀ i : Fin n, q i * whiteVel K q w i
          = a * (q i * w i) + b * s * (q i) ^ 2 := by
        intro i; rw [hval i]; ring
      calc (∑ i, q i * whiteVel K q w i)
          = ∑ i, (a * (q i * w i) + b * s * (q i) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = a * (∑ i, q i * w i) + b * s * (∑ i, (q i) ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = s := by
            rw [← hsdef, show (∑ i, (q i) ^ 2) = rncRadialSq q from rfl]
            linear_combination s * hsum
    have hsq : ∀ i : Fin n, (whiteVel K q w i) ^ 2
        = a ^ 2 * (w i) ^ 2 + 2 * a * b * s * (q i * w i) + b ^ 2 * s ^ 2 * (q i) ^ 2 := by
      intro i; rw [hval i]; ring
    have hexp : rncRadialSq (whiteVel K q w)
        = a ^ 2 * rncRadialSq w + (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 := by
      calc rncRadialSq (whiteVel K q w)
          = ∑ i, (whiteVel K q w i) ^ 2 := rfl
        _ = ∑ i, (a ^ 2 * (w i) ^ 2 + 2 * a * b * s * (q i * w i)
              + b ^ 2 * s ^ 2 * (q i) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hsq i
        _ = a ^ 2 * (∑ i, (w i) ^ 2) + 2 * a * b * s * (∑ i, q i * w i)
              + b ^ 2 * s ^ 2 * (∑ i, (q i) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum]
        _ = a ^ 2 * rncRadialSq w + (2 * a * b + b ^ 2 * rncRadialSq q) * s ^ 2 := by
            rw [← hsdef, show (∑ i, (w i) ^ 2) = rncRadialSq w from rfl,
              show (∑ i, (q i) ^ 2) = rncRadialSq q from rfl]
            ring
    -- assemble through the banked closed quadratic form
    rw [quadForm_curvedRNC K q (whiteVel K q w), hdot, hexp]
    linear_combination (rncRadialSq w) * haα + s ^ 2 * hkey
      + s ^ 2 * (1 - K / 3 * rncRadialSq q) * b * hsum

/-- **★ The whitened witness Gaussian in closed flat form**:
    `whiteW κ q τ w = √det g^κ(q) · gaussDdim τ w` — the whitened phase IS the flat Euclidean
    phase in the whitened chart velocity, with the frozen van-Vleck prefactor.  This is the
    Sol J4-620/J4-621 "minimal change" statement, exact.  NOT `a₁ = R/6`. -/
theorem whiteW_eq_det_mul_gaussDdim (κ : ℝ) (hκ : κ ≤ 0) (q : Point n) (τ : ℝ) (w : Point n) :
    whiteW κ q τ w
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ w := by
  simp only [whiteW, frozenGauss]
  rw [quadForm_whiteVel κ hκ q w, gaussDdim_closed]
  ring

/-- At the center the whitened witness Gaussian is EXACTLY the flat Gaussian. -/
theorem whiteW_center (κ τ : ℝ) (w : Point n) :
    whiteW κ (0 : Point n) τ w = gaussDdim τ w := by
  simp only [whiteW]
  rw [whiteVel_center]
  exact frozenGauss_curvedRNC_center κ τ w

/-! ### 4. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- The probe co-vector at `n = 2`: `w = (1,−1)` — `⟨probeQ, probeW⟩ = 0`, so the whitening acts
    on it purely by the tangential eigenvalue `a < 1`. -/
noncomputable def probeW : Point 2 := fun k => if k = 0 then 1 else -1

/-- **Non-vacuity: the whitened velocity map is genuinely NOT the identity** at the curved
    off-center witness (`κ = −1`, `q = (1,1)`, `w = (1,−1)`): `(E_q w)₀ = a·1 < 1 = w₀`. -/
theorem whiteVel_nondegenerate :
    whiteVel (-1 : ℝ) probeQ probeW 0 ≠ probeW 0 := by
  have hr2 : rncRadialSq probeQ = 2 := by
    simp [rncRadialSq, probeQ]
  have hs : (∑ a, probeQ a * probeW a) = 0 := by
    simp [probeQ, probeW, Fin.sum_univ_two]
  have hval : whiteVel (-1 : ℝ) probeQ probeW 0
      = 1 / Real.sqrt (5 / 3) := by
    rw [whiteVel_apply (-1 : ℝ) probeQ probeW 0, hs, hr2]
    norm_num [probeW]
  have hsq : Real.sqrt (5 / 3 : ℝ) > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha : 1 / Real.sqrt (5 / 3 : ℝ) < 1 := by
    rw [div_lt_one (lt_trans one_pos hsq)]; exact hsq
  rw [hval]
  have hW0 : probeW 0 = 1 := by simp [probeW]
  rw [hW0]
  exact ne_of_lt ha

/-- The curved off-center witness sits in the fat ball of radius 2. -/
theorem probeQ_mem_ball : probeQ ∈ Metric.closedBall (0 : Point 2) 2 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  intro i
  simp [probeQ]

/-- **★ THE ADVERSARIAL CONTRAST GATE.**  At the SAME genuinely curved, genuinely off-center
    witness (`n = 2`, `κ = −1`, `q = (1,1)` in the fat ball of radius 2):
    (i) the WHITENED chart's value-jet trace equals `n` (the δ-frame holds), while
    (ii) the AS-BUILT chart's value-jet trace does NOT equal `n`
    (`uniformFlow_perq_chart_frame_defect`).  The whitening genuinely repairs the exact defect
    the as-built chart exhibits — both statements exercised at one witness, neither vacuous.
    NOT `a₁ = R/6`. -/
theorem white_vs_asBuilt_frame_gate :
    (∑ i, whitePullbackMetric (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) probeQ 0 i i) = ((2 : ℕ) : ℝ)
    ∧ (∑ i, uniformFlowPullbackMetric (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
        (curvedRNC_hChr (-1 : ℝ) (by norm_num)) (isCompact_closedBall (0 : Point 2) 2) probeQ
        0 i i) ≠ ((2 : ℕ) : ℝ) := by
  constructor
  · have hjet : ∀ i : Fin 2, whitePullbackMetric (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) probeQ 0 i i = 1 := by
      intro i
      rw [whitePullbackMetric_zero (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) probeQ probeQ_mem_ball i i]
      rw [if_pos rfl]
    rw [Finset.sum_congr rfl fun i _ => hjet i]
    simp
  · exact uniformFlow_perq_chart_frame_defect (-1 : ℝ) (by norm_num) le_rfl
      (curvedRNC_hChr (-1 : ℝ) (by norm_num)) (isCompact_closedBall (0 : Point 2) 2)
      probeQ probeQ_mem_ball probeQ_ne_zero

/-- **Non-vacuity of the no-go pin**: the pin's hypotheses are inhabited at the genuinely curved
    `n = 2`, `κ = −1` instantiation (the pin is a theorem about a realizable configuration). -/
theorem flatPhase_hpkgBound_fails_witness :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ p q : Point 2,
      |heatOp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
          (fun t x y => flatPhaseModel t x y) τ p q|
        ≤ C * gaussDdim (2 * τ) (fun i => p i - q i) :=
  flatPhase_hpkgBound_fails (-1 : ℝ) (by norm_num) le_rfl

end QIQTH.WhiteWitness

section AxiomChecks
open QIQTH.WhiteWitness
#print axioms QIQTH.WhiteWitness.flatPhaseModel_heatOp_diag
#print axioms QIQTH.WhiteWitness.flatPhaseModel_heatOp_diag_ne_zero
#print axioms QIQTH.WhiteWitness.flatPhase_hpkgBound_fails
#print axioms QIQTH.WhiteWitness.flatPhaseModel_eq_trivialParametrix
#print axioms QIQTH.WhiteWitness.curvedWhitening_zero
#print axioms QIQTH.WhiteWitness.curvedRNC_whitening_all
#print axioms QIQTH.WhiteWitness.whitePullbackMetric_zero
#print axioms QIQTH.WhiteWitness.pd_comp_linearVel
#print axioms QIQTH.WhiteWitness.whitePullbackMetric_pd_zero
#print axioms QIQTH.WhiteWitness.whiteVel_radialSq_le
#print axioms QIQTH.WhiteWitness.whiteVel_radialSq_ge
#print axioms QIQTH.WhiteWitness.whiteVel_radialSq_ge_uniform
#print axioms QIQTH.WhiteWitness.whiteVel_norm_le
#print axioms QIQTH.WhiteWitness.quadForm_whiteVel
#print axioms QIQTH.WhiteWitness.whiteW_eq_det_mul_gaussDdim
#print axioms QIQTH.WhiteWitness.whiteW_center
#print axioms QIQTH.WhiteWitness.whiteVel_nondegenerate
#print axioms QIQTH.WhiteWitness.white_vs_asBuilt_frame_gate
#print axioms QIQTH.WhiteWitness.flatPhase_hpkgBound_fails_witness
end AxiomChecks
