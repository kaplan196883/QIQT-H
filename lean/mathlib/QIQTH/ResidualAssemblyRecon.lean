/-
  ResidualAssemblyRecon — J4-260: the RESIDUAL-ASSEMBLY RECON of the width-free `hEboundW_le` slot.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file records the recon of the width-free capstone's residual slot and banks
  the width-lift that COMPOSES the already-proved width-2 residual provider onto the width-parametric
  capstone `WideA1Assembly.wide_a1_R6_of_residue_inf_v5`.  It carries no coefficient/geometry content of
  its own; it is pure width plumbing on top of banked machinery.

  ── THE SLOT.  `wide_a1_R6_of_residue_inf_v5` (and `wide_a1_R6_of_residue_inf`) carries
        `hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
            |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q| ≤ C · baseKernelW κ 0 τ p q`
     where `heatOp g gi H τ x y = ∂_τ(H · x y) − Δ_{g,x}(H τ · y)` is the spatial heat operator
     (`TrueHeatKernel.heatOp`, def verbatim: `deriv (fun u => K u x y) t − laplaceBeltrami g gi
     (fun p => K t p y) x`).  The SLOT has NO `τ⁻¹` — the naive triangle bound `|∂_τ H| + |Δ H|` from
     the wide bank's zeroth (`|H_G| ≤ C·gaussDdim(lam·τ)`) and second (`|D²H| ≤ C·τ⁻¹·gaussDdim(lam·τ)`)
     dominations is `O(τ⁻¹)·G` — TOO WEAK.  The heat-equation / DeWitt CANCELLATION is essential.

  ── HOW THE WIDTH-2 PROVIDER PROVES THE `O(1)·G` BOUND (the recon answer).
     `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final` (via the `_lin`/`cutoffResidualN1_…_below_lin`
     chain) does NOT triangle-bound the two pieces.  It uses the PARAMETRIX-RESIDUAL IDENTITY: on the
     gate, `heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b W) τ (exp_q v) q` equals the DeWitt
     residual `radialCutoff a b v · ∂_τ(heatParametrix 1 Θ u · v) − Δ_{g̃_q}(χ·heatParametrix 1 Θ u τ) v`
     `= parametrixResidualN 1 g̃_q g̃⁻¹_q Θ u τ v` (CoeffU1Fix `htransport`).  The transport (DeWitt)
     equations bake the `τ⁻¹` and `τ⁰` singular cancellations INTO `parametrixResidualN`, so the residual
     coefficient `totalRadialO1_coeff` is `O(r²)` (`O(r)` at the shifted profile `u'`, since `∂w₁(0)≠0`).
     The leftover `(1/τ)·G·O(r)` is then converted to `O(1)·G` by the ODD/EVEN-power GAUSSIAN WIDTH
     ABSORPTION `r^m·G_c ≤ C·τ^{m/2}·G_d` (`rncRadial_mul_gaussDdim_le_width`, `c<d`): the `r/τ`
     becomes `√τ/τ`, folded on `(0,t]` via `√τ ≤ 1+τ` into the affine `(B₀+B₁τ)·G_{3/2}` shape.  THAT
     is the cancellation — NOT a bound on the pieces, but the residual identity + the narrow (`3/2`)
     margin spent on `r`-power absorption.

  ── THE CHART-IMAGE → BASE-POINT HANDLING (the CRITICAL sub-answer).
     The residual is proved in RNC `z`-space at width `3/2` (`gaussDdim (3/2·τ) v`), but `heatOp` is
     evaluated at the AMBIENT chart image `x = uniformFlowExp g gi hC hK q v` and the TARGET is a
     base-point Gaussian at `q` (`baseKernelW 2 0 = gaussDdim(2·τ)(p−q)`).  The provider closes the gap
     with `gaussDdim_le_gaussDdim_chart (c:=3/2) (d:=2)` under the near-isometry DISPLACEMENT budget
     `uniformFlowExp_hdisp_ball` (`(3/2)·‖exp_q v − q‖² ≤ 2·‖v‖²` on a ball): the `3/2 → 2` WIDTH GAP is
     EXACTLY the near-isometry distortion budget.  So the provider is intrinsically at WIDTH 2 — the
     `3/2` residual margin pays for `r`-power absorption, the `3/2 → 2` step pays for the chart
     distortion.  The gate `(a,b,S)` is PROVIDER-CHOSEN (returned existentially); the provider pins it.

  ── THE VERDICT:  **REUSABLE-AT-WIDE for `κ ≥ 2` (COMPOSE), GENUINELY-NEW below 2.**
     • For `κ ≥ 2`: the cancellation is ALREADY DONE (inside `parametrixResidualN`) and the chart
       transfer is ALREADY DONE (`3/2 → 2` margin).  The provider's width-2 output composes with a
       pure WIDTH-UP transfer `baseKernelW 2 0 ≤ √(κ/2)ⁿ·baseKernelW κ 0` (from `gaussDdim_le_gaussDdim
       _chart` at `c=2, d=κ, v=w=p−q`) to fill the slot at ANY `κ ≥ 2`.  No new content.  This is banked
       below as `baseKernelW_two_le_of_two_le` (T1) + `hEboundW_widen` (T2a) + `hEboundW_wide_from_
       geometry` (T2b) + the assembled wide capstone `wide_a1_R6_of_residue_inf_hEboundW_discharged` (T3).
     • For `κ < 2`: GENUINELY-NEW — the chart step CONSUMES the `3/2 → 2` margin (near-isometry budget
       `L² ≤ 9/8`); landing below width 2 needs a TIGHTER near-isometry constant, i.e. new geometry.
     • THE STANDING WALL is NOT width and NOT cancellation but the **W3 GATE-COMPATIBILITY** issue
       (`FixedGateSourceProviders` header, "NOT BUILT"): the wide bank's zeroth/second dominations are
       re-exported at an EXTERNALLY-FIXED gate `(P.a,P.b,P.S,P.lam)` from a `WideAmplitudePackage`, but
       the residual provider CHOOSES its own gate; a unified single-gate assembly needs a fixed-gate
       version of `gatedWitnessN1_hEboundW_le_vanVleck_final`.  T3 sidesteps this by EXISTENTIALIZING the
       gate to the provider's own choice (the residual slot alone needs no external gate) — exactly the
       `EboundWiringHD1.a1_R6_of_residue_inf_v2` pattern, lifted to the WIDE capstone.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.
  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EboundWiringHD1
import QIQTH.WideA1Assembly

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.PullbackMetric QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.EboundWiringHD1 QIQTH.WideA1Assembly
open scoped BigOperators Topology ContDiff

namespace QIQTH.ResidualAssemblyRecon

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### T1 — THE WIDTH-UP TRANSFER `baseKernelW 2 0 ≤ √(κ/2)ⁿ · baseKernelW κ 0` (`κ ≥ 2`).
    ############################################################################### -/

/-- **★ J4-260 (T1) — the width-up transfer.**  For `κ ≥ 2` and `τ > 0`,
      `baseKernelW 2 0 τ p q ≤ √(κ/2)ⁿ · baseKernelW κ 0 τ p q`.
    A degenerate instance of the chart transfer `gaussDdim_le_gaussDdim_chart` at `c = 2`, `d = κ`,
    `v = w = p − q` (the width budget `2·r² ≤ κ·r²` is just `κ ≥ 2` times `r² ≥ 0`).  This is the ONLY
    new ingredient the `κ ≥ 2` wide route needs on top of the banked width-2 residual provider.  NOT
    `a₁ = R/6`. -/
theorem baseKernelW_two_le_of_two_le {κ : ℝ} (hκ : 2 ≤ κ) {τ : ℝ} (hτ : 0 < τ) (p q : Point n) :
    baseKernelW (2 : ℝ) (0 : ℝ) τ p q ≤ Real.sqrt (κ / 2) ^ n * baseKernelW κ (0 : ℝ) τ p q := by
  have hnorm : (2 : ℝ) * rncRadialSq (p - q) ≤ κ * rncRadialSq (p - q) :=
    mul_le_mul_of_nonneg_right hκ (rncRadialSq_nonneg (p - q))
  have hchart := gaussDdim_le_gaussDdim_chart (c := (2 : ℝ)) (d := κ) (by norm_num)
    (by linarith) hτ (v := p - q) (w := p - q) hnorm
  rw [baseKernelW_zero_apply, baseKernelW_zero_apply]
  exact hchart

/-! ###############################################################################
    ### T2a — THE ABSTRACT WIDTH-LIFTER of a width-2 `hEboundW` to any `κ ≥ 2`.
    ############################################################################### -/

/-- **★★ J4-260 (T2a) — `hEboundW_widen`.**  ABSTRACT in the kernel `H`: any width-2 heat-operator
    Gaussian domination `|heatOp g gi H τ p q| ≤ C·baseKernelW 2 0 τ p q` (`0 < τ ≤ t`) lifts to the
    width-`κ` domination `≤ (C·√(κ/2)ⁿ)·baseKernelW κ 0 τ p q` for ANY `κ ≥ 2`, via T1.  This is the
    honest core of the `REUSABLE-AT-WIDE` verdict: the width-2 residual provider's OUTPUT (whatever its
    internal cancellation) lifts to the width parameter the wide capstone consumes, with NO new content.
    NOT `a₁ = R/6`. -/
theorem hEboundW_widen (g gi : Point n → Fin n → Fin n → ℝ) (H : ℝ → Point n → Point n → ℝ)
    {C t : ℝ} (hC : 0 ≤ C) {κ : ℝ} (hκ : 2 ≤ κ)
    (hbound : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q| ≤ (C * Real.sqrt (κ / 2) ^ n) * baseKernelW κ (0 : ℝ) τ p q := by
  intro τ p q hτ hτt
  calc |heatOp g gi H τ p q|
      ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := hbound τ p q hτ hτt
    _ ≤ C * (Real.sqrt (κ / 2) ^ n * baseKernelW κ (0 : ℝ) τ p q) :=
        mul_le_mul_of_nonneg_left (baseKernelW_two_le_of_two_le hκ hτ p q) hC
    _ = (C * Real.sqrt (κ / 2) ^ n) * baseKernelW κ (0 : ℝ) τ p q := by ring

/-! ###############################################################################
    ### T2b — THE CONCRETE WIDE PROVIDER, composing the width-2 geometry provider.
    ############################################################################### -/

/-- **★★★ J4-260 (T2b) — `hEboundW_wide_from_geometry`.**  The width-`κ` (`κ ≥ 2`) analogue of
    `EboundWiringHD1.hEboundW_from_geometry`: the `wide_a1_R6_of_residue_inf_v5` `hEboundW_le` slot,
    delivered from geometry at a FREE width `κ ≥ 2`, by composing the banked width-2 van-Vleck residual
    provider `gatedWitnessN1_hEboundW_le_vanVleck_final` (via `hEboundW_from_geometry`) with the abstract
    width-lifter T2a.  The gate parameters `a b` and the gate map `S` are PROVIDER-CHOSEN (existential),
    matching the wide capstone's residual slot verbatim.  This is the residual side of the wide route,
    DISCHARGED.  NOT `a₁ = R/6`. -/
theorem hEboundW_wide_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (t : ℝ) (ht : 0 ≤ t) (κ : ℝ) (hκ : 2 ≤ κ) :
    ∃ a b C'' : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C'' ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C'' * baseKernelW κ (0 : ℝ) τ p q := by
  obtain ⟨a, b, C', ha, hab, hC0, S, hbound⟩ :=
    hEboundW_from_geometry g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0 t ht
  refine ⟨a, b, C' * Real.sqrt (κ / 2) ^ n, ha, hab,
    mul_nonneg hC0 (by positivity), S, ?_⟩
  exact hEboundW_widen g gi (vanVleckGatedWitness g gi hChr hK S a b) hC0 hκ hbound

/-! ###############################################################################
    ### T3 — THE WIDE CAPSTONE with `hEboundW_le` DISCHARGED at free width `κ ≥ 2`.
    ############################################################################### -/

/-- **★★★★ J4-260 (T3) — `wide_a1_R6_of_residue_inf_hEboundW_discharged`.**  The width-`κ` (`κ ≥ 2`)
    `∞`-capstone `WideA1Assembly.wide_a1_R6_of_residue_inf` with the residual Gaussian-domination carry
    `hEboundW_le` DISCHARGED internally from geometry (T2b, composing the banked width-2 van-Vleck
    residual provider with the width-up transfer).  The gate parameters `a b` and gate map `S` are now
    PROVIDER-CHOSEN (existential); the remaining honest carries — the gate-centre membership `hS0`, the
    Levi/Duhamel interface (`hInt`/`hDuhamel`/`hInter`/`hDConv`), and the two spatial-`C²` slots
    (`hCH`/`hCConv`) — are inner hypotheses (satisfiable interface assembly, never the conclusion).
    Relative to `wide_a1_R6_of_residue_inf` the OUTER carry list is shorter by exactly the `hEboundW_le`
    slot, AT A FREE WIDTH `κ ≥ 2`.  This is the WIDE mirror of `EboundWiringHD1.a1_R6_of_residue_inf_v2`.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem wide_a1_R6_of_residue_inf_hEboundW_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (κ : ℝ) (hκ : 2 ≤ κ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ a b C' : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧ 0 ≤ C' ∧
      ((0 : Point n) ∈ S 0 →
        IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ 0 C' →
        (heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
            = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
              + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0) →
        (heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                (fun τ p q => (-1 : ℝ) ^ (k + 1)
                  * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
                t 0 0) →
        DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t →
        ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) →
        ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
            (0 : Point n) →
        heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
        ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                                t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  obtain ⟨a, b, C', ha, hab, hC0, S, hbound⟩ :=
    hEboundW_wide_from_geometry g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0 t ht.le κ hκ
  refine ⟨a, b, C', S, ha, hab, hC0, ?_⟩
  intro hS0 hInt hDuhamel hInter hDConv hCH hCConv
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  exact wide_a1_R6_of_residue_inf g gi Ric t ht C' hC0 κ (by linarith) hChr hK S a b ha hab hK0 hS0
    (vanVleckGatedWitness g gi hChr hK S a b) rfl hg hg0' hgi hΓ hdg0 htr hsrc
    hbound hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.ResidualAssemblyRecon

section AxiomChecks
open QIQTH.ResidualAssemblyRecon
#print axioms baseKernelW_two_le_of_two_le
#print axioms hEboundW_widen
#print axioms hEboundW_wide_from_geometry
#print axioms wide_a1_R6_of_residue_inf_hEboundW_discharged
end AxiomChecks
