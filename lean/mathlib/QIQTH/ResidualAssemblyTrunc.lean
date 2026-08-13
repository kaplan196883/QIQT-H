/-
  ResidualAssemblyTrunc — J4-667: gap-(i) BRICK 4 — the TRUNCATED-`hInt` rethread of the
  `hEboundW_le`-DISCHARGED wide `a₁` residual capstone.  ONE brick of the `a₁ = R/6` heat-kernel
  campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6` (R/6 stays a labelled carrier; gaps
  (ii)–(v) + `c<δ₀` + `hw`/`hu` untouched).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — GAP (i) BRICK 4 ONLY.  This file rethreads the ONE capstone that both
  (a) DISCHARGES the residual Gaussian-domination slot `hEboundW_le` from geometry (at free width
  `κ ≥ 2`) AND (b) EXISTENTIALIZES the gate — `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_
  hEboundW_discharged` — so that its remaining per-step integrability arrow `hInt` consumes the
  SMALL-TIME truncated family `TruncatedHIntRethread.IterConvIntegrableWOn (heatOp …) κ 0 C' t`
  (window `(0, t]`, `t` = the outer conclusion time) instead of the all-τ
  `HeatResidualBound.IterConvIntegrableW (heatOp …) κ 0 C'`.  It carries no coefficient/geometry
  content of its own; it is pure integrability plumbing on top of banked machinery.  It does NOT
  close `a₁ = R/6`.

  ── WHY THIS IS A DROP-IN (no 130-binder body reconstruction).  The truncated MIDDLE capstone
     `WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc` (J4-263) is already the byte-for-byte
     mirror of `WideA1Assembly.wide_a1_R6_of_residue_inf` with the ONE `hInt`-touching line
     `leviSeries_summableW_le → leviSeries_summableW_le_trunc` (at `T := t`, `htT := le_rfl`) swapped
     and the `hInt` binder retyped to `IterConvIntegrableWOn … t`.  So the discharged-trunc capstone
     is obtained from the banked `wide_a1_R6_of_residue_inf_hEboundW_discharged` by the IDENTICAL
     transformation applied ONE level up: obtain the gate from
     `ResidualAssemblyRecon.hEboundW_wide_from_geometry` (unchanged), then thread
     `wide_a1_R6_of_residue_inf_trunc` in place of `wide_a1_R6_of_residue_inf` (the ONLY line that
     touched `hInt`).  The gate/leading-term steps are truncation-independent; the CONCLUSION and
     every OTHER binder are IDENTICAL to the original.  The banked capstone body is NOT restated.

  ── POST-RETHREAD ANTECEDENT LIST (honest; identical to
     `wide_a1_R6_of_residue_inf_hEboundW_discharged` EXCEPT the `hInt` arrow retyped).  OUTER binders:
     `g gi Ric t (ht:0<t) κ (hκ:2≤κ) hChr {K} hK hK0 hg hg0 hgi hΓ hdg0 htr hsrc hgnd hgsymm hinvF
     hframeK hw`.  RETURNED (gate `a b C' S` existential, provider-chosen): under `(0:Point n) ∈ S 0`
     the arrows `hInt : IterConvIntegrableWOn (heatOp …) κ 0 C' t`  (★ TRUNCATED — was
     `IterConvIntegrableW`), `hDuhamel`, `hInter`, `hDConv`, `hCH`, `hCConv` ⟹ the heat-equation
     + `a₁ = R/6`-shaped expansion.  Every carry is satisfiable, non-vacuous, never the conclusion.

  ── CURVED FEED (NOT DIRECT — honestly assessed, brick 4 residue).  `TruncHIntCarries.curved_hIntOn_
     from_geometry_closed` (J4-666) produces `IterConvIntegrableWOn (heatOp (curvedRNCMetric κ)
     (curvedRNCInv κ) …) 2 0 (C·(1+T₀)) T₀` at the CURVED witness metric and the `constGate … c`
     gate.  Feeding it into this capstone's `hInt` slot is NOT direct: (i) the capstone is over a
     GENERAL metric `(g,gi)` and would have to be instantiated at `(curvedRNCMetric κ, curvedRNCInv
     κ)`; (ii) more bindingly, the capstone's gate `(a,b,S)` is EXISTENTIALIZED to the residual
     provider's own choice (`hEboundW_wide_from_geometry`), an INDEPENDENT existential with no reason
     to coincide with the curved closure's `constGate … c`.  Bridging the two gates (unifying the
     provider gate with `constGate`) is a SEPARATE gate-unification brick, not this rethread.  So the
     curved instantiation corollary is deliberately NOT materialized here; brick 4 delivers the
     retyped capstone (the mechanical rethread the §CARRIED note flagged), and the gate-unification
     stays an explicit residue.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ResidualAssemblyRecon
import QIQTH.WideA1AssemblyTrunc

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.PullbackMetric QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatResidualBound QIQTH.WideA1Assembly
open QIQTH.TruncatedHIntRethread QIQTH.ResidualAssemblyRecon QIQTH.WideA1AssemblyTrunc
open scoped BigOperators Topology ContDiff

namespace QIQTH.ResidualAssemblyTrunc

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE DISCHARGED-`hEboundW` WIDE CAPSTONE with the `hInt` slot TRUNCATED (`IterConvIntegrableWOn`).
    ############################################################################### -/

/-- **★★★★ J4-667 (brick 4) — `wide_a1_R6_of_residue_inf_hEboundW_discharged_trunc`.**  The
    width-`κ` (`κ ≥ 2`) `∞`-capstone `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_hEboundW_
    discharged` with the residual Gaussian-domination carry `hEboundW_le` DISCHARGED internally from
    geometry (T2b) and the gate `(a,b,S)` PROVIDER-CHOSEN (existential), rethreaded so its per-step
    integrability arrow `hInt` consumes the SMALL-TIME truncated family
    `TruncatedHIntRethread.IterConvIntegrableWOn (heatOp …) κ 0 C' t` (window `(0, t]`) instead of the
    all-τ `IterConvIntegrableW (heatOp …) κ 0 C'`.  Sound because the entire capstone lineage consumes
    `hInt` only at the outer conclusion time `t` (the C-route verdict, `TruncatedHIntRethread`); the
    rethread is the ONE line `wide_a1_R6_of_residue_inf → wide_a1_R6_of_residue_inf_trunc` (which
    internally swaps `leviSeries_summableW_le → leviSeries_summableW_le_trunc` at `T := t`).  Every
    OTHER binder and the CONCLUSION are IDENTICAL to the original.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem wide_a1_R6_of_residue_inf_hEboundW_discharged_trunc
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
        IterConvIntegrableWOn (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ 0 C' t →
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
  -- ★ THE ONE RETHREAD: `wide_a1_R6_of_residue_inf → wide_a1_R6_of_residue_inf_trunc`, the ONLY
  --   `hInt`-touching call (internally swaps `leviSeries_summableW_le → …_trunc` at `T := t`).
  exact wide_a1_R6_of_residue_inf_trunc g gi Ric t ht C' hC0 κ (by linarith) hChr hK S a b ha hab
    hK0 hS0 (vanVleckGatedWitness g gi hChr hK S a b) rfl hg hg0' hgi hΓ hdg0 htr hsrc
    hbound hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.ResidualAssemblyTrunc

/-! ## Axiom checks — the public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ResidualAssemblyTrunc
#print axioms wide_a1_R6_of_residue_inf_hEboundW_discharged_trunc
end AxiomChecks
