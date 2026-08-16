/-
  GatedGlobalWitnessLeviIntInter — discharge the Levi/Duhamel INTEGRABILITY carry `hInt` AND the
  tsum/heatConv INTERCHANGE carry `hInter` (plus the already-banked diagonal `hDH`) for the CONCRETE
  order-0 gated cutoff-parametrix `a₁ = R/6` capstone, reducing its surviving census from the
  Levi/Duhamel pentad to a single shared base-measurability carry `hEmeas`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DOES.

  `TrueKernelA1EboundWired.trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged` (and its
  `hDH`-discharged refinement `GatedGlobalWitnessDiagDH.…_hDH_discharged`) carries, on the CONCRETE
  order-0 gated witness
      `H := gatedKernel K S (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK))`,
  the Levi/Duhamel census `hHdiag · hInt · hDuhamel · hInter · hDConv · hCH · hCConv`.

  Two of these — `hInt` (`IterConvIntegrableW (heatOp g gi H) 2 0 B`) and `hInter` (the tsum/heatConv
  interchange for `E := heatOp g gi H`) — are NOT independent analytic walls: BOTH reduce, via
  ALREADY-BANKED abstract lemmas, to the SAME three leaf facts about the residual `E = heatOp g gi H`:

      hEbound  (`∀ τ p q, 0<τ → |E τ p q| ≤ B·baseKernelW 2 0 τ p q`)   — ALREADY INTERNAL
                 (`gatedWitness_hEboundW_unconditional`, J4-759 / J4-100, the discharged C4c bound);
      hEzero   (`∀ τ ≤ 0, ∀ p q, E τ p q = 0`)                          — DISCHARGED HERE (needs `1 ≤ n`);
      hEmeas   (`StronglyMeasurable (fun w => E w.1 w.2.1 w.2.2)`)      — the single carried leaf.

  Specifically:
    • `hInt`   ← `IterEMeasurable.iterConvIntegrableW_of_bound_baseMeas E B hEbound hEzero hEmeas`;
    • `hInter` ← `LeviInterchange.heatConv_leviSeries_interchange E B (0≤B) hEbound hEzero hEmeas t ht 0 0`
      — whose conclusion is VERBATIM the capstone's `hInter` shape.

  This CORRECTS the stale `CapstoneWiring` census, which classified `hInter` as a
  `[hDuhamel/Levi WALL]`: it is not — it is a dominated-convergence corollary of the same
  `{hEbound, hEzero, hEmeas}` family that produces `hInt`.  (The same reduction was already banked for
  the SEPARATE `vanVleckGatedWitness` chain in `ResidueThreading.a1_R6_of_residue_hCH_hInter_discharged`;
  here it is wired, for the FIRST time, into the order-0 `globalCutoffParametrixWitness` chain that the
  `GatedGlobalWitnessDiagDH` capstone actually uses.)

  RESULT.
    • `gatedGlobalWitness_residual_hEzero` — `hEzero` for the order-0 gated cutoff-parametrix residual
      (`1 ≤ n`), a near-verbatim port of `CoeffBoundsN1.heatOp_gatedWitnessN1_eq_zero_of_nonpos`
      (the Gaussian kills the profile at `τ ≤ 0`; the `∂_τ` slot is `0` for `τ<0` by local constancy
      and at `τ=0` by the `Set.Iic 0` within-derivative-uniqueness junk-convention argument).
    • `trueKernel_diagonal_a1_eq_R6_residual_hInt_hInter_hDH_discharged` — the `hEboundW`-discharged
      capstone with `hInt`, `hInter` AND `hDH` all supplied internally; the surviving carries drop to
          `hHdiag · hDuhamel · hDConv · hCH · hCConv`  +  the single `hEmeas`.

  ⚠ HONEST SCOPE (binding).  STILL a CONDITIONAL capstone.  `hHdiag` in particular CANNOT hold for this
  ORDER-0 witness (the `N ≥ 1` re-plumb remains owed — see `CapstoneWiring`'s census), and `hDuhamel`
  (the parametrix Duhamel output, resting on the locally-uniform `Da`-limit `hDaLimLU`), `hDConv`
  (same `hDaLimLU` wall) and `hCConv` (the `hD1` CLM-lift wall) are the genuine remaining analytic
  walls.  This is NOT an unconditional `a₁ = R/6`.  What it IS: two of the Levi/Duhamel carries (`hInt`,
  `hInter`) — one of them previously mislabelled a wall — are no longer assumed inputs, collapsed to a
  single shared measurability carry `hEmeas`.  No axioms beyond the standard three, no `sorry`, no
  vacuous hypotheses.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessDiagDH
import QIQTH.IterEMeasurable
import QIQTH.LeviInterchange

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. `hEzero` for the order-0 gated cutoff-parametrix residual. -/

/-- **`gatedGlobalWitness_residual_hEzero` — `hEzero` for the concrete order-0 gated witness.**

    For `1 ≤ n`, the heat operator of the ORDER-0 gated cutoff-parametrix witness
    `H = gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap)` VANISHES at nonpositive time:
        `∀ τ ≤ 0, ∀ p q, heatOp g gi H τ p q = 0`.
    Near-verbatim port of `CoeffBoundsN1.heatOp_gatedWitnessN1_eq_zero_of_nonpos` (the `N = 1` sibling):
    for `1 ≤ n` the Gaussian `gaussDdim τ` is `0` at `τ ≤ 0`, so the whole gated witness vanishes on
    `Iic 0`; the spatial `Δ`-slot is then `Δ` of the zero field, and the `∂_τ`-slot is `0` for `τ<0`
    (local constancy on `Iio 0`) and at `τ=0` by the `Set.Iic 0` within-derivative-uniqueness junk
    convention.  The ONLY change from the `N = 1` proof is `globalCutoffParametrixWitness` (order-0) in
    place of `globalCutoffParametrixWitnessN 1`; the profile-vanishing simp is identical
    (`heatParametrix` at time `τ ≤ 0` is `0·…`).  NOT `a₁ = R/6`. -/
theorem gatedGlobalWitness_residual_hEzero (g gi : Point n → Fin n → Fin n → ℝ)
    (hn : 1 ≤ n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (Vmap : Point n → Point n → Point n) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap)) τ p q = 0 := by
  -- the gated witness vanishes at nonpositive time.
  have hker0 : ∀ s : ℝ, s ≤ 0 → ∀ p' q' : Point n,
      gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap) s p' q' = 0 := by
    intro s hs p' q'
    have hwit : globalCutoffParametrixWitness Θ u a b Vmap s p' q' = 0 := by
      simp only [globalCutoffParametrixWitness, heatParametrix,
        gaussDdim_eq_zero_of_nonpos hn hs, zero_mul, mul_zero]
    simp only [gatedKernel]
    split_ifs <;> simp [hwit]
  intro τ hτ p q
  set Kn : ℝ → Point n → Point n → ℝ :=
    gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap) with hKn
  -- the spatial `Δ`-slot: `Δ` of the zero field.
  have hlap : laplaceBeltrami g gi (fun x => Kn τ x q) p = 0 := by
    have hzero : (fun x => Kn τ x q) = (fun _ => (0 : ℝ)) := by
      funext x; exact hker0 τ hτ x q
    rw [hzero]; exact QIQTH.HeatTransportRecursion.laplaceBeltrami_const g gi 0 p
  -- the `∂_τ`-slot.
  have hderiv : deriv (fun s => Kn s p q) τ = 0 := by
    set φ : ℝ → ℝ := fun s => Kn s p q with hφ
    rcases lt_or_eq_of_le hτ with hτ0 | hτ0
    · -- `τ < 0`: locally zero on `Iio 0`.
      have hnbhd : Set.Iio (0 : ℝ) ∈ 𝓝 τ := isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hτ0)
      have heq : φ =ᶠ[𝓝 τ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hnbhd] with s hs using hker0 s (le_of_lt (Set.mem_Iio.mp hs)) p q
      rw [heq.deriv_eq, deriv_const]
    · -- `τ = 0`: `Set.Iic 0` within-derivative uniqueness.
      subst hτ0
      by_cases hd : DifferentiableAt ℝ φ 0
      · have huniq := uniqueDiffWithinAt_Iic (0 : ℝ)
        have hbase : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic (0 : ℝ)) 0 :=
          hasDerivWithinAt_const (0 : ℝ) (Set.Iic (0 : ℝ)) (0 : ℝ)
        have hwithin : HasDerivWithinAt φ 0 (Set.Iic (0 : ℝ)) 0 :=
          hbase.congr (fun s hs => hker0 s hs p q) (hker0 0 le_rfl p q)
        rw [← hd.derivWithin huniq]
        exact hwithin.derivWithin huniq
      · exact deriv_zero_of_not_differentiableAt hd
  -- assemble `heatOp = ∂_τ − Δ = 0 − 0`.
  simp only [heatOp, hderiv, hlap, sub_zero]

/-! ### 2. The reduced capstone — `hInt`, `hInter`, `hDH` all discharged. -/

/-- **★ `hInt` + `hInter` (+ `hDH`) DISCHARGED into the order-0 Seeley–DeWitt capstone.**

    Identical to `trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged` (with `hDH` already
    supplied by `gatedGlobalWitness_diag_hDH`) except the Levi/Duhamel INTEGRABILITY carry `hInt` and
    the tsum/heatConv INTERCHANGE carry `hInter` are GONE — both are produced internally from the
    already-internal residual bound (`gatedWitness_hEboundW_unconditional`), the order-0 residual
    vanishing `gatedGlobalWitness_residual_hEzero` (needs `1 ≤ n`), and a SINGLE carried base
    measurability `hEmeas` of `heatOp g gi H`:
      • `hInt`   ← `iterConvIntegrableW_of_bound_baseMeas`;
      • `hInter` ← `heatConv_leviSeries_interchange`.
    The surviving Levi/Duhamel census drops to `hHdiag · hDuhamel · hDConv · hCH · hCConv` + `hEmeas`.

    STILL CONDITIONAL; NOT unconditional `a₁ = R/6`.  (`hHdiag` still cannot hold at this ORDER-0
    witness; `hDuhamel`/`hDConv` rest on the `hDaLimLU` wall, `hCConv` on the `hD1` wall.) -/
theorem trueKernel_diagonal_a1_eq_R6_residual_hInt_hInter_hDH_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    ∃ (a b B : ℝ), 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      (let H := gatedKernel K S
          (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK));
        H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n) →
        StronglyMeasurable (fun w : ℝ × Point n × Point n => heatOp g gi H w.1 w.2.1 w.2.2) →
        heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
            = leviSeries (heatOp g gi H) t 0 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
        DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t →
        ContDiff ℝ ⊤ (fun p => H t p 0) →
        ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) →
        heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
        ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  obtain ⟨a, b, B, ha, hab, hB, S, hbound⟩ :=
    gatedWitness_hEboundW_unconditional g gi hg hChr hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, S, ?_⟩
  intro H hHdiag hEmeas hDuhamel hDConv hCH hCConv
  -- `hEzero` for the concrete order-0 gated residual (needs `1 ≤ n`).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0 :=
    gatedGlobalWitness_residual_hEzero g gi hn K S Θ u a b
      (uniformInverseChart g gi hChr hK)
  -- `hInt` from the residual bound + vanishing + base measurability.
  have hInt : IterConvIntegrableW (heatOp g gi H) 2 0 B :=
    iterConvIntegrableW_of_bound_baseMeas (heatOp g gi H) B hbound hEzero hEmeas
  -- `hInter` (the tsum/heatConv interchange) from the SAME family.
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    heatConv_leviSeries_interchange (heatOp g gi H) B hB hbound hEzero hEmeas t ht 0 0
  -- `hDH` (diagonal time-differentiability) already banked for this concrete witness.
  have hDH : DifferentiableAt ℝ (fun w => H w 0 0) t :=
    gatedGlobalWitness_diag_hDH g gi hChr hK Θ u a b S t ht
  exact trueKernel_diagonal_a1_eq_R6_residual g gi Ric N hN t ht H B hB
    hg hg0 hgi hΓ hdg0 htr hsrc hHdiag hbound hInt hDuhamel hInter hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound
