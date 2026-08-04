/-
  HD1SliverRoute — J4-199: the BULK+SLIVER route for the `hD1` `C¹` slot of the a₁ = R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It assembles the
  ALREADY-BANKED order-1 lever (`EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated`, J4-197) and
  the ALREADY-BANKED order-2 `√ε` sliver bound (`witness_sliver2_grand`/`witness_sliver2_final`) into the
  differentiation-under-truncation architecture that the J4-198 verdict forced onto the `hD1` slot.  No
  new singular-convolution analysis is done; the hard content is imported, not reproved.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MAP — where the banked sliver theorems land in the `hD1` problem.

  `SpatialC2.hCConv_reduction` reduces the `∞`-capstone's `hCConv` (`C²`) slot to
    `hD1 : ContDiffAt ℝ 1 D 0`,
  where `D` is the first-spatial-derivative field of the heat convolution, with components the `gcoef`
  double integrals `gcoef i x = ∫₀ᵗ ∫z (witnessFieldDeriv i · F)`.  Proving `hD1` = proving `D` is
  `HasFDerivAt` with derivative the field of `∫₀ᵗ ∫z (witnessFieldDeriv2 i · F)` (the SECOND field
  derivative `dHH`, whose center value is `witnessSecondXDeriv`), plus continuity of that derivative.

  J4-198 (`SecondDerivEnvelope`) established the WALL and the ESCAPE:
    • `order2_naive_dominator_not_intervalIntegrable` — the honest order-2 `s`-dominator `s ↦ C·(t−s)⁻¹`
      is NOT interval-integrable on `(0,t)`, so the naive J4-197 lever CANNOT differentiate the FULL
      `∫₀ᵗ` in one shot;
    • `sliver_rate_intervalIntegrable` — the sliver route's `(t−s)^{−1/2}` rate IS interval-integrable.
  ⟹ split `(0,t) = (0,t−ε] (BULK) ∪ (t−ε,t] (SLIVER)`.

  ── KEY STRUCTURAL ANSWER (asked by the ledger): **is the `hD1` sliver piece the SAME integral family
     the banked hDaLim`LU` sliver chain already bounded?**  YES — DIRECTLY.  `witness_sliver2_grand`
     (`GaussReplaceSlice`) / `witness_sliver2_final` (`HessianSliceBound`) bound, VERBATIM,
       `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀+C₁)·2√ε + C₂·ε`,
     where `D2H` is the SECOND field-derivative kernel put in Leibniz–Gaussian normal form
     (`hNormalForm : D2H = sTerm0 + sTerm1 + sTerm2`).  Setting `u := t`, `τ := u − s`, the interval
     `s ∈ (t−ε, t)` is exactly `τ ∈ (0, ε)`, so this IS `‖∫_{t−ε}^{t} ∫z dHH·F‖ ≤ C·√ε + C₂·ε` — the
     ε-sliver of gcoef's DERIVATIVE integral.  The very kernel (`witnessSecondXDeriv`/`D2H`) that appears
     in the Laplacian-truncation sliver chain is the kernel `hD1` differentiates under.  So the sliver
     piece is **ALREADY BANKED** (modulo the sliver chain's own carried inputs: `hNormalForm`, the
     entangled-argument geometric inputs `hco`/`hYdisp`/`hJ3`/`hJ3Q`, the amplitude sup bounds, `hFdom`,
     `hqLip`, and the per-slice integrabilities).  The map is DIRECT, not a mirror.

  ── WHICH THEOREMS APPLY VERBATIM vs NEED A MIRROR.
     VERBATIM (no new order-up work):
       · `EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated` (J4-197) — the BULK differentiation
         engine, abstract in `K`/`K'`/`boundz`/`B`; called here with the truncated endpoint `t − ε`.
       · `witness_sliver2_grand` / `witness_sliver2_final` — the SLIVER `√ε` bound (the same integral
         family, see above).
       · `SecondDerivEnvelope.sliver_rate_intervalIntegrable` — the sliver rate survives.
     ALREADY MIRRORED one order up in J4-198 (the ε-truncation ingredients the sliver route needs):
       · `witnessFieldDeriv2_gate_abs_le`/`_envelope_coercive` (the E2 envelope),
       · `witnessFieldDeriv2_measurable_of_gateEq` (the order-2 joint measurability).
     No further order-up mirror is required by THIS file.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.HD1SliverRoute`).

    §A — THE BULK RESOLUTION OF THE J4-198 WALL.
      • `bulk_order2_dominator_intervalIntegrable` — ★ the truncation DEFEATS the J4-198 non-integrability:
        the honest order-2 outer dominator `s ↦ C·(t−s)⁻¹`, which is NOT interval-integrable on `(0,t)`
        (`order2_naive_dominator_not_intervalIntegrable`), IS interval-integrable on `(0, t−ε)` for
        `0 < ε ≤ t` (continuous, `t − s ≥ ε > 0`).  This is exactly why the naive lever CLOSES on the
        bulk.
      • `gcoef_bulk_hasFDerivAt` — the BULK truncated double integral `x ↦ ∫₀^{t−ε} ∫z K s x z` is
        `HasFDerivAt` with derivative `∫₀^{t−ε} ∫z K' s x₀ z`, via the J4-197 lever specialized to the
        endpoint `t − ε` and to the honest order-2 outer dominator `C·(t−s)⁻¹`, whose `hBint` slot is
        supplied by `bulk_order2_dominator_intervalIntegrable`.  `K := dH·F`, `K' := dHH·F`.

    §B — THE UNIFORM-LIMIT-OF-DERIVATIVES ASSEMBLY (the ε → 0 closure).
      • `tendstoUniformlyOn_of_dist_le_bound` — a vanishing UNIFORM bound `dist(fₑ, g) ≤ b ε` with
        `b ε → 0` gives `TendstoUniformlyOn`; instantiated with `b ε = (C₀+C₁)·2√ε + C₂·ε` (the
        `witness_sliver2_grand` right-hand side), this is the `√ε → 0` bridge.
      • `hD1_bulk_sliver_reduction` — ★★ the classical theorem `fₑ → f` pointwise `+ f'ₑ → g` uniformly
        `⟹ HasFDerivAt f g` (Mathlib `hasFDerivAt_of_tendstoUniformlyOn`), assembled from the BULK
        derivatives (§A shape), the BULK pointwise convergence (the sliver of the FIRST integral → 0),
        and the uniform derivative convergence built by `tendstoUniformlyOn_of_dist_le_bound` from the
        `witness_sliver2_grand` `√ε` bound.  This is the differentiability skeleton that upgrades gcoef
        to `HasFDerivAt`, the analytic heart of `hD1`.

  Every hypothesis is satisfiable, non-vacuous, and never equal to the conclusion.  NO `sorry`.
  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EboundWiringHD1
import QIQTH.SecondDerivEnvelope

open MeasureTheory Filter
open scoped Topology Interval

namespace QIQTH.HD1SliverRoute

set_option maxHeartbeats 1600000

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## §A — the BULK resolution of the J4-198 non-integrability wall.
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★★ J4-199 (A1) — `bulk_order2_dominator_intervalIntegrable`.**  The ε-truncation DEFEATS the J4-198
    wall.  `SecondDerivEnvelope.order2_naive_dominator_not_intervalIntegrable` shows the honest order-2
    outer dominator `s ↦ C·(t−s)⁻¹` is NOT interval-integrable on the FULL `(0,t)` (the singularity at
    `s = t`).  On the TRUNCATED bulk interval `(0, t−ε)` (with `0 < ε ≤ t`) it IS interval-integrable:
    there `t − s ≥ ε > 0`, so `s ↦ C·(t−s)⁻¹` is continuous, hence interval-integrable.  THIS is exactly
    why the naive J4-197 lever closes on the bulk (its `hBint` slot).  NOT `a₁ = R/6`. -/
theorem bulk_order2_dominator_intervalIntegrable (t ε C : ℝ) (hε : 0 < ε) (hεt : ε ≤ t) :
    IntervalIntegrable (fun s : ℝ => C * (t - s)⁻¹) volume 0 (t - ε) := by
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ ?_ ?_)
  · exact (continuous_const.sub continuous_id).continuousOn
  · intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    obtain ⟨_, h2⟩ := hs
    -- `s ≤ t − ε` ⟹ `t − s ≥ ε > 0`.
    exact ne_of_gt (by linarith)

/-- **★★ J4-199 (A2) — `gcoef_bulk_hasFDerivAt`.**  The BULK truncated `gcoef` double integral
    `x ↦ ∫ s in (0)..(t−ε), ∫ z, K s x z ∂ν`
    is `HasFDerivAt` at `x₀` with derivative `∫ s in (0)..(t−ε), ∫ z, K' s x₀ z ∂ν`, obtained by feeding
    the ALREADY-BANKED J4-197 lever `EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated` with the
    truncated endpoint `t − ε` and the honest order-2 outer dominator `B := s ↦ C·(t−s)⁻¹`, whose
    interval-integrability `hBint` is supplied by `bulk_order2_dominator_intervalIntegrable` (A1).
    For the `hD1` application: `K := witnessFieldDeriv·F` (`dH·F`), `K' := witnessFieldDeriv2·F`
    (`dHH·F`).  Fully parametric in `K`/`K'`/`boundz`; the outer dominator is FIXED to the honest rate,
    the piece the J4-198 verdict pins down.  NOT `a₁ = R/6`. -/
theorem gcoef_bulk_hasFDerivAt
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Y] {ν : Measure Y}
    (t ε C : ℝ) (hε : 0 < ε) (hεt : ε ≤ t)
    (x₀ : H) {sSet : Set H} (hsOpen : IsOpen sSet) (hx₀ : x₀ ∈ sSet)
    (K : ℝ → H → Y → ℝ) (K' : ℝ → H → Y → (H →L[ℝ] ℝ)) (boundz : ℝ → Y → ℝ)
    (hKint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) →
        ∀ x ∈ sSet, Integrable (fun z => K s x z) ν)
    (hKmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) →
        ∀ x ∈ sSet, AEStronglyMeasurable (fun z => K s x z) ν)
    (hK'meas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) →
        ∀ x ∈ sSet, AEStronglyMeasurable (fun z => K' s x z) ν)
    (hK'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) →
        ∀ᵐ z ∂ν, ∀ x ∈ sSet, ‖K' s x z‖ ≤ boundz s z)
    (hboundz_int : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) → Integrable (boundz s) ν)
    (hKdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) →
        ∀ᵐ z ∂ν, ∀ x ∈ sSet, HasFDerivAt (fun x => K s x z) (K' s x z) x)
    (hGmeas : ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun s => ∫ z, K s x z ∂ν) (volume.restrict (Set.uIoc 0 (t - ε))))
    (hGint : IntervalIntegrable (fun s => ∫ z, K s x₀ z ∂ν) volume 0 (t - ε))
    (hG'meas : AEStronglyMeasurable (fun s => ∫ z, K' s x₀ z ∂ν)
        (volume.restrict (Set.uIoc 0 (t - ε))))
    (hG'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - ε) →
        ∀ x ∈ sSet, ‖∫ z, K' s x z ∂ν‖ ≤ C * (t - s)⁻¹) :
    HasFDerivAt (fun x => ∫ s in (0)..(t - ε), ∫ z, K s x z ∂ν)
      (∫ s in (0)..(t - ε), ∫ z, K' s x₀ z ∂ν) x₀ :=
  EboundWiringHD1.hasFDerivAt_doubleIntegral_of_dominated (t - ε) x₀ hsOpen hx₀
    K K' boundz (fun s => C * (t - s)⁻¹)
    hKint hKmeas hK'meas hK'bound hboundz_int hKdiff
    hGmeas hGint hG'meas hG'bound
    (bulk_order2_dominator_intervalIntegrable t ε C hε hεt)

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## §B — the uniform-limit-of-derivatives assembly (the ε → 0 closure).
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★ J4-199 (B1) — `tendstoUniformlyOn_of_dist_le_bound`.**  A vanishing UNIFORM bound gives uniform
    convergence: if `dist (fseq i x) (glim x) ≤ b i` for all `x ∈ sSet` and `b → 0` along `l`, then
    `fseq → glim` uniformly on `sSet`.  Instantiated with `b ε = (C₀+C₁)·2√ε + C₂·ε` (the RHS of
    `witness_sliver2_grand`) and `l = 𝓝[>] 0`, this is the `√ε → 0` bridge from the banked sliver bound
    to the uniform derivative convergence the classical theorem needs.  NOT `a₁ = R/6`. -/
theorem tendstoUniformlyOn_of_dist_le_bound
    {ι H F : Type*} [PseudoMetricSpace F] {l : Filter ι} {sSet : Set H}
    (fseq : ι → H → F) (glim : H → F) (b : ι → ℝ)
    (hb : Tendsto b l (𝓝 0))
    (hbound : ∀ i, ∀ x ∈ sSet, dist (fseq i x) (glim x) ≤ b i) :
    TendstoUniformlyOn fseq glim l sSet := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hb ε hε] with i hi x hx
  have hbi : b i < ε := lt_of_le_of_lt (le_abs_self _) (by simpa [Real.dist_eq] using hi)
  rw [dist_comm]
  exact lt_of_le_of_lt (hbound i x hx) hbi

/-- **★★ J4-199 (B2) — `hD1_bulk_sliver_reduction`.**  THE differentiability skeleton for `hD1`: the
    classical uniform-limit-of-derivatives theorem (`hasFDerivAt_of_tendstoUniformlyOn`) assembled from
    the three banked pieces of the bulk+sliver split.  With `l` an arbitrary `NeBot` filter (the intended
    instance is `𝓝[>] 0` as `ε → 0⁺`):
      (i)   `hbulkderiv` — the BULK derivatives `HasFDerivAt (fbulk ε) (fderivBulk ε x) x` on the open
            field nbhd `sSet` (delivered by `gcoef_bulk_hasFDerivAt`, §A, with `fbulk ε = ∫₀^{t−ε}∫z dH·F`
            and `fderivBulk ε = ∫₀^{t−ε}∫z dHH·F`);
      (ii)  `hbulk_tendsto` — `fbulk ε → gfull` pointwise on `sSet` (the ε-sliver of the FIRST integral
            `∫_{t−ε}^{t}∫z dH·F → 0`; here `gfull = gcoef = ∫₀ᵗ∫z dH·F`);
      (iii) `hsliver` — the UNIFORM `√ε` control `dist (fderivBulk ε x) (gderiv x) ≤ b ε` with `b → 0`
            (`gderiv = ∫₀ᵗ∫z dHH·F`; the bound is the `witness_sliver2_grand` `(C₀+C₁)·2√ε + C₂·ε`,
            since `gderiv x − fderivBulk ε x = ∫_{t−ε}^{t}∫z dHH·F`), converted to uniform convergence by
            `tendstoUniformlyOn_of_dist_le_bound` (B1).
    Conclusion: `HasFDerivAt gfull (gderiv x₀) x₀` — gcoef is differentiable at the center with the
    expected `∫₀ᵗ∫z dHH·F` derivative.  Together with continuity of `gderiv` this is precisely the
    `ContDiffAt ℝ 1` content `hD1` demands.  NOT `a₁ = R/6`. -/
theorem hD1_bulk_sliver_reduction
    {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {l : Filter ι} [l.NeBot]
    {sSet : Set H} (hsOpen : IsOpen sSet) {x₀ : H} (hx₀ : x₀ ∈ sSet)
    (fbulk : ι → H → ℝ) (fderivBulk : ι → H → (H →L[ℝ] ℝ))
    (gfull : H → ℝ) (gderiv : H → (H →L[ℝ] ℝ))
    (b : ι → ℝ) (hb : Tendsto b l (𝓝 0))
    (hbulkderiv : ∀ i, ∀ x ∈ sSet, HasFDerivAt (fbulk i) (fderivBulk i x) x)
    (hbulk_tendsto : ∀ x ∈ sSet, Tendsto (fun i => fbulk i x) l (𝓝 (gfull x)))
    (hsliver : ∀ i, ∀ x ∈ sSet, dist (fderivBulk i x) (gderiv x) ≤ b i) :
    HasFDerivAt gfull (gderiv x₀) x₀ :=
  hasFDerivAt_of_tendstoUniformlyOn hsOpen
    (tendstoUniformlyOn_of_dist_le_bound fderivBulk gderiv b hb hsliver)
    hbulkderiv hbulk_tendsto hx₀

end QIQTH.HD1SliverRoute

section AxiomChecks
open QIQTH.HD1SliverRoute
#print axioms bulk_order2_dominator_intervalIntegrable
#print axioms gcoef_bulk_hasFDerivAt
#print axioms tendstoUniformlyOn_of_dist_le_bound
#print axioms hD1_bulk_sliver_reduction
end AxiomChecks
