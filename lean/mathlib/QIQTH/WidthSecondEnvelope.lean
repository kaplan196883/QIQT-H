/-
  WidthSecondEnvelope — the pointwise `hSecondEnv` two-term Gaussian envelope, ASSEMBLED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE IS

  The `WideWitnessAmplitude.WideAmplitudeData` bundle carries a hypothesis `hSecondEnv`:

      |witnessSecondXDeriv … i τ z|
        ≤ (B₀ + B₁·(rncRadialSq z / τ))·τ⁻¹·gaussDdim τ (W₀ z)          (the CHART-IMAGE envelope).

  Per the ledger (J4-251/J4-537) this envelope was flagged as a FOLLOW-ON, dischargeable from
  "`CompactJetBounds` lever + the upper near-isometry", but the assembly was never built — it was
  carried verbatim.  This file BUILDS that assembly (the pointwise layer):

  * `chartImage_second_envelope_abstract` — the pure real-analysis core.  Given the banked chart-image
    Leibniz–Gaussian normal form of the second field `x`-derivative (four terms sharing the common
    Gaussian factor `G ≥ 0`), together with ELEMENTARY pointwise data — the upper near-isometry bound
    `P² ≤ cW·r²` on the Gaussian-argument inner product `P = ⟨W₀z, ∂ᵢ⟩`, sup bounds on the chart jets
    (`|P|`, `|S₂|`, `|PQ|`) and on the amplitude 0/1/2-jets (`M₀,M₁,M₂`), and the time cap `τ ≤ τ₀` —
    the two-term envelope holds.  The genuine content is the **τ-power bookkeeping**: the quadratic
    `P²/(4τ²)` term lands in the `B₁·(r²/τ)·τ⁻¹` slot via `P² ≤ cW·r²`, and the bare second-jet term
    `M₂` lands in `B₀·τ⁻¹` via `τ ≤ τ₀` (this is exactly WHY the clean single-constant `hAdom2` is
    FALSE — only the `τ⁻¹`-prefactored form survives; see `CurvedRNCHeatOpDom2` header).

  * `witnessSecondXDeriv_chartImage_envelope` — the TIED layer.  Rewrites the concrete
    `witnessSecondXDeriv` via the banked `SliverCConvBatch.witnessSecondXDeriv_chartImage_expand`
    equality and applies the abstract core, delivering the exact `hSecondEnv` RHS shape at a single
    `(i, τ, z)`.  The per-point constants `B₀,B₁` are explicit in the carried sup bounds; the UNIFORM
    (over the compact gate box) version of `hSecondEnv` needs the `CompactJetBounds` uniformisation of
    those sup bounds and the `chartW0_rncRadialSq_error` near-isometry — a separate plumbing layer.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It is the pointwise assembly of the carried
  `hSecondEnv` envelope from strictly weaker, elementary pointwise data (sup bounds + upper
  near-isometry) — a genuine reduction, NOT a re-export: none of the hypotheses is the conclusion, and
  each is a manifestly satisfiable pointwise fact (continuity sup bounds + the banked near-isometry).
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-equal hypothesis, no
  existing file edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverCConvBatch

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.VanVleck QIQTH.SliverCConvBatch
open scoped BigOperators

namespace QIQTH.WidthSecondEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `chartImage_second_envelope_abstract` — the pure τ-power envelope core.**

    The chart-image Leibniz–Gaussian value
    `W = G·[ (P²/(4τ²) − (S₂+PQ)/(2τ))·a₀  −  P/(2τ)·a₁  −  P/(2τ)·a₁  +  a₂ ]`
    (the exact shape of `witnessSecondXDeriv_chartImage_expand`, with `G ≥ 0` the common Gaussian
    factor, `P = ⟨W₀z,∂ᵢ⟩`, `S₂,PQ` the jet contractions, `a₀,a₁,a₂` the amplitude 0/1/2-jets) is
    dominated by the two-term envelope
    `(B₀ + B₁·(r²/τ))·τ⁻¹·G`
    with `B₁ = cW·M₀/4` and `B₀ = (CS+CPQ)·M₀/2 + CP·M₁ + M₂·τ₀`, PROVIDED the upper near-isometry
    `P² ≤ cW·r²`, the jet sup bounds `|P|≤CP, |S₂|≤CS, |PQ|≤CPQ`, the amplitude sup bounds
    `|a₀|≤M₀,|a₁|≤M₁,|a₂|≤M₂`, and the time cap `τ ≤ τ₀`.  NOT `a₁ = R/6`. -/
theorem chartImage_second_envelope_abstract
    (t τ₀ r2 G P S2 PQ a0 a1 a2 cW CP CS CPQ M0 M1 M2 : ℝ)
    (ht : 0 < t) (htτ : t ≤ τ₀)
    (hG : 0 ≤ G) (hcW : 0 ≤ cW) (hr2 : 0 ≤ r2)
    (hP2 : P ^ 2 ≤ cW * r2) (hPabs : |P| ≤ CP)
    (hS2 : |S2| ≤ CS) (hPQ : |PQ| ≤ CPQ)
    (hM0 : |a0| ≤ M0) (hM1 : |a1| ≤ M1) (hM2 : |a2| ≤ M2)
    (hM0n : 0 ≤ M0) (hM1n : 0 ≤ M1) (hM2n : 0 ≤ M2)
    (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCPQ : 0 ≤ CPQ) :
    |G * ((P * P / (4 * t ^ 2) - (S2 + PQ) / (2 * t)) * a0
          - P / (2 * t) * a1 - P / (2 * t) * a1 + a2)|
      ≤ (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
          + cW * M0 / 4 * (r2 / t)) * t⁻¹ * G := by
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  set A : ℝ := P * P / (4 * t ^ 2) - (S2 + PQ) / (2 * t) with hA
  set Br : ℝ := A * a0 - P / (2 * t) * a1 - P / (2 * t) * a1 + a2 with hBr
  -- Triangle bound on the bracket magnitude.
  have htri : |Br| ≤ |A| * M0 + |P| / (2 * t) * M1 + |P| / (2 * t) * M1 + M2 := by
    have h1 : |Br| ≤ |A * a0| + |P / (2 * t) * a1| + |P / (2 * t) * a1| + |a2| := by
      have e1 : Br = A * a0 + -(P / (2 * t) * a1) + -(P / (2 * t) * a1) + a2 := by
        rw [hBr]; ring
      calc |Br| = |A * a0 + -(P / (2 * t) * a1) + -(P / (2 * t) * a1) + a2| := by rw [e1]
        _ ≤ |A * a0 + -(P / (2 * t) * a1) + -(P / (2 * t) * a1)| + |a2| := abs_add_le _ _
        _ ≤ (|A * a0 + -(P / (2 * t) * a1)| + |-(P / (2 * t) * a1)|) + |a2| := by
              gcongr; exact abs_add_le _ _
        _ ≤ ((|A * a0| + |-(P / (2 * t) * a1)|) + |-(P / (2 * t) * a1)|) + |a2| := by
              gcongr; exact abs_add_le _ _
        _ = |A * a0| + |P / (2 * t) * a1| + |P / (2 * t) * a1| + |a2| := by
              simp only [abs_neg]
    -- bound each factor
    have hAa : |A * a0| ≤ |A| * M0 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hM0 (abs_nonneg _)
    have hPa : |P / (2 * t) * a1| ≤ |P| / (2 * t) * M1 := by
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * t)]
      exact mul_le_mul_of_nonneg_left hM1 (by positivity)
    have ha2 : |a2| ≤ M2 := hM2
    calc |Br| ≤ |A * a0| + |P / (2 * t) * a1| + |P / (2 * t) * a1| + |a2| := h1
      _ ≤ |A| * M0 + |P| / (2 * t) * M1 + |P| / (2 * t) * M1 + M2 := by
            gcongr
  have htne : t ≠ 0 := ne_of_gt ht
  -- bound |A|
  have hAabs : |A| ≤ P ^ 2 / (4 * t ^ 2) + (CS + CPQ) / (2 * t) := by
    have hAeq : A = P * P / (4 * t ^ 2) + -((S2 + PQ) / (2 * t)) := by rw [hA]; ring
    have hsplit : |A| ≤ |P * P / (4 * t ^ 2)| + |(S2 + PQ) / (2 * t)| := by
      rw [hAeq]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
    have hq : |P * P / (4 * t ^ 2)| = P ^ 2 / (4 * t ^ 2) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * t ^ 2),
          abs_of_nonneg (mul_self_nonneg P)]
      ring_nf
    have hl : |(S2 + PQ) / (2 * t)| ≤ (CS + CPQ) / (2 * t) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * t)]
      gcongr
      exact (abs_add_le _ _).trans (by gcongr)
    calc |A| ≤ |P * P / (4 * t ^ 2)| + |(S2 + PQ) / (2 * t)| := hsplit
      _ = P ^ 2 / (4 * t ^ 2) + |(S2 + PQ) / (2 * t)| := by rw [hq]
      _ ≤ P ^ 2 / (4 * t ^ 2) + (CS + CPQ) / (2 * t) := by gcongr
  -- assemble bracket bound
  have hTsum : |Br| ≤ (P ^ 2 / (4 * t ^ 2) + (CS + CPQ) / (2 * t)) * M0
                      + CP / (2 * t) * M1 + CP / (2 * t) * M1 + M2 := by
    have hPa2 : |P| / (2 * t) * M1 ≤ CP / (2 * t) * M1 := by
      gcongr
    have hstep : |A| * M0 ≤ (P ^ 2 / (4 * t ^ 2) + (CS + CPQ) / (2 * t)) * M0 :=
      mul_le_mul_of_nonneg_right hAabs hM0n
    calc |Br| ≤ |A| * M0 + |P| / (2 * t) * M1 + |P| / (2 * t) * M1 + M2 := htri
      _ ≤ (P ^ 2 / (4 * t ^ 2) + (CS + CPQ) / (2 * t)) * M0
            + CP / (2 * t) * M1 + CP / (2 * t) * M1 + M2 := by
            gcongr
  -- now |G * Br| = G * |Br| ≤ G * RHS'
  rw [abs_mul, abs_of_nonneg hG]
  have hRHS' : |Br| ≤ (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
                        + cW * M0 / 4 * (r2 / t)) * t⁻¹ := by
    refine hTsum.trans ?_
    rw [← sub_nonneg]
    have hkey : (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀) + cW * M0 / 4 * (r2 / t)) * t⁻¹
        - ((P ^ 2 / (4 * t ^ 2) + (CS + CPQ) / (2 * t)) * M0
            + CP / (2 * t) * M1 + CP / (2 * t) * M1 + M2)
        = (cW * r2 - P ^ 2) * M0 / 4 * (t⁻¹ * t⁻¹)
          + M2 * (τ₀ - t) * t⁻¹ := by
      field_simp
      ring
    rw [hkey]
    have h1 : 0 ≤ (cW * r2 - P ^ 2) * M0 / 4 * (t⁻¹ * t⁻¹) := by
      have : 0 ≤ cW * r2 - P ^ 2 := by linarith [hP2]
      positivity
    have h2 : 0 ≤ M2 * (τ₀ - t) * t⁻¹ := by
      have : 0 ≤ τ₀ - t := by linarith [htτ]
      positivity
    linarith
  calc G * |Br| ≤ G * ((((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
                    + cW * M0 / 4 * (r2 / t)) * t⁻¹) :=
        mul_le_mul_of_nonneg_left hRHS' hG
    _ = (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
          + cW * M0 / 4 * (r2 / t)) * t⁻¹ * G := by ring

/-- **★★★ `witnessSecondXDeriv_chartImage_envelope` — the pointwise `hSecondEnv` envelope, TIED to the
    concrete witness.**  Rewriting the concrete second field `x`-derivative via the banked chart-image
    expansion `SliverCConvBatch.witnessSecondXDeriv_chartImage_expand` and applying the abstract τ-power
    core, the two-term Gaussian envelope holds at a single `(i, τ, z)` on the open gate:

        |witnessSecondXDeriv … i τ z|
          ≤ (B₀ + B₁·(rncRadialSq z / τ))·τ⁻¹·gaussDdim τ (W₀ z)

    with `B₁ = cW·M₀/4`, `B₀ = (CS+CPQ)·M₀/2 + CP·M₁ + M₂·τ₀`.  This is EXACTLY the `hSecondEnv` RHS
    shape (`WideWitnessAmplitude.WideAmplitudeData.hSecondEnv`).  The carried inputs are the upper
    near-isometry `⟨W₀z,Pi 0⟩² ≤ cW·rncRadialSq z` (satisfiable via `chartW0_rncRadialSq_error`
    + Cauchy–Schwarz), the chart-jet sup bounds, and the amplitude 0/1/2-jet sup bounds — all strictly
    weaker than, and none equal to, the conclusion.  The UNIFORM-over-the-compact-box `hSecondEnv`
    (fixed `B₀,B₁`) needs the `CompactJetBounds` uniformisation of these constants — a further layer.
    ⚠ NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_chartImage_envelope
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (Pi : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ x ∈ S z, ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (Pi x k) (x i))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pi (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hAmpj1 : ∀ x ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
    (hAmpi1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i (0 : Point n))
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (τ₀ cW CP CS CPQ M0 M1 M2 : ℝ) (hτ0 : τ ≤ τ₀) (hcW : 0 ≤ cW)
    (hP2 : (∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k) ^ 2 ≤ cW * rncRadialSq z)
    (hPabs : |∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k| ≤ CP)
    (hS2 : |∑ k, Pi 0 k * Pi 0 k| ≤ CS)
    (hPQ : |∑ k, uniformInverseChart g gi hC hK z 0 k * Q k| ≤ CPQ)
    (hM0 : |chartFieldAmp g gi hC hK a b τ z 0| ≤ M0)
    (hM1 : |pd (chartFieldAmp g gi hC hK a b τ z) i 0| ≤ M1)
    (hM2 : |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i 0| ≤ M2)
    (hM0n : 0 ≤ M0) (hM1n : 0 ≤ M1) (hM2n : 0 ≤ M2)
    (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCPQ : 0 ≤ CPQ) :
    |witnessSecondXDeriv g gi hC hK S a b i τ z|
      ≤ (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
          + cW * M0 / 4 * (rncRadialSq z / τ)) * τ⁻¹
          * gaussDdim τ (uniformInverseChart g gi hC hK z 0) := by
  rw [witnessSecondXDeriv_chartImage_expand g gi hC hK S a b i τ hτ z hz hSopen h0
        Pi Q hJetVi hJetQ hAmpj1 hAmpi1 hAmp2]
  set G : ℝ := gaussDdim τ (uniformInverseChart g gi hC hK z 0) with hGdef
  set P : ℝ := ∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k with hPdef
  set S2 : ℝ := ∑ k, Pi 0 k * Pi 0 k with hS2def
  set PQ : ℝ := ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k with hPQdef
  set a0 : ℝ := chartFieldAmp g gi hC hK a b τ z 0 with ha0def
  set a1 : ℝ := pd (chartFieldAmp g gi hC hK a b τ z) i 0 with ha1def
  set a2 : ℝ := pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i 0 with ha2def
  have hGnn : 0 ≤ G := by rw [hGdef]; exact QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hr2nn : 0 ≤ rncRadialSq z := by
    unfold rncRadialSq; positivity
  refine le_of_eq_of_le ?_
    (chartImage_second_envelope_abstract τ τ₀ (rncRadialSq z) G P S2 PQ a0 a1 a2
      cW CP CS CPQ M0 M1 M2 hτ hτ0 hGnn hcW hr2nn hP2 hPabs hS2 hPQ hM0 hM1 hM2
      hM0n hM1n hM2n hCP hCS hCPQ)
  congr 1
  ring

end QIQTH.WidthSecondEnvelope
