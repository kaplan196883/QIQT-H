/-
  SliverCConvBatch — J4-249: the sliver `hD2Hexpand` VERDICT brick + the final-distance map recon.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  recon-and-bank brick.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses, no conclusion-in-disguise, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE `hD2Hexpand` VERDICT (map item [3], the KEY question).

  `AmplitudePackage.AmplitudeDerivativeData`'s hard field `hD2Hexpand` DEMANDS, for the concrete
  second field-`pd` object `witnessSecondXDeriv g gi hC hK S a b i τ z` (`= ∂²_{xᵢ}(x' ↦ H_G τ x' z)(0)`),
  the 3-term Leibniz–Gaussian normal form with the Gaussian and the moments at the **BASE POINT `z`**:
      `witnessSecondXDeriv … i τ z
         = (zᵢ²−2τ)/(4τ²)·gaussDdim τ z·Aamp τ z
           + zᵢ/(2τ)·gaussDdim τ z·A1amp τ z
           + gaussDdim τ z·A2amp τ z`,
  together with the τ-UNIFORM sup-bounds `|Aamp|≤M₀`, `|A1amp|≤M₁`, `|A2amp|≤M₂`.

  Tonight's banked general-index Leibniz–Gaussian second-derivative normal form
  `ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed` (+ the satisfiable-`∀ x ∈ S z` port
  `Field2NbhdReshape.witnessMixed_gate_eq_nbhd`) produces, on the open gate at field point `p`,
      `∂ᵢ∂ⱼ(G∘W · A) = G_W·[⟨W,Pi⟩·⟨W,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨W,Q⟩)/(2τ)]·A + …`,
  with `G_W := gaussDdim τ (W z p)` the **CHART-IMAGE** Gaussian (`W := uniformInverseChart g gi hC hK z`)
  and the moments in the **CHART JETS** `⟨W z p, Pi⟩`, `⟨Pi,Pj⟩`, `⟨W z p, Q⟩`.

  ── VERDICT: **MISMATCH** (documented delta, NOT a pure instantiation).  Specialising the banked
  mixed form to the diagonal `j = i`, field-centre `p = 0` gives `witnessSecondXDeriv` in the
  **chart-image** normal form — banked verbatim below as `witnessSecondXDeriv_chartImage_expand`.  The
  `hD2Hexpand` target is the **flat / RNC-linearised** normal form (Gaussian at `z`, moments in `zᵢ`,
  `‖Pi(0)‖² = 1` so the diagonal `−(‖Pi‖²+⟨W,Q⟩)/(2τ)` collapses to `−2τ/(4τ²)`).  The two coincide iff
    (i)  `‖W z 0‖ = ‖z‖`         (Gaussian-argument near-isometry `d_g(z,0) = ‖z‖`; the exact BLOCKER
                                  isolated by `AmplitudePackage.vanVleckGatedWitness_zero_factor`),
    (ii) `⟨W z 0, Pi(0)⟩ = zᵢ`, `‖Pi(0)‖² = 1`, `⟨W z 0, Q⟩` absorbed  (Jacobian orthonormality at the
                                  centre + second-jet absorption).
  The residual Gaussian ratio `G_W/G_z = exp(−(‖W z 0‖²−‖z‖²)/(4τ)) = exp(−O(‖z‖⁴)/(4τ))` cannot be
  folded into the amplitudes while keeping the τ-uniform sup-bounds — the `O(‖z‖⁴)/(4τ)` blow-up as
  `τ→0` is exactly the genuine geometric step.  A trivial algebraic solution (`Aamp = A1amp = 0`,
  `A2amp := witnessSecondXDeriv/gaussDdim τ z`) satisfies the *identity* but VIOLATES `hA2ampBdd`
  (`A2amp` inherits the `1/τ²` singularity), so the bounds — not the identity — are what make
  `hD2Hexpand` genuinely blocked.  Hence `hD2Hexpand_concrete` is NOT constructible from tonight's bank;
  the AmplitudeDerivativeData bundle does NOT close at the concrete witness, and `amplitudePackage_sliver_bound`
  does NOT fire.  The blocking field is `hD2Hexpand` (chart near-isometry + Gaussian-ratio absorption);
  every OTHER AmplitudeDerivativeData field is either banked or DATA conditional on a bounded amplitude
  decomposition that only the near-isometry provides.

  ── WHAT LANDS (this file, unconditionally, std-3):
    • `witnessSecondXDeriv_chartImage_expand` — ★ the diagonal (`j = i`, `p = 0`) specialisation of the
      banked mixed on-gate normal form: the concrete second field-`pd` in the CHART-IMAGE Leibniz–Gaussian
      form.  This is the exact honest form the `hD2Hexpand` discharge must START from — the second-order
      analog of `vanVleckGatedWitness_zero_factor` — and pins the precise delta to the demanded base-point
      form.  Satisfiable `∀ x ∈ S z` jet/amplitude carries (never the global-∀ vacuity).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AmplitudePackage
import QIQTH.Field2NbhdReshape

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.VanVleck
open scoped Topology BigOperators ContDiff

namespace QIQTH.SliverCConvBatch

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ `witnessSecondXDeriv_chartImage_expand` — the CHART-IMAGE Leibniz–Gaussian normal form of the
    concrete second field-`pd` at the field centre (the `hD2Hexpand` verdict brick).**  On the open gate
    (`z ∈ K`, `0 ∈ S z`, `0 < τ`), with the `i`-line chart first jet field `Pi` (carried satisfiably
    `∀ x ∈ S z`), the mixed second jet `Q` at the centre, and the amplitude regularity, the concrete
    formal second-`x`-derivative object `witnessSecondXDeriv` of the gated `N = 1` van-Vleck witness
    equals the DIAGONAL mixed Leibniz–Gaussian normal form at chart image `W z 0` and chart amplitude:
      `witnessSecondXDeriv … i τ z
         = G_W·[ ⟨W z 0, Pi 0⟩²/(4τ²) − (‖Pi 0‖² + ⟨W z 0, Q⟩)/(2τ) ]·A 0
           + 2·(G_W·(−⟨W z 0, Pi 0⟩/(2τ)))·∂ᵢA 0
           + G_W·∂ᵢ∂ᵢA 0`,   `G_W := gaussDdim τ (W z 0)`,  `W := uniformInverseChart g gi hC hK z`,
      `A := chartFieldAmp g gi hC hK a b τ z`.
    Route: `witnessSecondXDeriv` is DEFEQ to `pd (pd (fun x' ↦ H_G τ x' z) i) i 0`, so this is the
    banked `Field2NbhdReshape.witnessMixed_gate_eq_nbhd` specialised to `j := i`, `p := 0`, `Pj := Pi`.

    ⚠ This is the chart-image (CURVED) form.  The `AmplitudePackage.hD2Hexpand` field demands the
    flat / base-point form (`gaussDdim τ z`, moments in `zᵢ`); reconciling the two is the chart
    near-isometry `‖W z 0‖ = ‖z‖` + Gaussian-ratio absorption — the genuine geometric BLOCKER, NOT a
    def-chain unfolding.  So this brick DELIMITS `hD2Hexpand` (pins the delta); it does not discharge it.
    NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_chartImage_expand (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i (0 : Point n)) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0)
          * ((∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k)
                * (∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k) / (4 * τ ^ 2)
              - ((∑ k, Pi 0 k * Pi 0 k)
                  + (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k)) / (2 * τ))
          * chartFieldAmp g gi hC hK a b τ z 0
        + (gaussDdim τ (uniformInverseChart g gi hC hK z 0)
              * (-(∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) i 0
        + (gaussDdim τ (uniformInverseChart g gi hC hK z 0)
              * (-(∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) i 0
        + gaussDdim τ (uniformInverseChart g gi hC hK z 0)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i 0 := by
  unfold witnessSecondXDeriv
  exact QIQTH.Field2NbhdReshape.witnessMixed_gate_eq_nbhd g gi hC hK S a b i i τ hτ z hz hSopen
    (0 : Point n) h0 Pi Pi Q (hJetVi 0 h0) hJetVi hJetQ hAmpj1 hAmpi1 hAmp2

end QIQTH.SliverCConvBatch

/-! ## Axiom check — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SliverCConvBatch
#print axioms witnessSecondXDeriv_chartImage_expand
end AxiomChecks
