/-
  Pd2ConvPerU — J4-365: the PER-`u` `hPd2conv` wrapper + the two first-derivative germ-link dischargers.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  packaging brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign: it lifts the banked single-
  `(H,F,u)` census discharger `Pd2ConvDissolution.hPd2conv_from_census` (J4-363) to the exact PER-`u`
  binder (viii) `hPd2conv` consumed by `LabelledRethreadV2.hDaLimLU_from_hgate` (J4-364), and supplies the
  two first-derivative germ links `hfull_pd1`/`hfrozen_pd1` those census producers require from already-
  banked families (the full-side `CConvV2Facade.hfam_v2`, the frozen-side `hQ1` W2 pointwise formula).
  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis,
  NONE equal to the conclusion, no existing file edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL
  on the whole `hDuhamel`/convergence-trio + geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TARGET (verbatim, `LabelledRethreadV2.hDaLimLU_from_hgate`'s binder (viii)):
      `hPd2conv : ∀ u ∈ U, ∀ i : Fin n, Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen H F u (u − epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0))`
  at `H := vanVleckGatedWitness g gi hChr hK S a b`, `F := leviSeries (heatOp g gi H)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## U0 — BANK SURVEY (what is already provided; the two families and the alignment).

  ### FULL side (`hfull_pd1`).  `CConvV2Facade.hfam_v2` gives, at the concrete kernels, the L1
    `∃`-nbhd `HasFDerivAt` family
      `∃ w ∈ 𝓝 0, ∀ x ∈ w, HasFDerivAt (fun p ↦ heatConv H F u p 0) (Dmap … F u x) x`
    (from its own `hlin` linewise family + the `hD1` sliver census).  `Pd2ConvDissolution.
    pd_germ_eq_of_family` turns any such family into the first-partial germ
      `(fun y ↦ ∂ᵢ(full conv) y) =ᶠ[𝓝 0] (fun y ↦ (Dmap … F u y)(eᵢ))`.
    So the census `gcoef i` is IDENTIFIED with the Dmap coefficient `fun y ↦ (Dmap … F u y)(eᵢ)`,
    which by `CConvV2DerivRep.Dmap_apply_single` equals the `s`-integral `∫₀ᵘ∫ witnessFieldDeriv … · F`
    — i.e. verbatim the sliver census's `hbulk_tendsto` limit.  This is the hypothesis-free definitional
    choice the mission anticipated.  ⟹ `hfull_pd1_concrete`.

  ### FROZEN side (`hfrozen_pd1`).  The bank's frozen first-derivative representation is the `hQ1` carry
    (binder in `GlobalRawBoundFacade` / `LabelledRethreadV2`, the W2 differentiation-under-∫ family):
      `∀ y ∈ V, ∂ᵢ(frozen_m conv)(y) = ∫₀^{u−εₘ} ∫ witnessFieldDeriv … i (u−s) y z · F s z 0`
    on an OPEN field nbhd `V ∋ 0`.  Since `V ∈ 𝓝 0`, this pointwise formula IS a germ equality directly
    — no `∃`-`HasFDerivAt` family needed on the frozen side.  ⟹ `hfrozen_pd1_from_hQ1` (with the census
    `fbulk i m` identified with that truncated integral).  This is CLEANER than the mission's fallback
    anticipated: `hQ1` already hands the germ over the nbhd.

  ## WHAT LANDS (this file, ns `QIQTH.Pd2ConvPerU`).
    • (U1a) `hfull_pd1_concrete`  — the full-side first-partial germ from `hfam_v2` (via
        `pd_germ_eq_of_family`), `gcoef i := fun y ↦ (Dmap … F u y)(eᵢ)`.
    • (U1b) `hfrozen_pd1_from_hQ1` — the frozen-side first-partial germ from the `hQ1` nbhd formula
        (via `Filter.eventuallyEq` over `V ∈ 𝓝 0`), abstract in the truncation integral `fb`.
    • (U2)  `hPd2conv_perU`       — ★ the EXACT per-`u` binder (viii) of `hDaLimLU_from_hgate`, the
        ∀-intro plumbing of `hPd2conv_from_census` over `u ∈ U` on the per-`u` census family + links.

  ## SATISFIABILITY / HONESTY.  Every carry is the banked, satisfiable, non-vacuous census datum: the
    width-2 Gaussian model of every sliver brick satisfies the whole `{sSet, gcoef, gderiv, fbulk,
    fderivBulk, bb, hb, hbulkderiv, hbulk_tendsto, hsliver}` census (documented in `Pd2ConvDissolution`),
    `hfam_v2`'s `hlin`/`hD1` are the banked facade-v2 carries, and `hQ1` is the banked W2 family.  NONE of
    the hypotheses equals the conclusion (`hfull_pd1`/`hfrozen_pd1` are FIRST-derivative germs; the
    conclusion is the SECOND-partial frozen→full Tendsto).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Pd2ConvDissolution
import QIQTH.CConvV2Facade

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.Pd2ConvPerU

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (U1a) `hfull_pd1_concrete` — the full-side first-partial germ, from `hfam_v2`.
    ############################################################################### -/

/-- **★ (U1a) `hfull_pd1_concrete`.**  The `hfull_pd1` link of `hPd2conv_from_census`, DISCHARGED at the
    concrete kernels from the banked full-side family `CConvV2Facade.hfam_v2`: the first coordinate
    partial of the FULL heat convolution agrees near `0` with the Dmap coefficient,
      `(fun y ↦ ∂ᵢ(heatConv H F u · 0) y) =ᶠ[𝓝 0] (fun y ↦ (Dmap … F u y)(eᵢ))`,
    where `H := vanVleckGatedWitness g gi hChr hK S a b`, `F := leviSeries (heatOp g gi H)`.  Route:
    `hfam_v2` supplies the `∃`-nbhd `HasFDerivAt` family with representative `Dmap … F u`; `Pd2Conv-
    Dissolution.pd_germ_eq_of_family` reads off the germ.  The census's abstract `gcoef i` is thus the
    Dmap coefficient `fun y ↦ (Dmap … F u y)(eᵢ)` (= the `hbulk_tendsto` limit, `Dmap_apply_single`).
    Carries EXACTLY `hfam_v2`'s satisfiable facade-v2 hypotheses (`hlin`, `hD1`, the open nbhd `nb`);
    none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hfull_pd1_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ)
    (nb : Set (Point n)) (hnb_open : IsOpen nb) (hnb0 : (0 : Point n) ∈ nb)
    (hlin : ∀ x ∈ nb, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK S a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x)
          (Pi.single i (1 : ℝ))) (x i))
    (hD1 : ContDiffAt ℝ 1 (Dmap g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u) (0 : Point n))
    (i : Fin n) :
    (fun y => pd (fun x => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y)
      =ᶠ[𝓝 (0 : Point n)]
      (fun y => (Dmap g gi hChr hK S a b
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u y)
        (Pi.single i (1 : ℝ))) :=
  pd_germ_eq_of_family
    (fun x => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0)
    (Dmap g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u) i
    (hfam_v2 g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
      nb hnb_open hnb0 hlin hD1)

/-! ###############################################################################
    ### (U1b) `hfrozen_pd1_from_hQ1` — the frozen-side first-partial germ, from `hQ1`.
    ############################################################################### -/

/-- **★ (U1b) `hfrozen_pd1_from_hQ1`.**  The `hfrozen_pd1` link of `hPd2conv_from_census`, DISCHARGED
    from the banked frozen first-derivative carry `hQ1` (the W2 differentiation-under-∫ pointwise
    formula, a binder in `GlobalRawBoundFacade` / `LabelledRethreadV2`).  Given that formula on an OPEN
    field nbhd `V ∋ 0` (`V ∈ 𝓝 0`),
      `∀ y ∈ V, ∂ᵢ(frozen_m conv)(y) = fb y`,
    it IS a germ equality directly:
      `(fun y ↦ ∂ᵢ(frozen_m conv) y) =ᶠ[𝓝 0] fb`.
    Abstract in the truncation function `fb` (concretely `fb y = ∫₀^{u−εₘ}∫ witnessFieldDeriv … y · F`,
    the sliver census's `fbulk i m`).  No `∃`-`HasFDerivAt` family is needed on the frozen side — `hQ1`
    already hands the germ over `V`.  `hQ1`/`V ∈ 𝓝 0` are the banked, satisfiable W2 carries; the
    conclusion is a FIRST-partial germ, not the census conclusion.  NOT `a₁ = R/6`. -/
theorem hfrozen_pd1_from_hQ1 (H F : ℝ → Point n → Point n → ℝ) (u : ℝ) (m : ℕ) (i : Fin n)
    (fb : Point n → ℝ)
    (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hQ1 : ∀ y ∈ V, pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y = fb y) :
    (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y)
      =ᶠ[𝓝 (0 : Point n)] fb := by
  filter_upwards [hV] with y hy using hQ1 y hy

/-! ###############################################################################
    ### (U2) `hPd2conv_perU` — ★ the exact per-`u` binder (viii), by ∀-intro plumbing.
    ############################################################################### -/

/-- **★★★ (U2) `hPd2conv_perU`.**  THE EXACT per-`u` `hPd2conv` binder (viii) of
    `LabelledRethreadV2.hDaLimLU_from_hgate`, at `H := vanVleckGatedWitness g gi hChr hK S a b`,
    `F := leviSeries (heatOp g gi H)` — the ∀-intro plumbing of the banked single-`(H,F,u)` discharger
    `Pd2ConvDissolution.hPd2conv_from_census` over `u ∈ U`.

    ── THE PER-`u` CENSUS (all satisfiable, all carried; none the conclusion).  For each `u ∈ U`:
      • `{sSet u, hsOpen u, hsnhds u}` — the open sliver nbhd of `0`;
      • `{gcoef u, gderiv u, fbulk u, fderivBulk u, bb u, hb u, hbulkderiv u, hbulk_tendsto u,
        hsliver u}` — the per-`u` hD1 SLIVER census (`hbulk_tendsto`'s limit `gcoef u i` = the full
        Dmap coefficient; `fbulk u i m` = the frozen truncation's first partial);
      • `hfull_pd1 u`/`hfrozen_pd1 u` — the two first-partial germ links (dischargeable per-`u` by
        `hfull_pd1_concrete` / `hfrozen_pd1_from_hQ1`).
    All census fields are `u`-indexed because the truncation integrals `∫₀^{u−εₘ}` / limit `∫₀ᵘ`
    genuinely depend on `u`; `sSet` may be shared but is kept `u`-indexed for uniformity.

    ── ROUTE.  For each `u ∈ U`, apply `hPd2conv_from_census` to the `u`-slice of every field.  Pure
    binder plumbing over the banked B3 discharger; no new analysis.  NOT `a₁ = R/6`. -/
theorem hPd2conv_perU (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (sSet : ℝ → Set (Point n))
    (hsOpen : ∀ u ∈ U, IsOpen (sSet u))
    (hsnhds : ∀ u ∈ U, sSet u ∈ 𝓝 (0 : Point n))
    (gcoef : ℝ → Fin n → Point n → ℝ)
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (fbulk : ℝ → Fin n → ℕ → Point n → ℝ)
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (bb : ℝ → Fin n → ℕ → ℝ)
    (hb : ∀ u ∈ U, ∀ i : Fin n, Tendsto (bb u i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        HasFDerivAt (fbulk u i m) (fderivBulk u i m x) x)
    (hbulk_tendsto : ∀ u ∈ U, ∀ i : Fin n, ∀ x ∈ sSet u,
        Tendsto (fun m => fbulk u i m x) atTop (𝓝 (gcoef u i x)))
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ sSet u,
        dist (fderivBulk u i m x) (gderiv u i x) ≤ bb u i m)
    (hfull_pd1 : ∀ u ∈ U, ∀ i : Fin n,
        (fun y => pd (fun x => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] gcoef u i)
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)] fbulk u i m) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)) :=
  fun u hu =>
    hPd2conv_from_census (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
      (sSet u) (hsOpen u hu) (hsnhds u hu) (gcoef u) (gderiv u) (fbulk u) (fderivBulk u)
      (bb u) (hb u hu) (hbulkderiv u hu) (hbulk_tendsto u hu) (hsliver u hu)
      (hfull_pd1 u hu) (hfrozen_pd1 u hu)

end QIQTH.Pd2ConvPerU

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.Pd2ConvPerU
#print axioms hfull_pd1_concrete
#print axioms hfrozen_pd1_from_hQ1
#print axioms hPd2conv_perU
end AxiomChecks
