/-
  ChartJetHessianMixed — J4-218: the MIXED-INDEX (`∂ᵢ∂ⱼ`, `i ≠ j`) Leibniz–Gaussian normal form and the
  general-index gate-equation second-field-`pd` representative (measurability brick **G-b MIXED**).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  derivative-layer + measurability plumbing brick.  No `sorry` (prose excepted), no new axioms, no
  vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.  Every carried hypothesis is a genuine
  first/second-`x`-jet `HasDerivAt`, a genuine `PdiffAt`, or a genuine MEASURABILITY (never a
  joint-continuity / `C¹` obligation) — the exact style of `ChartJetHessian.gaussComp_amp_pd_pd`
  (diagonal) and `GatedDerivRepProduct.gatedDeriv2RepProd` (product diagonal), generalised to the
  off-diagonal index pair.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GAP THIS CLOSES.  `GatedDerivRepProduct` (J4-216) discharged `BorelDischargeSurface` conjunct
  (3) only on the DIAGONAL slice `i = i` (`secondFieldPd_prod_diag_measurable`), leaving the mixed
  `∂ᵢ(∂ⱼ …)`, `i ≠ j`, off-diagonal case as its §B gap (needing a NEW off-diagonal closed form).  This
  file supplies that form and, through it, the FULL conjunct (3) for ALL `(i, j)`, and finally
  instantiates `GatedTauDerivRep.tripleHEmeas_concrete_of_mixed`'s carried `hP2` slot ⟹ the concrete
  triple `hEmeas` (S1) of `HEmeasBorelAudit.tripleHEmeas`, carrying only measurable-supplier existentials.

  ── THE MIXED NORMAL FORM (the point).  For `V : Point n → Point n`, `A : Point n → ℝ`, first `i`-line
  jet field `Pi`, first `j`-line jet field `Pj`, and MIXED second jet `Q k = ∂ᵢ(Pj · k)`, the
  off-diagonal second coordinate partial of the amplitude-weighted composed Gaussian is
    `∂ᵢ∂ⱼ(G_τ∘V · A)`
      ` = G·[ (⟨V,Pi⟩·⟨V,Pj⟩)/(4τ²) − (⟨Pi,Pj⟩ + ⟨V,Q⟩)/(2τ) ]·A`
      ` + G·(−⟨V,Pj⟩/(2τ))·∂ᵢA + G·(−⟨V,Pi⟩/(2τ))·∂ⱼA + G·∂ᵢ∂ⱼA`,  `G := gaussDdim τ (V ·)`.
  The mixed Gaussian second moment is the PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩` of two first-moment factors — with NO
  `−1/(2τ)` diagonal term — plus the cross-jet `⟨Pi,Pj⟩` and second-jet `⟨V,Q⟩` corrections.  Setting
  `Pi = Pj = P`, `i = j` recovers the banked diagonal `gaussComp_amp_pd_pd` (the two gradient terms merge
  to `2·(…)·∂ᵢA`), so ONE general-index representative covers both the mixed and the diagonal case.

  ── HOW THE MIXED `∂ᵢ∂ⱼ gaussDdim` IS OBTAINED.  DERIVED here (no banked off-diagonal Gaussian second
  derivative exists): the log-derivative of the flat product Gaussian gives `∂ⱼ(G∘V) = G·(−⟨V,Pj⟩/(2τ))`
  (banked `gaussComp_pd`); differentiating THAT normal form once more along `i` (a genuine function
  equality via `gaussComp_pd` ∀ y) by the product rule yields the mixed second partial `gaussComp_pd_pd_mixed`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessian
import QIQTH.EngineInstantiation
import QIQTH.GatedTauDerivRep

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.ChartJetHessianMixed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the MIXED (off-diagonal) Leibniz–Gaussian normal forms (parametric `V`, `A`).
    ############################################################################### -/

/-- **§A — the mixed second coordinate partial of the composed Gaussian.**  With first `i`-line jet field
    `Pi`, first `j`-line jet field `Pj` (both ∀ `x`), and MIXED second jet `Q k` (`hQ`, the `i`-derivative
    of `Pj·k` at `x₀`) of the components of `V`,
      `pd (pd (fun z => gaussDdim τ (V z)) j) i x₀
          = gaussDdim τ (V x₀) · [ ⟨V,Pi⟩·⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩ + ⟨V,Q⟩)/(2τ) ]`.
    Route: inner `∂ⱼ(G∘V) = G·(−⟨V,Pj⟩/(2τ))` (`gaussComp_pd` ∀ y is a genuine function equality), then
    differentiate along `i` by the product rule; `∂ᵢ⟨V,Pj⟩ = ⟨Pi,Pj⟩ + ⟨V,Q⟩`.  Setting `Pi = Pj = P`,
    `i = j` recovers the diagonal `gaussComp_pd_pd`.  NOT `a₁ = R/6`. -/
theorem gaussComp_pd_pd_mixed (V : Point n → Point n)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (hVi : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (Pi x k) (x i))
    (hVj : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x j s) k) (Pj x k) (x j))
    (hQ : ∀ k, HasDerivAt (fun s : ℝ => Pj (Function.update x₀ i s) k) (Q k) (x₀ i)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z)) j y) i x₀
      = gaussDdim τ (V x₀)
        * ((∑ k, V x₀ k * Pi x₀ k) * (∑ k, V x₀ k * Pj x₀ k) / (4 * τ ^ 2)
            - ((∑ k, Pi x₀ k * Pj x₀ k) + (∑ k, V x₀ k * Q k)) / (2 * τ)) := by
  -- (1) inner `pd` along `j` as a function (S1a ∀ y)
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z)) j y)
      = (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * Pj y k) / (2 * τ))) :=
    funext (fun y => gaussComp_pd V (Pj y) τ hτ j y (fun k => hVj y k))
  rw [hinner]
  -- (2) differentiabilities of the two factors at `x₀` along `i`
  have hGf : PdiffAt (fun y => gaussDdim τ (V y)) i x₀ :=
    (gaussComp_hasDerivAt_line V (Pi x₀) τ hτ i x₀ (fun k => hVi x₀ k)).differentiableAt
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hVi x₀ k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => Pj (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hQ k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * Pj y k) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) (x₀ i)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * Pj y k) / (2 * τ)) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) / (2 * τ))
        (x₀ i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  -- (3) Leibniz on the S1a normal form
  rw [pd_mul (fun y => gaussDdim τ (V y)) (fun y => -(∑ k, V y k * Pj y k) / (2 * τ)) i x₀ hGf hhf,
      gaussComp_pd V (Pi x₀) τ hτ i x₀ (fun k => hVi x₀ k),
      pd_neg_div_const (fun y => ∑ k, V y k * Pj y k) (2 * τ) i x₀ hsumPdiff]
  -- (4) `∂ᵢ⟨V,Pj⟩ = ∑ (Pi·Pj + V·Q)`
  have hpdsum : pd (fun y => ∑ k, V y k * Pj y k) i x₀
      = ∑ k, (Pi x₀ k * Pj x₀ k + V x₀ k * Q k) := by
    rw [pd_sum (Finset.univ) (fun k y => V y k * Pj y k) i x₀
        (fun k _ => (hdV k).mul (hdP k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pd_mul (fun y => V y k) (fun y => Pj y k) i x₀ (hdV k) (hdP k)]
    have h1 : pd (fun y => V y k) i x₀ = Pi x₀ k := by simp only [pd]; exact (hVi x₀ k).deriv
    have h2 : pd (fun y => Pj y k) i x₀ = Q k := by simp only [pd]; exact (hQ k).deriv
    rw [h1, h2]
  rw [hpdsum, Finset.sum_add_distrib]
  have hτ' : τ ≠ 0 := hτ.ne'
  field_simp
  ring

/-- **§A — the mixed Leibniz normal form for the amplitude-weighted composed Gaussian.**  For
    `H = (fun x => gaussDdim τ (V x)·A x)`, the off-diagonal second coordinate partial is the twice-along-
    two-lines product rule
      `pd (pd H j) i x₀
          = [mixed S1b]·A x₀
          + (G·(−⟨V,Pj⟩/(2τ)))·∂ᵢA + (G·(−⟨V,Pi⟩/(2τ)))·∂ⱼA + G·∂ᵢ∂ⱼA`,
    `[mixed S1b] = gaussComp_pd_pd_mixed`, `G := gaussDdim τ (V ·)`.  The two gradient (`∂A`) terms are
    NO LONGER equal (distinct jet/amplitude directions), unlike the diagonal `2·(…)·∂ᵢA`.  NOT `a₁ = R/6`. -/
theorem gaussComp_amp_pd_pd_mixed (V : Point n → Point n) (A : Point n → ℝ)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (hVi : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (Pi x k) (x i))
    (hVj : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x j s) k) (Pj x k) (x j))
    (hQ : ∀ k, HasDerivAt (fun s : ℝ => Pj (Function.update x₀ i s) k) (Q k) (x₀ i))
    (hAj1 : ∀ x, PdiffAt A j x)
    (hAi1 : PdiffAt A i x₀)
    (hA2 : PdiffAt (fun y => pd A j y) i x₀) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) j y) i x₀
      = gaussDdim τ (V x₀)
          * ((∑ k, V x₀ k * Pi x₀ k) * (∑ k, V x₀ k * Pj x₀ k) / (4 * τ ^ 2)
              - ((∑ k, Pi x₀ k * Pj x₀ k) + (∑ k, V x₀ k * Q k)) / (2 * τ)) * A x₀
        + (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * Pj x₀ k) / (2 * τ))) * pd A i x₀
        + (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * Pi x₀ k) / (2 * τ))) * pd A j x₀
        + gaussDdim τ (V x₀) * pd (fun y => pd A j y) i x₀ := by
  -- Gaussian factor differentiabilities
  have hGfPj : ∀ y, PdiffAt (fun z => gaussDdim τ (V z)) j y :=
    fun y => (gaussComp_hasDerivAt_line V (Pj y) τ hτ j y (fun k => hVj y k)).differentiableAt
  have hGfPi : PdiffAt (fun z => gaussDdim τ (V z)) i x₀ :=
    (gaussComp_hasDerivAt_line V (Pi x₀) τ hτ i x₀ (fun k => hVi x₀ k)).differentiableAt
  -- S1a normal form for `pd_j Gf` as a function
  have hGinner : (fun y => pd (fun z => gaussDdim τ (V z)) j y)
      = (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * Pj y k) / (2 * τ))) :=
    funext (fun y => gaussComp_pd V (Pj y) τ hτ j y (fun k => hVj y k))
  -- PdiffAt of `gⱼ` along `i` at `x₀`
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hVi x₀ k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => Pj (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hQ k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * Pj y k) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) (x₀ i)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * Pj y k) / (2 * τ)) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) / (2 * τ))
        (x₀ i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  have hpdGf_pdiff : PdiffAt (fun y => pd (fun z => gaussDdim τ (V z)) j y) i x₀ := by
    rw [hGinner]; exact hGfPi.mul hhf
  -- (1) inner Leibniz along `j` (∀ y)
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z) * A z) j y)
      = (fun y => pd (fun z => gaussDdim τ (V z)) j y * A y
          + gaussDdim τ (V y) * pd A j y) :=
    funext (fun y => pd_mul (fun z => gaussDdim τ (V z)) A j y (hGfPj y) (hAj1 y))
  rw [hinner]
  -- (2) outer sum + two Leibniz splits along `i`
  rw [pd_add (fun y => pd (fun z => gaussDdim τ (V z)) j y * A y)
        (fun y => gaussDdim τ (V y) * pd A j y) i x₀
        (hpdGf_pdiff.mul hAi1) (hGfPi.mul hA2),
      pd_mul (fun y => pd (fun z => gaussDdim τ (V z)) j y) A i x₀ hpdGf_pdiff hAi1,
      pd_mul (fun y => gaussDdim τ (V y)) (fun y => pd A j y) i x₀ hGfPi hA2]
  -- (3) substitute mixed S1b + S1a along `i` and along `j`
  rw [gaussComp_pd_pd_mixed V Pi Pj Q τ hτ i j x₀ hVi hVj hQ,
      gaussComp_pd V (Pj x₀) τ hτ j x₀ (fun k => hVj x₀ k),
      gaussComp_pd V (Pi x₀) τ hτ i x₀ (fun k => hVi x₀ k)]
  ring

/-! ###############################################################################
    ### §B — the mixed on-gate closed form for the concrete gated van-Vleck witness.
    ############################################################################### -/

/-- **Mixed second-order germ congruence of `pd∘pd`.**  The `SecondDerivEnvelope.pd_pd_congr_at`
    (diagonal `pd (pd f i) i`) at OFF-diagonal indices: if `f =ᶠ[𝓝 p] f'` then
    `pd (pd f j) i p = pd (pd f' j) i p` (outer along `i`, inner along `j`).  Same route
    (`pd_congr_of_eventuallyEq` on an open `V ∋ p`, twice). -/
theorem pd_pd_congr_at_mixed (f f' : Point n → ℝ) (i j : Fin n) (p : Point n)
    (h : ∀ᶠ x in 𝓝 p, f x = f' x) :
    pd (fun y => pd f j y) i p = pd (fun y => pd f' j y) i p := by
  apply pd_congr_of_eventuallyEq
  obtain ⟨V, hVeq, hVopen, hVp⟩ := eventually_nhds_iff.mp h
  refine eventually_nhds_iff.mpr ⟨V, ?_, hVopen, hVp⟩
  intro y hyV
  exact pd_congr_of_eventuallyEq f f' j y (eventually_nhds_iff.mpr ⟨V, hVeq, hVopen, hyV⟩)

/-- **★ §B — `witnessMixed_gate_eq` — THE ON-GATE MIXED ORDER-2 FORMULA.**  On the OPEN gate
    (base `z ∈ K`, field point `p ∈ S z`), with carried `i`/`j` chart field jets `Pi`/`Pj`, mixed second
    jet `Q`, and amplitude differentiabilities, the OFF-DIAGONAL second field-`pd` of the gated `N = 1`
    van-Vleck witness equals the mixed Leibniz–Gaussian normal form (`gaussComp_amp_pd_pd_mixed` at
    `x₀ = p`).  The off-diagonal counterpart of `SecondDerivEnvelope.witnessFieldDeriv2_gate_eq`.
    NOT `a₁ = R/6`. -/
theorem witnessMixed_gate_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (Pi x k) (x i))
    (hJetVj : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x j s) k) (Pj x k) (x j))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pj (Function.update p i s) k) (Q k) (p i))
    (hAmpj1 : ∀ x, PdiffAt (chartFieldAmp g gi hC hK a b τ z) j x)
    (hAmpi1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p) :
    pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y) i p
      = gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * ((∑ k, uniformInverseChart g gi hC hK z p k * Pi p k)
                * (∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (4 * τ ^ 2)
              - ((∑ k, Pi p k * Pj p k)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ))
          * chartFieldAmp g gi hC hK a b τ z p
        + (gaussDdim τ (uniformInverseChart g gi hC hK z p)
              * (-(∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) i p
        + (gaussDdim τ (uniformInverseChart g gi hC hK z p)
              * (-(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) j p
        + gaussDdim τ (uniformInverseChart g gi hC hK z p)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p := by
  -- on-gate nbhd factorisation of the witness in the field slot.
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
  -- transfer the local mixed `pd∘pd` off the factored form, then apply the mixed normal form.
  rw [pd_pd_congr_at_mixed
        (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z)
        (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
          * chartFieldAmp g gi hC hK a b τ z x') i j p hev,
      gaussComp_amp_pd_pd_mixed (uniformInverseChart g gi hC hK z)
        (chartFieldAmp g gi hC hK a b τ z) Pi Pj Q τ hτ i j p hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]

/-- **`witnessMixed_offGate_eq_zero`.**  Off the base gate (`z ∉ K`) the witness is identically `0` in the
    field slot, so its mixed second field-`pd` vanishes.  The off-diagonal counterpart of
    `witnessFieldDeriv2_offGate_eq_zero`.  NOT `a₁ = R/6`. -/
theorem witnessMixed_offGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (p z : Point n) (hz : z ∉ K) :
    pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y) i p = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x'
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  have hin : (fun y : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext y
    simp only [hzero]
    exact pd_const 0 j y
  rw [hin]
  exact pd_const 0 i p

/-- **`witnessMixed_eq_zero_of_nonpos`.**  For `τ ≤ 0` (`0 < n`) the whole gated witness slot vanishes in
    the field variable (`gaussDdim τ = 0` on the gate; `gatedKernel = 0` off it), so its mixed second
    field-`pd` is `0`.  The off-diagonal counterpart of `SecondDerivEnvelope.witnessFieldDeriv2_eq_zero_of_nonpos`.
    NOT `a₁ = R/6`. -/
theorem witnessMixed_eq_zero_of_nonpos (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (p z : Point n) (hτ : τ ≤ 0) :
    pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y) i p = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x'
    by_cases hpS : x' ∈ S z
    · by_cases hzK : z ∈ K
      · rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hzK hpS,
            gaussDdim_eq_zero_of_nonpos hn τ (uniformInverseChart g gi hC hK z x') hτ]
        ring
      · unfold vanVleckGatedWitness
        exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hzK)
    · unfold vanVleckGatedWitness
      exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inr hpS)
  have hin : (fun y : Point n =>
        pd (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext y
    simp only [hzero]
    exact pd_const 0 j y
  rw [hin]
  exact pd_const 0 i p

/-! ###############################################################################
    ### §C — the general-index (mixed) product-coordinate representative + measurability.
    ############################################################################### -/

/-- **`gatedMixed2RepProd` — the product-coordinate GENERAL-INDEX representative of the mixed second
    field-`pd`.**  Field point `w.2.1`, base `w.2.2`, time `w.1`; carried `i`/`j` first jet fields
    `Pifield`/`Pjfield` and mixed second jet field `Qfield`.  The `w.2.2 ∈ K`-indicator of the mixed
    order-2 on-gate closed form (`witnessMixed_gate_eq`).  Covers BOTH the mixed and (`i = j`,
    `Pi = Pj`) diagonal case.  NOT `a₁ = R/6`. -/
noncomputable def gatedMixed2RepProd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * ((∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
                * (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                / (4 * w.1 ^ 2)
              - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                  + (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k))
                / (2 * w.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + (gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
              * (-(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
                  / (2 * w.1)))
            * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1
        + (gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
              * (-(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
                  / (2 * w.1)))
            * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)

/-- **★ `gatedMixed2RepProd_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the general-index
    product representative, from the carried factor measurabilities (chart, `i`/`j` first jet fields,
    mixed second jet field, amplitude and its `i`/`j`/mixed field-`pd`s).  `gaussDdim` via
    `gaussDdim_uncurry_measurable`; the `1/τ²`/`1/τ` denominators are `measurable_fst`-built.  NO
    continuity.  NOT `a₁ = R/6`. -/
theorem gatedMixed2RepProd_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i j : Fin n)
    (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)) :
    Measurable (gatedMixed2RepProd g gi hC hK a b i j Pifield Pjfield Qfield) := by
  unfold gatedMixed2RepProd
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hVPi : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hPimeas k)
  have hVPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hPjmeas k)
  have hPiPj : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact (hPimeas k).mul (hPjmeas k)
  have hVQ : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hQmeas k)
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable
      (fun w : ℝ × Point n × Point n =>
        (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k)
            * (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
            / (4 * w.1 ^ 2)
          - ((∑ k, Pifield w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k)
              + (∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Qfield w.2.2 w.2.1 k))
            / (2 * w.1)) :=
    ((hVPi.mul hVPj).div hden2).sub ((hPiPj.add hVQ).div hden1)
  have hGradj : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pjfield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPj.neg.div hden1
  have hGradi : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ k, uniformInverseChart g gi hC hK w.2.2 w.2.1 k * Pifield w.2.2 w.2.1 k) / (2 * w.1)) :=
    hVPi.neg.div hden1
  exact (((((hG.mul hHess).mul hAmpMeas).add
      ((hG.mul hGradj).mul hAmpDerivIMeas)).add
      ((hG.mul hGradi).mul hAmpDerivJMeas)).add
      (hG.mul hAmpDeriv2Meas)).indicator (measurable_snd.snd hKmeasSet)

/-- **★ `witnessMixed2_eq_gatedMixed2RepProd` — THE PRODUCT MIXED EVERYWHERE IDENTITY.**  The raw
    off-diagonal second field-`pd` of the concrete witness EQUALS the general-index product representative
    at every `w`, via the three-way dichotomy (`w.2.2 ∉ K` / `w.2.2 ∈ K, w.1 ≤ 0` / `w.2.2 ∈ K, 0 < w.1`,
    the on-gate mixed formula `witnessMixed_gate_eq`).  NOT `a₁ = R/6`. -/
theorem witnessMixed2_eq_gatedMixed2RepProd (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) :
    ∀ w : ℝ × Point n × Point n,
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
        = gatedMixed2RepProd g gi hC hK a b i j Pifield Pjfield Qfield w := by
  intro w
  simp only [gatedMixed2RepProd]
  by_cases hzK : w.2.2 ∈ K
  · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hpS, hjetVi, hjetVj, hjetQ, hampj, hampi, hamp2⟩ := hgate w hzK hτ
      exact witnessMixed_gate_eq g gi hC hK S a b i j w.1 hτ w.2.2 hzK hSopen w.2.1 hpS
        (Pifield w.2.2) (Pjfield w.2.2) (Qfield w.2.2 w.2.1) hjetVi hjetVj hjetQ hampj hampi hamp2
    · rw [not_lt] at hτ
      rw [witnessMixed_eq_zero_of_nonpos hn g gi hC hK S a b i j w.1 w.2.1 w.2.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    exact witnessMixed_offGate_eq_zero g gi hC hK S a b i j w.1 w.2.1 w.2.2 hzK

/-- **★★ `secondFieldPd_prod_measurable` — G-b MIXED, the general-index product-coordinate second-`pd`
    measurability.**  The joint `(τ,p,q)`-Borel measurability of the raw off-diagonal second field-`pd`
    kernel with the field point varying, via the mixed everywhere identity glued to
    `gatedMixed2RepProd_measurable`.  Discharges conjunct (3) of `BorelDischargeSurface` for ANY `(i, j)`
    (mixed AND diagonal).  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_measurable (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) :
    Measurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1)
      = gatedMixed2RepProd g gi hC hK a b i j Pifield Pjfield Qfield := by
    funext w
    exact witnessMixed2_eq_gatedMixed2RepProd hn g gi hC hK S a b i j Pifield Pjfield Qfield hgate w
  rw [hrw]
  exact gatedMixed2RepProd_measurable g gi hC hK a b i j Pifield Pjfield Qfield hKmeasSet
    hChartMeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas

/-- **★★ `secondFieldPd_prod_stronglyMeasurable` — BorelDischargeSurface CONJUNCT (3), CONCRETE, ALL `(i,j)`.**
    For the concrete gated witness `G := vanVleckGatedWitness g gi hC hK S a b`,
      `∀ i j, StronglyMeasurable (fun w => pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1)`,
    the EXACT `hP2` shape of `GatedTauDerivRep.tripleHEmeas_concrete_of_mixed`.  Each `(i, j)` supplies
    (via `hcar`) its `i`/`j` first jet fields, mixed second jet field, the factor measurabilities and the
    on-gate data; `secondFieldPd_prod_measurable` closes measurability and ℝ-valued
    `Measurable ⟹ StronglyMeasurable`.  CONTINUITY-FREE.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_stronglyMeasurable (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (hcar : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)) :
    ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  intro i j
  obtain ⟨Pifield, Pjfield, Qfield, hChartMeas, hPimeas, hPjmeas, hQmeas, hAmpMeas,
    hAmpDerivIMeas, hAmpDerivJMeas, hAmpDeriv2Meas, hgate⟩ := hcar i j
  exact (secondFieldPd_prod_measurable hn g gi hC hK S a b i j Pifield Pjfield Qfield hKmeasSet
    hChartMeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas
    hgate).stronglyMeasurable

/-! ###############################################################################
    ### §D — ★ THE PAYOFF: the concrete triple `hEmeas` (S1), continuity-free.
    ############################################################################### -/

/-- **★★★ `tripleHEmeas_concrete` — S1 FOR THE CONCRETE WITNESS, FULLY DISCHARGED.**  The triple `hEmeas`
    (S1) of `HEmeasBorelAudit.tripleHEmeas` for the concrete gated van-Vleck witness
    `G := vanVleckGatedWitness g gi hC hK S a b`, with EVERY derivative-field conjunct discharged
    continuity-free:
      • conjunct (1) — `∂_τ` — via `GatedTauDerivRep` (G-c) from `hcarTau`;
      • conjunct (2) — first field-`pd` — via `GatedDerivRepProduct` (G-a) from `hcarField`;
      • conjunct (3) — the FULL second field-`pd` Hessian `∂ᵢ(∂ⱼ …)` for ALL `(i, j)` — via
        `secondFieldPd_prod_stronglyMeasurable` (G-b MIXED, this file) from `hcarField2`, closing the
        mixed off-diagonal residue that `GatedDerivRepProduct` (J4-216) left open;
      • conjuncts (4)/(5) — `gi` / `christoffel` measurabilities — from `hgi` / `hchr`.
    Assembled through `GatedTauDerivRep.tripleHEmeas_concrete_of_mixed`, whose only previously-open slot
    was exactly the mixed `hP2`.  This closes the entire Route-B measurability family for the concrete
    witness, carrying ONLY the measurable-supplier existentials.  Continuity-free.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_concrete (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) :=
  QIQTH.GatedTauDerivRep.tripleHEmeas_concrete_of_mixed hn g gi hC hK S a b hKmeasSet
    hcarTau hcarField
    (secondFieldPd_prod_stronglyMeasurable hn g gi hC hK S a b hKmeasSet hcarField2)
    hgi hchr

end QIQTH.ChartJetHessianMixed

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ChartJetHessianMixed
#print axioms gaussComp_pd_pd_mixed
#print axioms gaussComp_amp_pd_pd_mixed
#print axioms pd_pd_congr_at_mixed
#print axioms witnessMixed_gate_eq
#print axioms witnessMixed_offGate_eq_zero
#print axioms witnessMixed_eq_zero_of_nonpos
#print axioms gatedMixed2RepProd_measurable
#print axioms witnessMixed2_eq_gatedMixed2RepProd
#print axioms secondFieldPd_prod_measurable
#print axioms secondFieldPd_prod_stronglyMeasurable
#print axioms tripleHEmeas_concrete
end AxiomChecks
