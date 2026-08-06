/-
  GaussInteriorMVT — the interior-MVT closure of the per-point first-variation Gauss identity
  (brick J4-347 of the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one of the four labelled inputs of `a1_R6_from_labelled`.  This
  file discharges the LAST analytic leg of the `hGauss` derivation — the per-point Gauss identity
  `∑ g_{exp_p v}(D exp_p(v)·w, γ̇(1)) = g_p(w, v)` — using ONLY the INTERIOR (`Ioo 0 1`) derivative data
  that the geodesic-variation flow actually provides (the J4-346 window finding), plus the flow's
  `Icc 0 1`-continuity, closed by the mean value theorem (which needs NO endpoint derivative).  Nothing
  here builds normal coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE CLOSURE ROUTE (documented in `GaussLemmaFlowData`'s header; executed here)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  For the concrete flow-derivative Jacobi field `J s = (Φ s (0,w)).1`, `Jp s = (Φ s (0,w)).2`
  (from `expDiff_flow_isGeodesicVariation`), set
    `E s := ∑ g_{ab}(γ s)·J(s)^a·γ̇(s)^b`   (the transverse pairing), and
    `W s := ∑ g_{ab}(γ s)·(∇J)(s)^a·γ̇(s)^b` (the covariant pairing, `∇J = Jp + Γ(γ)·γ̇·J`).
  Then, using ONLY the interior first-order flow system and `Icc`-continuity:
    (1) INTERIOR derivatives on `Ioo 0 1`:  `E' = W` (banked `transverse_pairing_hasDerivAt`) and
        `W' = 0` (banked `covariant_pairing_hasDerivAt_zero` + `hvanish_from_antisym` +
        `jacobi_covariant_ode`, fed by the ONE new computation `covariant_field_hasDerivAt` — the
        interior product rule for the covariant field `∇J`).
    (2) `Icc 0 1`-continuity of `E, W`:  the flow's within-`Icc` law gives `ContinuousWithinAt` at the
        ENDPOINTS (hence `ContinuousOn`) for `J, Jp`; `γ` is two-sided-`C¹` on `Ioo(-2,2) ⊇ Icc 0 1`.
    (3) MVT closure:  `W` continuous on `Icc` with `W' = 0` on `Ioo` ⟹ `W` constant (Lagrange MVT,
        `exists_hasDerivAt_eq_slope` — NO endpoint derivative needed); then `E(1) − E(0) = W(0)` by the
        same MVT applied to `E − s·W(0)`.  With `E(0) = 0` (`J(0)=0`) and `W(0) = g_p(w,v)`
        (`Jp(0)=w`, `J(0)=0`): **`E(1) = g_p(w,v)`**.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED (fully derived, axiom-free, no `sorry`)
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • M1  `covariant_field_hasDerivAt` — the interior product rule for the covariant field
       `∇J = Jp + Γ(γ)·γ̇·J` (the ONE new computation); `const_of_ioo_deriv_zero` /
       `linear_of_interior` — the MVT constancy + linear-growth closure (M2).
   • M2  wired inside `gauss_interior_identity` (Icc-continuity + the two MVT constancy steps).
   • M3  `hgball_concrete` — the per-`v`, per-`i` (`w = eᵢ`) Gauss identity in the EXACT shape
       `GaussLemmaFlowData.hGauss_pullback`'s `hgball` binder wants; `hGauss_pullback_concrete` — the
       germ `∀ i, (fun x => ∑ j, g̃_ij(x)·x^j) =ᶠ[𝓝 0] (fun x => x^i)` with the Gauss carry DISCHARGED.

  NET: the `hGauss` per-point first-variation identity is now DERIVED from the flow (no interval-window
  carry, no differentiation carry).  What survives on the pullback route is the geometry data — the
  base gauge `g_p = I` and the metric hypotheses `hsymm/hinv/hg` (all satisfiable) — plus the separate
  capstone-transport residues recorded in `GaussLemmaFlowData`'s F4 verdict (the C∞-vs-C⁴ smoothness
  binder (i), and the derivable `∂g̃(0)=0` / inverse-positivity legs (iii)/(iv)).  This is STILL NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.ExpDiffVariation
import QIQTH.JacobiEquation
import QIQTH.CovariantJacobi
import QIQTH.PullbackMetric
import QIQTH.GaussLemmaTransverse
import QIQTH.RiemannFirstPairAntisym
import QIQTH.GaussLemmaHomogeneity
import QIQTH.GaussLemmaFlowData

namespace QIQTH.GaussInteriorMVT

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open QIQTH.GaussLemmaTransverse QIQTH.RiemannFirstPairAntisym QIQTH.GaussLemmaHomogeneity
open QIQTH.PullbackMetric
open Finset Topology

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### M2a — the MVT constancy helper: a function continuous on `[0,1]` with zero interior derivative
    is constant.  Uses Lagrange's mean value theorem (`exists_hasDerivAt_eq_slope`), which needs the
    derivative ONLY on the OPEN interior — NO endpoint derivative data.  ⚠ NOT a₁ = R/6. -/
theorem const_of_ioo_deriv_zero (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f 0 x) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, f s = f 0 := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0]
  · have hIcc : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc le_rfl hs.2
    have hIoo : Set.Ioo (0 : ℝ) s ⊆ Set.Ioo (0 : ℝ) 1 := Set.Ioo_subset_Ioo le_rfl hs.2
    obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) h0
      (hcont.mono hIcc) (fun x hx => hderiv x (hIoo hx))
    have hs0 : s - 0 ≠ 0 := by
      rw [sub_zero]; exact ne_of_gt h0
    rw [eq_div_iff hs0, zero_mul] at hslope
    linarith [hslope]

/-! ### M2b — the linear-growth closure: `E(1) = E(0) + W(0)` from `Icc`-continuity of `E, W`, plus
    `E' = W` and `W' = 0` on the OPEN interior.  Two MVT constancy invocations.  ⚠ NOT a₁ = R/6. -/
theorem linear_of_interior (E W : ℝ → ℝ)
    (hEcont : ContinuousOn E (Set.Icc (0 : ℝ) 1))
    (hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1))
    (hE : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt E (W s) s)
    (hW : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt W 0 s) :
    E 1 = E 0 + W 0 := by
  have hWconst : ∀ s ∈ Set.Icc (0 : ℝ) 1, W s = W 0 :=
    const_of_ioo_deriv_zero W hWcont hW
  have hHcont : ContinuousOn (fun r => E r - r * W 0) (Set.Icc (0 : ℝ) 1) :=
    hEcont.sub (continuousOn_id.mul continuousOn_const)
  have hHderiv : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun r => E r - r * W 0) 0 s := by
    intro s hs
    have hd := (hE s hs).sub ((hasDerivAt_id s).mul_const (W 0))
    rw [hWconst s (Set.Ioo_subset_Icc_self hs), show W 0 - 1 * W 0 = 0 from by ring] at hd
    exact hd
  have hconst := const_of_ioo_deriv_zero (fun r => E r - r * W 0) hHcont hHderiv 1
    (Set.right_mem_Icc.mpr (by norm_num))
  simp only [zero_mul, sub_zero, one_mul] at hconst
  linarith [hconst]

/-! ### M1 — the interior product rule for the covariant field `∇J = Jp + Γ(γ)·γ̇·J`.

    Along a geodesic phase-curve `Y` of a `C^∞`-Christoffel metric (`hYd : HasDerivAt Y (geodesicField
    (Y s)) s`), given the interior first-order flow data `J' = Jp` (`hJc`) and `Jp' = −jacobiOperator`
    (`hJpc`), the covariant field `s ↦ Jp s a + ∑_{c,d} Γ^a_{cd}(γ s)·γ̇(s)^c·J(s)^d` has the exact
    product-rule derivative demanded by `jacobi_covariant_ode`'s `hcJp` binder (the `∂(Γ∘γ)`, geodesic
    acceleration `γ̈ = −Γ(γ̇,γ̇)`, and `J'` atoms).  This is the one new computation of the closure route;
    everything else wires banked pieces.  ⚠ NOT a₁ = R/6. -/
theorem covariant_field_hasDerivAt
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Y : ℝ → Point n × Point n) (J Jp : ℝ → Point n) {s : ℝ}
    (hYd : HasDerivAt Y (geodesicField g gi (Y s)) s)
    (hJc : ∀ a, HasDerivAt (fun r => J r a) (Jp s a) s)
    (hJpc : ∀ a, HasDerivAt (fun r => Jp r a)
        (-jacobiOperator g gi (Y s).1 (Y s).2 (J s) (Jp s) a) s)
    (a : Fin n) :
    HasDerivAt
      (fun r => Jp r a + ∑ c, ∑ d, christoffel g gi a c d (Y r).1 * (Y r).2 c * J r d)
      (-jacobiOperator g gi (Y s).1 (Y s).2 (J s) (Jp s) a
        + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l (Y s).1 * (Y s).2 l)
              * (Y s).2 c * J s d
          + christoffel g gi a c d (Y s).1
              * (-∑ e, ∑ f, christoffel g gi c e f (Y s).1 * (Y s).2 e * (Y s).2 f) * J s d
          + christoffel g gi a c d (Y s).1 * (Y s).2 c * Jp s d)) s := by
  -- position derivative `(Y·).1' = γ̇` (project `hYd` onto the first factor).
  have hx : HasDerivAt (fun r => (Y r).1) ((Y s).2) s := by
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt s hYd
    simpa [geodesicField] using h
  -- velocity-component derivative `γ̇^c ' = γ̈^c = (geodesicField (Y s)).2 c`.
  have hvc : ∀ c, HasDerivAt (fun r => (Y r).2 c) ((geodesicField g gi (Y s)).2 c) s := by
    intro c
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt s hYd
    have hcp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) c).hasFDerivAt.comp_hasDerivAt s h
    simpa using hcp
  -- per-summand triple-product derivative of the connection term `Γ(γ)·γ̇^c·J^d`.
  have hsm : ∀ c d, HasDerivAt
      (fun r => christoffel g gi a c d (Y r).1 * (Y r).2 c * J r d)
      ((∑ l, pd (fun z => christoffel g gi a c d z) l (Y s).1 * (Y s).2 l) * (Y s).2 c * J s d
        + christoffel g gi a c d (Y s).1
            * (-∑ e, ∑ f, christoffel g gi c e f (Y s).1 * (Y s).2 e * (Y s).2 f) * J s d
        + christoffel g gi a c d (Y s).1 * (Y s).2 c * Jp s d) s := by
    intro c d
    have hA := QIQTH.ExpMap.hasDerivAt_comp_curve (fun z => christoffel g gi a c d z)
      (fun u => (Y u).1) ((Y s).2) s (hC a c d) hx
    have hraw := (hA.mul (hvc c)).mul (hJc d)
    convert hraw using 1
    simp only [geodesicField, Pi.mul_apply]
    ring
  -- sum over `(c,d)` of the connection derivatives, plus the `Jp' = −jacobiOperator` atom.
  have hSum : HasDerivAt
      (fun r => ∑ c, ∑ d, christoffel g gi a c d (Y r).1 * (Y r).2 c * J r d)
      (∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l (Y s).1 * (Y s).2 l)
            * (Y s).2 c * J s d
        + christoffel g gi a c d (Y s).1
            * (-∑ e, ∑ f, christoffel g gi c e f (Y s).1 * (Y s).2 e * (Y s).2 f) * J s d
        + christoffel g gi a c d (Y s).1 * (Y s).2 c * Jp s d)) s := by
    apply HasDerivAt.fun_sum
    intro c _
    apply HasDerivAt.fun_sum
    intro d _
    exact hsm c d
  exact (hJpc a).add hSum

/-! ### M1+M2 — the assembled per-point first-variation Gauss identity for the concrete flow. -/

/-- **`gauss_interior_identity`.**  The per-point first-variation Gauss identity
    `∑ g_{exp_p v}(D exp_p(v)·w, γ̇(1)) = g_p(w, v)` (in components), derived DIRECTLY from the concrete
    geodesic-variation flow using ONLY its interior (`Ioo 0 1`) first-order derivative system and its
    `Icc 0 1`-continuity — the interior-MVT closure.  No `Ioo(-2,2)` window carry, no abstract
    differentiation hypothesis: `hJd`/`hcJd`/`hcJp` of the banked assembly are all discharged here for
    the actual flow (`covariant_field_hasDerivAt` supplies the covariant product rule), and the
    linear-growth step uses the mean value theorem (`linear_of_interior`).  ⚠ NOT a₁ = R/6. -/
theorem gauss_interior_identity
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p v w : Point n) (hv : ‖v‖ < expRho g gi hC p) :
    (∑ a, ∑ b, g (expMap g gi hC p v) a b
        * (fderiv ℝ (expMap g gi hC p) v) w a * (expTube g gi hC p v 1).2 b)
      = ∑ a, ∑ b, g p a b * w a * v b := by
  classical
  obtain ⟨Φ, hΦ0, hFD, hvar⟩ := expDiff_flow_isGeodesicVariation g gi hC p v hv
  obtain ⟨hY0, hYd, -⟩ := expTube_spec g gi hC p v hv.le
  have hgd : ∀ a b, Differentiable ℝ (fun y => g y a b) := fun a b => (hg a b).differentiable (by simp)
  -- interval inclusions.
  have hIcc_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hIoo_sub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the concrete flow-derivative Jacobi field.
  set J : ℝ → Point n := fun s => (Φ s ((0 : Point n), w)).1 with hJdef
  set Jp : ℝ → Point n := fun s => (Φ s ((0 : Point n), w)).2 with hJpdef
  -- initial data.
  have hJ0 : J 0 = 0 := by show (Φ 0 ((0 : Point n), w)).1 = 0; rw [hΦ0]; rfl
  have hJp0 : Jp 0 = w := by show (Φ 0 ((0 : Point n), w)).2 = w; rw [hΦ0]; rfl
  -- endpoint identification `J 1 = D exp_p(v)·w`.
  have hJ1 : ∀ a, J 1 a = (fderiv ℝ (expMap g gi hC p) v) w a := by
    intro a
    have heq : (Φ 1 ((0 : Point n), w)).1 = (fderiv ℝ (expMap g gi hC p) v) w := by
      rw [hFD.fderiv]
      simp only [ContinuousLinearMap.comp_apply, expJetIota_apply, expJetPi_apply]
    show (Φ 1 ((0 : Point n), w)).1 a = (fderiv ℝ (expMap g gi hC p) v) w a
    rw [heq]
  -- interior first-order system `J' = Jp`.
  have hJd : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ a, HasDerivAt (fun r => J r a) (Jp s a) s := by
    intro s hs a
    have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hwithin := hvar ((0 : Point n), w) s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hVJ : HasDerivAt (fun r => Φ r ((0 : Point n), w))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))) s :=
      hwithin.hasDerivAt hnhds
    have hval : fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))
        = ((Φ s ((0 : Point n), w)).2,
           -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2) :=
      geodesicField_fderiv_eq_jacobiOperator g gi hC (expTube g gi hC p v s).1
        (expTube g gi hC p v s).2 (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2
    rw [hval] at hVJ
    have hfst : HasDerivAt (fun r => (Φ r ((0 : Point n), w)).1) (Φ s ((0 : Point n), w)).2 s :=
      ((ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt).comp_hasDerivAt s hVJ
    exact ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt s hfst
  -- interior first-order system `Jp' = −jacobiOperator`.
  have hJpd : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ a, HasDerivAt (fun r => Jp r a)
      (-jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
          (J s) (Jp s) a) s := by
    intro s hs a
    have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hwithin := hvar ((0 : Point n), w) s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hVJ : HasDerivAt (fun r => Φ r ((0 : Point n), w))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))) s :=
      hwithin.hasDerivAt hnhds
    have hval : fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s) (Φ s ((0 : Point n), w))
        = ((Φ s ((0 : Point n), w)).2,
           -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2) :=
      geodesicField_fderiv_eq_jacobiOperator g gi hC (expTube g gi hC p v s).1
        (expTube g gi hC p v s).2 (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2
    rw [hval] at hVJ
    have hsnd : HasDerivAt (fun r => (Φ r ((0 : Point n), w)).2)
        (-jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
            (Φ s ((0 : Point n), w)).1 (Φ s ((0 : Point n), w)).2) s :=
      ((ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt).comp_hasDerivAt s hVJ
    exact ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt s hsnd
  -- `Icc 0 1`-continuity of the flow field and the geodesic tube.
  have hΦcont : ContinuousOn (fun s => Φ s ((0 : Point n), w)) (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hvar ((0 : Point n), w) t ht).continuousWithinAt
  have hJcont : ContinuousOn J (Set.Icc (0 : ℝ) 1) := continuous_fst.comp_continuousOn hΦcont
  have hJpcont : ContinuousOn Jp (Set.Icc (0 : ℝ) 1) := continuous_snd.comp_continuousOn hΦcont
  have hYcont : ContinuousOn (expTube g gi hC p v) (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hYd t (hIcc_sub ht)).continuousAt.continuousWithinAt
  have hY1cont : ContinuousOn (fun s => (expTube g gi hC p v s).1) (Set.Icc (0 : ℝ) 1) :=
    continuous_fst.comp_continuousOn hYcont
  have hY2cont : ContinuousOn (fun s => (expTube g gi hC p v s).2) (Set.Icc (0 : ℝ) 1) :=
    continuous_snd.comp_continuousOn hYcont
  -- the transverse pairing `E` and covariant pairing `W`.
  set E : ℝ → ℝ := fun s => ∑ a, ∑ b,
      g (expTube g gi hC p v s).1 a b * J s a * (expTube g gi hC p v s).2 b with hEdef
  set W : ℝ → ℝ := fun s => ∑ a, ∑ b, g (expTube g gi hC p v s).1 a b
      * (Jp s a + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v s).1
            * (expTube g gi hC p v s).2 c * J s d)
      * (expTube g gi hC p v s).2 b with hWdef
  -- STEP (1): `E' = W` on the interior.
  have hE : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt E (W s) s := by
    intro s hs
    have h := transverse_pairing_hasDerivAt g gi hsymm hinv hgd (expTube g gi hC p v) J (Jp s)
      (hYd s (hIoo_sub hs)) (hJd s hs)
    simpa only [hEdef, hWdef] using h
  -- STEP (1): `W' = 0` on the interior (curvature-kill via Jacobi + first-pair antisymmetry).
  have hW : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt W 0 s := by
    intro s hs
    have hYds : HasDerivAt (expTube g gi hC p v)
        (geodesicField g gi (expTube g gi hC p v s)) s := hYd s (hIoo_sub hs)
    have hcJd : ∀ a, HasDerivAt
        (fun r => Jp r a + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v r).1
            * (expTube g gi hC p v r).2 c * J r d)
        (-jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2 (J s) (Jp s) a
          + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l (expTube g gi hC p v s).1
                    * (expTube g gi hC p v s).2 l) * (expTube g gi hC p v s).2 c * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (-∑ e, ∑ f, christoffel g gi c e f (expTube g gi hC p v s).1
                      * (expTube g gi hC p v s).2 e * (expTube g gi hC p v s).2 f) * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (expTube g gi hC p v s).2 c * Jp s d)) s :=
      fun a => covariant_field_hasDerivAt g gi hC (expTube g gi hC p v) J Jp hYds
        (fun a => hJd s hs a) (fun a => hJpd s hs a) a
    have hJac := jacobi_covariant_ode g gi hsymm (expTube g gi hC p v s).1
      (expTube g gi hC p v s).2 (J s) (Jp s)
      (fun a => -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
        (J s) (Jp s) a) (fun _ => rfl)
      (fun a => Jp s a + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v s).1
        * (expTube g gi hC p v s).2 c * J s d)
      (fun a => -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2 (J s) (Jp s) a
          + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l (expTube g gi hC p v s).1
                    * (expTube g gi hC p v s).2 l) * (expTube g gi hC p v s).2 c * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (-∑ e, ∑ f, christoffel g gi c e f (expTube g gi hC p v s).1
                      * (expTube g gi hC p v s).2 e * (expTube g gi hC p v s).2 f) * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (expTube g gi hC p v s).2 c * Jp s d))
      (fun _ => rfl) (fun _ => rfl)
    have hvanish := hvanish_from_antisym g gi hsymm hg hC (expTube g gi hC p v s).1 hinv
      (expTube g gi hC p v s).2 (J s)
      (fun a => Jp s a + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v s).1
        * (expTube g gi hC p v s).2 c * J s d)
      (fun a => -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2 (J s) (Jp s) a
          + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l (expTube g gi hC p v s).1
                    * (expTube g gi hC p v s).2 l) * (expTube g gi hC p v s).2 c * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (-∑ e, ∑ f, christoffel g gi c e f (expTube g gi hC p v s).1
                      * (expTube g gi hC p v s).2 e * (expTube g gi hC p v s).2 f) * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (expTube g gi hC p v s).2 c * Jp s d))
      hJac
    have hcov := covariant_pairing_hasDerivAt_zero g gi hsymm hinv hgd (expTube g gi hC p v)
      (fun r => fun a => Jp r a + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v r).1
          * (expTube g gi hC p v r).2 c * J r d)
      (fun a => -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2 (J s) (Jp s) a
          + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l (expTube g gi hC p v s).1
                    * (expTube g gi hC p v s).2 l) * (expTube g gi hC p v s).2 c * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (-∑ e, ∑ f, christoffel g gi c e f (expTube g gi hC p v s).1
                      * (expTube g gi hC p v s).2 e * (expTube g gi hC p v s).2 f) * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (expTube g gi hC p v s).2 c * Jp s d))
      hYds hcJd hvanish
    simpa only [hWdef] using hcov
  -- STEP (2): `Icc`-continuity of `E` and `W`.
  have hEcont : ContinuousOn E (Set.Icc (0 : ℝ) 1) := by
    rw [hEdef]
    refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
    exact ((((hg a b).continuous).comp_continuousOn hY1cont).mul
      ((continuous_apply a).comp_continuousOn hJcont)).mul
      ((continuous_apply b).comp_continuousOn hY2cont)
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := by
    rw [hWdef]
    refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
    refine (((((hg a b).continuous).comp_continuousOn hY1cont).mul ?_).mul
      ((continuous_apply b).comp_continuousOn hY2cont))
    refine ((continuous_apply a).comp_continuousOn hJpcont).add
      (continuousOn_finsetSum _ (fun c _ => continuousOn_finsetSum _ (fun d _ => ?_)))
    exact ((((hC a c d).continuous).comp_continuousOn hY1cont).mul
      ((continuous_apply c).comp_continuousOn hY2cont)).mul
      ((continuous_apply d).comp_continuousOn hJcont)
  -- STEP (3): the MVT linear closure `E 1 = E 0 + W 0`.
  have hlin := linear_of_interior E W hEcont hWcont hE hW
  -- initial conditions.
  have hE0 : E 0 = 0 := by
    simp only [hEdef]
    rw [hY0]
    simp [hJ0]
  have hW0 : W 0 = ∑ a, ∑ b, g p a b * w a * v b := by
    simp only [hWdef]
    rw [hY0]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [hJ0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hJp0]
  -- the endpoint value `E 1` is the target LHS after the exp-differential identification.
  have hE1 : E 1 = ∑ a, ∑ b, g (expMap g gi hC p v) a b * J 1 a * (expTube g gi hC p v 1).2 b := by
    simp only [hEdef, expMap]
  have hLHS : (∑ a, ∑ b, g (expMap g gi hC p v) a b
        * (fderiv ℝ (expMap g gi hC p) v) w a * (expTube g gi hC p v 1).2 b) = E 1 := by
    rw [hE1]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hJ1 a]))
  rw [hLHS, hlin, hE0, hW0, zero_add]

/-! ### M3 — the ball-family of per-point Gauss identities and the discharged germ. -/

/-- **M3 — `hgball_concrete`.**  The per-`v`, per-column (`w = eᵢ`) first-variation Gauss identity for
    every `v` in the tube ball, in the EXACT shape consumed by `GaussLemmaFlowData.hGauss_pullback`'s
    `hgball` hypothesis.  Each instance is `gauss_interior_identity` at `w = Pi.single i 1`.
    ⚠ NOT a₁ = R/6. -/
theorem hgball_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) :
    ∀ v : Point n, ‖v‖ < expRho g gi hC p → ∀ i,
      (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b :=
  fun v hv i => gauss_interior_identity g gi hC hsymm hinv hg p v (Pi.single i 1) hv

/-- **M3 — `hGauss_pullback_concrete`.**  The germ shape of the Gauss lemma for the exp-pullback metric,
    with the per-point first-variation Gauss carry DISCHARGED (fed by `hgball_concrete`):
      `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j · x^j) =ᶠ[𝓝 0] (fun x => x^i)`.
    Surviving hypotheses: the metric geometry `hsymm/hinv/hg` and the base gauge `g_p = I` (`hgauge`) —
    all satisfiable geometry data.  The remaining pullback-route residues (the C∞-vs-C⁴ smoothness
    binder, and the derivable `∂g̃(0)=0` / inverse-positivity legs) are recorded in
    `GaussLemmaFlowData`'s F4 verdict.  ⚠ NOT a₁ = R/6. -/
theorem hGauss_pullback_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) (hgauge : ∀ a b, g p a b = if a = b then 1 else 0) :
    ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => x i) :=
  QIQTH.GaussLemmaFlowData.hGauss_pullback g gi hC p hgauge
    (hgball_concrete g gi hC hsymm hinv hg p)

end QIQTH.GaussInteriorMVT

section AxiomChecks
open QIQTH.GaussInteriorMVT
#print axioms const_of_ioo_deriv_zero
#print axioms linear_of_interior
#print axioms covariant_field_hasDerivAt
#print axioms gauss_interior_identity
#print axioms hgball_concrete
#print axioms hGauss_pullback_concrete
end AxiomChecks
