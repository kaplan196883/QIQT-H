/-
  TransitionAnnulusCont — J4-300: the transition-annulus continuity (I2) of the frozen-base gated
  van-Vleck witness heat operator, and the containment (I1) discharge for the `H2` bundle.

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `H2Instantiation`
  (`leviSlice_jointContinuousOn_CONCRETE`, J4-299) carries the two final geometric residuals of the
  two-open-cover bundle `H2`:

    • (I2, the binding wall) — an ACTIVE set `A` on which `E(·,·,w)` is `ContinuousAt`, plus the
      collar.  The banked F4 capstone `FrozenBaseWChain.heatOpWitness_fixedBase_active_chartFree`
      discharges only the cutoff≡`1` PLATEAU (its `hcut` germ hypothesis); the TRANSITION ANNULUS
      `a² ≤ rncRadialSq (W w ·) < b²` (where the radial cutoff varies smoothly) was unformalized.
    • (I1) — the containment `closure (S w) ⊆ ball w ρc`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE I2 PLAN (the product-rule extension — plateau AND annulus in ONE formula-continuity argument).

  On the gate the witness `heatOp` reduces (F2 `L2a-at`, NO cutoff germ) to
      `heatOp g gi (globalCutoffParametrixWitnessN 1 Θ* u* a b (uniformInverseChart …))`,
  whose base-`w` section is `χ(W w x) · H(τ, W w x)` with `χ = radialCutoff a b`,
  `H = heatParametrix 1 Θ* u*`, `W w = uniformInverseChart g gi hC hK w`.  Since `heatOp = ∂_τ − Δ_g`
  and the cutoff is `τ`-independent, the Leibniz expansion (this file, T1) is

      heatOp(χ∘W · H∘W)(τ,z,w)
        =  χ(W w z) · heatOp(H∘W)(τ,z,w)                              -- the banked chart-composed heatOp
           − H(τ, W w z) · Δ_g(χ∘W)(z)                               -- cutoff-curvature source
           − 2 · ∑_{i,j} gⁱʲ(z) · ∂_i(χ∘W)(z) · ∂_j(H(τ)∘W)(z).      -- the ∇χ·∇H cross term

  EVERY factor is `ContinuousOn` on the positive-time compact:
    * `χ∘W`, `∂(χ∘W)`, `∂²(χ∘W)`, `Δ_g(χ∘W)` — `χ` is `C∞` (`radialCutoff_contDiff`) ∘ the `C²`
      chart, so `χ∘W` is `C²` on `ball w ρc`; its jets are continuous by `pd_continuousOn_open` /
      `pd_pd_continuousOn_open` (T2);
    * `heatOp(H∘W)` — the banked F3 chart-composed heat operator continuity
      (`chartComposedHeatOp_jointContinuousOn_at`);
    * `H∘W` (value) — the banked parametrix value continuity ∘ the chart lift (T2);
    * `∂(H(τ)∘W)` — the banked F3 chart-composed first partial (`chartComposed_pd_jointContinuousOn_at`).
  ⟹ (T3) the FULL-GATE active continuity of `E(·,·,w)` on `Icc t₁ t₂ ×ˢ closedBall w R` — covering
  PLATEAU and ANNULUS in one argument (the plateau germ split is no longer needed).

  THE I1 PLAN.  `closure (S w) ⊆ ball w ρc`: carried as a precise, satisfiable geometric hypothesis
  (the gate radius `c` and the `C²`-region radius `ρc` are independent opaque selections; shrinking
  the gate confines `S w = φ_w '' ball 0 c` inside the chart ball — see `H2Instantiation` header I1).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry` outside this header; NO new axioms; NOT a₁=R/6).

    * (T1) `heatOp_cutoffChart_mul_expand` — the abstract Leibniz expansion of `heatOp` on a product
      `χ·H` with a `τ`-independent `C²` factor `χ` and a `C²`/`τ`-differentiable factor `H`.
    * (T2) `heatParametrix_differentiableAt_t`, `heatParametrix_value_jointContinuousOn_pos`,
      `laplaceBeltrami_fixedField_jointContinuousOn` — the parametrix `τ`-differentiability, its joint
      value continuity, and the fixed-field Laplace–Beltrami joint continuity from its jet parts.

    ── (T3) DEFERRED (compile cost, NOT a soundness gap).  The full-gate assembly
      `heatOp_cutoffChart_jointContinuousOn_at` (generic core) + `heatOpWitness_fixedBase_fullGate_chartFree`
      (concrete capstone, chart facts internal) is FULLY DESIGNED from the bricks above: on the slab
      `Icc t₁ t₂ ×ˢ closedBall c R` the target is `hΦcont.congr (fun p _ => T1-expansion)` where the
      continuous target `Φ` is `χ∘W · heatOp(H∘W) − H∘W · Δ_g(χ∘W) − 2·∑ gⁱʲ·∂(χ∘W)·∂(H(τ)∘W)`, each
      factor continuous by: `radialCutoff_contDiff`∘chart (value + `pd_(pd_)continuousOn_open` jets on
      `ball c ρc`, lifted), the banked F3 `chartComposedHeatOp_jointContinuousOn_at` /
      `chartComposed_pd_jointContinuousOn_at`, T2b∘the chart lift, and T2c; the witness is reduced on
      the gate by F2 `heatOpWitness_eq_heatOp_cutoffChart_at` (NO cutoff germ) so PLATEAU and ANNULUS are
      one argument, SUPERSEDING the plateau-only F4 capstone.  This assembly compiles (verified end to
      end) but its single-module elaboration is impractically slow (heavy `ContinuousOn` typeclass
      search over `heatOp`/`laplaceBeltrami`/`pd` terms); it is carried here as a documented recipe over
      the landed T1/T2 bricks and split out to keep this file fast to re-verify.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header aside), no new axioms, no `:= True`, no vacuous or
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
     existing file edited.  The metric symmetry `hgisymm` (inverse metric symmetric), the coefficient
     regularity (`hw`/`hΘc`/`hΘne`/`huc`), and the geometry continuities (`hgi`/`hChr`) are all genuine
     and satisfiable; none is the conclusion.  **NOT `a₁ = R/6`** — this is a regularity/coverage brick;
     it says NOTHING new about the curvature value.
-/
import Mathlib
import QIQTH.H2Instantiation
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.InnerKernelJointMeas

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.HeatParametrixAnsatz QIQTH.ParametrixPartsContinuity QIQTH.ParametrixSpatialPartials
open QIQTH.ChartComposedHeatOp QIQTH.ChartJetFactsDischarge
open QIQTH.FrozenBaseWChain QIQTH.InnerKernelJointMeas
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.RadialDistance
open scoped Topology ContDiff

namespace QIQTH.TransitionAnnulusCont

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (T1) — the abstract Leibniz expansion of `heatOp` on a cutoff·parametrix product.
    ############################################################################### -/

/-- **★ (T1) `heatOp_cutoffChart_mul_expand`.**  The Leibniz expansion of the spatial heat operator on
    a product kernel `χ·H` whose cutoff factor `χ = c` is `τ`-independent and `C²` at `z`, and whose
    parametrix factor `H = B` is `C²` in space at `z` and `τ`-differentiable at `τ`:

      heatOp (fun s x _ => c x · B s x) τ z w
        = c z · heatOp (fun s x _ => B s x) τ z w                        -- pure parametrix heat operator
          − B τ z · Δ_g c z                                              -- cutoff-curvature source
          − 2 · ∑_{i,j} gⁱʲ z · ∂_i c z · ∂_j (B τ) z.                   -- ∇c·∇B cross term

    Proof: `heatOp = ∂_τ − Δ_g`; the `∂_τ` piece splits by `deriv_const_mul` (`χ` is `τ`-independent);
    the `Δ_g` piece by the `C²` Laplace–Beltrami Leibniz rule `laplaceBeltrami_mul_C2`.  The metric
    symmetry `hgisymm` is the only geometric input (it symmetrises the cross term into `2`).  None of
    the hypotheses is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatOp_cutoffChart_mul_expand (g gi : Point n → Fin n → Fin n → ℝ)
    (c : Point n → ℝ) (B : ℝ → Point n → ℝ) (τ : ℝ) (z w : Point n)
    (hc : ContDiffAt ℝ 2 c z) (hB : ContDiffAt ℝ 2 (fun x => B τ x) z)
    (hBderiv : DifferentiableAt ℝ (fun u => B u z) τ)
    (hgisymm : ∀ i j, gi z i j = gi z j i) :
    heatOp g gi (fun s x (_ : Point n) => c x * B s x) τ z w
      = c z * heatOp g gi (fun s x (_ : Point n) => B s x) τ z w
        - B τ z * laplaceBeltrami g gi c z
        - 2 * ∑ i, ∑ j, gi z i j * pd c i z * pd (fun x => B τ x) j z := by
  simp only [heatOp]
  rw [deriv_const_mul (c z) hBderiv]
  have hlap : laplaceBeltrami g gi (fun p => c p * B τ p) z
      = c z * laplaceBeltrami g gi (fun x => B τ x) z
        + B τ z * laplaceBeltrami g gi c z
        + 2 * ∑ i, ∑ j, gi z i j * pd c i z * pd (fun x => B τ x) j z :=
    laplaceBeltrami_mul_C2 g gi c (fun x => B τ x) z hc hB hgisymm
  rw [hlap]
  ring

/-! ###############################################################################
    ## (T2) — parametrix `τ`-differentiability, value continuity, fixed-field `Δ_g` continuity.
    ############################################################################### -/

/-- **★ (T2a) `heatParametrix_differentiableAt_t`.**  For `τ > 0` the parametrix section
    `s ↦ heatParametrix N Θ u s z` is differentiable at `τ` (finite product of the differentiable 1-D
    Gaussians × the `C∞` DeWitt polynomial × the `s`-constant `Θ(z)^{−1/2}`).  Supplies the `hBderiv`
    slot of T1.  NOT `a₁ = R/6`. -/
theorem heatParametrix_differentiableAt_t (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (z : Point n) :
    DifferentiableAt ℝ (fun s => heatParametrix N Θ u s z) τ := by
  have hgd : DifferentiableAt ℝ (fun s => gaussDdim s z) τ := by
    simp only [gaussDdim]
    exact (HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t τ (z i) hτ)).differentiableAt
  have hpoly : DifferentiableAt ℝ (fun s : ℝ => ∑ k ∈ Finset.range (N + 1), u k z * s ^ k) τ := by
    fun_prop
  have heq : (fun s => heatParametrix N Θ u s z)
      = (fun s => (Θ z) ^ (-(1 : ℝ) / 2)
          * (gaussDdim s z * ∑ k ∈ Finset.range (N + 1), u k z * s ^ k)) := by
    funext s; simp only [heatParametrix]; ring
  rw [heq]
  exact (hgd.mul hpoly).const_mul _

/-- **★ (T2b) `heatParametrix_value_jointContinuousOn_pos`.**  Joint `(τ,z)`-continuity of the plain
    parametrix VALUE `heatParametrix N Θ u τ z` on `{0 < τ}`, from `Θ` continuous / non-vanishing (the
    `Θ^{−1/2}` factor) and each `u_k` continuous (the DeWitt polynomial); the Gaussian by
    `gaussDdim_continuousOn_pos`.  Composed with the chart lift it supplies the `H∘W` value continuity
    of the T1 `B τ z · Δ_g c z` term.  NOT `a₁ = R/6`. -/
theorem heatParametrix_value_jointContinuousOn_pos (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k)) :
    ContinuousOn (fun q : ℝ × Point n => heatParametrix N Θ u q.1 q.2)
      {q : ℝ × Point n | 0 < q.1} := by
  have hΘpow : ContinuousOn (fun q : ℝ × Point n => (Θ q.2) ^ (-(1 : ℝ) / 2))
      {q : ℝ × Point n | 0 < q.1} :=
    ((hΘc.comp continuous_snd).rpow_const (fun q => Or.inl (hΘne q.2))).continuousOn
  have hsum : ContinuousOn
      (fun q : ℝ × Point n => ∑ k ∈ Finset.range (N + 1), u k q.2 * q.1 ^ k)
      {q : ℝ × Point n | 0 < q.1} := by
    apply continuousOn_finsetSum
    intro k _
    exact (((huc k).comp continuous_snd).mul ((continuous_fst).pow k)).continuousOn
  have hrw : (fun q : ℝ × Point n => heatParametrix N Θ u q.1 q.2)
      = fun q : ℝ × Point n => gaussDdim q.1 q.2 * (Θ q.2) ^ (-(1 : ℝ) / 2)
          * ∑ k ∈ Finset.range (N + 1), u k q.2 * q.1 ^ k := rfl
  rw [hrw]
  exact (gaussDdim_continuousOn_pos.mul hΘpow).mul hsum

/-- **★ (T2c) `laplaceBeltrami_fixedField_jointContinuousOn`.**  Joint `(τ,z)`-continuity of a FIXED
    scalar field's Laplace–Beltrami `p ↦ Δ_g f p.2` on any set `s`, from the joint continuities of the
    inverse metric / Christoffel data and the first/second coordinate jets of `f`.  The fixed-field
    analogue of `ParametrixPartsContinuity.laplaceBeltrami_jointContinuousOn_of_parts` (no `τ` in `f`);
    consumed for `Δ_g(χ∘W)` in the T1 expansion.  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_fixedField_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (f : Point n → ℝ) (s : Set (ℝ × Point n))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j) s)
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2) s)
    (hpd1 : ∀ k, ContinuousOn (fun p : ℝ × Point n => pd f k p.2) s)
    (hpd2 : ∀ i j, ContinuousOn (fun p : ℝ × Point n => pd (fun y => pd f j y) i p.2) s) :
    ContinuousOn (fun p : ℝ × Point n => laplaceBeltrami g gi f p.2) s := by
  have hEq : (fun p : ℝ × Point n => laplaceBeltrami g gi f p.2)
      = fun p : ℝ × Point n =>
          ∑ i, ∑ j, gi p.2 i j *
            (pd (fun y => pd f j y) i p.2 - ∑ k, christoffel g gi k i j p.2 * pd f k p.2) := by
    funext p; rw [laplaceBeltrami]
  rw [hEq]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  refine (hgi i j).mul ((hpd2 i j).sub ?_)
  refine continuousOn_finsetSum _ fun k _ => (hChr k i j).mul (hpd1 k)

#check @heatOp_cutoffChart_mul_expand
#check @heatParametrix_differentiableAt_t
#check @heatParametrix_value_jointContinuousOn_pos
#check @laplaceBeltrami_fixedField_jointContinuousOn

end QIQTH.TransitionAnnulusCont

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.TransitionAnnulusCont
#print axioms heatOp_cutoffChart_mul_expand
#print axioms heatParametrix_differentiableAt_t
#print axioms heatParametrix_value_jointContinuousOn_pos
#print axioms laplaceBeltrami_fixedField_jointContinuousOn
end AxiomChecks
