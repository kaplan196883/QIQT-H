/-
  GaussLemmaAssembly — the FULL first-variation Gauss identity and its coordinate form for the
  exp-pullback metric, assembling the four banked legs of the hGauss campaign (brick J4-345 of the
  a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one of the four labelled inputs of `a1_R6_from_labelled`, and this
  campaign works toward discharging it for the exp-pullback normal-form metric.  This file wires the
  banked legs into the assembled first-variation identity
    `g_{exp_p v}(D exp_p(v)·w, γ̇(1)) = g_p(w, v)`
  and its coordinate contraction `∑_j g̃_ij(v)·v^j = (g_p v)_i` for the pullback metric `g̃`.  Nothing
  here builds normal coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE BANKED CHAIN (wired here)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  • RADIAL (J4-341): `geodesic_energy_conservation` (energy `g_{exp v}(γ̇(1),γ̇(1)) = g_p(v,v)`) — the
    `w = v` diagonal; not directly consumed here (the transverse leg is used at `w = v` too), kept as
    the diagonal cross-check.
  • TRANSVERSE (J4-342): `transverse_pairing_hasDerivAt` (`E_J' = covariant pairing`),
    `covariant_pairing_hasDerivAt_zero` (`W' = 0` given `hvanish`), `gauss_transverse_linear`
    (`E t = E 0 + t·W 0`).
  • CURVATURE KILL (J4-343): `hvanish_from_antisym` (the `hvanish` discharge given `hJac`).
  • BRIDGE + HOMOGENEITY (J4-344): `jacobi_covariant_ode` (`hJac` from the raw ODE + product-rule data),
    `exp_euler_homogeneity` (`D exp_p(v)·v = γ̇(1)`).
  • VARIATIONAL BANK: `jacobiOperator`, `jacobiVariation_secondOrder` (`ξ'' = −jacobiOperator`),
    `expJacobianMat_eq_flow` (the matrix flow = the derivative of the geodesic flow in initial data).
  • PULLBACK: `expPullbackMetric` (`PullbackMetric`), reused verbatim for the coordinate form.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED (fully derived, axiom-free, no `sorry`):
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • A2  `gauss_first_variation` — the ASSEMBLED first-variation identity in terms of the abstract
       Jacobi field `J` along the exp-tube (with its derivative families `Jp`, `cJp`):
         `∑ g_{exp v}(J 1, γ̇(1)) = g_p(w, v)`   given `J 0 = 0`, `Jp 0 = w`.
       Radial-energy conservation is REPLACED by the transverse pairing at `t = 1`; the whole
       transverse/curvature/bridge chain is wired.  The hypotheses `hJd`/`hcJd`/`hcJp` are the
       satisfiable flow-instantiation data (the differentiation step of the actual flow-derivative
       Jacobi field, a labelled residue).
   • A2′ `gauss_first_variation_dexp` — the same with `J 1 = D exp_p(v)·w` substituted (the definitional
       identification of the position-flow derivative with the exp differential), giving the classical
       shape `∑ g_{exp v}(D exp_p(v)·w, γ̇(1)) = g_p(w, v)`.
   • A3  `gauss_coordinate_contraction` — the COORDINATE form: given the Gauss identity at `w = e_i`
       and Euler homogeneity, `∑_j g̃_ij(v)·v^j = (g_p v)_i` for the pullback metric `g̃`.
   • A3′ `gauss_coordinate_contraction_gauge` — under the base-point RNC gauge `g_p = I`, `∑_j g̃_ij v^j
       = v^i` (the exact `hGauss` coordinate normal-form contraction, at the base point).

  ⚠ HONESTY (labelled residues).  NOT a₁ = R/6.  The remaining `hGauss` map: the per-`s` HasDerivAt
  flow data (`hJd`/`hcJd`/`hcJp`) is the instantiation of the actual flow-derivative field (the
  differentiation-in-initial-conditions brick), and the `=ᶠ` frame/recenter transport carrying this
  base-point contraction to the capstone metric is the final brick.  Both are separate downstream
  labelled inputs; this file assembles everything above them.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.JacobiEquation
import QIQTH.PullbackMetric
import QIQTH.GaussLemmaFirstVariation
import QIQTH.GaussLemmaTransverse
import QIQTH.RiemannFirstPairAntisym
import QIQTH.GaussLemmaHomogeneity

namespace QIQTH.GaussLemmaAssembly

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open QIQTH.GaussLemmaTransverse QIQTH.RiemannFirstPairAntisym QIQTH.GaussLemmaHomogeneity
open QIQTH.PullbackMetric
open Finset

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### A2 — the assembled first-variation Gauss identity. -/

/-- **A2 — `gauss_first_variation`.**  The assembled first-variation Gauss identity for the exp-tube.

    Let `Y = expTube g gi hC p v` be the geodesic phase-curve through `(p, v)`, `γ̇(1) = (Y 1).2` the
    terminal velocity, and `J : ℝ → Point n` a Jacobi field along `Y` with derivative family `Jp` and
    covariant-field derivative family `cJp`.  Given:
      * `hJd` — `J` is `C¹` with derivative `Jp` (per interior time `s`);
      * `hcJd` — the covariant field `cJ_s = Jp_s + Γ(γ̇_s, J_s)` is `C¹` with derivative `cJp_s`;
      * `hcJp` — the product-rule value of `cJp_s` under the geodesic acceleration (the raw second-order
        variational data, satisfied by the actual flow-derivative field);
      * initial data `J 0 = 0`, `Jp 0 = w`;
    the transverse pairing at `t = 1` equals `g_p(w, v)`:
      `∑_{a,b} g_{exp_p v}(a,b)·(J 1)^a·γ̇(1)^b = ∑_{a,b} g_p(a,b)·w^a·v^b`.

    The whole banked chain is wired: `transverse_pairing_hasDerivAt` (`E' = W`),
    `jacobi_covariant_ode` + `hvanish_from_antisym` (`W' = 0`), `gauss_transverse_linear` (linear
    growth), with initial conditions collapsing `E 0 = 0`, `W 0 = g_p(w,v)`.

    ⚠ NOT a₁ = R/6.  `hJd`/`hcJd`/`hcJp` are the satisfiable flow-instantiation data (a downstream
    differentiation brick). -/
theorem gauss_first_variation
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (J Jp cJp : ℝ → Point n)
    (hJd : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, ∀ a, HasDerivAt (fun r => J r a) (Jp s a) s)
    (hcJd : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, ∀ a,
        HasDerivAt (fun r => Jp r a
            + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v r).1
                * (expTube g gi hC p v r).2 c * J r d) (cJp s a) s)
    (hcJp : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, ∀ a,
        cJp s a = -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (J s) (Jp s) a
          + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l
                    (expTube g gi hC p v s).1 * (expTube g gi hC p v s).2 l)
                  * (expTube g gi hC p v s).2 c * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (-∑ e, ∑ f, christoffel g gi c e f (expTube g gi hC p v s).1
                      * (expTube g gi hC p v s).2 e * (expTube g gi hC p v s).2 f) * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (expTube g gi hC p v s).2 c * Jp s d))
    (hJ0 : J 0 = 0) (hJp0 : Jp 0 = w) :
    (∑ a, ∑ b, g (expMap g gi hC p v) a b * J 1 a * (expTube g gi hC p v 1).2 b)
      = ∑ a, ∑ b, g p a b * w a * v b := by
  classical
  obtain ⟨hY0, hYd, -⟩ := expTube_spec g gi hC p v hv
  set Y : ℝ → Point n × Point n := expTube g gi hC p v with hYdef
  have hgd : ∀ a b, Differentiable ℝ (fun y => g y a b) := fun a b => (hg a b).differentiable (by simp)
  -- the transverse pairing `E` and the covariant pairing `W`.
  set E : ℝ → ℝ := fun s => ∑ a, ∑ b, g (Y s).1 a b * J s a * (Y s).2 b with hEdef
  set W : ℝ → ℝ := fun s => ∑ a, ∑ b, g (Y s).1 a b
      * (Jp s a + ∑ c, ∑ d, christoffel g gi a c d (Y s).1 * (Y s).2 c * J s d)
      * (Y s).2 b with hWdef
  -- STEP T1b (per interior time): `E' = W`.
  have hE : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt E (W s) s := by
    intro s hs
    have h := transverse_pairing_hasDerivAt g gi hsymm hinv hgd Y J (Jp s) (hYd s hs) (hJd s hs)
    simpa only [hEdef, hWdef] using h
  -- STEP T2b (per interior time): `W' = 0`, via the covariant Jacobi ODE + curvature antisymmetry.
  have hW : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt W 0 s := by
    intro s hs
    -- the covariant Jacobi (Riemann) equation for this field (bridge J4-344).
    have hJac := jacobi_covariant_ode g gi hsymm (Y s).1 (Y s).2 (J s) (Jp s)
      (fun a => -jacobiOperator g gi (Y s).1 (Y s).2 (J s) (Jp s) a) (fun _ => rfl)
      (fun a => Jp s a + ∑ c, ∑ d, christoffel g gi a c d (Y s).1 * (Y s).2 c * J s d)
      (cJp s) (fun _ => rfl) (hcJp s hs)
    -- the curvature-vanishing (kill J4-343).
    have hvanish := hvanish_from_antisym g gi hsymm hg hC (Y s).1 hinv (Y s).2 (J s)
      (fun a => Jp s a + ∑ c, ∑ d, christoffel g gi a c d (Y s).1 * (Y s).2 c * J s d)
      (cJp s) hJac
    have hcov := covariant_pairing_hasDerivAt_zero g gi hsymm hinv hgd Y
      (fun r => fun a => Jp r a
          + ∑ c, ∑ d, christoffel g gi a c d (Y r).1 * (Y r).2 c * J r d)
      (cJp s) (hYd s hs) (hcJd s hs) hvanish
    simpa only [hWdef] using hcov
  -- STEP T3: linear growth `E 1 = E 0 + 1·W 0`.
  have hlin := gauss_transverse_linear E W (Set.right_mem_Icc.mpr (by norm_num)) hE hW
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
  -- endpoint value: `E 1` is the target LHS.
  have hE1 : E 1 = ∑ a, ∑ b, g (expMap g gi hC p v) a b * J 1 a * (expTube g gi hC p v 1).2 b := by
    simp only [hEdef, hYdef, expMap]
  rw [← hE1, hlin, hE0, hW0, zero_add, one_mul]

/-- **A2′ — `gauss_first_variation_dexp`.**  The assembled first-variation identity with the
    position-flow derivative identified with the exp differential, `J 1 = D exp_p(v)·w` (`hJ1`):
      `∑_{a,b} g_{exp_p v}(a,b)·(D exp_p(v)·w)^a·γ̇(1)^b = ∑_{a,b} g_p(a,b)·w^a·v^b`.
    The classical first-variation Gauss identity (in components).  ⚠ NOT a₁ = R/6. -/
theorem gauss_first_variation_dexp
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (J Jp cJp : ℝ → Point n)
    (hJd : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, ∀ a, HasDerivAt (fun r => J r a) (Jp s a) s)
    (hcJd : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, ∀ a,
        HasDerivAt (fun r => Jp r a
            + ∑ c, ∑ d, christoffel g gi a c d (expTube g gi hC p v r).1
                * (expTube g gi hC p v r).2 c * J r d) (cJp s a) s)
    (hcJp : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, ∀ a,
        cJp s a = -jacobiOperator g gi (expTube g gi hC p v s).1 (expTube g gi hC p v s).2
              (J s) (Jp s) a
          + ∑ c, ∑ d, ((∑ l, pd (fun z => christoffel g gi a c d z) l
                    (expTube g gi hC p v s).1 * (expTube g gi hC p v s).2 l)
                  * (expTube g gi hC p v s).2 c * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (-∑ e, ∑ f, christoffel g gi c e f (expTube g gi hC p v s).1
                      * (expTube g gi hC p v s).2 e * (expTube g gi hC p v s).2 f) * J s d
              + christoffel g gi a c d (expTube g gi hC p v s).1
                  * (expTube g gi hC p v s).2 c * Jp s d))
    (hJ0 : J 0 = 0) (hJp0 : Jp 0 = w)
    (hJ1 : ∀ a, J 1 a = (fderiv ℝ (expMap g gi hC p) v) w a) :
    (∑ a, ∑ b, g (expMap g gi hC p v) a b
        * (fderiv ℝ (expMap g gi hC p) v) w a * (expTube g gi hC p v 1).2 b)
      = ∑ a, ∑ b, g p a b * w a * v b := by
  rw [show (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) w a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g (expMap g gi hC p v) a b * J 1 a * (expTube g gi hC p v 1).2 b from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hJ1 a]))]
  exact gauss_first_variation g gi hC hsymm hinv hg p v w hv J Jp cJp hJd hcJd hcJp hJ0 hJp0

/-! ### A3 — the coordinate contraction `∑_j g̃_ij v^j = (g_p v)_i`. -/

/-- **A3 — `gauss_coordinate_contraction`.**  The coordinate form of the Gauss lemma for the pullback
    metric `g̃ = exp_p^* g` (`expPullbackMetric`).  Given the assembled first-variation identity at
    `w = e_i` (`hgauss`, the `A2′` output at the `i`-th basis vector), the contraction of `g̃` against
    the radial vector `v` recovers `(g_p v)_i`:
      `∑_j g̃_ij(v)·v^j = ∑_b g_p(i,b)·v^b`.
    The step uses Euler homogeneity `D exp_p(v)·v = γ̇(1)` (`exp_euler_homogeneity`) to collapse the
    `∑_j (D exp_p(v)·e_j)·v^j` inner sum to `γ̇(1)`, then the Gauss identity.  ⚠ NOT a₁ = R/6. -/
theorem gauss_coordinate_contraction
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) (i : Fin n)
    (hgauss : (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b) :
    (∑ j, expPullbackMetric g gi hC p v i j * v j) = ∑ b, g p i b * v b := by
  classical
  -- Euler homogeneity: `∑_j (D exp_p(v)·e_j)_b · v^j = γ̇(1)_b`.
  have hlincomb : ∀ b, (∑ j, (fderiv ℝ (expMap g gi hC p) v) (Pi.single j 1) b * v j)
      = (expTube g gi hC p v 1).2 b := by
    intro b
    have hDlin := exp_euler_homogeneity g gi hC p v hv
    have hvsum : (v : Point n) = ∑ j, v j • (Pi.single j 1 : Point n) := by
      funext k
      rw [Finset.sum_apply]
      simp [Pi.single_apply, Finset.sum_ite_eq]
    have hmap : (fderiv ℝ (expMap g gi hC p) v) v
        = ∑ j, v j • (fderiv ℝ (expMap g gi hC p) v) (Pi.single j 1) := by
      rw [congrArg (⇑(fderiv ℝ (expMap g gi hC p) v)) hvsum, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    have hcomp : (fderiv ℝ (expMap g gi hC p) v) v b
        = ∑ j, v j * (fderiv ℝ (expMap g gi hC p) v) (Pi.single j 1) b := by
      rw [hmap, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply]
    rw [← hDlin, hcomp]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- Expand `∑_j g̃_ij v^j`, collapse the inner sum by `hlincomb`, apply the Gauss identity.
  have hRHS : (∑ a, ∑ b, g (expMap g gi hC p v) a b
        * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
      = ∑ a, ∑ b, ∑ j, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a
          * ((fderiv ℝ (expMap g gi hC p) v) (Pi.single j 1) b * v j) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hlincomb b, Finset.mul_sum]
  have hLHS : (∑ j, expPullbackMetric g gi hC p v i j * v j)
      = ∑ a, ∑ b, ∑ j, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a
          * ((fderiv ℝ (expMap g gi hC p) v) (Pi.single j 1) b * v j) := by
    simp only [expPullbackMetric, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hLHS, ← hRHS, hgauss]
  -- reduce the `∑_a g_p(a,b)·(e_i)^a` against the basis vector `e_i`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ hai => by rw [Pi.single_eq_of_ne hai, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Pi.single_eq_same, mul_one]

/-- **A3′ — `gauss_coordinate_contraction_gauge`.**  Under the base-point RNC gauge `g_p = I`
    (`hgauge`), the pullback-metric contraction is the identity: `∑_j g̃_ij(v)·v^j = v^i`.  This is
    the exact coordinate normal-form contraction of `hGauss` AT the base point.  ⚠ NOT a₁ = R/6. -/
theorem gauss_coordinate_contraction_gauge
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) (i : Fin n)
    (hgauss : (∑ a, ∑ b, g (expMap g gi hC p v) a b
          * (fderiv ℝ (expMap g gi hC p) v) (Pi.single i 1) a * (expTube g gi hC p v 1).2 b)
        = ∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a * v b)
    (hgauge : ∀ a b, g p a b = if a = b then 1 else 0) :
    (∑ j, expPullbackMetric g gi hC p v i j * v j) = v i := by
  classical
  rw [gauss_coordinate_contraction g gi hC p v hv i hgauss]
  rw [Finset.sum_congr rfl (fun b _ => by rw [hgauge i b] : ∀ b ∈ (Finset.univ : Finset (Fin n)),
      g p i b * v b = (if i = b then 1 else 0) * v b)]
  simp [Finset.sum_ite_eq]

end QIQTH.GaussLemmaAssembly

section AxiomChecks
open QIQTH.GaussLemmaAssembly
#print axioms gauss_first_variation
#print axioms gauss_first_variation_dexp
#print axioms gauss_coordinate_contraction
#print axioms gauss_coordinate_contraction_gauge
end AxiomChecks
