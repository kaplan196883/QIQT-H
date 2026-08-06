/-
  RiemannFirstPairAntisym — the GENERAL-POINT first-pair antisymmetry of the lowered Riemann
  tensor, and the discharge of the `hvanish` carry of `GaussLemmaTransverse` (brick J4-343 of the
  hGauss campaign, toward the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one labelled input of `a1_R6_from_labelled`; this campaign works
  toward discharging it.  Here we discharge the CURVATURE-ANTISYMMETRY half of the `hvanish` carry of
  `GaussLemmaTransverse.covariant_pairing_hasDerivAt_zero`, reducing that carry to the (separately
  labelled, satisfiable) Jacobi-field equation `∇∇J = −R(J,γ̇)γ̇`.  Nothing here builds normal
  coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE MATH (classical first-pair antisymmetry of the lowered Riemann tensor, in the pd-calculus)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Notation.  `Point n = Fin n → ℝ`, metric `g`, inverse `gi`, `christoffel g gi μ ν ρ x = Γ^μ_{νρ}`,
  `pd f i x = ∂ᵢ f`, sign convention `R^ρ_{σμν} = ∂_μΓ^ρ_{νσ} − ∂_νΓ^ρ_{μσ} + ΓΓ − ΓΓ` (`riemann`).
  The **lowered** Riemann tensor is `Rlow_{abcd} := ∑_ρ g_{aρ} R^ρ_{bcd}` (`riemannLower`).

  V1 (the general-point expansion, `riemannLower_expansion`).  Product rule on the two `g·∂Γ` terms
  (`g·∂Γ = ∂(g·Γ) − (∂g)·Γ`), `christoffel_lower` to turn `∑ g·Γ` into the Koszul half-sum of `∂g`,
  and metric compatibility `∂_c g_{aρ} = ∑ Γg + ∑ Γg` to expand `(∂g)·Γ`, gives the closed form
    `Rlow_{abcd} = ½(∂_c∂_b g_{ad} − ∂_c∂_a g_{bd} − ∂_d∂_b g_{ac} + ∂_d∂_a g_{bc})`
                 `+ ∑_{τρ} g_{τρ}(Γ^τ_{da}Γ^ρ_{cb} − Γ^τ_{ca}Γ^ρ_{db})`.
  (This is the general-point analog of J4-318's `riemann_at_zero`, whose proof at `0` used `Γ(0)=0` to
  drop the `ΓΓ`; here they are kept.)  The four leftover `g_{aσ}ΓΓ` terms cancel pairwise against the
  Riemann's own `ΓΓ` part — the honest bookkeeping is in the proof.

  V2 (first-pair antisymmetry, `riemannLower_first_pair_antisymm`).  `Rlow_{abcd} + Rlow_{bacd} = 0`.
  The `∂∂g` part is antisymmetric in `(a,b)` after Schwarz (`pd_comm`); the `ΓΓg` part is antisymmetric
  in `(a,b)` by the `g`-symmetry `g_{τρ}=g_{ρτ}` (relabel the contracted `τ↔ρ`).

  V3 (`hvanish_from_antisym`).  For a symmetric antisymmetric-first-pair `Rlow`, contracting the first
  pair against `u⊗u` (symmetric) kills it: `∑_{i,j} Rlow_{ijep} u^i u^j = 0` (`antisym_contract`).
  Given the Jacobi input `∇∇J = −R(J,γ̇)γ̇` (the vector Jacobi equation, `hJac`), the exact `hvanish`
  expression of `covariant_pairing_hasDerivAt_zero` reduces to that contraction and vanishes.

  DELIVERED (fully derived, axiom-free, no `sorry`):
   • `antisym_contract` — `∑ᵢⱼ Aᵢⱼuⁱuʲ = 0` for antisymmetric `A` (the antisym-against-sym argument).
   • `riemannLower` — the lowered Riemann tensor `∑_ρ g_{aρ} R^ρ_{bcd}`.
   • `riemannLower_expansion` (V1) — the general-point `∂∂g + ΓΓg` closed form.
   • `riemannLower_first_pair_antisymm` (V2) — `Rlow_{abcd} + Rlow_{bacd} = 0`.
   • `hvanish_from_antisym` (V3) — the exact `hvanish` shape discharged from V2 + the Jacobi input.

  ⚠ NOT a₁ = R/6; the residual `hvanish` carry is now the Jacobi-field ODE (a separate labelled input).
-/
import Mathlib
import QIQTH.Curvature

namespace QIQTH.RiemannFirstPairAntisym

open QIQTH.Curvature
open Finset

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### The antisymmetric-against-symmetric contraction (feeds V3). -/

/-- **`antisym_contract`.**  A rank-2 array `A` that is antisymmetric (`A i j = −A j i`) contracted
    against the symmetric tensor `u ⊗ u` vanishes: `∑_{i,j} A_{ij} u^i u^j = 0`.  The standard
    `S = −S ⟹ S = 0` argument (swap the two summation variables).  ⚠ NOT a₁ = R/6. -/
theorem antisym_contract (A : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hA : ∀ i j, A i j = - A j i) :
    (∑ i, ∑ j, A i j * u i * u j) = 0 := by
  have hswap : (∑ i, ∑ j, A i j * u i * u j) = ∑ i, ∑ j, A j i * u i * u j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum0 : (∑ i, ∑ j, A i j * u i * u j) + (∑ i, ∑ j, A j i * u i * u j) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hA i j]; ring
  linarith [hsum0, hswap]

/-! ### The lowered Riemann tensor. -/

/-- **Lowered Riemann tensor** `Rlow_{abcd} = ∑_ρ g_{aρ} R^ρ_{bcd}` (lower the upper index with `g`). -/
noncomputable def riemannLower (g gi : Point n → Fin n → Fin n → ℝ)
    (a b c d : Fin n) (x : Point n) : ℝ :=
  ∑ ρ, g x a ρ * riemann g gi ρ b c d x

/-! ### The metric-compatibility `∂g` identity at a point (the `hmc` used throughout). -/

/-- The metric-compatibility identity `∂_e g_{pq} = ∑σ Γ^σ_{ep} g_{σq} + ∑σ Γ^σ_{eq} g_{pσ}` at `x`,
    extracted from `metric_compat` (`∇g = 0`). -/
theorem pd_g_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (e p q : Fin n) :
    pd (fun y => g y p q) e x
      = (∑ σ, christoffel g gi σ e p x * g x σ q)
        + (∑ σ, christoffel g gi σ e q x * g x p σ) := by
  have h := metric_compat g gi hsymm x hinv e p q
  simp only [covDeriv02] at h
  linarith

/-! ### V1 machinery — the product rule and the differentiated lowered Christoffel. -/

/-- **Product rule for the lowered `∂Γ` term** — `∑_ρ g_{aρ} ∂_dir Γ^ρ_{ef} = ∂_dir(∑_ρ g_{aρ}Γ^ρ_{ef})
    − ∑_ρ (∂_dir g_{aρ}) Γ^ρ_{ef}` (Leibniz, needs `g`, `Γ` differentiable). -/
private theorem lowered_pd_christoffel (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x : Point n) (a e f dir : Fin n) :
    (∑ ρ, g x a ρ * pd (fun y => christoffel g gi ρ e f y) dir x)
    = pd (fun y => ∑ ρ, g y a ρ * christoffel g gi ρ e f y) dir x
      - ∑ ρ, pd (fun y => g y a ρ) dir x * christoffel g gi ρ e f x := by
  rw [pd_sum univ (fun ρ y => g y a ρ * christoffel g gi ρ e f y) dir x
        (fun ρ _ => (PdiffAt_of_contDiff _ (hg a ρ) dir x).mul
          (PdiffAt_of_contDiff _ (hC ρ e f) dir x))]
  rw [Finset.sum_congr rfl (fun ρ _ => pd_mul (fun y => g y a ρ)
        (fun y => christoffel g gi ρ e f y) dir x
        (PdiffAt_of_contDiff _ (hg a ρ) dir x) (PdiffAt_of_contDiff _ (hC ρ e f) dir x))]
  rw [Finset.sum_add_distrib]
  ring

/-- **The differentiated lowered Christoffel** — `∂_dir(∑_ρ g_{aρ}Γ^ρ_{ef}) = ½(∂_dir∂_e g_{af} +
    ∂_dir∂_f g_{ae} − ∂_dir∂_a g_{ef})` (via `christoffel_lower` pointwise + differentiation). -/
private theorem pd_lowered_christoffel (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (x : Point n) (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (a e f dir : Fin n) :
    pd (fun y => ∑ ρ, g y a ρ * christoffel g gi ρ e f y) dir x
    = (1/2) * (pd (fun y => pd (fun w => g w a f) e y) dir x
             + pd (fun y => pd (fun w => g w a e) f y) dir x
             - pd (fun y => pd (fun w => g w e f) a y) dir x) := by
  have hfun : (fun y : Point n => ∑ ρ, g y a ρ * christoffel g gi ρ e f y)
      = (fun y => (1/2) * (pd (fun w => g w a f) e y + pd (fun w => g w a e) f y
                         - pd (fun w => g w e f) a y)) := by
    funext y
    rw [show (∑ ρ, g y a ρ * christoffel g gi ρ e f y)
          = ∑ ρ, g y ρ a * christoffel g gi ρ e f y from
        Finset.sum_congr rfl (fun ρ _ => by rw [hsymm y a ρ])]
    exact christoffel_lower g gi hsymm y (hinv y) a e f
  have p1 : PdiffAt (fun y => pd (fun w => g w a f) e y) dir x := PdiffAt_pd _ (hg a f) e dir x
  have p2 : PdiffAt (fun y => pd (fun w => g w a e) f y) dir x := PdiffAt_pd _ (hg a e) f dir x
  have p3 : PdiffAt (fun y => pd (fun w => g w e f) a y) dir x := PdiffAt_pd _ (hg e f) a dir x
  rw [hfun, pd_const_mul (1/2) _ dir x ((p1.add p2).sub p3),
      pd_sub _ _ dir x (p1.add p2) p3, pd_add _ _ dir x p1 p2]

/-- **`DlowerG`** — the lowered `∂Γ` term as `½(∂∂g)` minus the metric-compat remainder. -/
private theorem DlowerG (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x : Point n) (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (a e f dir : Fin n) :
    (∑ ρ, g x a ρ * pd (fun y => christoffel g gi ρ e f y) dir x)
    = (1/2) * (pd (fun y => pd (fun w => g w a f) e y) dir x
             + pd (fun y => pd (fun w => g w a e) f y) dir x
             - pd (fun y => pd (fun w => g w e f) a y) dir x)
      - ∑ ρ, pd (fun y => g y a ρ) dir x * christoffel g gi ρ e f x := by
  rw [lowered_pd_christoffel g gi hg hC x a e f dir,
      pd_lowered_christoffel g gi hsymm hg x hinv a e f dir]

/-! ### V1 — the ΓΓ cancellation and the general-point lowered-Riemann expansion. -/

/-- **The ΓΓ cancellation** — the Riemann's own `ΓΓ` part minus the two metric-compat `∂g·Γ` remainders
    collapses to the clean `g_{τρ}(ΓΓ − ΓΓ)` form.  The four `g_{aσ}ΓΓ` terms cancel pairwise. -/
private theorem gamma_cancellation (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (a b c d : Fin n) :
    (∑ ρ, g x a ρ * (∑ l, (christoffel g gi ρ c l x * christoffel g gi l d b x
                         - christoffel g gi ρ d l x * christoffel g gi l c b x)))
    - (∑ ρ, pd (fun y => g y a ρ) c x * christoffel g gi ρ d b x)
    + (∑ ρ, pd (fun y => g y a ρ) d x * christoffel g gi ρ c b x)
    = ∑ τ, ∑ ρ, g x τ ρ * (christoffel g gi τ d a x * christoffel g gi ρ c b x
                         - christoffel g gi τ c a x * christoffel g gi ρ d b x) := by
  have hQUAD : (∑ ρ, g x a ρ * (∑ l, (christoffel g gi ρ c l x * christoffel g gi l d b x
                         - christoffel g gi ρ d l x * christoffel g gi l c b x)))
      = (∑ τ, ∑ ρ, g x a τ * christoffel g gi τ c ρ x * christoffel g gi ρ d b x)
        - (∑ τ, ∑ ρ, g x a τ * christoffel g gi τ d ρ x * christoffel g gi ρ c b x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hMC1 : (∑ ρ, pd (fun y => g y a ρ) c x * christoffel g gi ρ d b x)
      = (∑ τ, ∑ ρ, g x τ ρ * christoffel g gi τ c a x * christoffel g gi ρ d b x)
        + (∑ τ, ∑ ρ, g x a τ * christoffel g gi τ c ρ x * christoffel g gi ρ d b x) := by
    have e1 : (∑ ρ, pd (fun y => g y a ρ) c x * christoffel g gi ρ d b x)
        = (∑ ρ, ∑ σ, christoffel g gi σ c a x * g x σ ρ * christoffel g gi ρ d b x)
          + (∑ ρ, ∑ σ, christoffel g gi σ c ρ x * g x a σ * christoffel g gi ρ d b x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [pd_g_eq g gi hsymm x hinv c a ρ, add_mul, Finset.sum_mul, Finset.sum_mul]
    rw [e1]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ρ _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ρ _ => by ring
  have hMC2 : (∑ ρ, pd (fun y => g y a ρ) d x * christoffel g gi ρ c b x)
      = (∑ τ, ∑ ρ, g x τ ρ * christoffel g gi τ d a x * christoffel g gi ρ c b x)
        + (∑ τ, ∑ ρ, g x a τ * christoffel g gi τ d ρ x * christoffel g gi ρ c b x) := by
    have e1 : (∑ ρ, pd (fun y => g y a ρ) d x * christoffel g gi ρ c b x)
        = (∑ ρ, ∑ σ, christoffel g gi σ d a x * g x σ ρ * christoffel g gi ρ c b x)
          + (∑ ρ, ∑ σ, christoffel g gi σ d ρ x * g x a σ * christoffel g gi ρ c b x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [pd_g_eq g gi hsymm x hinv d a ρ, add_mul, Finset.sum_mul, Finset.sum_mul]
    rw [e1]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ρ _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ρ _ => by ring
  have hTarget : (∑ τ, ∑ ρ, g x τ ρ * (christoffel g gi τ d a x * christoffel g gi ρ c b x
                       - christoffel g gi τ c a x * christoffel g gi ρ d b x))
      = (∑ τ, ∑ ρ, g x τ ρ * christoffel g gi τ d a x * christoffel g gi ρ c b x)
        - (∑ τ, ∑ ρ, g x τ ρ * christoffel g gi τ c a x * christoffel g gi ρ d b x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  linarith [hQUAD, hMC1, hMC2, hTarget]

/-- **V1 — the general-point lowered-Riemann expansion.**  For a symmetric, invertible, smooth metric,
      `Rlow_{abcd} = ½(∂_c∂_b g_{ad} − ∂_c∂_a g_{db} − ∂_d∂_b g_{ac} + ∂_d∂_a g_{cb})`
                   `+ ∑_{τρ} g_{τρ}(Γ^τ_{da}Γ^ρ_{cb} − Γ^τ_{ca}Γ^ρ_{db})`.
    Product rule on the two `g·∂Γ` terms, `christoffel_lower`, metric compatibility (`pd_g_eq`), and
    the pairwise `ΓΓ` cancellation (`gamma_cancellation`); the shared `∂_c∂_d g_{ab}` cancels by Schwarz
    (`pd_comm`).  The general-point analog of `riemann_at_zero`.  ⚠ NOT a₁ = R/6. -/
theorem riemannLower_expansion (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x : Point n) (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (a b c d : Fin n) :
    riemannLower g gi a b c d x
      = (1/2) * (pd (fun y => pd (fun w => g w a d) b y) c x
               - pd (fun y => pd (fun w => g w d b) a y) c x
               - pd (fun y => pd (fun w => g w a c) b y) d x
               + pd (fun y => pd (fun w => g w c b) a y) d x)
        + ∑ τ, ∑ ρ, g x τ ρ * (christoffel g gi τ d a x * christoffel g gi ρ c b x
                             - christoffel g gi τ c a x * christoffel g gi ρ d b x) := by
  have hexp : riemannLower g gi a b c d x
      = (∑ ρ, g x a ρ * pd (fun y => christoffel g gi ρ d b y) c x)
        - (∑ ρ, g x a ρ * pd (fun y => christoffel g gi ρ c b y) d x)
        + (∑ ρ, g x a ρ * (∑ l, (christoffel g gi ρ c l x * christoffel g gi l d b x
                               - christoffel g gi ρ d l x * christoffel g gi l c b x))) := by
    simp only [riemannLower, riemann]
    rw [show (∑ ρ, g x a ρ * (pd (fun y => christoffel g gi ρ d b y) c x
                - pd (fun y => christoffel g gi ρ c b y) d x
                + ∑ l, (christoffel g gi ρ c l x * christoffel g gi l d b x
                      - christoffel g gi ρ d l x * christoffel g gi l c b x)))
          = ∑ ρ, (g x a ρ * pd (fun y => christoffel g gi ρ d b y) c x
                - g x a ρ * pd (fun y => christoffel g gi ρ c b y) d x
                + g x a ρ * (∑ l, (christoffel g gi ρ c l x * christoffel g gi l d b x
                      - christoffel g gi ρ d l x * christoffel g gi l c b x)))
          from Finset.sum_congr rfl (fun ρ _ => by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hexp, DlowerG g gi hsymm hg hC x hinv a d b c,
      DlowerG g gi hsymm hg hC x hinv a c b d]
  have hsch : pd (fun y => pd (fun w => g w a b) d y) c x
            = pd (fun y => pd (fun w => g w a b) c y) d x :=
    pd_comm (fun w => g w a b) c d x (hg a b)
  have hgc := gamma_cancellation g gi hsymm x (hinv x) a b c d
  linarith [hsch, hgc]

/-! ### V2 — the first-pair antisymmetry. -/

/-- **V2 — first-pair antisymmetry of the lowered Riemann tensor.**  `Rlow_{abcd} + Rlow_{bacd} = 0`.
    From the V1 expansion: the `∂∂g` part is antisymmetric in `(a,b)` after Schwarz (`pd_comm` is baked
    into V1) and the metric symmetry `g_{db}=g_{bd}`, `g_{cb}=g_{bc}`; the `ΓΓg` part is antisymmetric
    by the metric symmetry `g_{τρ}=g_{ρτ}` (relabel the contracted pair).  ⚠ NOT a₁ = R/6. -/
theorem riemannLower_first_pair_antisymm (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x : Point n) (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (a b c d : Fin n) :
    riemannLower g gi a b c d x + riemannLower g gi b a c d x = 0 := by
  rw [riemannLower_expansion g gi hsymm hg hC x hinv a b c d,
      riemannLower_expansion g gi hsymm hg hC x hinv b a c d]
  have h1 : pd (fun y => pd (fun w => g w a d) b y) c x
          = pd (fun y => pd (fun w => g w d a) b y) c x := by
    rw [show (fun w : Point n => g w a d) = (fun w => g w d a) from funext fun w => hsymm w a d]
  have h2 : pd (fun y => pd (fun w => g w d b) a y) c x
          = pd (fun y => pd (fun w => g w b d) a y) c x := by
    rw [show (fun w : Point n => g w d b) = (fun w => g w b d) from funext fun w => hsymm w d b]
  have h3 : pd (fun y => pd (fun w => g w a c) b y) d x
          = pd (fun y => pd (fun w => g w c a) b y) d x := by
    rw [show (fun w : Point n => g w a c) = (fun w => g w c a) from funext fun w => hsymm w a c]
  have h4 : pd (fun y => pd (fun w => g w c b) a y) d x
          = pd (fun y => pd (fun w => g w b c) a y) d x := by
    rw [show (fun w : Point n => g w c b) = (fun w => g w b c) from funext fun w => hsymm w c b]
  have hΓ : (∑ τ, ∑ ρ, g x τ ρ * (christoffel g gi τ d a x * christoffel g gi ρ c b x
                             - christoffel g gi τ c a x * christoffel g gi ρ d b x))
          + (∑ τ, ∑ ρ, g x τ ρ * (christoffel g gi τ d b x * christoffel g gi ρ c a x
                             - christoffel g gi τ c b x * christoffel g gi ρ d a x)) = 0 := by
    rw [show (∑ τ, ∑ ρ, g x τ ρ * (christoffel g gi τ d b x * christoffel g gi ρ c a x
                             - christoffel g gi τ c b x * christoffel g gi ρ d a x))
          = ∑ τ, ∑ ρ, g x ρ τ * (christoffel g gi ρ d b x * christoffel g gi τ c a x
                             - christoffel g gi ρ c b x * christoffel g gi τ d a x)
        from Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [hsymm x ρ τ]; ring
  linarith [h1, h2, h3, h4, hΓ]

/-! ### V3 — the reindex helper and the `hvanish` discharge. -/

/-- Rotate the outermost of five nested sums to innermost. -/
private theorem sum5_head_to_tail (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, F i j k l m)
    = ∑ j, ∑ k, ∑ l, ∑ m, ∑ i, F i j k l m := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]

/-- **V3 — the `hvanish` discharge.**  For a symmetric, invertible, smooth metric, given the Jacobi-field
    equation `∇∇J = −R(J,γ̇)γ̇` in components (`hJac`: the parenthesized second-covariant vector equals
    `−(R(J,u)u)^a`), the exact `hvanish` expression of
    `GaussLemmaTransverse.covariant_pairing_hasDerivAt_zero` vanishes.  The curvature scalar
    `∑ g_{ab}(R(J,u)u)^a u^b` is killed by the first-pair antisymmetry (V2) contracted against `u⊗u`
    (`antisym_contract`).  The residual carry is now the Jacobi ODE (`hJac`), a separate labelled input.
    ⚠ NOT a₁ = R/6. -/
theorem hvanish_from_antisym (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (X : Point n) (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (u J cJ cJp : Fin n → ℝ)
    (hJac : ∀ a, cJp a + ∑ c, ∑ d, christoffel g gi a c d X * u c * cJ d
        = -(∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p)) :
    (∑ a, ∑ b, g X a b * (cJp a + ∑ c, ∑ d, christoffel g gi a c d X * u c * cJ d) * u b) = 0 := by
  -- The lowered-Riemann contraction (with e,p,J-weights) is antisymmetric in the first pair.
  have hAA : ∀ i j, (∑ e, ∑ p, riemannLower g gi i j e p X * J e * u p)
                  + (∑ e, ∑ p, riemannLower g gi j i e p X * J e * u p) = 0 := by
    intro i j
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [show riemannLower g gi i j e p X * J e * u p + riemannLower g gi j i e p X * J e * u p
          = (riemannLower g gi i j e p X + riemannLower g gi j i e p X) * (J e * u p) from by ring,
        riemannLower_first_pair_antisymm g gi hsymm hg hC X hinv i j e p, zero_mul]
  have hA : ∀ i j, (∑ e, ∑ p, riemannLower g gi i j e p X * J e * u p)
      = -(∑ e, ∑ p, riemannLower g gi j i e p X * J e * u p) := fun i j => by linarith [hAA i j]
  have hac := antisym_contract (fun i j => ∑ e, ∑ p, riemannLower g gi i j e p X * J e * u p) u hA
  -- The curvature scalar equals the antisymmetric contraction (a five-index reindex).
  have hL : (∑ a, ∑ b, g X a b
              * (∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p) * u b)
      = ∑ a, ∑ b, ∑ σ, ∑ e, ∑ p,
          g X a b * riemann g gi a σ e p X * u σ * J e * u p * u b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hR : (∑ i, ∑ j, (∑ e, ∑ p, riemannLower g gi i j e p X * J e * u p) * u i * u j)
      = ∑ a, ∑ b, ∑ σ, ∑ e, ∑ p,
          g X a b * riemann g gi a σ e p X * u σ * J e * u p * u b := by
    rw [sum5_head_to_tail (fun a b σ e p =>
          g X a b * riemann g gi a σ e p X * u σ * J e * u p * u b)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [riemannLower]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [hsymm X b a]; ring
  have key : (∑ a, ∑ b, g X a b
              * (∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p) * u b) = 0 := by
    rw [hL, ← hR]; exact hac
  -- discharge `hvanish` via the Jacobi equation.
  have hsub : (∑ a, ∑ b, g X a b
                * (cJp a + ∑ c, ∑ d, christoffel g gi a c d X * u c * cJ d) * u b)
      = ∑ a, ∑ b, g X a b
          * (-(∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p)) * u b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hJac a]
  rw [hsub]
  calc (∑ a, ∑ b, g X a b
          * (-(∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p)) * u b)
      = ∑ a, ∑ b, -(g X a b
          * (∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p) * u b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a, -(∑ b, g X a b
          * (∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p) * u b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_neg_distrib]
    _ = -(∑ a, ∑ b, g X a b
          * (∑ σ, ∑ e, ∑ p, riemann g gi a σ e p X * u σ * J e * u p) * u b) := by
        rw [Finset.sum_neg_distrib]
    _ = 0 := by rw [key, neg_zero]

end QIQTH.RiemannFirstPairAntisym

section AxiomChecks
open QIQTH.RiemannFirstPairAntisym
#print axioms antisym_contract
#print axioms riemannLower_expansion
#print axioms riemannLower_first_pair_antisymm
#print axioms hvanish_from_antisym
end AxiomChecks
