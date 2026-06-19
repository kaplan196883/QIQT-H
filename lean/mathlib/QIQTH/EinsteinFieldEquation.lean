import QIQTH.Curvature
import QIQTH.EinsteinEquationOfState

/-!
# The Einstein field equation from the thermodynamic equation of state

This file **completes the step `EinsteinEquationOfState.lean` explicitly defers** ("conservation
`∇^μT=0` and the contracted Bianchi identity then fix `f = −½R + Λ`, giving the Einstein
equation — that last step is cited, not here").

Given
  * the **post-crux relation** `a·T_{μν} = R_{μν} + f·g_{μν}` — the per-null-direction Clausius
    relation upgraded to a tensor by `symmTensor_eq_smul_metric_of_null` (Jacobson's heat/area
    input; the differential geometry that produces it is cited physics, supplied as a hypothesis),
  * **local conservation** `∇^μ(a·T)_{μν} = 0`,
  * the **contracted Bianchi identity** `∇^μ R_{μν} = ½ ∂_ν R` (geometry — the `∇^μG_{μν}=0`
    identity whose hard lemmas are machine-checked in `Curvature.lean`),
  * **metric compatibility** `∇g = 0` (`metric_compat`),

the **Einstein field equation** follows:
      `a·T_{μν} = G_{μν} + Λ·g_{μν}`,   `G_{μν} := R_{μν} − ½R·g_{μν}`,
with `Λ := f + ½R` **covariantly constant** (`∂_ν Λ = 0`) — the cosmological constant emerging as
Jacobson's integration constant. Axiom-free; every cited input is an explicit labeled hypothesis.
-/

namespace QIQTH.Curvature

variable {n : ℕ}

/-- **Raised divergence** `∇^μ X_{μν} = g^{μρ} ∇_ρ X_{μν}` of a `(0,2)` tensor field. -/
noncomputable def div02 (g gi : Point n → Fin n → Fin n → ℝ)
    (X : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n) : ℝ :=
  ∑ μ, ∑ ρ, gi x μ ρ * covDeriv02 g gi X ρ μ ν x

/-- The raised divergence is additive in the tensor field. -/
theorem div02_add (g gi : Point n → Fin n → Fin n → ℝ)
    (X Y : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hX : ∀ a b ρ, PdiffAt (fun y => X y a b) ρ x) (hY : ∀ a b ρ, PdiffAt (fun y => Y y a b) ρ x)
    (ν : Fin n) :
    div02 g gi (fun y a b => X y a b + Y y a b) ν x = div02 g gi X ν x + div02 g gi Y ν x := by
  simp only [div02]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro μ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ρ _
  have hcd : covDeriv02 g gi (fun y a b => X y a b + Y y a b) ρ μ ν x
      = covDeriv02 g gi X ρ μ ν x + covDeriv02 g gi Y ρ μ ν x := by
    simp only [covDeriv02]
    rw [pd_add (fun y => X y μ ν) (fun y => Y y μ ν) ρ x (hX μ ν ρ) (hY μ ν ρ)]
    simp only [Finset.sum_add_distrib, mul_add]; ring
  rw [hcd]; ring

/-- **The divergence of `f·g` is `∂_ν f`.** Metric compatibility kills the connection terms; the
    inverse metric collapses the contraction. (This is what makes the cosmological-constant term
    `Λ·g` covariantly constant.) -/
theorem div02_scalar_metric (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (f : Point n → ℝ) (x : Point n) (hf : ∀ ρ, PdiffAt f ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (ν : Fin n) :
    div02 g gi (fun y a b => f y * g y a b) ν x = pd f ν x := by
  have key : ∀ ρ μ : Fin n,
      covDeriv02 g gi (fun y a b => f y * g y a b) ρ μ ν x = pd f ρ x * g x μ ν := by
    intro ρ μ
    have hmc := metric_compat g gi hsymm x (fun p q => hinv x p q) ρ μ ν
    simp only [covDeriv02] at hmc ⊢
    rw [pd_mul f (fun y => g y μ ν) ρ x (hf ρ) (hg μ ν ρ)]
    have e1 : (∑ σ, christoffel g gi σ ρ μ x * (f x * g x σ ν))
        = f x * (∑ σ, christoffel g gi σ ρ μ x * g x σ ν) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _; ring
    have e2 : (∑ σ, christoffel g gi σ ρ ν x * (f x * g x μ σ))
        = f x * (∑ σ, christoffel g gi σ ρ ν x * g x μ σ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro σ _; ring
    have hg0 : pd (fun y => g y μ ν) ρ x
        = (∑ σ, christoffel g gi σ ρ μ x * g x σ ν) + (∑ σ, christoffel g gi σ ρ ν x * g x μ σ) := by
      linarith [hmc]
    rw [e1, e2, hg0]; ring
  have hcol : ∀ ρ : Fin n, (∑ μ, gi x μ ρ * g x μ ν) = if ν = ρ then (1 : ℝ) else 0 := by
    intro ρ
    rw [show (∑ μ, gi x μ ρ * g x μ ν) = ∑ μ, g x ν μ * gi x μ ρ from by
          apply Finset.sum_congr rfl; intro μ _; rw [hsymm x ν μ]; ring]
    exact hinv x ν ρ
  rw [div02, Finset.sum_congr rfl (fun μ (_ : μ ∈ Finset.univ) =>
        Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) => by rw [key ρ μ]))]
  rw [show (∑ μ, ∑ ρ, gi x μ ρ * (pd f ρ x * g x μ ν))
        = ∑ ρ, pd f ρ x * (∑ μ, gi x μ ρ * g x μ ν) from by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro ρ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro μ _; ring]
  rw [Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) => by rw [hcol ρ])]
  simp [Finset.sum_ite_eq, mul_ite]

/-- **T3 of the twice-contracted Bianchi**: `∑_ρ ∑_{σν} g^{σν} ∇_ρ R^ρ_{σνλ} = −∇^μ Ric_{μλ}`.
    Sum `gi_trace_covDerivRiem_ricci` over `ρ` and match `−div02(ricci)` (raised Ricci divergence)
    term-by-term via `sum_comm` + metric symmetry. -/
theorem divRiemann_trace_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam : Fin n) (x : Point n) :
    (∑ ρ, ∑ σ, ∑ ν, gi x σ ν * covDerivRiem g gi ρ ρ σ ν lam x)
      = - div02 g gi (fun y a b => ricci g gi a b y) lam x := by
  have hL1 : (∑ μ, ∑ ρ, gi x μ ρ * pd (fun y => ricci g gi μ lam y) ρ x)
      = ∑ ρ, ∑ β, gi x ρ β * pd (fun y => ricci g gi β lam y) ρ x := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro β _; rw [hsymm_gi x β ρ]
  have hL2 : (∑ μ, ∑ ρ, ∑ κ, gi x μ ρ * (christoffel g gi κ ρ μ x * ricci g gi κ lam x))
      = ∑ ρ, ∑ β, ∑ κ, christoffel g gi β ρ κ x * gi x ρ κ * ricci g gi β lam x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ρ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro κ _
    apply Finset.sum_congr rfl; intro μ _
    rw [hsymm_gi x μ ρ]; ring
  have hL3 : (∑ μ, ∑ ρ, ∑ κ, gi x μ ρ * (christoffel g gi κ ρ lam x * ricci g gi μ κ x))
      = ∑ ρ, ∑ β, ∑ κ, christoffel g gi κ ρ lam x * gi x ρ β * ricci g gi β κ x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro β _
    apply Finset.sum_congr rfl; intro κ _
    rw [hsymm_gi x β ρ]; ring
  rw [Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) =>
        gi_trace_covDerivRiem_ricci g gi hsymm hsymm_gi hinv hCg hCgi hC ρ lam x)]
  simp only [div02, covDeriv02, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_sub, neg_add]
  rw [← hL1, ← hL2, ← hL3]; ring

/-- **The twice-contracted (second) Bianchi identity** `∇^μ Ric_{μλ} = ½ ∂_λ R` — the contracted Bianchi
    `∇^μ G_{μλ}=0` in trace form. Obtained by contracting `second_bianchi_contracted` with `g^{σν}`:
    the three traced terms are `∂_λR` (`gi_trace_covDeriv_ricci`), `div02(ricci)` (the Ricci divergence),
    and `−div02(ricci)` (`divRiemann_trace_eq`), giving `∂_λR − div02 − div02 = 0`. Machine-checked,
    axiom-free — this **discharges the `bianchi` hypothesis** of `einstein_field_equation`. -/
theorem twice_contracted_bianchi (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (lam : Fin n) (x : Point n) :
    div02 g gi (fun y a b => ricci g gi a b y) lam x
      = (1 / 2 : ℝ) * pd (fun y => scalarCurv g gi y) lam x := by
  have hsum : (∑ σ, ∑ ν, gi x σ ν *
      (covDeriv02 g gi (fun y a b => ricci g gi a b y) lam σ ν x
        - covDeriv02 g gi (fun y a b => ricci g gi a b y) ν σ lam x
        + (∑ ρ, covDerivRiem g gi ρ ρ σ ν lam x))) = 0 := by
    apply Finset.sum_eq_zero; intro σ _; apply Finset.sum_eq_zero; intro ν _
    rw [second_bianchi_contracted g gi hsymm hC lam σ ν x, mul_zero]
  have hT2 : (∑ σ, ∑ ν, gi x σ ν * covDeriv02 g gi (fun y a b => ricci g gi a b y) ν σ lam x)
      = div02 g gi (fun y a b => ricci g gi a b y) lam x := by
    simp only [div02]
  have hT3 : (∑ σ, ∑ ν, gi x σ ν * (∑ ρ, covDerivRiem g gi ρ ρ σ ν lam x))
      = - div02 g gi (fun y a b => ricci g gi a b y) lam x := by
    rw [← divRiemann_trace_eq g gi hsymm hsymm_gi hinv hCg hCgi hC lam x]
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_comm), Finset.sum_comm]
  simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [gi_trace_covDeriv_ricci g gi hsymm hsymm_gi hinv hCg hCgi hC lam x, hT2, hT3] at hsum
  linarith [hsum]

/-- **The Einstein tensor is divergence-free: `∇^μ G_{μν} = 0`.**  The contracted-Bianchi identity in
    its most physically-famous form — the *geometric* origin of local energy–momentum conservation
    (it is exactly why `∇^μ(a·T_{μν}) = 0` is consistent with `a·T = G + Λg`).  Immediate from
    `twice_contracted_bianchi` (`∇^μ Ric_{μν} = ½∂_ν R`) and `div02_scalar_metric`
    (`∇^μ(f·g_{μν}) = ∂_ν f`): writing `G = Ric + (−½R)·g`, its divergence is `½∂_ν R − ½∂_ν R = 0`.
    Machine-checked, axiom-free. -/
theorem einsteinTensor_divergence_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (ν : Fin n) (x : Point n) :
    div02 g gi (fun y a b => einsteinTensor g gi a b y) ν x = 0 := by
  have htr : ∀ ρ, PdiffAt (fun y => scalarCurv g gi y) ρ x := fun ρ =>
    PdiffAt_sum _ _ ρ x (fun σ _ => PdiffAt_sum _ _ ρ x (fun μ _ =>
      (PdiffAt_of_contDiff _ (hCgi σ μ) ρ x).mul (PdiffAt_ricci g gi hC σ μ ρ x)))
  have hf : ∀ ρ, PdiffAt (fun y => -(1 / 2 : ℝ) * scalarCurv g gi y) ρ x := fun ρ =>
    (differentiableAt_const _).mul (htr ρ)
  have hsplit : (fun y a b => einsteinTensor g gi a b y)
      = fun y a b => ricci g gi a b y + (-(1 / 2 : ℝ) * scalarCurv g gi y) * g y a b := by
    funext y a b; simp only [einsteinTensor]; ring
  rw [hsplit, div02_add g gi (fun y a b => ricci g gi a b y)
        (fun y a b => (-(1 / 2 : ℝ) * scalarCurv g gi y) * g y a b) x
        (fun a b ρ => PdiffAt_ricci g gi hC a b ρ x)
        (fun a b ρ => (hf ρ).mul (PdiffAt_of_contDiff _ (hCg a b) ρ x)) ν,
      twice_contracted_bianchi g gi hsymm hsymm_gi hinv hCg hCgi hC ν x,
      div02_scalar_metric g gi hsymm hinv (fun y => -(1 / 2 : ℝ) * scalarCurv g gi y) x hf
        (fun a b ρ => PdiffAt_of_contDiff _ (hCg a b) ρ x) ν,
      pd_const_mul (-(1 / 2 : ℝ)) (fun y => scalarCurv g gi y) ν x (htr ν)]
  ring

/-- **The metric–inverse-metric trace is the dimension: `g^{μν} g_{μν} = n`.**  Contracting the metric
    with its inverse over both indices yields `∑_μ δ^μ_μ = n` (the number of dimensions). -/
theorem metric_contraction_trace (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (x : Point n) :
    (∑ μ, ∑ ν, gi x μ ν * g x μ ν) = (n : ℝ) := by
  have hrow : ∀ μ, (∑ ν, gi x μ ν * g x μ ν) = 1 := by
    intro μ
    rw [show (∑ ν, gi x μ ν * g x μ ν) = ∑ ν, g x μ ν * gi x ν μ from
      Finset.sum_congr rfl (fun ν _ => by rw [hsymm_gi x μ ν]; ring)]
    simpa using hinv x μ μ
  rw [Finset.sum_congr rfl (fun μ _ => hrow μ), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **The trace of the Einstein tensor: `g^{μν} G_{μν} = (1 − n/2)·R`.**  Taking the metric trace of
    `G = Ric − ½R·g` gives `R − ½R·n = (1 − n/2)R` — in `n = 4` dimensions this is `−R` (the
    "trace-reversed" relation: the trace of `a·T = G + Λg` reads `a·g^{μν}T_{μν} = (1 − n/2)R + nΛ`).
    Uses `metric_contraction_trace` (`g^{μν}g_{μν}=n`) and the definition `R = g^{σν}R_{σν}`. -/
theorem einstein_trace_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (x : Point n) :
    (∑ σ, ∑ ν, gi x σ ν * einsteinTensor g gi σ ν x)
      = (1 - (n : ℝ) / 2) * scalarCurv g gi x := by
  have key : ∀ σ ν, gi x σ ν * einsteinTensor g gi σ ν x
      = gi x σ ν * ricci g gi σ ν x
        - (1 / 2 * scalarCurv g gi x) * (gi x σ ν * g x σ ν) := by
    intro σ ν; simp only [einsteinTensor]; ring
  have hsplit : (∑ σ, ∑ ν, gi x σ ν * einsteinTensor g gi σ ν x)
      = (∑ σ, ∑ ν, gi x σ ν * ricci g gi σ ν x)
        - (1 / 2 * scalarCurv g gi x) * (∑ σ, ∑ ν, gi x σ ν * g x σ ν) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ν _ => key σ ν)
  rw [hsplit, metric_contraction_trace g gi hsymm_gi hinv x]
  show scalarCurv g gi x - (1 / 2 * scalarCurv g gi x) * (n : ℝ) = (1 - (n : ℝ) / 2) * scalarCurv g gi x
  ring

/-- **The Einstein field equation as the thermodynamic equation of state** (Jacobson, PRL 1995),
    completed: from the post-crux relation + conservation + contracted Bianchi + metric
    compatibility, `a·T_{μν} = G_{μν} + Λ·g_{μν}` with `Λ := f + ½R` **covariantly constant**.
    The cited physics (Clausius/Raychaudhuri → `crux`, conservation → `conserv`) and the geometry
    (contracted Bianchi → `bianchi`) are explicit labeled hypotheses; the closure is machine-checked,
    axiom-free. `tr` is the scalar curvature `R`. -/
theorem einstein_field_equation (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (T Ric : Point n → Fin n → Fin n → ℝ) (f tr : Point n → ℝ) (a : ℝ) (x : Point n)
    (hf : ∀ ρ, PdiffAt f ρ x) (htr : ∀ ρ, PdiffAt tr ρ x)
    (hg : ∀ a b ρ, PdiffAt (fun y => g y a b) ρ x)
    (hRic : ∀ a b ρ, PdiffAt (fun y => Ric y a b) ρ x)
    -- post-crux Clausius relation (cited physics): `a·T_{μν} = R_{μν} + f·g_{μν}`
    (crux : ∀ y a' b, a * T y a' b = Ric y a' b + f y * g y a' b)
    -- local conservation (physics): `∇^μ(a·T)_{μν} = 0`
    (conserv : ∀ ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0)
    -- contracted Bianchi (geometry): `∇^μ R_{μν} = ½ ∂_ν R`
    (bianchi : ∀ ν, div02 g gi Ric ν x = (1 / 2 : ℝ) * pd tr ν x) :
    (∀ μ ν, a * T x μ ν
        = (Ric x μ ν - (1 / 2 : ℝ) * tr x * g x μ ν) + (f x + (1 / 2 : ℝ) * tr x) * g x μ ν)
    ∧ (∀ ν, pd (fun y => f y + (1 / 2 : ℝ) * tr y) ν x = 0) := by
  refine ⟨fun μ ν => by rw [crux x μ ν]; ring, fun ν => ?_⟩
  -- Take the divergence of the crux relation.
  have heq : (fun y a' b => a * T y a' b) = (fun y a' b => Ric y a' b + f y * g y a' b) := by
    funext y a' b; exact crux y a' b
  have h1 := conserv ν
  rw [heq, div02_add g gi Ric (fun y a' b => f y * g y a' b) x hRic
        (fun a' b ρ => (hf ρ).mul (hg a' b ρ)) ν,
      bianchi ν, div02_scalar_metric g gi hsymm hinv f x hf hg ν] at h1
  -- h1 : ½ ∂_ν tr + ∂_ν f = 0.  Conclude ∂_ν(f + ½tr) = 0.
  rw [pd_add f (fun y => (1 / 2 : ℝ) * tr y) ν x (hf ν) ((htr ν).const_mul (1 / 2 : ℝ)),
      pd_const_mul (1 / 2 : ℝ) tr ν x (htr ν)]
  linarith [h1]

/-- **The Einstein field equation from the thermodynamic equation of state — with the ACTUAL curvature.**
    Instantiating `einstein_field_equation` at `Ric = ricci g gi`, `R = scalarCurv g gi`, and discharging
    the `bianchi` hypothesis with the machine-checked `twice_contracted_bianchi` (`∇^μRic=½∂R`). The
    conclusion now features the **genuine Einstein tensor** `einsteinTensor = Ric − ½R·g`:
        `a·T_{μν} = G_{μν} + Λ·g_{μν}`,  `Λ := f + ½R` covariantly constant.
    The ONLY remaining hypotheses are the **cited physics** — the post-crux Clausius relation
    `a·T = Ric + f·g` (area law + Unruh + Raychaudhuri, supplied as `crux`) and local conservation
    `∇^μ(aT)=0` (`conserv`). Everything geometric is now proven; axiom-free. -/
theorem einstein_field_equation_real (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (T : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ) (a : ℝ) (x : Point n)
    (hf : ∀ ρ, PdiffAt f ρ x)
    (crux : ∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b)
    (conserv : ∀ ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    (∀ μ ν, a * T x μ ν
        = einsteinTensor g gi μ ν x + (f x + (1 / 2 : ℝ) * scalarCurv g gi x) * g x μ ν)
    ∧ (∀ ν, pd (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y) ν x = 0) := by
  have htr : ∀ ρ, PdiffAt (fun y => scalarCurv g gi y) ρ x := fun ρ =>
    PdiffAt_sum _ _ ρ x (fun σ _ => PdiffAt_sum _ _ ρ x (fun ν _ =>
      (PdiffAt_of_contDiff _ (hCgi σ ν) ρ x).mul (PdiffAt_ricci g gi hC σ ν ρ x)))
  have hmain := einstein_field_equation g gi hsymm hinv T (fun y a' b => ricci g gi a' b y)
    f (fun y => scalarCurv g gi y) a x hf htr
    (fun a' b ρ => PdiffAt_of_contDiff _ (hCg a' b) ρ x)
    (fun a' b ρ => PdiffAt_ricci g gi hC a' b ρ x) crux conserv
    (fun ν => twice_contracted_bianchi g gi hsymm hsymm_gi hinv hCg hCgi hC ν x)
  exact ⟨fun μ ν => by rw [einsteinTensor]; exact hmain.1 μ ν, hmain.2⟩

/-- **The Einstein field equation with a GENUINE cosmological constant.** If the cited physics holds at
    *every* point (`crux` everywhere — it already is — and `conserv` everywhere), then `Λ := f + ½R` is a
    true **constant** (not just covariantly constant at a point), by `const_of_pd_zero` on the connected
    domain `Point n`. The Einstein field equation holds globally:
        `a·T_{μν} = G_{μν} + Λ·g_{μν}`   for a single constant `Λ`.
    Axiom-free; the only hypotheses are the cited physics + smoothness of `f + ½R`. -/
theorem einstein_field_equation_real_global (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (T : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ) (a : ℝ)
    (hf : ∀ x ρ, PdiffAt f ρ x)
    (hFdiff : Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y))
    (crux : ∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b)
    (conserv : ∀ x ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    ∃ Λ : ℝ, ∀ x μ ν, a * T x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  have hzero : ∀ x ν, pd (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y) ν x = 0 := fun x ν =>
    (einstein_field_equation_real g gi hsymm hsymm_gi hinv hCg hCgi hC T f a x (hf x) crux
      (conserv x)).2 ν
  refine ⟨f (0 : Point n) + (1 / 2 : ℝ) * scalarCurv g gi (0 : Point n), fun x μ ν => ?_⟩
  have hc : f x + (1 / 2 : ℝ) * scalarCurv g gi x
      = f (0 : Point n) + (1 / 2 : ℝ) * scalarCurv g gi (0 : Point n) :=
    const_of_pd_zero (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y) hFdiff hzero x 0
  rw [(einstein_field_equation_real g gi hsymm hsymm_gi hinv hCg hCgi hC T f a x (hf x) crux
        (conserv x)).1 μ ν, hc]

/-- **Phase 3 — wire the per-null Clausius relation to the tensor crux.** This *derives* the `crux`
    hypothesis (`a·T = R + f·g`) used everywhere above, from the genuinely primitive **per-null
    Clausius relation**: at each point, the heat tensor `a·T − R` vanishes on the *entire null cone*
    of the metric `g x`. That per-null relation is exactly Jacobson's premise (the Clausius relation
    `δQ = TδS` imposed on every local Rindler horizon, with horizon entropy `∝` area). The upgrade
    from per-null-direction to a tensor is the algebraic crux, here for the **general (curved)
    Lorentzian metric** via `symmTensor_eq_smul_metric_of_null_general` — the Lorentzian structure
    enters as the pointwise congruence to Minkowski `g x = Pᵀ·η·P` (Sylvester's law). The scalar
    field `f` is produced pointwise; its smoothness (needed to run the field-equation closure) is the
    one honest analytic residual, not derivable from the per-null relation alone. Axiom-free. -/
theorem crux_of_pernull (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (a : ℝ)
    (hT_symm : ∀ x a' b, T x a' b = T x b a')
    (hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1:ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1:ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j)
    (pernull : ∀ (x : Point 4) (v : Fin 4 → ℝ),
        QIQTH.EinsteinEOS.BL (g x) v = 0 →
        QIQTH.EinsteinEOS.BL (fun a' b => a * T x a' b - ricci g gi a' b x) v = 0) :
    ∃ f : Point 4 → ℝ, ∀ x a' b, a * T x a' b = ricci g gi a' b x + f x * g x a' b := by
  have hpt : ∀ x : Point 4, ∃ c : ℝ, ∀ a' b,
      a * T x a' b - ricci g gi a' b x = c * g x a' b := by
    intro x
    have hCsymm : ∀ i j, (a * T x i j - ricci g gi i j x) = (a * T x j i - ricci g gi j i x) := by
      intro i j; rw [hT_symm x i j, hric_symm x i j]
    exact QIQTH.EinsteinEOS.symmTensor_eq_smul_metric_of_null_general
      (fun a' b => a * T x a' b - ricci g gi a' b x) (g x) hCsymm
      (P x) (Pinv x) (hPP x) (hPP' x) (hcong x) (pernull x)
  choose f hf using hpt
  exact ⟨f, fun x a' b => by have := hf x a' b; linarith⟩

/-- # THE END-TO-END THEOREM — Jacobson's Einstein equation of state, wired together

`jacobson_einstein_equation_of_state` is the **single** theorem assembling the whole derivation:
from the per-null Clausius relation (Jacobson's one physics premise) to the **Einstein field equation
with a genuine cosmological constant**, `a·T_{μν} = G_{μν} + Λ·g_{μν}`. It composes the two halves —
`crux_of_pernull` (front) and `einstein_field_equation_real_global` (back) — through the
proportionality scalar `f`. **All geometry is discharged internally and is axiom-free.**

## Provenance of each hypothesis / discharged step

* `pernull` — **the per-null Clausius relation** `a·T(k,k) = R(k,k)` for all null `k` (Jacobson's
  premise). Its own provenance, machine-checked elsewhere in this project, is:
    - the Ricci focusing term `R_{σν}k^σk^ν` ⟸ **Raychaudhuri** (`raychaudhuri_geodesic`, axiom-free);
    - the temperature `T = ℏκ/2π` ⟸ **Unruh** (`QIQTH.Unruh.kms_periodicity`: the accelerated
      two-point function is KMS at `β = 2π/a`, axiom-free);
    - and, *cited* (not geometry): the **area law** `δS = ηδA` (gap 1 — the holographic postulate) and
      the **Clausius** relation `δQ = TδS`. The integral step that combines these into `pernull` is the
      one physics gluing bundled into this premise.
* `P, Pinv, hcong, …` — the **Lorentzian structure** (`g = Pᵀ·η·P`, Sylvester's law).
* `pernull ⟹ a·T = R + f·g` — the **null-cone tensor lemma** (`crux_of_pernull` /
  `symmTensor_eq_smul_metric_of_null_general`), discharged here.
* `hreg` — the **one analytic residual**: the proportionality scalar `f` is regular (the only thing the
  per-null relation alone does not give).
* `conserv` + the **contracted Bianchi** `∇^μG_{μν}=0` (`twice_contracted_bianchi`, axiom-free) fix
  `f = −R/2 + Λ` and make `Λ` a genuine constant — discharged via `einstein_field_equation_real_global`.

Net: **modulo exactly the cited physics — the area law (gap 1), Clausius, and the form of the
free-field correlator behind Unruh — the entire chain from the Clausius premise to `G+Λg=a·T` is one
machine-checked, axiom-free theorem.** -/
theorem jacobson_einstein_equation_of_state
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (T : Point 4 → Fin 4 → Fin 4 → ℝ) (a : ℝ)
    (hT_symm : ∀ x a' b, T x a' b = T x b a')
    (hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * QIQTH.EinsteinEOS.gm k l * P x l j)
    (pernull : ∀ (x : Point 4) (v : Fin 4 → ℝ),
        QIQTH.EinsteinEOS.BL (g x) v = 0 →
        QIQTH.EinsteinEOS.BL (fun a' b => a * T x a' b - ricci g gi a' b x) v = 0)
    (hreg : ∀ f : Point 4 → ℝ,
        (∀ y a' b, a * T y a' b = ricci g gi a' b y + f y * g y a' b) →
        (∀ x ρ, PdiffAt f ρ x) ∧
          Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y))
    (conserv : ∀ x ν, div02 g gi (fun y a' b => a * T y a' b) ν x = 0) :
    ∃ Λ : ℝ, ∀ x μ ν, a * T x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  obtain ⟨f, hf_real⟩ :=
    crux_of_pernull g gi T a hT_symm hric_symm P Pinv hPP hPP' hcong pernull
  obtain ⟨hf, hFdiff⟩ := hreg f hf_real
  exact einstein_field_equation_real_global g gi hsymm hsymm_gi hinv hCg hCgi hC
    T f a hf hFdiff hf_real conserv

end QIQTH.Curvature
