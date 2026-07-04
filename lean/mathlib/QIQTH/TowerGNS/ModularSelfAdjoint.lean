/-
  THE VON NEUMANN CAMPAIGN — VN5 (THE_VON_NEUMANN_PLAN.md) — ★ THE HEADLINE ★:
  **Δ† = Δ — the von Neumann SELF-ADJOINTNESS of the tower modular operator.**

  The assembly of the whole campaign, in one application: VN1's abstract von Neumann
  criterion (`isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective`, at `𝕜 = ℂ`) fed by
  * the DENSE domain (`dense_towerModularOp_domain`, M5.5),
  * the SYMMETRY (`towerModularOp_isFormalAdjoint`, M5.2),
  * the RANGE CONDITION `ran (1 + Δ) = ⊤` (`towerModularOp_one_add_surjective`, VN4 —
    itself the graph decomposition of the closed S̄ (VN2) + the i-twist).

  Corollaries harvested here:
  * `towerModularOp_adjoint_eq` — the raw adjoint equation `Δ.adjoint = Δ`;
  * `towerModularOp_isClosed` — Δ is CLOSED (self-adjoint ⟹ closed; Mathlib's
    `IsSelfAdjoint.isClosed`) — so the M6 closability was in fact equality;
  * `towerModularOp_closure_eq` — `Δ.closure = Δ` (the graph is already closed);
  * `towerModularOp_eq_zero` — KERNEL TRIVIALITY: `Δ x = 0 → x = 0` (positivity
    `⟪Δx, x⟫ = ‖S̄x‖²` + the kernel triviality of S̄, `towerTomitaBar_eq_zero`);
  * `norm_le_norm_add_towerModularOp` — THE RESOLVENT BOUND `‖x‖ ≤ ‖x + Δx‖`
    (positivity of `re ⟪x, Δx⟫` inside the norm expansion), the injectivity half of the
    resolvent `(1 + Δ)⁻¹`.

  NOT here (deliberately): Δ^{1/2}, J, the polar decomposition S̄ = JΔ^{1/2}, Δ^{it},
  KMS, any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.ModularSurjective
import QIQTH.VonNeumann.SelfAdjointCriterion

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### VN5.1 — ★★★ THE HEADLINE ★★★ Δ† = Δ -/

/-- **★★★ Δ† = Δ — THE TOWER MODULAR OPERATOR IS SELF-ADJOINT (von Neumann) ★★★**:
the abstract criterion VN1 (`isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective`,
at `𝕜 = ℂ`) applied to the dense domain (M5.5), the symmetry (M5.2), and the range
condition `ran (1 + Δ) = ⊤` (VN4 — the graph decomposition of the closed S̄ + the
i-twist). The genuinely UNBOUNDED self-adjointness, in Mathlib's `LinearPMap.adjoint`
sense, of the modular operator of the tower limit state. -/
theorem towerModularOp_isSelfAdjoint :
    IsSelfAdjoint (towerModularOp L ω β) :=
  QIQTH.VonNeumann.isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective
    (dense_towerModularOp_domain L ω β)
    (towerModularOp_isFormalAdjoint L ω β)
    (towerModularOp_one_add_surjective L ω β)

/-- The headline in raw adjoint-equation form: `Δ.adjoint = Δ` (unfolded from the `Star`
instance through `LinearPMap.isSelfAdjoint_def`, for downstream consumers that avoid
`IsSelfAdjoint`). -/
theorem towerModularOp_adjoint_eq :
    (towerModularOp L ω β).adjoint = towerModularOp L ω β :=
  LinearPMap.isSelfAdjoint_def.mp (towerModularOp_isSelfAdjoint L ω β)

/-! ### VN5.2 — Δ is closed; the closure is Δ itself -/

/-- **Δ IS CLOSED** — every self-adjoint operator is closed (Mathlib's
`IsSelfAdjoint.isClosed`: the adjoint of a densely-defined operator is closed, and Δ IS
its own adjoint). The M6 closability `towerModularOp_isClosable` is hereby upgraded:
the closed extension was Δ itself. -/
theorem towerModularOp_isClosed :
    (towerModularOp L ω β).IsClosed :=
  (towerModularOp_isSelfAdjoint L ω β).isClosed

/-- **`Δ.closure = Δ`** — the closure of the (already closed) modular operator is
itself: the graph of the closure is the topological closure of the (closed) graph. -/
theorem towerModularOp_closure_eq :
    (towerModularOp L ω β).closure = towerModularOp L ω β :=
  LinearPMap.eq_of_eq_graph <| by
    rw [← (towerModularOp_isClosed L ω β).isClosable.graph_closure_eq_closure_graph]
    exact (towerModularOp_isClosed L ω β).submodule_topologicalClosure_eq

/-! ### VN5.3 — kernel triviality: Δ x = 0 → x = 0

    Positivity `⟪Δx, x⟫ = ‖S̄x‖²` (M5.1) forces `S̄x = 0`, and the kernel triviality of
    S̄ (`towerTomitaBar_eq_zero`, the swap-graph argument) forces `x = 0`. Mind the
    two-layer domain: the first-layer membership is extracted through
    `mem_bar_of_mem_towerModularDom`; membership-proof transport is by the `_congr`
    adapter, never a rw under a subtype. -/

/-- **KERNEL TRIVIALITY**: `Δ x = 0 → x = 0` — positivity `⟪Δx, x⟫ = ‖S̄x‖²` collapses to
`‖S̄x‖² = 0`, so `S̄x = 0`, and S̄ has trivial kernel (`towerTomitaBar_eq_zero`). Together
with the resolvent bound below this is the injectivity of Δ (and of `1 + Δ`). -/
theorem towerModularOp_eq_zero (x : (towerModularOp L ω β).domain)
    (hx : towerModularOp L ω β x = 0) : (x : TowerGNS L ω β) = 0 := by
  have hbar := mem_bar_of_mem_towerModularDom L ω β x.2
  have hF := barF_of_mem_towerModularDom L ω β x.2 hbar
  -- transport Δ's value to the ⟨↑x, mem⟩ presentation (proof irrelevance, congr adapter)
  have hmk : towerModularOp L ω β
        ⟨(x : TowerGNS L ω β), mem_towerModularDom L ω β hbar hF⟩
      = towerModularOp L ω β x :=
    towerModularOp_congr L ω β (mem_towerModularDom L ω β hbar hF) x.2 rfl
  have hinner := towerModularOp_inner_self L ω β hbar hF
  rw [hmk, hx, inner_zero_left] at hinner
  -- hinner : 0 = (‖S̄ ⟨↑x, hbar⟩‖ : ℂ) ^ 2, so the norm vanishes
  have hnorm : ‖towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hbar⟩‖ = 0 := by
    have h2 : (‖towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), hbar⟩‖ : ℂ) = 0 :=
      sq_eq_zero_iff.mp hinner.symm
    exact_mod_cast h2
  exact towerTomitaBar_eq_zero L ω β ⟨(x : TowerGNS L ω β), hbar⟩
    (norm_eq_zero.mp hnorm)

/-! ### VN5.4 — THE RESOLVENT BOUND: ‖x‖ ≤ ‖x + Δx‖

    `‖x + Δx‖² = ‖x‖² + 2 re ⟪x, Δx⟫ + ‖Δx‖²`, and `re ⟪x, Δx⟫ = re ⟪Δx, x⟫ = ‖S̄x‖² ≥ 0`
    by positivity (M5.1), so `‖x‖² ≤ ‖x + Δx‖²`; take square roots. -/

/-- **THE RESOLVENT BOUND**: `‖x‖ ≤ ‖x + Δx‖` on the domain of Δ — the norm expansion
`‖x + Δx‖² = ‖x‖² + 2 re ⟪x, Δx⟫ + ‖Δx‖²` with the positivity `re ⟪x, Δx⟫ = ‖S̄x‖² ≥ 0`.
The quantitative injectivity of `1 + Δ`, i.e. the boundedness (by 1) of the resolvent
`(1 + Δ)⁻¹` on its range — which VN4 proved is EVERYTHING. -/
theorem norm_le_norm_add_towerModularOp (x : (towerModularOp L ω β).domain) :
    ‖(x : TowerGNS L ω β)‖
      ≤ ‖(x : TowerGNS L ω β) + towerModularOp L ω β x‖ := by
  have hbar := mem_bar_of_mem_towerModularDom L ω β x.2
  have hF := barF_of_mem_towerModularDom L ω β x.2 hbar
  have hmk : towerModularOp L ω β
        ⟨(x : TowerGNS L ω β), mem_towerModularDom L ω β hbar hF⟩
      = towerModularOp L ω β x :=
    towerModularOp_congr L ω β (mem_towerModularDom L ω β hbar hF) x.2 rfl
  have hinner := towerModularOp_inner_self L ω β hbar hF
  rw [hmk] at hinner
  -- positivity of the cross term: re ⟪x, Δx⟫ = re ⟪Δx, x⟫ = ‖S̄x‖² ≥ 0
  have hre : 0 ≤ RCLike.re
      ⟪(x : TowerGNS L ω β), towerModularOp L ω β x⟫_ℂ := by
    rw [inner_re_symm, hinner, ← Complex.ofReal_pow, RCLike.re_to_complex,
      Complex.ofReal_re]
    exact sq_nonneg _
  -- the norm expansion over ℂ
  have hexp : ‖(x : TowerGNS L ω β) + towerModularOp L ω β x‖ ^ 2
      = ‖(x : TowerGNS L ω β)‖ ^ 2
        + 2 * RCLike.re ⟪(x : TowerGNS L ω β), towerModularOp L ω β x⟫_ℂ
        + ‖towerModularOp L ω β x‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) _ _
  have hsq : ‖(x : TowerGNS L ω β)‖ ^ 2
      ≤ ‖(x : TowerGNS L ω β) + towerModularOp L ω β x‖ ^ 2 := by
    rw [hexp]
    have h0 := sq_nonneg ‖towerModularOp L ω β x‖
    linarith
  calc ‖(x : TowerGNS L ω β)‖
      = Real.sqrt (‖(x : TowerGNS L ω β)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖(x : TowerGNS L ω β) + towerModularOp L ω β x‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ‖(x : TowerGNS L ω β) + towerModularOp L ω β x‖ :=
        Real.sqrt_sq (norm_nonneg _)

end QIQTH.TowerGNS
