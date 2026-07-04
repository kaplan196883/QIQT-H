/-
  ID2 (THE_IDENTIFICATION_PLAN.md) — GNS EIGENVECTORS OF Δ AND R: the coerced pure
  matrix-unit components are eigenvectors of the modular operator AND of the resolvent,
  with EXPLICIT eigenvalues.

  ID1 established the finite modular eigenbasis — `modAut ρ_β (E_{nm} c) = (w_n/w_m)•(E_{nm} c)`
  (`modAut_gibbsDensity_single`). This increment transports it to the GNS completion:

  • Δ side — `towerModularOp_of` (Δ acts as `modAut ρ` on the pure-component core) turns the
    finite eigenvector equation into

        Δ ↑(of C (E_{nm} c)) = (w_n / w_m) • ↑(of C (E_{nm} c)),

    the scalar pushed through `of`/the completion coercion (`lof` linearity +
    `towerCoe_smul_raw`).

  • R side — the GENERAL resolvent eigenvector transport: if `Δ⟨x, hx⟩ = δ•x` with `0 < δ`,
    then `R x = (1+δ)⁻¹ • x` — the subtype-smul pattern (`towerModularOp_smul_cyclicVec`)
    applied to `y := (1+δ)⁻¹ • x`, whose `(1+Δ)`-image is `((1+δ)⁻¹ + (1+δ)⁻¹δ) • x = x`,
    so `towerResolvent_one_add` reads off `R x = ↑y`.

  • The specialization: `R ↑(of C (E_{nm} c)) = (1 + w_n/w_m)⁻¹ • ↑(of C (E_{nm} c))` —
    the eigenvalue positivity from ID1's `gibbsWeight_div_pos`.

  Deliverables:
  • `towerOf_smul_coe` — the scalar pushes through `of` and the coercion (the single-scalar
    form of `towerOf_sum_single_smul_coe`);
  • `towerModularOp_of_single` ★ — the Δ-eigenvector equation on the GNS space;
  • `towerResolvent_of_eigen` ★ — the general Δ-eigenvector → R-eigenvector transport;
  • `towerResolvent_of_single` — the two combined at `δ = w_n/w_m`.

  HONEST SCOPE (binding): eigenvector statements for Δ and R only. No `Δ^{it}`-eigenvector
  claim is made here (that is ID3); no identification `towerFlow = Δ^{it}` is claimed
  (that is ID4). Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ModularEigenbasis
import QIQTH.TowerGNS.Resolvent

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped Matrix DirectSum

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The single-scalar coercion push -/

/-- **The scalar pushes through `of` and the completion coercion**:
    `↑(of C (d • x)) = d • ↑(of C x)` — the single-scalar form of
    `towerOf_sum_single_smul_coe` (`lof` linearity crossed back to `of`, then
    `towerCoe_smul_raw`). -/
theorem towerOf_smul_coe (C : Finset M) (d : ℂ) (x : DiamondAlg L C) :
    ((towerOf L ω β C (d • x) : TowerPre L ω β) : TowerGNS L ω β)
      = d • ((towerOf L ω β C x : TowerPre L ω β) : TowerGNS L ω β) := by
  show towerCoe L ω β
    (DirectSum.of (fun C : Finset M => DiamondAlg L C) C (d • x)) = _
  rw [← DirectSum.lof_eq_of ℂ, map_smul, DirectSum.lof_eq_of]
  exact towerCoe_smul_raw L ω β d _

/-! ### ★ The Δ-eigenvector equation on the GNS space -/

/-- **★ THE GNS Δ-EIGENVECTOR EQUATION**: the coerced pure matrix-unit component is an
    eigenvector of the modular operator with eigenvalue the Gibbs weight ratio —
    `Δ ↑(of C (E_{nm} c)) = (w_n / w_m) • ↑(of C (E_{nm} c))`.
    Route: `towerModularOp_of` (Δ acts as `modAut ρ` on the core) + ID1's
    `modAut_gibbsDensity_single` + the scalar push `towerOf_smul_coe`. -/
theorem towerModularOp_of_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    towerModularOp L ω β
        ⟨((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β),
          of_mem_towerModularDom L ω β C (Matrix.single n m c)⟩
      = ((gibbsWeight L C ω β n / gibbsWeight L C ω β m : ℝ) : ℂ)
        • ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  rw [towerModularOp_of L ω β C (Matrix.single n m c),
    modAut_gibbsDensity_single L ω β C n m c]
  exact towerOf_smul_coe L ω β C _ _

/-! ### ★ The eigenvector transport Δ → R -/

/-- **★ THE EIGENVECTOR TRANSPORT Δ → R**: a Δ-eigenvector with strictly positive
    eigenvalue is an R-eigenvector — `Δ⟨x, hx⟩ = δ • x` with `0 < δ` gives
    `R x = (1+δ)⁻¹ • x`. The subtype-smul pattern at `y := (1+δ)⁻¹ • x`:
    `↑y + Δy = ((1+δ)⁻¹ + (1+δ)⁻¹·δ) • x = x` (the field identity, `1+δ ≠ 0` from `hδ`),
    so `towerResolvent_one_add` reads off `R x = ↑y`. -/
theorem towerResolvent_of_eigen {x : TowerGNS L ω β}
    (hx : x ∈ towerModularDom L ω β) {δ : ℝ} (hδ : 0 < δ)
    (hΔ : towerModularOp L ω β ⟨x, hx⟩ = (δ : ℂ) • x) :
    towerResolvent L ω β x = (((1 + δ)⁻¹ : ℝ) : ℂ) • x := by
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  have hδℂ : (1 : ℂ) + (δ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr h1δ.ne'
  set r : ℂ := (((1 + δ)⁻¹ : ℝ) : ℂ) with hr
  have hymem : r • x ∈ towerModularDom L ω β :=
    Submodule.smul_mem _ r hx
  have hz : (⟨r • x, hymem⟩ : (towerModularOp L ω β).domain)
      = r • (⟨x, hx⟩ : (towerModularOp L ω β).domain) := Subtype.ext rfl
  have hΔy : towerModularOp L ω β ⟨r • x, hymem⟩ = (r * (δ : ℂ)) • x := by
    rw [hz, LinearPMap.map_smul, hΔ, smul_smul]
  have hcoef : r + r * (δ : ℂ) = 1 := by
    rw [hr, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one, ← mul_one_add]
    exact inv_mul_cancel₀ hδℂ
  have hsum : (r • x) + towerModularOp L ω β ⟨r • x, hymem⟩ = x := by
    rw [hΔy, ← add_smul, hcoef, one_smul]
  have hres : towerResolvent L ω β
        ((r • x) + towerModularOp L ω β ⟨r • x, hymem⟩) = r • x :=
    towerResolvent_one_add L ω β ⟨r • x, hymem⟩
  rw [hsum] at hres
  exact hres

/-! ### The R-eigenvector equation on the matrix units -/

/-- **THE GNS R-EIGENVECTOR EQUATION**: the coerced pure matrix-unit component is an
    eigenvector of the resolvent with eigenvalue `(1 + w_n/w_m)⁻¹` — the Δ-eigenvector
    equation (`towerModularOp_of_single`) transported through `towerResolvent_of_eigen`
    at `δ = w_n/w_m > 0` (ID1's `gibbsWeight_div_pos`). This is the input to ID3's
    `borelFC` symbol evaluation `(1−r)/r = δ` at `r = (1+δ)⁻¹`. -/
theorem towerResolvent_of_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    towerResolvent L ω β
        ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β)
      = (((1 + gibbsWeight L C ω β n / gibbsWeight L C ω β m)⁻¹ : ℝ) : ℂ)
        • ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) :
            TowerGNS L ω β) :=
  towerResolvent_of_eigen L ω β
    (of_mem_towerModularDom L ω β C (Matrix.single n m c))
    (gibbsWeight_div_pos L ω β C n m)
    (towerModularOp_of_single L ω β C n m c)

end QIQTH.TowerGNS
