/-
  THE REPRESENTATION R3 (THE_REPRESENTATION_PLAN.md) — THE PRE-HILBERT SPACE.

  `TowerPre L ω β := ⨁ (C : Finset M), DiamondAlg L C` — the direct sum of ALL finite corners,
  with the stabilized pairing as a (DELIBERATELY SEMIDEFINITE) pre-inner product: the null
  vectors `of C' (ι a) − of C a` ARE the direct-limit gluing, and Mathlib's chain
  (`PreInnerProductSpace.Core` → `InnerProductSpace.Core.toSeminormedAddCommGroup` →
  `InnerProductSpace.ofCore` → `UniformSpace.Completion`) is seminorm-tolerant end to end, so
  the completion `TowerGNS` is a genuine Hilbert space with no quotient ever taken. The instance
  architecture copies Mathlib's `GelfandNaimarkSegal.lean` (binding verdict): the synonym
  carries the state parameters (ω, β) exactly as `PreGNS` carries `f`, so the seminorm instance
  is state-dependent and never leaks to the bare direct sum.

  LEAN ARCHITECTURE NOTE: all working lemmas live at the RAW `⨁` type (`rawInner`, `collapseRaw`,
  `rawInner_eq_collapse`) — mixing the synonym's `inferInstanceAs` instances with the direct
  sum's own instances inside `rw`-based proofs causes instance-path mismatches; the Core fields
  DELEGATE to the raw lemmas by definitional equality (application position only, never rw).

  The analytic engine is STAGE COLLAPSE: `collapseRaw K` embeds every component supported under
  K into the single corner K, and `rawInner_eq_collapse` identifies the tower inner product with
  the per-stage GNS form there — positivity is R2's stage positivity.
-/
import Mathlib
import QIQTH.TowerGNS.StageInner

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The pairing slot laws (R2 lemmas pushed through the embeddings) -/

theorem pairInner_add_left (C C' : Finset M) (a₁ a₂ : DiamondAlg L C) (b : DiamondAlg L C') :
    pairInner L ω β C C' (a₁ + a₂) b
      = pairInner L ω β C C' a₁ b + pairInner L ω β C C' a₂ b := by
  rw [pairInner, pairInner, pairInner, cornerEmbed_add, gnsInner_add_left]

theorem pairInner_add_right (C C' : Finset M) (a : DiamondAlg L C) (b₁ b₂ : DiamondAlg L C') :
    pairInner L ω β C C' a (b₁ + b₂)
      = pairInner L ω β C C' a b₁ + pairInner L ω β C C' a b₂ := by
  rw [pairInner, pairInner, pairInner, cornerEmbed_add, gnsInner_add_right]

theorem pairInner_smul_left (C C' : Finset M) (r : ℂ) (a : DiamondAlg L C)
    (b : DiamondAlg L C') :
    pairInner L ω β C C' (r • a) b = starRingEnd ℂ r * pairInner L ω β C C' a b := by
  rw [pairInner, pairInner, cornerEmbed_smul, gnsInner_smul_left]

theorem pairInner_conj_symm (C C' : Finset M) (a : DiamondAlg L C) (b : DiamondAlg L C') :
    starRingEnd ℂ (pairInner L ω β C' C b a) = pairInner L ω β C C' a b := by
  rw [pairInner_embed L ω β C' C (C ⊔ C') Finset.subset_union_right Finset.subset_union_left
    b a, gnsInner_conj_symm]
  rfl

/-! ### The raw layer (everything at `⨁` — no synonym instances in sight) -/

/-- The pairing at fixed stages, bundled additively in the second slot. -/
noncomputable def pairHom (C C' : Finset M) (a : DiamondAlg L C) : DiamondAlg L C' →+ ℂ :=
  AddMonoidHom.mk' (fun b => pairInner L ω β C C' a b) (pairInner_add_right L ω β C C' a)

/-- The tower inner product at the raw direct sum, bundled additively in both slots (A3:
    `toAddMonoid` twice, no `DFinsupp.sum` anywhere). -/
noncomputable def rawInner :
    (⨁ C : Finset M, DiamondAlg L C) →+ ((⨁ C : Finset M, DiamondAlg L C) →+ ℂ) :=
  DirectSum.toAddMonoid fun C =>
    AddMonoidHom.mk'
      (fun a => DirectSum.toAddMonoid fun C' => pairHom L ω β C C' a)
      (fun a₁ a₂ => DirectSum.addHom_ext fun C' b => by
        show (DirectSum.toAddMonoid fun C' => pairHom L ω β C C' (a₁ + a₂))
              (DirectSum.of _ C' b)
            = (DirectSum.toAddMonoid fun C' => pairHom L ω β C C' a₁)
                (DirectSum.of _ C' b)
              + (DirectSum.toAddMonoid fun C' => pairHom L ω β C C' a₂)
                (DirectSum.of _ C' b)
        rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        exact pairInner_add_left L ω β C C' a₁ a₂ b)

@[simp] theorem rawInner_of_of (C C' : Finset M) (a : DiamondAlg L C) (b : DiamondAlg L C') :
    rawInner L ω β (DirectSum.of _ C a) (DirectSum.of _ C' b)
      = pairInner L ω β C C' a b := by
  rw [rawInner, DirectSum.toAddMonoid_of, AddMonoidHom.mk'_apply, DirectSum.toAddMonoid_of]
  rfl

/-- **The stage collapse** (raw): project every component supported under `K` into the corner
    `K` (components not under `K` are killed — used only under support hypotheses). -/
noncomputable def collapseRaw (K : Finset M) :
    (⨁ C : Finset M, DiamondAlg L C) →ₗ[ℂ] DiamondAlg L K :=
  DirectSum.toModule ℂ (Finset M) (DiamondAlg L K) fun C =>
    if h : C ⊆ K then cornerEmbedₗ L C K h else 0

@[simp] theorem collapseRaw_of_le {K C : Finset M} (h : C ⊆ K) (a : DiamondAlg L C) :
    collapseRaw L K (DirectSum.of _ C a) = cornerEmbed L C K h a := by
  rw [← DirectSum.lof_eq_of ℂ, collapseRaw]
  erw [DirectSum.toModule_lof]
  rw [dif_pos h]
  rfl

@[simp] theorem collapseRaw_of_not_le {K C : Finset M} (h : ¬ C ⊆ K) (a : DiamondAlg L C) :
    collapseRaw L K (DirectSum.of _ C a) = 0 := by
  rw [← DirectSum.lof_eq_of ℂ, collapseRaw]
  erw [DirectSum.toModule_lof]
  rw [dif_neg h]
  rfl

theorem gnsInner_sum_left {ι : Type*} (K : Finset M) (s : Finset ι)
    (f : ι → DiamondAlg L K) (y : DiamondAlg L K) :
    gnsInner L ω β K (∑ i ∈ s, f i) y = ∑ i ∈ s, gnsInner L ω β K (f i) y :=
  map_sum (AddMonoidHom.mk' (fun x => gnsInner L ω β K x y)
    (fun a b => gnsInner_add_left L ω β K a b y)) f s

theorem gnsInner_sum_right {ι : Type*} (K : Finset M) (x : DiamondAlg L K) (s : Finset ι)
    (f : ι → DiamondAlg L K) :
    gnsInner L ω β K x (∑ i ∈ s, f i) = ∑ i ∈ s, gnsInner L ω β K x (f i) :=
  map_sum (AddMonoidHom.mk' (gnsInner L ω β K x)
    (gnsInner_add_right L ω β K x)) f s

/-- **R3 KEY — the inner product collapses to a single stage** (raw): if all components of `x`
    and `y` live under `K`, the tower inner product is the per-stage GNS form of the
    collapses. -/
theorem rawInner_eq_collapse (K : Finset M) (x y : ⨁ C : Finset M, DiamondAlg L C)
    (hx : ∀ C, x C ≠ 0 → C ⊆ K) (hy : ∀ C, y C ≠ 0 → C ⊆ K) :
    rawInner L ω β x y
      = gnsInner L ω β K (collapseRaw L K x) (collapseRaw L K y) := by
  classical
  have hxsum : x = ∑ C ∈ DFinsupp.support x, DirectSum.of _ C (x C) :=
    (DirectSum.sum_support_of x).symm
  have hysum : y = ∑ C ∈ DFinsupp.support y, DirectSum.of _ C (y C) :=
    (DirectSum.sum_support_of y).symm
  rw [hxsum, hysum]
  rw [map_sum (rawInner L ω β) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
  rw [AddMonoidHom.finsetSum_apply]
  rw [map_sum (collapseRaw L K) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
  rw [map_sum (collapseRaw L K) (fun C => DirectSum.of _ C (y C)) (DFinsupp.support y)]
  rw [gnsInner_sum_left]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCK : C ⊆ K := hx C (DFinsupp.mem_support_iff.mp hC)
  rw [map_sum (rawInner L ω β (DirectSum.of _ C (x C)))
    (fun C' => DirectSum.of _ C' (y C')) (DFinsupp.support y)]
  rw [gnsInner_sum_right]
  refine Finset.sum_congr rfl fun C' hC' => ?_
  have hC'K : C' ⊆ K := hy C' (DFinsupp.mem_support_iff.mp hC')
  rw [rawInner_of_of, collapseRaw_of_le L hCK, collapseRaw_of_le L hC'K,
    pairInner_embed L ω β C C' K hCK hC'K]

/-! ### The raw Core laws -/

theorem rawInner_conj_symm (x y : ⨁ C : Finset M, DiamondAlg L C) :
    starRingEnd ℂ (rawInner L ω β y x) = rawInner L ω β x y := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (rawInner L ω β y), map_zero (rawInner L ω β),
      AddMonoidHom.zero_apply, map_zero]
  | of C a =>
    induction y using DirectSum.induction_on with
    | zero =>
      rw [map_zero (rawInner L ω β), AddMonoidHom.zero_apply,
        map_zero (rawInner L ω β (DirectSum.of _ C a)), map_zero]
    | of C' b => rw [rawInner_of_of, rawInner_of_of]; exact pairInner_conj_symm L ω β C C' a b
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (rawInner L ω β), AddMonoidHom.add_apply,
        map_add (rawInner L ω β (DirectSum.of _ C a)), map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (rawInner L ω β), AddMonoidHom.add_apply,
      map_add (rawInner L ω β y), map_add, h₁, h₂]

theorem rawInner_smul_left (x y : ⨁ C : Finset M, DiamondAlg L C) (r : ℂ) :
    rawInner L ω β (r • x) y = starRingEnd ℂ r * rawInner L ω β x y := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [smul_zero, map_zero (rawInner L ω β), AddMonoidHom.zero_apply, mul_zero]
  | of C a =>
    have hsm : r • DirectSum.of (fun C : Finset M => DiamondAlg L C) C a
        = DirectSum.of (fun C : Finset M => DiamondAlg L C) C (r • a) := by
      rw [← DirectSum.lof_eq_of ℂ, ← DirectSum.lof_eq_of ℂ, map_smul]
    rw [hsm]
    induction y using DirectSum.induction_on with
    | zero =>
      rw [map_zero (rawInner L ω β (DirectSum.of _ C (r • a))),
        map_zero (rawInner L ω β (DirectSum.of _ C a)), mul_zero]
    | of C' b =>
      rw [rawInner_of_of, rawInner_of_of]
      exact pairInner_smul_left L ω β C C' r a b
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (rawInner L ω β (DirectSum.of _ C (r • a))), h₁, h₂,
        map_add (rawInner L ω β (DirectSum.of _ C a)), mul_add]
  | add x₁ x₂ h₁ h₂ =>
    rw [smul_add, map_add (rawInner L ω β), AddMonoidHom.add_apply, h₁, h₂,
      map_add (rawInner L ω β), AddMonoidHom.add_apply, mul_add]

theorem rawInner_add_left (x y z : ⨁ C : Finset M, DiamondAlg L C) :
    rawInner L ω β (x + y) z = rawInner L ω β x z + rawInner L ω β y z := by
  rw [map_add (rawInner L ω β), AddMonoidHom.add_apply]

theorem rawInner_self_re_nonneg (x : ⨁ C : Finset M, DiamondAlg L C) :
    0 ≤ RCLike.re (rawInner L ω β x x) := by
  classical
  set K : Finset M := (DFinsupp.support x).sup id with hK
  have hx : ∀ C, x C ≠ 0 → C ⊆ K := fun C hC =>
    Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hC)
  rw [rawInner_eq_collapse L ω β K x x hx hx]
  exact (RCLike.nonneg_iff.mp (gnsInner_self_nonneg L ω β K (collapseRaw L K x))).1

/-! ### The synonym, the Core, and the instances (GNS-file order — the binding verdict) -/

set_option linter.unusedVariables false in
/-- **The tower pre-Hilbert space**: the direct sum of all finite corners. The state parameters
    ride in the SYNONYM (as `PreGNS` carries `f`) so the seminorm instance is state-dependent
    and never leaks to the bare direct sum. -/
@[nolint unusedArguments]
def TowerPre (L : LinkDims M) (ω : M → ℝ) (β : ℝ) : Type _ :=
  ⨁ C : Finset M, DiamondAlg L C

noncomputable instance : AddCommGroup (TowerPre L ω β) :=
  inferInstanceAs (AddCommGroup (⨁ C : Finset M, DiamondAlg L C))

noncomputable instance : Module ℂ (TowerPre L ω β) :=
  inferInstanceAs (Module ℂ (⨁ C : Finset M, DiamondAlg L C))

/-- The canonical inclusion of a corner component into the synonym. -/
noncomputable def towerOf (C : Finset M) (a : DiamondAlg L C) : TowerPre L ω β :=
  DirectSum.of (fun C : Finset M => DiamondAlg L C) C a

/-- The tower pre-inner-product Core — DELIBERATELY semidefinite (the null directions are the
    direct-limit gluing; the completion kills them). All fields delegate to the raw layer by
    definitional equality. -/
noncomputable abbrev towerCore : PreInnerProductSpace.Core ℂ (TowerPre L ω β) where
  inner x y := rawInner L ω β x y
  conj_inner_symm x y := rawInner_conj_symm L ω β x y
  re_inner_nonneg x := rawInner_self_re_nonneg L ω β x
  add_left x y z := rawInner_add_left L ω β x y z
  smul_left x y r := rawInner_smul_left L ω β x y r

noncomputable instance : SeminormedAddCommGroup (TowerPre L ω β) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := towerCore L ω β)

noncomputable instance : InnerProductSpace ℂ (TowerPre L ω β) :=
  InnerProductSpace.ofCore (towerCore L ω β)

/-- **THE HILBERT SPACE OF THE TOWER**: the completion of the semidefinite pre-space — the
    degenerate directions die here, with no quotient ever taken. -/
abbrev TowerGNS (L : LinkDims M) (ω : M → ℝ) (β : ℝ) : Type _ :=
  UniformSpace.Completion (TowerPre L ω β)

theorem towerInner_def (x y : TowerPre L ω β) :
    ⟪x, y⟫_ℂ = rawInner L ω β x y := rfl

/-- The inner product of two pure components is the stabilized pairing. -/
theorem towerInner_of_of (C C' : Finset M) (a : DiamondAlg L C) (b : DiamondAlg L C') :
    ⟪towerOf L ω β C a, towerOf L ω β C' b⟫_ℂ = pairInner L ω β C C' a b := by
  rw [towerInner_def]
  exact rawInner_of_of L ω β C C' a b

end QIQTH.TowerGNS
