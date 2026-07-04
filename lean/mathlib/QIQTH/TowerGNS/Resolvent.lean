/-
  THE RESOLVENT CAMPAIGN — R1 (THE_RESOLVENT_PLAN.md) — **the resolvent
  `towerResolvent = (1+Δ)⁻¹` as an everywhere-defined CLM contraction.**

  THE VON NEUMANN campaign left Δ self-adjoint with `ran (1+Δ) = ⊤`
  (`towerModularOp_one_add_surjective`, VN4) and the bound `‖x‖ ≤ ‖x+Δx‖`
  (`norm_le_norm_add_towerModularOp`, VN5). This increment inverts `1+Δ` WITHOUT any
  CLM-inverse machinery:

  * CHOICE HYGIENE: `towerResolventAux h := Classical.choose (surjectivity at h)` plus the
    ONE spec lemma `↑(aux h) + Δ(aux h) = h` — the choice is never unfolded again.
  * UNIQUENESS (`one_add_modularOp_injOn`): `x + Δx = y + Δy → x = y` — apply the VN5
    bound to `x − y` (a domain element by `sub_mem`; `LinearPMap.map_sub` splits the
    value), whose `1+Δ`-image vanishes, so `‖x−y‖ ≤ 0`.
  * LINEARITY from uniqueness: `aux (h₁+h₂)` and `aux h₁ + aux h₂` both solve the defining
    equation at `h₁+h₂` (similarly ℂ-smul) — packaged as `towerResolventLM`, then
    `towerResolvent := LinearMap.mkContinuous _ 1` (the a-priori VN5 bound IS the
    operator bound: `‖R h‖ = ‖↑(aux h)‖ ≤ ‖↑(aux h) + Δ(aux h)‖ = ‖h‖`).
  * CONSUMER API (aux never mentioned downstream): membership `R h ∈ dom Δ`;
    `R h + Δ(R h) = h`; `R(x + Δx) = x`; kernel triviality of R; range R = dom Δ (dense);
    `Δ∘R = 1−R` and `R(Δx) = x − Rx`.

  NOT here (deliberately): self-adjointness/positivity/spectrum of R (R2), the Borel
  functional calculus and Δ^{it} (R4–R6), Δ^{1/2}, J, KMS, any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.ModularSelfAdjoint

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### R1.1 — choice hygiene: the witness and the ONE spec lemma

    `towerResolventAux` is `Classical.choose` of VN4's surjectivity; the spec lemma below
    is the ONLY fact ever extracted from the choice — never unfold `towerResolventAux`
    after this point. -/

/-- **The resolvent witness** (choice hygiene): for each `h`, THE domain element `x` with
`x + Δx = h`, chosen from VN4's surjectivity `ran (1+Δ) = ⊤`. Consumed ONLY through
`towerResolventAux_spec`; downstream files use `towerResolvent` and its API, never this. -/
noncomputable def towerResolventAux (h : TowerGNS L ω β) :
    (towerModularOp L ω β).domain :=
  Classical.choose (towerModularOp_one_add_surjective L ω β h)

/-- **THE ONE SPEC LEMMA for the witness**: `↑(aux h) + Δ (aux h) = h` — the defining
equation of the resolvent, discharged from the choice exactly once. -/
theorem towerResolventAux_spec (h : TowerGNS L ω β) :
    (towerResolventAux L ω β h : TowerGNS L ω β)
      + towerModularOp L ω β (towerResolventAux L ω β h) = h :=
  Classical.choose_spec (towerModularOp_one_add_surjective L ω β h)

/-! ### R1.2 — uniqueness: 1 + Δ is injective on its domain

    The VN5 bound `‖x‖ ≤ ‖x + Δx‖` applied to the difference `x − y` (a domain element by
    `sub_mem`); `LinearPMap.map_sub` splits the value; the hypothesis kills the right side. -/

/-- **UNIQUENESS**: `x + Δx = y + Δy → x = y` — the solution of the defining equation is
unique, because the VN5 resolvent bound at `x − y` gives
`‖x − y‖ ≤ ‖(x − y) + Δ(x − y)‖ = ‖(x + Δx) − (y + Δy)‖ = 0`. The injectivity that turns
the choice witness into a (linear) FUNCTION of `h`. -/
theorem one_add_modularOp_injOn (x y : (towerModularOp L ω β).domain)
    (h : (x : TowerGNS L ω β) + towerModularOp L ω β x
      = (y : TowerGNS L ω β) + towerModularOp L ω β y) : x = y := by
  have hle := norm_le_norm_add_towerModularOp L ω β (x - y)
  rw [LinearPMap.map_sub, Submodule.coe_sub] at hle
  have hzero : (x : TowerGNS L ω β) - (y : TowerGNS L ω β)
      + (towerModularOp L ω β x - towerModularOp L ω β y) = 0 := by
    rw [sub_add_sub_comm, h, sub_self]
  rw [hzero, norm_zero] at hle
  have h0 : (x : TowerGNS L ω β) - (y : TowerGNS L ω β) = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact Subtype.ext (sub_eq_zero.mp h0)

/-! ### R1.3 — linearity of the witness, from uniqueness

    `aux (h₁ + h₂)` and `aux h₁ + aux h₂` both solve the defining equation at `h₁ + h₂`
    (`LinearPMap.map_add` + regrouping); uniqueness identifies them. Same for ℂ-smul. -/

/-- **Additivity of the witness**: `aux (h₁ + h₂) = aux h₁ + aux h₂` — both sides solve
`x + Δx = h₁ + h₂` (regroup by `add_add_add_comm` and apply the spec twice), so uniqueness
identifies them. -/
theorem towerResolventAux_add (h₁ h₂ : TowerGNS L ω β) :
    towerResolventAux L ω β (h₁ + h₂)
      = towerResolventAux L ω β h₁ + towerResolventAux L ω β h₂ := by
  have key : ((towerResolventAux L ω β h₁ + towerResolventAux L ω β h₂ :
        (towerModularOp L ω β).domain) : TowerGNS L ω β)
      + towerModularOp L ω β
          (towerResolventAux L ω β h₁ + towerResolventAux L ω β h₂)
      = h₁ + h₂ := by
    rw [LinearPMap.map_add, Submodule.coe_add, add_add_add_comm,
      towerResolventAux_spec L ω β h₁, towerResolventAux_spec L ω β h₂]
  exact one_add_modularOp_injOn L ω β _ _
    ((towerResolventAux_spec L ω β (h₁ + h₂)).trans key.symm)

/-- **ℂ-homogeneity of the witness**: `aux (c • h) = c • aux h` — the smul of a solution
solves the smul equation (`LinearPMap.map_smul` + `smul_add`), so uniqueness identifies
them. NO conjugation: Δ is ℂ-LINEAR (M4.3), hence so is its resolvent. -/
theorem towerResolventAux_smul (c : ℂ) (h : TowerGNS L ω β) :
    towerResolventAux L ω β (c • h) = c • towerResolventAux L ω β h := by
  have key : ((c • towerResolventAux L ω β h :
        (towerModularOp L ω β).domain) : TowerGNS L ω β)
      + towerModularOp L ω β (c • towerResolventAux L ω β h)
      = c • h := by
    rw [LinearPMap.map_smul, Submodule.coe_smul, ← smul_add,
      towerResolventAux_spec L ω β h]
  exact one_add_modularOp_injOn L ω β _ _
    ((towerResolventAux_spec L ω β (c • h)).trans key.symm)

/-! ### R1.4 — the resolvent CLM: `towerResolvent = (1+Δ)⁻¹`

    The linear package of the witness, made continuous by `LinearMap.mkContinuous` with
    constant 1 — the VN5 bound `‖↑(aux h)‖ ≤ ‖↑(aux h) + Δ(aux h)‖ = ‖h‖` IS the operator
    bound, a priori (no open-mapping, no CLM-inverse machinery). -/

/-- The resolvent as a ℂ-linear map (the linearity of the witness, packaged). Internal:
downstream uses `towerResolvent`. -/
noncomputable def towerResolventLM : TowerGNS L ω β →ₗ[ℂ] TowerGNS L ω β where
  toFun h := (towerResolventAux L ω β h : TowerGNS L ω β)
  map_add' h₁ h₂ := by
    rw [towerResolventAux_add L ω β h₁ h₂]
    exact Submodule.coe_add _ _
  map_smul' c h := by
    rw [towerResolventAux_smul L ω β c h]
    exact Submodule.coe_smul _ _

/-- **★ THE RESOLVENT `(1+Δ)⁻¹` ★** — an everywhere-defined continuous linear map with
norm bound 1 (a CONTRACTION), inverting `1 + Δ`: `towerResolvent h` is THE solution `x` of
`x + Δx = h`. The boundedness is the a-priori VN5 resolvent bound — no open-mapping
theorem, no invertibility machinery. Self-adjointness, positivity, `0 ≤ R ≤ 1`, and the
spectrum in `[0,1]` are R2; the Borel calculus and `Δ^{it}` are R4–R6. -/
noncomputable def towerResolvent : TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  LinearMap.mkContinuous (towerResolventLM L ω β) 1 (fun h => by
    rw [one_mul]
    show ‖(towerResolventAux L ω β h : TowerGNS L ω β)‖ ≤ ‖h‖
    have hb := norm_le_norm_add_towerModularOp L ω β (towerResolventAux L ω β h)
    rw [towerResolventAux_spec L ω β h] at hb
    exact hb)

/-- The spec of the CLM package: `towerResolvent h = ↑(aux h)` — the LAST mention of
`towerResolventAux`; every consumer below (and every downstream file) works from
`towerResolvent` alone. -/
theorem towerResolvent_apply (h : TowerGNS L ω β) :
    towerResolvent L ω β h = (towerResolventAux L ω β h : TowerGNS L ω β) :=
  rfl

/-! ### R1.5 — the consumer API

    Everything below is stated in terms of `towerResolvent` only. Membership is stated on
    `towerModularDom` (the form of `mem_towerModularDom` and its extractors in M4;
    `(towerModularOp L ω β).domain = towerModularDom L ω β` is `rfl` —
    `towerModularOp_domain`). -/

/-- **The pointwise contraction bound**: `‖towerResolvent h‖ ≤ ‖h‖`. -/
theorem norm_towerResolvent_apply_le (h : TowerGNS L ω β) :
    ‖towerResolvent L ω β h‖ ≤ ‖h‖ := by
  rw [towerResolvent_apply]
  have hb := norm_le_norm_add_towerModularOp L ω β (towerResolventAux L ω β h)
  rw [towerResolventAux_spec L ω β h] at hb
  exact hb

/-- **MEMBERSHIP**: the resolvent lands in the domain of Δ — `towerResolvent h` carries
the two-layer membership `↑(aux h).2` (stated on `towerModularDom`, the M4 form). -/
theorem towerResolvent_mem (h : TowerGNS L ω β) :
    towerResolvent L ω β h ∈ towerModularDom L ω β := by
  rw [towerResolvent_apply]
  exact (towerResolventAux L ω β h).2

/-- **THE DEFINING EQUATION, consumer form**: `R h + Δ (R h) = h` — the spec transported
to the `⟨towerResolvent h, towerResolvent_mem⟩` presentation through the congr adapter
(never rw under a subtype). -/
theorem towerResolvent_add_modularOp (h : TowerGNS L ω β) :
    towerResolvent L ω β h
      + towerModularOp L ω β
          ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩
      = h := by
  have hcongr : towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩
      = towerModularOp L ω β (towerResolventAux L ω β h) :=
    towerModularOp_congr L ω β (towerResolvent_mem L ω β h)
      (towerResolventAux L ω β h).2 (towerResolvent_apply L ω β h)
  rw [hcongr, towerResolvent_apply]
  exact towerResolventAux_spec L ω β h

/-- **THE LEFT-INVERSE EQUATION**: `R (x + Δx) = x` for `x` in the domain of Δ — from
uniqueness (`x` and `aux (x + Δx)` both solve the defining equation at `x + Δx`). Together
with `towerResolvent_add_modularOp` this says `R = (1+Δ)⁻¹` exactly. -/
theorem towerResolvent_one_add (x : (towerModularOp L ω β).domain) :
    towerResolvent L ω β ((x : TowerGNS L ω β) + towerModularOp L ω β x)
      = (x : TowerGNS L ω β) := by
  have haux : towerResolventAux L ω β
        ((x : TowerGNS L ω β) + towerModularOp L ω β x) = x :=
    one_add_modularOp_injOn L ω β _ x
      (towerResolventAux_spec L ω β
        ((x : TowerGNS L ω β) + towerModularOp L ω β x))
  rw [towerResolvent_apply, haux]

/-- **KERNEL TRIVIALITY of the resolvent**: `R h = 0 → h = 0` — if the solution vanishes
then the defining equation reads `0 + Δ0 = h`, and `Δ 0 = 0` (`LinearPMap.map_zero`). The
input to the R3/R5 spectral statement `E({0}) = 0` (no spectral weight at the junk
point). -/
theorem towerResolvent_injective {h : TowerGNS L ω β}
    (h0 : towerResolvent L ω β h = 0) : h = 0 := by
  have haux : towerResolventAux L ω β h = 0 := by
    refine Subtype.ext ?_
    rw [← towerResolvent_apply L ω β h, h0]
    rfl
  have hspec := towerResolventAux_spec L ω β h
  rw [haux, LinearPMap.map_zero] at hspec
  simpa using hspec.symm

/-- **THE RANGE**: `ran R = dom Δ` — the resolvent lands in the domain
(`towerResolvent_mem`) and hits all of it (`x = R (x + Δx)`, the left-inverse
equation). -/
theorem range_towerResolvent :
    Set.range (towerResolvent L ω β)
      = (towerModularDom L ω β : Set (TowerGNS L ω β)) := by
  ext v
  constructor
  · rintro ⟨h, rfl⟩
    exact towerResolvent_mem L ω β h
  · intro hv
    exact ⟨v + towerModularOp L ω β ⟨v, hv⟩,
      towerResolvent_one_add L ω β ⟨v, hv⟩⟩

/-- **DENSE RANGE**: `ran R = dom Δ` is dense (M5.5) — the input to the R2/R4 spectral
side (a self-adjoint contraction with dense range and trivial kernel). -/
theorem dense_range_towerResolvent :
    Dense (Set.range (towerResolvent L ω β)) := by
  rw [range_towerResolvent]
  exact dense_towerModularDom L ω β

/-- **`Δ ∘ R = 1 − R`**: `Δ (R h) = h − R h` — the defining equation rearranged; the
identity through which every unbounded statement about Δ becomes a bounded statement
about R (the whole point of the resolvent). -/
theorem modularOp_towerResolvent (h : TowerGNS L ω β) :
    towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩
      = h - towerResolvent L ω β h := by
  rw [eq_sub_iff_add_eq, add_comm]
  exact towerResolvent_add_modularOp L ω β h

/-- **`R ∘ Δ = 1 − R` on dom Δ**: `R (Δ x) = x − R x` — write `Δx = (x + Δx) − x`, split
by linearity of the CLM, and apply the left-inverse equation. -/
theorem towerResolvent_modularOp (x : (towerModularOp L ω β).domain) :
    towerResolvent L ω β (towerModularOp L ω β x)
      = (x : TowerGNS L ω β)
        - towerResolvent L ω β (x : TowerGNS L ω β) := by
  have hsplit : towerModularOp L ω β x
      = ((x : TowerGNS L ω β) + towerModularOp L ω β x)
        - (x : TowerGNS L ω β) := by abel
  rw [hsplit, map_sub, towerResolvent_one_add L ω β x]

end QIQTH.TowerGNS
