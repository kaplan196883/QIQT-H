/-
  THE RESOLVENT CAMPAIGN — R6 (THE_RESOLVENT_PLAN.md) — **`Δ^{it}` commutes with `R` and
  with `Δ`, preserving `dom Δ` — the spectral flow is consistent with the modular
  operator; still NO claim `U = towerFlow`.**

  R4/R5 delivered `U_t = towerModUnitary t = u_t(R)`, a strongly continuous one-parameter
  unitary group fixing `Ω`.  This file proves the COMPATIBILITY package binding the group
  back to the operator it was built from:

  * **`R = ∫λ dE`** (`towerResolvent_eq_borelFC`) — the R3 generic operator spectral
    theorem `eq_borelFC` instantiated at the resolvent (a one-liner), plus the FC form of
    `1 − R` (`one_sub_towerResolvent_eq_borelFC`, via `boundedFC_sub`).

  * **`[U_t, R] = 0`** (`towerModUnitary_commute_towerResolvent`, `*`/`∘L`/pointwise
    forms) — the verbatim `modUnitary_commute_rvdRC` port: rewrite `R` as `borelFC(coord)`
    and use two `borelFC_mul` applications with the pointwise `mul_comm` of the symbols
    (the local `towerBorelFC_comm`, ported like R4's `towerBorelFC_adjoint` — no
    StandardSubspace coupling).

  * **`U_t (dom Δ) ⊆ dom Δ`** (`towerModUnitary_mapsTo_modularDom`) — since
    `dom Δ = ran R` (R1) and `U_t(Rh) = R(U_t h)`.

  * ★ **`Δ ∘ U_t = U_t ∘ Δ` on `dom Δ`** (`towerModUnitary_commute_modularOp`) — write
    `x = Rh`; both sides equal `U_t h − R(U_t h)` through `Δ∘R = 1−R` (R1) and the
    commutation, with all subtype-membership transport routed through
    `towerModularOp_congr` (never rw under a subtype).

  NOT here (deliberately): `Δ^{1/2}`, `J`, polar decomposition, KMS, Tomita's theorem,
  `towerGen = log Δ`, any claim that `towerModUnitary` equals the transported `towerFlow`
  (the exponential-recovery wall — the named next campaign), any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.ModularUnitary
import QIQTH.Spectral.UnboundedFC

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.SpectralTheorem
open scoped InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### R6.1 — `R = ∫λ dE` and `1 − R = ∫(1−λ) dE`

    The R3 generic operator spectral theorem `eq_borelFC`, instantiated at the resolvent:
    the operator the whole FC tower was built on is itself the FC of the coordinate. -/

/-- **`R = borelFC(coord) = ∫λ dE`** — the R3 generic operator spectral theorem
    (`eq_borelFC`) at `T = towerResolvent`: the resolvent is the bounded Borel FC of the
    coordinate symbol on its own spectrum. -/
theorem towerResolvent_eq_borelFC :
    towerResolvent L ω β
      = borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
          (specCoordFn_measurable (towerResolvent L ω β))
          (specCoordFn_bound_nonneg (towerResolvent L ω β))
          (specCoordFn_norm_le (towerResolvent L ω β)) :=
  eq_borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)

/-- **`1 − R = borelFC(1 − coord)`** — the FC presentation of `1 − R` (which equals
    `Δ∘R` by R1's `modularOp_towerResolvent`): symbol-subtractivity of the bounded FC
    (`boundedFC_sub`) at the constant-`1` symbol and the coordinate. -/
theorem one_sub_towerResolvent_eq_borelFC :
    1 - towerResolvent L ω β
      = borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
          (f := fun r => 1 - specCoordFn (towerResolvent L ω β) r)
          (measurable_const.sub (specCoordFn_measurable (towerResolvent L ω β)))
          (add_nonneg (norm_nonneg (1 : ℂ))
            (specCoordFn_bound_nonneg (towerResolvent L ω β)))
          (fun r => le_trans (norm_sub_le 1 (specCoordFn (towerResolvent L ω β) r))
            (add_le_add le_rfl (specCoordFn_norm_le (towerResolvent L ω β) r))) := by
  have hsub := (PVM_of_selfAdjoint (towerResolvent L ω β)
      (towerResolvent_isSelfAdjoint L ω β)).boundedFC_sub
    (measurable_const :
      Measurable (fun _ : spectrum ℝ (towerResolvent L ω β) => (1 : ℂ)))
    (norm_nonneg (1 : ℂ)) (fun _ => le_rfl)
    (specCoordFn_measurable (towerResolvent L ω β))
    (specCoordFn_bound_nonneg (towerResolvent L ω β))
    (specCoordFn_norm_le (towerResolvent L ω β))
  calc 1 - towerResolvent L ω β
      = borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
            (f := fun _ => (1 : ℂ)) measurable_const (norm_nonneg 1) (fun _ => le_rfl)
        - borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
            (specCoordFn_measurable (towerResolvent L ω β))
            (specCoordFn_bound_nonneg (towerResolvent L ω β))
            (specCoordFn_norm_le (towerResolvent L ω β)) := by
        rw [borelFC_one (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β),
          ← towerResolvent_eq_borelFC L ω β]
    _ = borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
          (f := fun r => 1 - specCoordFn (towerResolvent L ω β) r)
          (measurable_const.sub (specCoordFn_measurable (towerResolvent L ω β)))
          (add_nonneg (norm_nonneg (1 : ℂ))
            (specCoordFn_bound_nonneg (towerResolvent L ω β)))
          (fun r => le_trans (norm_sub_le 1 (specCoordFn (towerResolvent L ω β) r))
            (add_le_add le_rfl (specCoordFn_norm_le (towerResolvent L ω β) r))) :=
        hsub.symm

/-! ### R6.2 — the commutation `[U_t, R] = 0`

    Two values of the bounded Borel FC of the resolvent commute (multiplicativity +
    pointwise `mul_comm` of the symbols) — the local port of `borelFC_comm`
    (StandardSubspaceModularFlow.lean), specialized to `towerResolvent` in R4's
    `towerBorelFC_adjoint` style (no StandardSubspace coupling). -/

/-- **Two values of the bounded Borel FC of the resolvent commute** — from `borelFC_mul`
    (both orders) and the pointwise commutativity of the symbol product. -/
theorem towerBorelFC_comm {f g : spectrum ℝ (towerResolvent L ω β) → ℂ}
    {Cf Cg Cfg Cgf : ℝ}
    (hf : Measurable f) (hC0f : 0 ≤ Cf) (hCf : ∀ r, ‖f r‖ ≤ Cf)
    (hg : Measurable g) (hC0g : 0 ≤ Cg) (hCg : ∀ r, ‖g r‖ ≤ Cg)
    (hfg : Measurable (fun r => f r * g r)) (hC0fg : 0 ≤ Cfg)
    (hCfg : ∀ r, ‖f r * g r‖ ≤ Cfg)
    (hgf : Measurable (fun r => g r * f r)) (hC0gf : 0 ≤ Cgf)
    (hCgf : ∀ r, ‖g r * f r‖ ≤ Cgf) :
    borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β) hf hC0f hCf
        * borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β) hg hC0g hCg
      = borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β) hg hC0g hCg
        * borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
            hf hC0f hCf := by
  rw [← borelFC_mul (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
        hf hC0f hCf hg hC0g hCg hfg hC0fg hCfg,
      ← borelFC_mul (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
        hg hC0g hCg hf hC0f hCf hgf hC0gf hCgf]
  exact borelFC_congr_fun (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
    hfg hC0fg hCfg hgf hC0gf hCgf (funext fun r => mul_comm _ _)

/-- **★ `[U_t, R] = 0` ★** (multiplicative form): the tower modular unitary commutes with
    the resolvent — rewrite `R = borelFC(coord)` (R6.1) and commute the two FC values
    (`towerBorelFC_comm`); the verbatim `modUnitary_commute_rvdRC` port. -/
theorem towerModUnitary_commute_towerResolvent (t : ℝ) :
    towerModUnitary L ω β t * towerResolvent L ω β
      = towerResolvent L ω β * towerModUnitary L ω β t := by
  have hfg : ∀ r, ‖towerModSpecFun L ω β t r * specCoordFn (towerResolvent L ω β) r‖
      ≤ 1 * (‖towerResolvent L ω β‖
          * ‖(1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β)‖) := fun r => by
    rw [norm_mul]
    exact mul_le_mul (towerModSpecFun_norm_le L ω β t r)
      (specCoordFn_norm_le (towerResolvent L ω β) r) (norm_nonneg _) zero_le_one
  have hgf : ∀ r, ‖specCoordFn (towerResolvent L ω β) r * towerModSpecFun L ω β t r‖
      ≤ (‖towerResolvent L ω β‖
          * ‖(1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β)‖) * 1 := fun r => by
    rw [norm_mul]
    exact mul_le_mul (specCoordFn_norm_le (towerResolvent L ω β) r)
      (towerModSpecFun_norm_le L ω β t r) (norm_nonneg _)
      (specCoordFn_bound_nonneg (towerResolvent L ω β))
  have h := towerBorelFC_comm L ω β
    (towerModSpecFun_measurable L ω β t) zero_le_one (towerModSpecFun_norm_le L ω β t)
    (specCoordFn_measurable (towerResolvent L ω β))
    (specCoordFn_bound_nonneg (towerResolvent L ω β))
    (specCoordFn_norm_le (towerResolvent L ω β))
    ((towerModSpecFun_measurable L ω β t).mul
      (specCoordFn_measurable (towerResolvent L ω β)))
    (mul_nonneg zero_le_one (specCoordFn_bound_nonneg (towerResolvent L ω β))) hfg
    ((specCoordFn_measurable (towerResolvent L ω β)).mul
      (towerModSpecFun_measurable L ω β t))
    (mul_nonneg (specCoordFn_bound_nonneg (towerResolvent L ω β)) zero_le_one) hgf
  rwa [← towerResolvent_eq_borelFC L ω β] at h

/-- **`[U_t, R] = 0`** (composition form; `*` and `∘L` agree definitionally on CLMs). -/
theorem towerModUnitary_comp_towerResolvent (t : ℝ) :
    towerModUnitary L ω β t ∘L towerResolvent L ω β
      = towerResolvent L ω β ∘L towerModUnitary L ω β t :=
  towerModUnitary_commute_towerResolvent L ω β t

/-- **`[U_t, R] = 0`** (pointwise): `U_t (R h) = R (U_t h)` — the form R6.3/R6.4
    consume. -/
theorem towerModUnitary_commute_towerResolvent_apply (t : ℝ) (h : TowerGNS L ω β) :
    towerModUnitary L ω β t (towerResolvent L ω β h)
      = towerResolvent L ω β (towerModUnitary L ω β t h) := by
  have hc := DFunLike.congr_fun (towerModUnitary_commute_towerResolvent L ω β t) h
  simpa only [ContinuousLinearMap.mul_apply] using hc

/-! ### R6.3 — `U_t` preserves the domain of Δ

    `dom Δ = ran R` (R1's `range_towerResolvent`), and `U_t(Rh) = R(U_t h) ∈ ran R`. -/

/-- `U_t` maps resolvent values into the domain of Δ: `U_t (R h) ∈ dom Δ` — the
    commutation plus `towerResolvent_mem`. -/
theorem towerModUnitary_mem_towerModularDom (t : ℝ) (h : TowerGNS L ω β) :
    towerModUnitary L ω β t (towerResolvent L ω β h) ∈ towerModularDom L ω β := by
  rw [towerModUnitary_commute_towerResolvent_apply L ω β t h]
  exact towerResolvent_mem L ω β (towerModUnitary L ω β t h)

/-- **★ `U_t (dom Δ) ⊆ dom Δ` ★** — the modular unitary group preserves the domain of the
    modular operator: every `x ∈ dom Δ` is a resolvent value `x = R h`
    (`range_towerResolvent`), and `U_t (R h) = R (U_t h) ∈ ran R = dom Δ`. -/
theorem towerModUnitary_mapsTo_modularDom (t : ℝ) {x : TowerGNS L ω β}
    (hx : x ∈ towerModularDom L ω β) :
    towerModUnitary L ω β t x ∈ towerModularDom L ω β := by
  have hxr : x ∈ Set.range (towerResolvent L ω β) := by
    rw [range_towerResolvent L ω β]
    exact hx
  obtain ⟨h, rfl⟩ := hxr
  exact towerModUnitary_mem_towerModularDom L ω β t h

/-! ### R6.4 — ★ `Δ ∘ U_t = U_t ∘ Δ` on dom Δ ★

    Write `x = R h`.  LHS: `Δ(U_t(Rh)) = Δ(R(U_t h)) = U_t h − R(U_t h)` (commutation
    transported through `towerModularOp_congr`, then `Δ∘R = 1−R` at `U_t h`).  RHS:
    `U_t(Δ(Rh)) = U_t(h − Rh) = U_t h − U_t(Rh) = U_t h − R(U_t h)` (`Δ∘R = 1−R` at `h`,
    linearity, commutation).  All membership transport by `towerModularOp_congr` —
    never rw under a subtype. -/

/-- **★ THE MODULAR UNITARY COMMUTES WITH THE MODULAR OPERATOR ★**:
    `Δ (U_t x) = U_t (Δ x)` for every `x ∈ dom Δ` (with `U_t x ∈ dom Δ` by R6.3) —
    both sides equal `U_t h − R (U_t h)` for the resolvent preimage `x = R h`, through
    `Δ∘R = 1−R` and `[U_t, R] = 0`.  The spectral flow is consistent with the modular
    operator; still NO claim that `U_t` equals the transported `towerFlow`. -/
theorem towerModUnitary_commute_modularOp (t : ℝ) {x : TowerGNS L ω β}
    (hx : x ∈ towerModularDom L ω β) :
    towerModularOp L ω β
        ⟨towerModUnitary L ω β t x, towerModUnitary_mapsTo_modularDom L ω β t hx⟩
      = towerModUnitary L ω β t (towerModularOp L ω β ⟨x, hx⟩) := by
  have hxr : x ∈ Set.range (towerResolvent L ω β) := by
    rw [range_towerResolvent L ω β]
    exact hx
  obtain ⟨h, rfl⟩ := hxr
  -- LHS: `Δ(U_t(Rh)) = Δ(R(U_t h)) = U_t h − R(U_t h)`
  have hL : towerModularOp L ω β
        ⟨towerModUnitary L ω β t (towerResolvent L ω β h),
          towerModUnitary_mapsTo_modularDom L ω β t hx⟩
      = towerModUnitary L ω β t h
        - towerResolvent L ω β (towerModUnitary L ω β t h) := by
    rw [towerModularOp_congr L ω β
        (towerModUnitary_mapsTo_modularDom L ω β t hx)
        (towerResolvent_mem L ω β (towerModUnitary L ω β t h))
        (towerModUnitary_commute_towerResolvent_apply L ω β t h),
      modularOp_towerResolvent L ω β (towerModUnitary L ω β t h)]
  -- RHS core: `Δ(Rh) = h − Rh` on the given membership presentation
  have hR : towerModularOp L ω β ⟨towerResolvent L ω β h, hx⟩
      = h - towerResolvent L ω β h := by
    rw [towerModularOp_congr L ω β hx (towerResolvent_mem L ω β h) rfl,
      modularOp_towerResolvent L ω β h]
  rw [hL, hR, map_sub, towerModUnitary_commute_towerResolvent_apply L ω β t h]

end QIQTH.TowerGNS
