/-
  THE RESOLVENT CAMPAIGN — R4 (THE_RESOLVENT_PLAN.md) — **the modular symbol and the
  unitary group `Δ^{it} := borelFC` of `((1−r)/r)^{it}` — NO claim this equals `towerFlow`.**

  R2 left the resolvent `R = towerResolvent = (1+Δ)⁻¹` bounded self-adjoint with
  `σ(R) ⊆ [0,1]`.  Since `Δ = (1−R)·R⁻¹` on the spectrum (`δ = (1−r)/r`), the modular
  unitary group is the bounded Borel functional calculus of `R` at the symbol

      `towerModChar t r = exp(i·t·log((1−r)/r))`   on `r ∈ (0,1)`,  `= 1` outside.

  This is the line-by-line port of the compiled `modChar`/`modUnitary` template
  (StandardSubspaceModularFlow.lean) with `(Ioo 0 1)` and `log((1−r)/r)` in place of
  `(Ioo 0 2)` and `log((2−r)/r)`, and `towerResolvent` in place of `rvdRC`:

  * THE SYMBOL: junk value `1` outside `(0,1)` makes ALL group laws pointwise-global on ℝ
    (no spectrum facts consumed): `‖u_t‖ = 1`, `u_0 = 1`, `u_{s+t} = u_s·u_t`,
    `conj u_t = u_{−t}`, plus Borel measurability.  The `exp(I·t·(real))` expSymbol shape
    is kept EXACTLY (R8's Stone-derivative instantiation depends on it).
  * THE GROUP: `towerModUnitary t := borelFC R (symbol)` with `U_0 = 1` (unitality),
    `U_{s+t} = U_s ∘L U_t` (`borelFC_mul`), `U_t⋆ = U_{−t}` (`Φ(f)⋆ = Φ(conj f)` from
    `bilinDiag_conj_symm`), unitarity, the isometry `‖U_t ξ‖ = ‖ξ‖`, and the inner
    cocycle `⟪U_a x, U_b y⟫ = ⟪x, U_{b−a} y⟫` (whence `⟪U_t x, U_t y⟫ = ⟪x, y⟫`).

  NOT here (deliberately): strong continuity + `U_tΩ = Ω` + `E({0}) = 0` (R5),
  commutation with `R`/`Δ` (R6), Δ^{1/2}, J, KMS, towerGen = log Δ, any claim that
  `towerModUnitary` equals the transported `towerFlow`, any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.ResolventOrder
import QIQTH.Spectral.PVMEigen

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.SpectralTheorem
open scoped InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### R4.1 — the modular character `u_t(r) = exp(i·t·log((1−r)/r))`

    A globally bounded Borel function on ℝ: on `(0,1)` it is the modular symbol
    `((1−r)/r)^{it} = δ^{it}`, and `1` outside — the junk-value convention that makes the
    group laws hold POINTWISE on all of ℝ (so no spectral localization is ever needed
    for the algebra; the endpooint atoms are handled in R3/R5). -/

/-- The tower modular character `u_t(r)`, a globally bounded Borel function on `ℝ`: on
    `(0,1)` it is `exp(i·t·log((1−r)/r))`, and `1` outside (the junk-value convention
    makes the group law hold pointwise).  The `exp(I·t·(real))` shape is the expSymbol
    form R8's Stone derivative consumes — do not refactor it. -/
noncomputable def towerModChar (t : ℝ) : ℝ → ℂ :=
  (Set.Ioo (0 : ℝ) 1).piecewise
    (fun r => Complex.exp (Complex.I * (t : ℂ) * (Real.log ((1 - r) / r) : ℂ)))
    (fun _ => 1)

theorem towerModChar_measurable (t : ℝ) : Measurable (towerModChar t) := by
  apply Measurable.piecewise measurableSet_Ioo _ measurable_const
  apply Complex.continuous_exp.measurable.comp
  apply Measurable.mul measurable_const
  exact Complex.continuous_ofReal.measurable.comp
    (Real.measurable_log.comp ((measurable_const.sub measurable_id).div measurable_id))

/-- **Unimodularity** `‖u_t(r)‖ = 1` — on the bulk branch the exponent `I·t·log(...)` is
    purely imaginary (`t`, `log` real), so `|exp| = e^0 = 1`; the junk branch is `1`. -/
theorem towerModChar_norm (t r : ℝ) : ‖towerModChar t r‖ = 1 := by
  unfold towerModChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.piecewise_eq_of_mem _ _ _ h, Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * (Real.log ((1 - r) / r) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero]
  · rw [Set.piecewise_eq_of_notMem _ _ _ h, norm_one]

theorem towerModChar_zero (r : ℝ) : towerModChar 0 r = 1 := by
  unfold towerModChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.piecewise_eq_of_mem _ _ _ h]
    simp
  · rw [Set.piecewise_eq_of_notMem _ _ _ h]

/-- **Pointwise group law** `u_{s+t} = u_s · u_t` — `exp_add` on the bulk, `1·1` on the
    junk branch (this is exactly what the junk value `1` buys). -/
theorem towerModChar_add (s t r : ℝ) :
    towerModChar (s + t) r = towerModChar s r * towerModChar t r := by
  unfold towerModChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.piecewise_eq_of_mem _ _ _ h, Set.piecewise_eq_of_mem _ _ _ h,
        Set.piecewise_eq_of_mem _ _ _ h, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [Set.piecewise_eq_of_notMem _ _ _ h, Set.piecewise_eq_of_notMem _ _ _ h,
        Set.piecewise_eq_of_notMem _ _ _ h, mul_one]

/-- **Conjugation law** `conj u_t = u_{−t}` — `conj I = −I` flips the sign of `t`. -/
theorem towerModChar_conj (t r : ℝ) :
    (starRingEnd ℂ) (towerModChar t r) = towerModChar (-t) r := by
  unfold towerModChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.piecewise_eq_of_mem _ _ _ h, Set.piecewise_eq_of_mem _ _ _ h, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  · rw [Set.piecewise_eq_of_notMem _ _ _ h, Set.piecewise_eq_of_notMem _ _ _ h, map_one]

/-! ### R4.2 — the symbol on the spectrum, and the modular unitary `U_t = u_t(R)` -/

/-- `u_t` restricted to `σ(towerResolvent)` — the function fed to the bounded Borel FC. -/
noncomputable def towerModSpecFun (t : ℝ) :
    spectrum ℝ (towerResolvent L ω β) → ℂ :=
  fun r => towerModChar t r.val

theorem towerModSpecFun_measurable (t : ℝ) :
    Measurable (towerModSpecFun L ω β t) :=
  (towerModChar_measurable t).comp measurable_subtype_coe

theorem towerModSpecFun_norm_le (t : ℝ) (r : spectrum ℝ (towerResolvent L ω β)) :
    ‖towerModSpecFun L ω β t r‖ ≤ 1 :=
  le_of_eq (towerModChar_norm t r.val)

/-- **The tower modular unitary `U_t = Δ^{it} = u_t(R)`** via the bounded Borel FC of the
    resolvent.  NO claim is made that this equals the transported `towerFlow` (that
    identification — `towerGen = log Δ` — is the named next campaign). -/
noncomputable def towerModUnitary (t : ℝ) :
    TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
    (towerModSpecFun_measurable L ω β t) zero_le_one (towerModSpecFun_norm_le L ω β t)

/-- **`U_0 = 1`** — the symbol at `t = 0` is the constant `1` (both branches), and the
    bounded Borel FC is unital. -/
theorem towerModUnitary_zero : towerModUnitary L ω β 0 = 1 := by
  rw [towerModUnitary,
      borelFC_congr_fun (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
        (towerModSpecFun_measurable L ω β 0) zero_le_one (towerModSpecFun_norm_le L ω β 0)
        measurable_const (norm_nonneg (1 : ℂ)) (fun _ => le_rfl)
        (funext fun r => towerModChar_zero r.val),
      borelFC_one]

/-- **Group law, multiplicative form `U_{s+t} = U_s · U_t`** — from `borelFC_mul` and the
    pointwise law `u_{s+t} = u_s·u_t` (junk-value-global, no spectrum fact used). -/
theorem towerModUnitary_mul (s t : ℝ) :
    towerModUnitary L ω β (s + t)
      = towerModUnitary L ω β s * towerModUnitary L ω β t := by
  have hpm : Measurable
      (fun r => towerModSpecFun L ω β s r * towerModSpecFun L ω β t r) :=
    (towerModSpecFun_measurable L ω β s).mul (towerModSpecFun_measurable L ω β t)
  have hpb : ∀ r, ‖towerModSpecFun L ω β s r * towerModSpecFun L ω β t r‖ ≤ 1 := fun r => by
    rw [norm_mul]
    exact mul_le_one₀ (towerModSpecFun_norm_le L ω β s r) (norm_nonneg _)
      (towerModSpecFun_norm_le L ω β t r)
  rw [towerModUnitary, towerModUnitary, towerModUnitary,
      ← borelFC_mul (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
        (towerModSpecFun_measurable L ω β s) zero_le_one (towerModSpecFun_norm_le L ω β s)
        (towerModSpecFun_measurable L ω β t) zero_le_one (towerModSpecFun_norm_le L ω β t)
        hpm zero_le_one hpb]
  exact borelFC_congr_fun (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
    (towerModSpecFun_measurable L ω β (s + t)) zero_le_one
    (towerModSpecFun_norm_le L ω β (s + t)) hpm zero_le_one hpb
    (funext fun r => towerModChar_add s t r.val)

/-- **Group law `U_{s+t} = U_s ∘L U_t`** (composition form; `*` and `∘L` agree
    definitionally on CLMs). -/
theorem towerModUnitary_add (s t : ℝ) :
    towerModUnitary L ω β (s + t)
      = towerModUnitary L ω β s ∘L towerModUnitary L ω β t :=
  towerModUnitary_mul L ω β s t

/-! ### R4.3 — the adjoint law `U_t⋆ = U_{−t}` and unitarity -/

/-- **Adjoint of the bounded Borel FC of the resolvent:** `f(R)⋆ = (conj f)(R)` — from the
    hermitian symmetry of the polarized bilinear form (`bilinDiag_conj_symm`); the
    verbatim `borelFC_adjoint` port, specialized to `towerResolvent`. -/
theorem towerBorelFC_adjoint {f : spectrum ℝ (towerResolvent L ω β) → ℂ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r, ‖f r‖ ≤ C)
    {C' : ℝ} (hcf : Measurable (fun r => (starRingEnd ℂ) (f r))) (hC0' : 0 ≤ C')
    (hcfb : ∀ r, ‖(starRingEnd ℂ) (f r)‖ ≤ C') :
    ContinuousLinearMap.adjoint
        (borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β) hf hC0 hC)
      = borelFC (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
          hcf hC0' hcfb := by
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_borelFC,
      inner_borelFC,
      (PVM_of_selfAdjoint (towerResolvent L ω β)
        (towerResolvent_isSelfAdjoint L ω β)).bilinDiag_conj_symm]

/-- **`U_t⋆ = U_{−t}`** — from the adjoint relation `Φ(f)⋆ = Φ(conj f)` and the pointwise
    conjugation law `conj u_t = u_{−t}`. -/
theorem towerModUnitary_adjoint (t : ℝ) :
    ContinuousLinearMap.adjoint (towerModUnitary L ω β t)
      = towerModUnitary L ω β (-t) := by
  have hcm : Measurable (fun r => (starRingEnd ℂ) (towerModSpecFun L ω β t r)) :=
    Complex.continuous_conj.measurable.comp (towerModSpecFun_measurable L ω β t)
  have hcb : ∀ r, ‖(starRingEnd ℂ) (towerModSpecFun L ω β t r)‖ ≤ 1 := fun r => by
    rw [RCLike.norm_conj]; exact towerModSpecFun_norm_le L ω β t r
  rw [towerModUnitary, towerModUnitary,
      towerBorelFC_adjoint L ω β (towerModSpecFun_measurable L ω β t) zero_le_one
        (towerModSpecFun_norm_le L ω β t) hcm zero_le_one hcb]
  exact borelFC_congr_fun (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
    hcm zero_le_one hcb (towerModSpecFun_measurable L ω β (-t)) zero_le_one
    (towerModSpecFun_norm_le L ω β (-t)) (funext fun r => towerModChar_conj t r.val)

/-- **★ `U_t` IS UNITARY ★** (`U_t⋆U_t = 1 = U_t U_t⋆`) — the tower modular unitary
    group: adjoint law + group law + `U_0 = 1`. -/
theorem towerModUnitary_unitary (t : ℝ) :
    towerModUnitary L ω β t ∈ unitary (TowerGNS L ω β →L[ℂ] TowerGNS L ω β) := by
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.star_eq_adjoint, towerModUnitary_adjoint, ← towerModUnitary_mul,
        neg_add_cancel, towerModUnitary_zero]
  · rw [ContinuousLinearMap.star_eq_adjoint, towerModUnitary_adjoint, ← towerModUnitary_mul,
        add_neg_cancel, towerModUnitary_zero]

/-! ### R4.4 — isometry and the inner cocycle -/

/-- **`U_t` is an isometry** (`‖U_t ξ‖ = ‖ξ‖`), from unitarity. -/
theorem norm_towerModUnitary_apply (t : ℝ) (ξ : TowerGNS L ω β) :
    ‖towerModUnitary L ω β t ξ‖ = ‖ξ‖ := by
  have hu := (Unitary.mem_iff.mp (towerModUnitary_unitary L ω β t)).1
  have key : inner ℂ (towerModUnitary L ω β t ξ) (towerModUnitary L ω β t ξ)
      = inner ℂ ξ ξ := by
    rw [← ContinuousLinearMap.adjoint_inner_right (towerModUnitary L ω β t) ξ
          (towerModUnitary L ω β t ξ),
        ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.star_eq_adjoint, hu,
        ContinuousLinearMap.one_apply]
  have hre : ‖towerModUnitary L ω β t ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), key]
  rw [← Real.sqrt_sq (norm_nonneg (towerModUnitary L ω β t ξ)),
      ← Real.sqrt_sq (norm_nonneg ξ), hre]

/-- **Inner cocycle identity:** `⟪U_a x, U_b y⟫ = ⟪x, U_{b−a} y⟫` — the identity R5's
    strong-continuity argument consumes (there at `x = y = ξ`). -/
theorem inner_towerModUnitary_towerModUnitary (a b : ℝ) (x y : TowerGNS L ω β) :
    inner ℂ (towerModUnitary L ω β a x) (towerModUnitary L ω β b y)
      = inner ℂ x (towerModUnitary L ω β (b - a) y) := by
  have hop : ContinuousLinearMap.adjoint (towerModUnitary L ω β a)
        * towerModUnitary L ω β b
      = towerModUnitary L ω β (b - a) := by
    rw [towerModUnitary_adjoint, ← towerModUnitary_mul, neg_add_eq_sub]
  rw [← ContinuousLinearMap.adjoint_inner_right (towerModUnitary L ω β a) x
        (towerModUnitary L ω β b y),
      ← ContinuousLinearMap.mul_apply, hop]

/-- **`U_t` preserves the inner product**: `⟪U_t x, U_t y⟫ = ⟪x, y⟫` — the cocycle at
    `a = b = t` plus `U_0 = 1`. -/
theorem inner_towerModUnitary_apply (t : ℝ) (x y : TowerGNS L ω β) :
    inner ℂ (towerModUnitary L ω β t x) (towerModUnitary L ω β t y) = inner ℂ x y := by
  rw [inner_towerModUnitary_towerModUnitary, sub_self, towerModUnitary_zero,
      ContinuousLinearMap.one_apply]

end QIQTH.TowerGNS
