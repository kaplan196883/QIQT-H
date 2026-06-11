/-
  Phase C — second quantization of the modular flow:  Γ(Δ^{it}) on the Fock space.

  The one-particle continuum modular flow `Δ^{it} = U_t = u_t(R)` (`StandardSubspaceModularFlow`)
  is a strongly-continuous one-parameter UNITARY group on the one-particle space `H`.  Its second
  quantization `Γ(Δ^{it})` (built on the existing generic functor `secondQuantPre`, Parthasarathy §19)
  is the modular flow at the FIELD / Fock level — the implementing unitaries of the modular automorphism
  group `σ_t(·) = Γ(Δ^{it})·Γ(Δ^{it})⋆` of the free-field von Neumann algebra (for the second-quantized
  free field, the local algebra's modular operator IS `Γ(Δ)` of the standard-subspace modular operator,
  Bisognano–Wichmann / the standard-subspace structure).

  Results (axiom-free):
    * `modUnitaryₗᵢ` — `Δ^{it}` repackaged as a one-particle linear isometry (from `modUnitary_unitary`);
    * `secondQuantModFlow` — `Γ(Δ^{it})` on the pre-Fock space, with `_expVec` (`Γ(Δ^{it}) e(f)=e(Δ^{it}f)`),
      `_vacuum` (`Γ(Δ^{it}) Ω = Ω`), `_zero` (`Γ(Δ^{i·0}) = id`), and the GROUP LAW `_add`
      (`Γ(Δ^{is})∘Γ(Δ^{it}) = Γ(Δ^{i(s+t)})`, from `modUnitary_add` + functoriality of `Γ`);
    * `fockInner_secondQuantModFlow` — `Γ(Δ^{it})` preserves the Fock inner product (it is isometric);
    * `secondQuantModFlowH` — `Γ(Δ^{it})` extended to the Fock HILBERT space, a genuine one-parameter
      group of isometries (`_isometry`, `_vacuum`, `_zero`, `_add`) — the continuum field-level modular flow.

  HONEST SCOPE: this builds the second-quantized modular FLOW (the field-level modular automorphism
  group's implementing unitaries) — the heart of Tomita–Takesaki at the field level, axiom-free.  The full
  von-Neumann-algebra relative ENTROPY `S(ρ‖σ)` additionally needs the RELATIVE modular operator of two
  states; for the free field, the Casini–Grillo–Pontello result reduces that to the one-particle entropy
  `cgpEntropy` already proved nonnegative in `ModularRelativeEntropy`.
-/

import QIQTH.Fock.SecondQuant
import QIQTH.Fock.WeylOp
import QIQTH.StandardSubspaceModularFlow

namespace QIQTH.Fock

open QIQTH.StandardSubspaceModular
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`Δ^{it}` as a one-particle linear isometry**, from unitarity of the modular flow
    (`⟪Δ^{it} x, Δ^{it} y⟫ = ⟪x, (Δ^{it})⋆ Δ^{it} y⟫ = ⟪x, y⟫`). -/
noncomputable def modUnitaryₗᵢ (S : StandardSubspace H) (t : ℝ) : H →ₗᵢ[ℂ] H :=
  LinearMap.isometryOfInner (modUnitary S t).toLinearMap (fun x y => by
    have hu : ContinuousLinearMap.adjoint (modUnitary S t) * modUnitary S t = 1 := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (Unitary.mem_iff.mp (modUnitary_unitary S t)).1
    show inner ℂ (modUnitary S t x) (modUnitary S t y) = inner ℂ x y
    rw [← ContinuousLinearMap.adjoint_inner_right (modUnitary S t) x (modUnitary S t y),
        ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply])

@[simp] theorem modUnitaryₗᵢ_apply (S : StandardSubspace H) (t : ℝ) (x : H) :
    modUnitaryₗᵢ S t x = modUnitary S t x := rfl

/-- **Γ(Δ^{it})** — the second quantization of the one-particle modular flow, on the pre-Fock space:
    `Γ(Δ^{it}) e(f) = e(Δ^{it} f)`. -/
noncomputable def secondQuantModFlow (S : StandardSubspace H) (t : ℝ) :
    FockPre H →ₗ[ℂ] FockPre H :=
  secondQuantPre (modUnitaryₗᵢ S t)

@[simp] theorem secondQuantModFlow_expVec (S : StandardSubspace H) (t : ℝ) (f : H) :
    secondQuantModFlow S t (FockPre.expVec f) = FockPre.expVec (modUnitary S t f) :=
  secondQuantPre_expVec _ f

/-- **Vacuum invariance** `Γ(Δ^{it}) Ω = Ω` (the modular flow fixes the vacuum). -/
@[simp] theorem secondQuantModFlow_vacuum (S : StandardSubspace H) (t : ℝ) :
    secondQuantModFlow S t (FockPre.expVec (0 : H)) = FockPre.expVec (0 : H) := by
  rw [secondQuantModFlow_expVec, map_zero]

/-- **`Γ(Δ^{i·0}) = id`.** -/
theorem secondQuantModFlow_zero (S : StandardSubspace H) (φ : FockPre H) :
    secondQuantModFlow S 0 φ = φ := by
  rw [secondQuantModFlow]
  show Finsupp.mapDomain (⇑(modUnitaryₗᵢ S 0)) φ = φ
  rw [show (⇑(modUnitaryₗᵢ S 0) : H → H) = id from
    funext fun x => by show modUnitary S 0 x = x; rw [modUnitary_zero]; rfl]
  exact Finsupp.mapDomain_id

/-- **The one-parameter group law** `Γ(Δ^{is}) ∘ Γ(Δ^{it}) = Γ(Δ^{i(s+t)})` — from the group law of the
    one-particle modular flow (`modUnitary_add`) and the functoriality of second quantization. -/
theorem secondQuantModFlow_add (S : StandardSubspace H) (s t : ℝ) (φ : FockPre H) :
    secondQuantModFlow S s (secondQuantModFlow S t φ) = secondQuantModFlow S (s + t) φ := by
  have hcomp : (modUnitaryₗᵢ S s).comp (modUnitaryₗᵢ S t) = modUnitaryₗᵢ S (s + t) := by
    refine LinearIsometry.ext (fun x => ?_)
    show modUnitary S s (modUnitary S t x) = modUnitary S (s + t) x
    rw [modUnitary_add]; rfl
  rw [secondQuantModFlow, secondQuantModFlow, secondQuantModFlow, secondQuantPre_comp, hcomp]

/-- **`Γ(Δ^{it})` is isometric** on the pre-Fock space — it preserves the coherent-state inner product. -/
theorem fockInner_secondQuantModFlow (S : StandardSubspace H) (t : ℝ) (φ ψ : FockPre H) :
    fockInner (secondQuantModFlow S t φ : H →₀ ℂ) (secondQuantModFlow S t ψ : H →₀ ℂ)
      = fockInner (φ : H →₀ ℂ) (ψ : H →₀ ℂ) :=
  fockInner_secondQuant (modUnitaryₗᵢ S t) φ ψ

/-- `Γ(Δ^{it})` as a linear isometry of the pre-Fock space. -/
noncomputable def secondQuantModFlowₗᵢ (S : StandardSubspace H) (t : ℝ) :
    FockPre H →ₗᵢ[ℂ] FockPre H :=
  LinearMap.isometryOfInner (secondQuantModFlow S t)
    (fun φ ψ => fockInner_secondQuant (modUnitaryₗᵢ S t) φ ψ)

/-- **Γ(Δ^{it}) on the Fock HILBERT space** — the continuum field-level modular flow (the unique
    isometric extension of the pre-level flow to the completion). -/
noncomputable def secondQuantModFlowH (S : StandardSubspace H) (t : ℝ) : Fock H → Fock H :=
  UniformSpace.Completion.map (secondQuantModFlowₗᵢ S t)

theorem secondQuantModFlowH_isometry (S : StandardSubspace H) (t : ℝ) :
    Isometry (secondQuantModFlowH S t) :=
  (secondQuantModFlowₗᵢ S t).isometry.completion_map

/-- **Vacuum invariance** `Γ(Δ^{it}) Ω = Ω` on the Fock Hilbert space. -/
theorem secondQuantModFlowH_vacuum (S : StandardSubspace H) (t : ℝ) :
    secondQuantModFlowH S t Fock.vacuum = Fock.vacuum := by
  have hΩ : (secondQuantModFlowₗᵢ S t) (FockPre.expVec 0) = FockPre.expVec 0 :=
    secondQuantModFlow_vacuum S t
  show UniformSpace.Completion.map (secondQuantModFlowₗᵢ S t)
      ((FockPre.expVec 0 : FockPre H) : Fock H) = ((FockPre.expVec 0 : FockPre H) : Fock H)
  rw [UniformSpace.Completion.map_coe (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous, hΩ]

/-- **`Γ(Δ^{i·0}) = id`** on the Fock Hilbert space. -/
theorem secondQuantModFlowH_zero (S : StandardSubspace H) (x : Fock H) :
    secondQuantModFlowH S 0 x = x := by
  rw [secondQuantModFlowH, show (⇑(secondQuantModFlowₗᵢ S 0) : FockPre H → FockPre H) = id from
    funext fun φ => secondQuantModFlow_zero S φ]
  exact congrFun UniformSpace.Completion.map_id x

/-- **The one-parameter group law on the Fock Hilbert space** `Γ(Δ^{is}) ∘ Γ(Δ^{it}) = Γ(Δ^{i(s+t)})`. -/
theorem secondQuantModFlowH_add (S : StandardSubspace H) (s t : ℝ) (x : Fock H) :
    secondQuantModFlowH S s (secondQuantModFlowH S t x) = secondQuantModFlowH S (s + t) x := by
  have hfun : (⇑(secondQuantModFlowₗᵢ S s)) ∘ (⇑(secondQuantModFlowₗᵢ S t))
      = ⇑(secondQuantModFlowₗᵢ S (s + t)) :=
    funext fun φ => secondQuantModFlow_add S s t φ
  rw [secondQuantModFlowH, secondQuantModFlowH, secondQuantModFlowH,
      ← Function.comp_apply (f := UniformSpace.Completion.map (secondQuantModFlowₗᵢ S s)),
      UniformSpace.Completion.map_comp (secondQuantModFlowₗᵢ S s).isometry.uniformContinuous
        (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous, hfun]

/-! ### Tomita's theorem at the field level: the modular flow acts on the CCR / Weyl algebra

  `σ_t(W(u)) = Γ(Δ^{it}) W(u) Γ(Δ^{-it}) = W(Δ^{it} u)`.  The second-quantized modular flow maps the Weyl
  (CCR) algebra of the standard subspace onto itself, transporting the one-particle test function by the
  modular flow — exactly the content of Tomita's theorem (`σ_t(M) = M`) for the free-field von Neumann
  algebra.  The engine is the isometry-invariance of the Weyl coefficient (`weylCoeff_isometry_invariant`). -/

/-- **Covariance of the Weyl operator under second quantization:** `Γ(A) W(u) = W(A u) Γ(A)` for any
    one-particle linear isometry `A`. -/
theorem secondQuantPre_weylPre (A : H →ₗᵢ[ℂ] H) (u : H) (φ : FockPre H) :
    secondQuantPre A (weylPre u φ) = weylPre (A u) (secondQuantPre A φ) := by
  have key : (secondQuantPre A).comp (weylPre u) = (weylPre (A u)).comp (secondQuantPre A) := by
    refine Finsupp.lhom_ext (fun g b => ?_)
    show secondQuantPre A (weylPre u (Finsupp.single g b))
        = weylPre (A u) (secondQuantPre A (Finsupp.single g b))
    have hb : (Finsupp.single g b : FockPre H) = b • FockPre.expVec g := by
      show (Finsupp.single g b : H →₀ ℂ) = b • (Finsupp.single g 1 : H →₀ ℂ)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [hb, map_smul, weylPre_expVec, secondQuantPre_expVec, map_add,
      Weyl.weylCoeff_isometry_invariant]
  exact congrFun (congrArg DFunLike.coe key) φ

/-- **The modular automorphism on the Weyl/CCR algebra (pre-Fock level):** `Γ(Δ^{it}) W(u) =
    W(Δ^{it} u) Γ(Δ^{it})`, i.e. `σ_t(W(u)) = W(Δ^{it} u)` — Tomita's theorem at the free-field level. -/
theorem secondQuantModFlow_weyl (S : StandardSubspace H) (t : ℝ) (u : H) (φ : FockPre H) :
    secondQuantModFlow S t (weylPre u φ)
      = weylPre (modUnitary S t u) (secondQuantModFlow S t φ) :=
  secondQuantPre_weylPre (modUnitaryₗᵢ S t) u φ

/-- **The modular Weyl covariance on the Fock HILBERT space:** `Γ(Δ^{it}) W(u) = W(Δ^{it} u) Γ(Δ^{it})`
    as a genuine identity of operators on `Fock H` — the modular automorphism group transports the
    field-level Weyl operators by the one-particle modular flow. -/
theorem secondQuantModFlowH_weylH (S : StandardSubspace H) (t : ℝ) (u : H) (x : Fock H) :
    secondQuantModFlowH S t (weylH u x)
      = weylH (modUnitary S t u) (secondQuantModFlowH S t x) := by
  have hfun : (⇑(secondQuantModFlowₗᵢ S t)) ∘ (⇑(weylₗᵢ u))
      = (⇑(weylₗᵢ (modUnitary S t u))) ∘ (⇑(secondQuantModFlowₗᵢ S t)) :=
    funext fun φ => secondQuantModFlow_weyl S t u φ
  show UniformSpace.Completion.map (secondQuantModFlowₗᵢ S t)
        (UniformSpace.Completion.map (weylₗᵢ u) x)
      = UniformSpace.Completion.map (weylₗᵢ (modUnitary S t u))
        (UniformSpace.Completion.map (secondQuantModFlowₗᵢ S t) x)
  rw [← Function.comp_apply (f := UniformSpace.Completion.map (secondQuantModFlowₗᵢ S t)),
      ← Function.comp_apply (f := UniformSpace.Completion.map (weylₗᵢ (modUnitary S t u))),
      UniformSpace.Completion.map_comp (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous
        (weylₗᵢ u).isometry.uniformContinuous,
      UniformSpace.Completion.map_comp (weylₗᵢ (modUnitary S t u)).isometry.uniformContinuous
        (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous, hfun]

/-! ### The vacuum is the modular state, and `Γ(Δ^{it})` is strongly continuous on coherent vectors

  Two further hallmarks of a genuine modular flow: the vacuum state is `σ_t`-invariant (the vacuum is the
  modular/KMS state of the free-field algebra), and `t ↦ Γ(Δ^{it})` is STRONGLY continuous — the
  second-quantized lift of the one-particle strong continuity `modUnitary_stronglyContinuous`, established
  here on the dense spanning set of coherent (exponential) vectors. -/

/-- **The vacuum (quasifree) state is `σ_t`-invariant:** `⟪Ω, W(Δ^{it} u) Ω⟫ = ⟪Ω, W(u) Ω⟫`.  Since
    `⟪Ω, W(v) Ω⟫ = exp(−½⟪v,v⟫)` depends only on `⟪v,v⟫`, which the modular flow preserves, the vacuum is
    invariant under the modular automorphism group — i.e. the vacuum is the modular state. -/
theorem weylVacuum_modFlow_invariant (S : StandardSubspace H) (t : ℝ) (u : H) :
    fockInner (FockPre.expVec (0 : H)) (weylPre (modUnitary S t u) (FockPre.expVec 0))
      = fockInner (FockPre.expVec (0 : H)) (weylPre u (FockPre.expVec 0)) := by
  rw [fockInner_vacuum_weyl, fockInner_vacuum_weyl]
  congr 2
  exact (modUnitaryₗᵢ S t).inner_map_map u u

/-- **Continuity of the coherent-state map** `f ↦ e(f)` (pre-Fock level): from the inner-product formula
    `⟪e(f), e(g)⟫ = exp⟪f,g⟫`, the squared distance `‖e(g) − e(f)‖²` is a continuous function of `g`
    vanishing at `g = f`. -/
theorem continuous_expVecPre : Continuous (fun f : H => (FockPre.expVec f : FockPre H)) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ g : H, ‖(FockPre.expVec g - FockPre.expVec f : FockPre H)‖ ^ 2
      = (Complex.exp ⟪g, g⟫_ℂ - Complex.exp ⟪g, f⟫_ℂ - Complex.exp ⟪f, g⟫_ℂ
          + Complex.exp ⟪f, f⟫_ℂ).re := by
    intro g
    have e1 : inner ℂ (FockPre.expVec g : FockPre H) (FockPre.expVec g) = Complex.exp ⟪g, g⟫_ℂ :=
      FockPre.inner_expVec g g
    have e2 : inner ℂ (FockPre.expVec g : FockPre H) (FockPre.expVec f) = Complex.exp ⟪g, f⟫_ℂ :=
      FockPre.inner_expVec g f
    have e3 : inner ℂ (FockPre.expVec f : FockPre H) (FockPre.expVec g) = Complex.exp ⟪f, g⟫_ℂ :=
      FockPre.inner_expVec f g
    have e4 : inner ℂ (FockPre.expVec f : FockPre H) (FockPre.expVec f) = Complex.exp ⟪f, f⟫_ℂ :=
      FockPre.inner_expVec f f
    have hinner : inner ℂ (FockPre.expVec g - FockPre.expVec f : FockPre H)
        (FockPre.expVec g - FockPre.expVec f)
        = Complex.exp ⟪g, g⟫_ℂ - Complex.exp ⟪g, f⟫_ℂ - Complex.exp ⟪f, g⟫_ℂ + Complex.exp ⟪f, f⟫_ℂ := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, e1, e2, e3, e4]; ring
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]; rfl
  have hcore : Continuous (fun g : H => (Complex.exp ⟪g, g⟫_ℂ - Complex.exp ⟪g, f⟫_ℂ
      - Complex.exp ⟪f, g⟫_ℂ + Complex.exp ⟪f, f⟫_ℂ).re) := by
    apply Complex.continuous_re.comp; fun_prop
  have hsqto : Filter.Tendsto (fun g => ‖(FockPre.expVec g - FockPre.expVec f : FockPre H)‖ ^ 2)
      (nhds f) (nhds 0) := by
    have h0 : (Complex.exp ⟪f, f⟫_ℂ - Complex.exp ⟪f, f⟫_ℂ - Complex.exp ⟪f, f⟫_ℂ
        + Complex.exp ⟪f, f⟫_ℂ).re = 0 := by norm_num
    have := hcore.tendsto f
    rw [h0] at this
    simpa only [hsq] using this
  have hfin := hsqto.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hfin

/-- Continuity of the coherent-state map `f ↦ e(f)` on the Fock Hilbert space. -/
theorem continuous_FockExpVec : Continuous (fun f : H => (Fock.expVec f : Fock H)) :=
  Continuous.comp (UniformSpace.Completion.continuous_coe (FockPre H)) continuous_expVecPre

/-- `Γ(Δ^{it})` acts on coherent vectors of the Fock Hilbert space by `Γ(Δ^{it}) e(f) = e(Δ^{it} f)`. -/
theorem secondQuantModFlowH_expVec (S : StandardSubspace H) (t : ℝ) (f : H) :
    secondQuantModFlowH S t (Fock.expVec f) = Fock.expVec (modUnitary S t f) := by
  show UniformSpace.Completion.map (secondQuantModFlowₗᵢ S t)
      ((FockPre.expVec f : FockPre H) : Fock H)
      = ((FockPre.expVec (modUnitary S t f) : FockPre H) : Fock H)
  rw [UniformSpace.Completion.map_coe (secondQuantModFlowₗᵢ S t).isometry.uniformContinuous]
  congr 1
  exact secondQuantModFlow_expVec S t f

/-- **Strong continuity of `Γ(Δ^{it})` on coherent vectors:** `t ↦ Γ(Δ^{it}) e(f)` is continuous — the
    second-quantized lift of the one-particle strong continuity `modUnitary_stronglyContinuous`, on the
    dense spanning set.  So `Γ(Δ^{it})` is a strongly-continuous-on-coherent-states one-parameter group:
    a genuine modular flow with a Stone generator. -/
theorem secondQuantModFlowH_continuous_expVec (S : StandardSubspace H) (f : H) :
    Continuous (fun t => secondQuantModFlowH S t (Fock.expVec f)) := by
  simp only [secondQuantModFlowH_expVec]
  exact continuous_FockExpVec.comp (modUnitary_stronglyContinuous S f)

end QIQTH.Fock
