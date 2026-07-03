/-
  THE CLOSURE C4 (THE_CLOSURE_PLAN.md) — the amplification toolkit: `Hⁿ = PiLp 2 (Fin n → H)`.

  THE FROZEN INTERFACE (binding verdict): all later files (C5/C6) go ONLY through the lemmas of
  this file and never unfold the `PiLp` synonym —
    coordIncl (ι i)  : H →L Hⁿ        (x in slot i, 0 elsewhere)
    coordProj (π i)  : Hⁿ →L H        (Mathlib's `PiLp.proj`)
    diagCLM a        : Hⁿ →L Hⁿ       (a acting diagonally)
  with the six interface lemmas (π∘ι same/ne, Σ ι∘π = 1, adjoint ι = π, π∘diag = a∘π,
  diag∘ι = ι∘a), the algebra laws of `diagCLM` (one/mul/add/smul), the ⋆-law
  `star (diagCLM a) = diagCLM (star a)` (via `eq_adjoint_iff` + `PiLp.inner_apply`), the
  entrywise extensionality `clm_ext_of_entries`, and the coordinate norm bound
  (`PiLp.norm_apply_le`, re-exported).

  Pure finite Hilbert-sum operator API — no algebra of operators, no commutant, no density
  statement here (C5/C6/C7).
-/
import Mathlib

namespace QIQTH.VonNeumann

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- `ι i` — the inclusion of the `i`-th coordinate. -/
noncomputable def coordIncl (i : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm :
      (∀ _ : Fin n, H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) ∘L
    ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℂ H else 0)

/-- `π i` — the projection onto the `i`-th coordinate (Mathlib's `PiLp.proj`). -/
noncomputable def coordProj (i : Fin n) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H :=
  PiLp.proj 2 (fun _ : Fin n => H) i

/-- `a` acting diagonally on the tuple space. -/
noncomputable def diagCLM (a : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm :
      (∀ _ : Fin n, H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) ∘L
    ContinuousLinearMap.pi (fun i => a ∘L coordProj i)

theorem coordProj_apply (i : Fin n) (v : PiLp 2 (fun _ : Fin n => H)) :
    coordProj i v = v i := rfl

theorem coordIncl_apply (i j : Fin n) (x : H) :
    coordIncl i x j = if j = i then x else 0 := by
  show (if j = i then ContinuousLinearMap.id ℂ H else 0) x = _
  by_cases h : j = i <;> simp [h]

theorem diagCLM_apply (a : H →L[ℂ] H) (v : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    diagCLM a v i = a (v i) := rfl

/-- Interface 1: `π i ∘ ι i = 1`. -/
theorem coordProj_comp_coordIncl_same (i : Fin n) :
    coordProj (H := H) i ∘L coordIncl i = ContinuousLinearMap.id ℂ H := by
  ext x
  simp [coordProj_apply, coordIncl_apply]

/-- Interface 2: `π j ∘ ι i = 0` off the diagonal. -/
theorem coordProj_comp_coordIncl_ne {i j : Fin n} (h : j ≠ i) :
    coordProj (H := H) j ∘L coordIncl i = 0 := by
  ext x
  simp [coordProj_apply, coordIncl_apply, h]

/-- Coordinate evaluation is additive over finite sums (via the `coordProj` CLM). -/
theorem piLp_sum_apply {ι' : Type*} (s : Finset ι') (f : ι' → PiLp 2 (fun _ : Fin n => H))
    (j : Fin n) :
    (∑ k ∈ s, f k) j = ∑ k ∈ s, f k j := by
  have := map_sum (coordProj (H := H) j) f s
  simpa [coordProj_apply] using this

/-- Interface 3 (applied form): the coordinate decomposition of a tuple vector. -/
theorem sum_coordIncl_coordProj_apply (v : PiLp 2 (fun _ : Fin n => H)) :
    ∑ i : Fin n, coordIncl i (coordProj i v) = v := by
  refine PiLp.ext fun j => ?_
  rw [piLp_sum_apply]
  rw [Finset.sum_eq_single j ?h0 ?h1]
  · simp [coordIncl_apply, coordProj_apply]
  case h0 =>
    intro i _ hij
    rw [coordIncl_apply, if_neg fun h => hij h.symm]
  case h1 =>
    intro h
    exact absurd (Finset.mem_univ j) h

/-- Interface 3: `Σᵢ ι i ∘ π i = 1` — the coordinate decomposition. -/
theorem sum_coordIncl_comp_coordProj :
    ∑ i : Fin n, coordIncl (H := H) i ∘L coordProj i = ContinuousLinearMap.id ℂ _ := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.sum_apply]
  exact sum_coordIncl_coordProj_apply v

/-- Interface 4: `ι i† = π i` (via `eq_adjoint_iff` + `PiLp.inner_apply`). -/
theorem adjoint_coordIncl (i : Fin n) :
    ContinuousLinearMap.adjoint (coordIncl (H := H) i) = coordProj i := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v x
  rw [coordProj_apply, PiLp.inner_apply]
  rw [Finset.sum_eq_single i ?h0 ?h1]
  · rw [coordIncl_apply, if_pos rfl]
  case h0 =>
    intro j _ hji
    rw [coordIncl_apply, if_neg hji, inner_zero_right]
  case h1 =>
    intro h
    exact absurd (Finset.mem_univ i) h

/-- Interface 5: `π i ∘ diag a = a ∘ π i`. -/
theorem coordProj_comp_diagCLM (a : H →L[ℂ] H) (i : Fin n) :
    coordProj (n := n) i ∘L diagCLM a = a ∘L coordProj i := by
  ext v
  simp [coordProj_apply, diagCLM_apply]

/-- Interface 6: `diag a ∘ ι i = ι i ∘ a`. -/
theorem diagCLM_comp_coordIncl (a : H →L[ℂ] H) (i : Fin n) :
    diagCLM (n := n) a ∘L coordIncl i = coordIncl i ∘L a := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine PiLp.ext fun j => ?_
  show diagCLM a (coordIncl i x) j = coordIncl i (a x) j
  rw [diagCLM_apply, coordIncl_apply, coordIncl_apply]
  by_cases h : j = i <;> simp [h]

/-- `diag 1 = 1`. -/
theorem diagCLM_one : diagCLM (n := n) (1 : H →L[ℂ] H) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun j => ?_
  rw [diagCLM_apply]
  rfl

/-- `diag (a b) = diag a ∘ diag b`. -/
theorem diagCLM_mul (a b : H →L[ℂ] H) :
    diagCLM (n := n) (a * b) = diagCLM a * diagCLM b := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun j => ?_
  show diagCLM (a * b) v j = diagCLM a (diagCLM b v) j
  rw [diagCLM_apply, diagCLM_apply, diagCLM_apply]
  rfl

/-- `diag (a + b) = diag a + diag b`. -/
theorem diagCLM_add (a b : H →L[ℂ] H) :
    diagCLM (n := n) (a + b) = diagCLM a + diagCLM b := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun j => ?_
  show diagCLM (a + b) v j = (diagCLM a v + diagCLM b v) j
  rw [PiLp.add_apply, diagCLM_apply, diagCLM_apply, diagCLM_apply,
    ContinuousLinearMap.add_apply]

/-- `diag (c • a) = c • diag a`. -/
theorem diagCLM_smul (c : ℂ) (a : H →L[ℂ] H) :
    diagCLM (n := n) (c • a) = c • diagCLM a := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun j => ?_
  show diagCLM (c • a) v j = (c • diagCLM a v) j
  rw [PiLp.smul_apply, diagCLM_apply, diagCLM_apply, ContinuousLinearMap.smul_apply]

/-- `(diag a)† = diag (a†)` — the one nontrivial star fact. -/
theorem adjoint_diagCLM (a : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (diagCLM (n := n) a) = diagCLM (ContinuousLinearMap.adjoint a) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diagCLM_apply, diagCLM_apply]
  exact ContinuousLinearMap.adjoint_inner_left a (w j) (v j)

/-- `star (diag a) = diag (star a)` (the form C5 consumes). -/
theorem star_diagCLM (a : H →L[ℂ] H) :
    star (diagCLM (n := n) a) = diagCLM (star a) := by
  rw [star_eq_adjoint, star_eq_adjoint, adjoint_diagCLM]

/-- **Entrywise extensionality**: operators on the tuple space agree iff all their
    `π i ∘ F ∘ ι j` entries agree (the coordinate decomposition `Σ ι∘π = 1`). -/
theorem clm_ext_of_entries {F G : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)}
    (h : ∀ i j, coordProj i ∘L F ∘L coordIncl j = coordProj i ∘L G ∘L coordIncl j) :
    F = G := by
  have hcol : ∀ (j : Fin n) (x : H), F (coordIncl j x) = G (coordIncl j x) := by
    intro j x
    refine PiLp.ext fun i => ?_
    have := congrArg (fun (T : H →L[ℂ] H) => T x) (h i j)
    simpa [coordProj_apply] using this
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = ∑ j : Fin n, coordIncl j (coordProj j v) :=
    (sum_coordIncl_coordProj_apply v).symm
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => hcol j (coordProj j v)

/-- The coordinate norm bound (Mathlib's `PiLp.norm_apply_le`, re-exported for the interface). -/
theorem norm_coord_le (v : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    ‖v i‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

end QIQTH.VonNeumann
