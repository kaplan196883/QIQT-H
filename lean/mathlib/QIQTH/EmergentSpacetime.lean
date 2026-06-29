/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# EMERGENT SPACETIME — finite proto-geometry cores (Track B)

Honest, axiom-free Lean cores toward *emergent spacetime* from QIQT-H's finite-capacity substrate —
the Tier-2/Tier-3 "geometry from a finite quantum-information substrate" program (`docs/qg_roadmap/`).
See `FIELDS_AND_SPACETIME_PLAN.md`.

**Honest scope (enforced).** These build finite PROTO-spacetime objects (no-go guards, reconstructed
metrics, capacity/entropy skeletons, causal orders) with explicit error bounds — NOT a
background-independent 4D Lorentzian manifold (open physics). The Jacobson/BW/Sakharov material elsewhere
ASSUMES geometry (Tier 1) and is not emergence evidence. **min-cut is the AREA/entropy primitive, not a
metric** (it violates the triangle inequality). Capacity is a constraint, not a generator.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import QIQTH.FQBoundMicro

namespace QIQTH.EmergentSpacetime

open Matrix
open scoped ComplexOrder

section NoGo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **★★ B0 — the finite exact-continuum no-go guard.**  On a *finite-dimensional* space, a unitary
conjugation cannot *rescale* a nonzero operator.  If `U` is an isometry (`Uᴴ U = 1`, hence unitary on the
finite space) and `U P Uᴴ = r • P` with the squared modulus `star r · r ≠ 1` (i.e. `|r| ≠ 1`), then
`P = 0`.

Reason: unitary conjugation preserves the Hilbert–Schmidt (Frobenius) norm — `Tr(Pᴴ P)` is invariant —
while `r •` rescales it by `|r|² = star r · r`; so `(star r · r) Tr(Pᴴ P) = Tr(Pᴴ P)`, forcing
`Tr(Pᴴ P) = 0`, i.e. `P = 0`.

This is the structural reason a **finite** regional Hilbert space cannot host an *exact* noncompact
continuum symmetry that scales a generator: no exact finite Borchers dilation `Δ^{it} P Δ^{-it} = e^{-ct}P`
(`c ≠ 0`), no exact finite Weyl/boost scaling. Tier-2 emergence must therefore be *approximate / in a
scaling limit*, with quantified error — the honest constraint, not a defect. -/
theorem finiteDim_scaling_forces_zero
    (U P : Matrix n n ℂ) (hU : Uᴴ * U = 1) (r : ℂ) (hr : star r * r ≠ 1)
    (hscale : U * P * Uᴴ = r • P) : P = 0 := by
  -- the conjugated operator's HS norm both equals Tr(Pᴴ P) and equals (star r · r) Tr(Pᴴ P)
  have hmat : (U * P * Uᴴ)ᴴ * (U * P * Uᴴ) = U * (Pᴴ * P) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (P * Uᴴ), hU, Matrix.one_mul]
  have e1 : ((U * P * Uᴴ)ᴴ * (U * P * Uᴴ)).trace = (Pᴴ * P).trace := by
    rw [hmat, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have e2 : ((U * P * Uᴴ)ᴴ * (U * P * Uᴴ)).trace = (star r * r) * (Pᴴ * P).trace := by
    rw [hscale]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
    ring
  have key : (Pᴴ * P).trace = (star r * r) * (Pᴴ * P).trace := e1.symm.trans e2
  have htr0 : (Pᴴ * P).trace = 0 := by
    have hzero : ((star r * r) - 1) * (Pᴴ * P).trace = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hr
    · exact h
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr0

/-- **★ B0 (corollary) — a nonzero operator cannot be scaled by a finite unitary conjugation.**  If
`U P Uᴴ = r • P` with `P ≠ 0`, then `star r · r = 1` (i.e. `|r| = 1`): the contrapositive of the guard.
So any exact finite "dilation/boost" symmetry acts on a nonzero charge/momentum operator only by a
*phase / unit-modulus* factor — never a genuine rescaling.  The exact noncompact dilation needed for
Borchers' theorem is thus unavailable in finite dimension; it is a continuum / scaling-limit object. -/
theorem scaling_of_nonzero_forces_unit_modulus
    (U P : Matrix n n ℂ) (hU : Uᴴ * U = 1) (r : ℂ) (hP : P ≠ 0)
    (hscale : U * P * Uᴴ = r • P) : star r * r = 1 := by
  by_contra h
  exact hP (finiteDim_scaling_forces_zero U P hU r h hscale)

end NoGo

section Metric

/-- An **approximate pseudometric** with slack `ε`: nonnegative, zero on the diagonal, symmetric, and
triangle up to `ε`.  `ε = 0` is an exact pseudometric.  This is the target type for any *emergent-distance
reconstruction* from the substrate's entanglement data — every reconstruction must be tagged with the `ε`
its error bound provides. -/
structure IsApproxPseudometric (ε : ℝ) {X : Type*} (d : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  self : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z + ε

/-- A 3-point "area / cut" function with the min-cut counterexample values: `λ(x,y)=λ(y,z)=2`,
`λ(x,z)=5` (and `0` on the diagonal, symmetric). -/
def cutEx : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 0 else if i.val + j.val = 2 then 5 else 2

/-- **★★ B1 — min-cut / RT-area is NOT a metric (the corrected-roadmap guard).**  There is a
nonnegative, symmetric, zero-diagonal "area / capacity" function (the shape of an RT/min-cut entanglement
area) that **violates the triangle inequality** — so min-cut area cannot be used as the emergent
*distance* (the error in the earlier Tier-3 §3.1 recipe).  Witness: `cutEx` with `λ(0,1)=λ(1,2)=2` but
`λ(0,2)=5 > 2+2`.  Distance must instead be reconstructed by a provably-metric rule (see
`embedDist_isPseudometric`); min-cut keeps its correct role as the *area/entropy* primitive. -/
theorem minCut_area_not_metric :
    ∃ (X : Type) (d : X → X → ℝ),
      (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧
      ¬ (∀ x y z, d x z ≤ d x y + d y z) := by
  refine ⟨Fin 3, cutEx, ?_, ?_, ?_, ?_⟩
  · intro x y; unfold cutEx; split_ifs <;> norm_num
  · intro x; unfold cutEx; rw [if_pos rfl]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [cutEx]
  · intro h
    have h12 := h 0 1 2
    have e02 : cutEx 0 2 = 5 := by simp [cutEx]
    have e01 : cutEx 0 1 = 2 := by simp [cutEx]
    have e12 : cutEx 1 2 = 2 := by simp [cutEx]
    rw [e02, e01, e12] at h12
    norm_num at h12

/-- A **metric-valid reconstruction**: the `L¹` / coordinate-embedding distance `d(x,y) = |f x − f y|`
pulled back from a reconstructed real "coordinate" `f`.  This is the 1-D case of the cut-cone / `L¹`
embedding reconstruction (a *genuine* metric, unlike raw min-cut). -/
def embedDist {X : Type*} (f : X → ℝ) : X → X → ℝ := fun x y => |f x - f y|

/-- **★★ B1 — the embedding reconstruction is an exact pseudometric.**  `embedDist f` satisfies all the
metric axioms (it is pulled back from `ℝ` along `f`): the honest, provably-metric replacement for the
min-cut "distance".  An emergent *coordinate* `f` (reconstructed from the substrate) yields an emergent
*distance* that really is one — with `ε = 0` (exact), the cleanest first Tier-3 reconstruction. -/
theorem embedDist_isPseudometric {X : Type*} (f : X → ℝ) :
    IsApproxPseudometric 0 (embedDist f) where
  nonneg := fun x y => abs_nonneg _
  self := fun x => by simp [embedDist]
  symm := fun x y => by rw [embedDist, embedDist, abs_sub_comm]
  triangle := fun x y z => by
    have := abs_sub_le (f x) (f y) (f z)
    simp only [embedDist, add_zero]
    linarith

end Metric

section GraphRT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **edge-cut "area"** of a region `S` on a finite weighted graph: the total edge weight crossing the
boundary `∂S`, `cut w S = ∑_{i∈S} ∑_{j∉S} w(i,j)`.  This is the finite RT/min-cut *area/entropy* primitive
(its **correct** role — recall it is NOT a metric, `minCut_area_not_metric`). -/
noncomputable def cut (w : V → V → ℝ) (S : Finset V) : ℝ := ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j

/-- **★ B2 — the cut area is nonnegative** (for nonnegative edge weights). -/
theorem cut_nonneg (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j) (S : Finset V) : 0 ≤ cut w S :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hw i j))

/-- **★★ B2 — purity: `S(A) = S(Aᶜ)`.**  The cut area of a region equals that of its complement
(`cut w Sᶜ = cut w S`), for a symmetric graph — the finite analogue of the RT/entanglement-entropy purity
`S(A) = S(Aᶜ)` of a globally pure state (the boundary `∂S = ∂Sᶜ` carries the same crossing edges). -/
theorem cut_compl (w : V → V → ℝ) (hsymm : ∀ i j, w i j = w j i) (S : Finset V) :
    cut w Sᶜ = cut w S := by
  unfold cut
  rw [compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsymm b a))

/-- **★★ B2 — subadditivity: `S(A ∪ B) ≤ S(A) + S(B)`.**  For disjoint regions the cut area is
subadditive (nonnegative weights) — the finite RT/min-cut analogue of subadditivity of entanglement
entropy.  (Crossing edges of `∂(A∪B)` are a subset of `∂A ∪ ∂B`.) -/
theorem cut_union_le (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j) (A B : Finset V) (hAB : Disjoint A B) :
    cut w (A ∪ B) ≤ cut w A + cut w B := by
  unfold cut
  rw [Finset.sum_union hAB]
  apply add_le_add
  · refine Finset.sum_le_sum (fun i _ => ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.compl_subset_compl.mpr Finset.subset_union_left) (fun j _ _ => hw i j)
  · refine Finset.sum_le_sum (fun i _ => ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.compl_subset_compl.mpr Finset.subset_union_right) (fun j _ _ => hw i j)

end GraphRT

section TensorNetworkCut

open QIQTH.QuantumEntropy

/-- **★ B3 — the bond/Schmidt entropy bound.**  A region's reduced state represented on a **cut / bond
space** of dimension `card dCut` has von Neumann entropy at most `log(card dCut)` — the Schmidt-rank /
bond-dimension bound across the cut (just `vonNeumannEntropy_le_log_card` read at the cut space). -/
theorem entropy_le_log_cutDim {dCut : Type*} [Fintype dCut] [DecidableEq dCut]
    {ρ : Matrix dCut dCut ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ Real.log (Fintype.card dCut) :=
  vonNeumannEntropy_le_log_card h

/-- **★★ B3 — the tensor-network cut bound (factor-through form).**  If a region's code state factors
through a cut of dimension `card dCut` (`card dC ≤ card dCut`, the bond cutting the network), its entropy
is bounded by the **log bond dimension**: `S_vN(ρ) ≤ log(card dC) ≤ log(card dCut)`.  The honest finite
statement of "entanglement across a cut ≤ log of the bond dimension". -/
theorem entropy_le_log_cutDim_of_factor {dC dCut : Type*} [Fintype dC] [DecidableEq dC] [Nonempty dC]
    [Fintype dCut] {ρ : Matrix dC dC ℂ} (h : IsDensity ρ) (hfit : Fintype.card dC ≤ Fintype.card dCut) :
    vonNeumannEntropy h ≤ Real.log (Fintype.card dCut) := by
  calc vonNeumannEntropy h
      ≤ Real.log (Fintype.card dC) := vonNeumannEntropy_le_log_card h
    _ ≤ Real.log (Fintype.card dCut) :=
        Real.log_le_log (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hfit)

/-- **★★★ B3 — the RT/min-cut entropy bound (wired to B2's `cut`).**  When the **bond dimension across
the cut fits the cut area** (`log(card dCut) ≤ cut w S`, the tensor-network / holographic bond bound — an
*assumption*, the network's defining property, NOT derived), the region's entanglement entropy obeys the
**RT/min-cut bound**:

  `S_vN(ρ) ≤ cut w S = ` the boundary area `∂S`.

So entanglement is bounded by the area through the cut — the finite, honest Ryu–Takayanagi inequality on
the substrate (`cut` in its correct *area* role, B2).  It does NOT derive the geometry, the metric, or the
saturation `S = area`; it is the inequality, conditional on the bond-fits-area hypothesis. -/
theorem entropy_le_cut {dCut : Type*} [Fintype dCut] [DecidableEq dCut] {ρ : Matrix dCut dCut ℂ}
    (h : IsDensity ρ) {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) (S : Finset V)
    (hbond : Real.log (Fintype.card dCut) ≤ cut w S) :
    vonNeumannEntropy h ≤ cut w S :=
  le_trans (vonNeumannEntropy_le_log_card h) hbond

end TensorNetworkCut

section Causal

variable {E : Type*} (sig : E → E → Prop)

/-- **Causal reachability**: the reflexive–transitive closure of the *supplied* one-step signalling
relation `sig`.  **Honest caveat:** a *directed* causal order requires the orientation of `sig` to be
SUPPLIED (an input/output slicing, channel orientation, or record order) — a reversible unitary runtime
alone does NOT provide a time direction.  This builds the operational causal order from that supplied
signalling structure; it does not derive Lorentzian light-cones from nothing. -/
def Reach : E → E → Prop := Relation.ReflTransGen sig

/-- Causal reachability is **reflexive** (every event reaches itself). -/
theorem reach_refl (x : E) : Reach sig x x := Relation.ReflTransGen.refl

/-- Causal reachability is **transitive** — the preorder law of the causal order. -/
theorem reach_trans {x y z : E} (h1 : Reach sig x y) (h2 : Reach sig y z) : Reach sig x z :=
  Relation.ReflTransGen.trans h1 h2

/-- The **causal future cone** of an event `x`: all events it can causally influence. -/
def future (x : E) : Set E := {y | Reach sig x y}

theorem mem_future_self (x : E) : x ∈ future sig x := reach_refl sig x

/-- **★★ B4 — causal-cone monotonicity (no signalling outside the cone).**  If `x` causally precedes `y`,
then `y`'s future cone is contained in `x`'s: `future y ⊆ future x`.  Equivalently the causal future is
transitively closed — nothing reachable from a successor escapes the predecessor's cone, the operational
light-cone structure. -/
theorem future_subset_of_reach {x y : E} (h : Reach sig x y) : future sig y ⊆ future sig x :=
  fun _ hz => reach_trans sig h hz

/-- **★ B4 — outside the cone = not reachable.**  An event is outside `x`'s causal future *iff* it cannot
be reached from `x` (the definitional content of the light-cone: causal influence is exactly
reachability). -/
theorem not_mem_future_iff {x y : E} : y ∉ future sig x ↔ ¬ Reach sig x y := Iff.rfl

/-- **Causal equivalence**: mutual reachability `x ⤳ y ∧ y ⤳ x` (a causal "diamond" / the events on a
common causal cycle). -/
def CausalEquiv (x y : E) : Prop := Reach sig x y ∧ Reach sig y x

/-- **★★ B4 — mutual reachability is an equivalence relation.**  `CausalEquiv` is reflexive, symmetric,
and transitive — so the events quotient into causal classes on which `Reach` descends to an
*antisymmetric* partial order (the causal poset).  This is the finite operational causal structure: a
preorder by reachability, a partial order after identifying mutually-reachable events. -/
theorem causalEquiv_equivalence : Equivalence (CausalEquiv sig) where
  refl x := ⟨reach_refl sig x, reach_refl sig x⟩
  symm h := ⟨h.2, h.1⟩
  trans h1 h2 := ⟨reach_trans sig h1.1 h2.1, reach_trans sig h2.2 h1.2⟩

end Causal

section CroftonMetric

/-- An **exact finite metric**: a `0`-approximate pseudometric that additionally *separates points*
(`d x y = 0 → x = y`).  (`IsApproxPseudometric 0` alone permits zero distance between distinct points.) -/
structure IsFiniteMetric {X : Type*} (d : X → X → ℝ) : Prop where
  toApprox : IsApproxPseudometric (0 : ℝ) d
  eq_of_dist_eq_zero : ∀ {x y : X}, d x y = 0 → x = y

/-- **★★ C1 — the weighted cut / L¹-Crofton distance.**  `d(x,y) = ∑ᵢ ωᵢ·|χᵢ(x) − χᵢ(y)|`: an L¹
embedding along a finite family of nonnegative-weighted *separating-cut / probe* coordinates `χ : I → X → ℝ`.
This is the honest **entanglement → distance** reconstruction (the cut-cone / L¹ rule), generalizing the
single-coordinate `embedDist` and *repairing* `minCut_area_not_metric` (min-cut area is never a distance;
this *is* a provable metric).  **Honest invariant:** the weights `ω` and probes `χ` must come from SUPPLIED
entanglement/cut data — the claim is conditional on that data, and the reconstructed metric is a *finite
proto-distance*, not identified with the physical spacetime metric. -/
def weightedCutDist {I X : Type*} [Fintype I] (ω : I → ℝ) (χ : I → X → ℝ) (x y : X) : ℝ :=
  ∑ i : I, ω i * |χ i x - χ i y|

/-- The probe family **separates points**: any two distinct points are distinguished by some positive-weight
probe. -/
def WeightedProbesSeparate {I X : Type*} (ω : I → ℝ) (χ : I → X → ℝ) : Prop :=
  ∀ {x y : X}, x ≠ y → ∃ i : I, 0 < ω i ∧ χ i x ≠ χ i y

theorem weightedCutDist_nonneg {I X : Type*} [Fintype I] {ω : I → ℝ} {χ : I → X → ℝ}
    (hω : ∀ i, 0 ≤ ω i) (x y : X) : 0 ≤ weightedCutDist ω χ x y :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hω i) (abs_nonneg _))

theorem weightedCutDist_self {I X : Type*} [Fintype I] (ω : I → ℝ) (χ : I → X → ℝ) (x : X) :
    weightedCutDist ω χ x x = 0 := by
  simp [weightedCutDist]

theorem weightedCutDist_symm {I X : Type*} [Fintype I] (ω : I → ℝ) (χ : I → X → ℝ) (x y : X) :
    weightedCutDist ω χ x y = weightedCutDist ω χ y x := by
  unfold weightedCutDist
  exact Finset.sum_congr rfl (fun i _ => by rw [abs_sub_comm])

theorem weightedCutDist_triangle {I X : Type*} [Fintype I] {ω : I → ℝ} {χ : I → X → ℝ}
    (hω : ∀ i, 0 ≤ ω i) (x y z : X) :
    weightedCutDist ω χ x z ≤ weightedCutDist ω χ x y + weightedCutDist ω χ y z := by
  unfold weightedCutDist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  calc ω i * |χ i x - χ i z|
      ≤ ω i * (|χ i x - χ i y| + |χ i y - χ i z|) :=
        mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (hω i)
    _ = ω i * |χ i x - χ i y| + ω i * |χ i y - χ i z| := by ring

/-- **★★ C1 — the weighted Crofton distance is an exact pseudometric** (for nonnegative weights). -/
theorem weightedCutDist_isPseudometric {I X : Type*} [Fintype I] {ω : I → ℝ} {χ : I → X → ℝ}
    (hω : ∀ i, 0 ≤ ω i) : IsApproxPseudometric 0 (weightedCutDist ω χ) where
  nonneg := weightedCutDist_nonneg hω
  self := weightedCutDist_self ω χ
  symm := weightedCutDist_symm ω χ
  triangle := fun x y z => by simpa using weightedCutDist_triangle hω x y z

/-- The distance vanishes exactly when every positive-weight probe agrees on the two points. -/
theorem weightedCutDist_eq_zero_iff {I X : Type*} [Fintype I] {ω : I → ℝ} {χ : I → X → ℝ}
    (hω : ∀ i, 0 ≤ ω i) (x y : X) :
    weightedCutDist ω χ x y = 0 ↔ ∀ i : I, 0 < ω i → χ i x = χ i y := by
  unfold weightedCutDist
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hω i) (abs_nonneg _))]
  constructor
  · intro h i hi
    rcases mul_eq_zero.mp (h i (Finset.mem_univ i)) with h0 | h0
    · exact absurd h0 (ne_of_gt hi)
    · exact sub_eq_zero.mp (abs_eq_zero.mp h0)
  · intro h i _
    rcases eq_or_lt_of_le (hω i) with hi | hi
    · rw [← hi, zero_mul]
    · rw [h i hi, sub_self, abs_zero, mul_zero]

/-- **★★★ C1 — `weightedCutDist` is a genuine finite *metric* iff the probe family separates points.**
So an emergent distance reconstructed from a *separating* family of entanglement/cut probes really is a
metric — the honest finite Tier-3 reconstruction (a proto-distance, tagged; not the physical metric). -/
theorem weightedCutDist_isFiniteMetric_iff {I X : Type*} [Fintype I] {ω : I → ℝ} {χ : I → X → ℝ}
    (hω : ∀ i, 0 ≤ ω i) :
    IsFiniteMetric (weightedCutDist ω χ) ↔ WeightedProbesSeparate ω χ := by
  constructor
  · intro hm x y hxy
    by_contra hcon
    push_neg at hcon
    exact hxy (hm.eq_of_dist_eq_zero ((weightedCutDist_eq_zero_iff hω x y).mpr hcon))
  · intro hsep
    refine ⟨weightedCutDist_isPseudometric hω, ?_⟩
    intro x y hxy0
    by_contra hne
    obtain ⟨i, hi, hne'⟩ := hsep hne
    exact hne' ((weightedCutDist_eq_zero_iff hω x y).mp hxy0 i hi)

/-- C1 recovers the B1 single-coordinate `embedDist` as the one-probe, unit-weight case. -/
theorem weightedCutDist_singleton_eq_embedDist {X : Type*} (f : X → ℝ) :
    weightedCutDist (fun _ : PUnit => (1 : ℝ)) (fun _ => f) = embedDist f := by
  funext x y
  simp [weightedCutDist, embedDist]

end CroftonMetric

end QIQTH.EmergentSpacetime
