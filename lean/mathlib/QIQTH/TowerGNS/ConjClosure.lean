/-
  THE CONJUGATE CLOSURE CC1–CC4 (THE_CONJUGATE_CLOSURE_PLAN.md) — the abstract layer.

  The minimal closure theory for a conjugate-linear (starRingEnd ℂ)-semilinear partial map,
  via the ℝ-REDUCTION (binding verdict A1): a conjugate-linear map IS ℝ-linear, and Mathlib's
  entire id-closure theory (IsClosable / closure / le_closure / closureHasCore, in
  Topology/Algebra/Module/LinearPMap.lean) applies verbatim at R = ℝ through the global
  priority-900 instances (Module.complexToReal, NormedSpace.complexToReal,
  IsScalarTower.complexToReal) — no letI, ever.

  This file is ABSTRACT: it imports Mathlib only and knows nothing about TowerGNS.
  The four pieces (the new mathematical content, per verdict A2):

  CC1 — `realRestrict`: the ℝ-linear view of a conjugate-linear partial map, plus
        `ConjHomogeneous` (the memory that the map was conjugate-linear) and the proof that
        `realRestrict` is conjugate-homogeneous, derived from `map_smulₛₗ` ALONE (verdict A5:
        the single source of truth for the twist — a silently swapped `c`/`conj c` could not
        enter here without `map_smulₛₗ` itself being wrong).
  CC2 — `isClosable_of_seq`: the sequence-criterion closability bridge (absent from Mathlib
        even for id-linear maps); the hypothesis shape matches `towerTomita₀_closable'`
        verbatim (verdict A3).
  CC3 — `ConjHomogeneous.closure`: conjugate-homogeneity survives closure, UNCONDITIONALLY
        (junk branch: a non-closable map has `closure = itself`). Engine: the twisted
        continuous map p ↦ (c • p.1, conj c • p.2) preserves the graph, hence its closure.
  CC4 — `GraphSymm` + `GraphSymm.closure`: a swap-invariant graph survives closure (swap is
        continuous), giving FULL involutivity of the closure on its domain — with trivial
        kernel and range = domain — with NO adjoint anywhere.

  NOT here (verdict A4): Δ, J, the polar decomposition, any adjoint, any inner product,
  KMS-at-the-limit, a von Neumann type. Instantiation at TowerGNS is CC5 (a separate file).
-/
import Mathlib

namespace QIQTH.ConjClosure

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### CC1 — the ℝ-restriction view -/

/-- The ℝ-linear restriction of a conjugate-linear (`starRingEnd ℂ`-semilinear) partial map:
same domain (with scalars restricted to ℝ), same values. This is the vehicle that carries a
conjugate-linear partial operator into Mathlib's id-linear closure theory. -/
noncomputable def realRestrict (f : E →ₛₗ.[starRingEnd ℂ] F) : E →ₗ.[ℝ] F where
  domain := f.domain.restrictScalars ℝ
  toFun :=
    { toFun := fun x => f ⟨(x : E), x.2⟩
      map_add' := fun x y => f.map_add ⟨(x : E), x.2⟩ ⟨(y : E), y.2⟩
      map_smul' := fun r x => by
        have hmem : ((r : ℂ) • (x : E)) ∈ f.domain := f.domain.smul_mem _ x.2
        calc f ⟨((r • x : f.domain.restrictScalars ℝ) : E), (r • x).2⟩
            = f ⟨(r : ℂ) • (x : E), hmem⟩ :=
              congrArg (fun y : f.domain => f y)
                (Subtype.ext (Complex.coe_smul r (x : E)).symm)
          _ = starRingEnd ℂ ((r : ℂ)) • f ⟨(x : E), x.2⟩ :=
              f.map_smulₛₗ ((r : ℂ)) ⟨(x : E), x.2⟩
          _ = ((r : ℂ)) • f ⟨(x : E), x.2⟩ := by rw [Complex.conj_ofReal]
          _ = r • f ⟨(x : E), x.2⟩ := Complex.coe_smul r _
          _ = (RingHom.id ℝ) r • f ⟨(x : E), x.2⟩ := rfl }

@[simp]
theorem realRestrict_domain (f : E →ₛₗ.[starRingEnd ℂ] F) :
    (realRestrict f).domain = f.domain.restrictScalars ℝ :=
  rfl

/-- The value of the ℝ-restriction is the value of the original map (memberships transported
by definitional equality of the carriers). -/
theorem realRestrict_apply (f : E →ₛₗ.[starRingEnd ℂ] F) {x : E}
    (hx : x ∈ f.domain) (hx' : x ∈ (realRestrict f).domain) :
    realRestrict f ⟨x, hx'⟩ = f ⟨x, hx⟩ :=
  rfl

/-- Density transports across the ℝ-restriction: the carriers are equal. -/
theorem realRestrict_dense (f : E →ₛₗ.[starRingEnd ℂ] F)
    (h : Dense (f.domain : Set E)) :
    Dense (((realRestrict f).domain : Submodule ℝ E) : Set E) :=
  h

/-- An ℝ-linear partial map is conjugate-homogeneous when its domain is closed under the
ℂ-action and it intertwines `c •` with `conj c •`. This is the predicate that remembers, at
the ℝ-linear level, that the map came from a conjugate-linear one. -/
def ConjHomogeneous (g : E →ₗ.[ℝ] F) : Prop :=
  ∀ (c : ℂ) (x : g.domain), ∃ hcx : c • (x : E) ∈ g.domain,
    g ⟨c • (x : E), hcx⟩ = starRingEnd ℂ c • g x

/-- Pointwise unfolding of `ConjHomogeneous` (definitional). -/
theorem conjHomogeneous_iff {g : E →ₗ.[ℝ] F} :
    ConjHomogeneous g ↔ ∀ (c : ℂ) (x : g.domain), ∃ hcx : c • (x : E) ∈ g.domain,
      g ⟨c • (x : E), hcx⟩ = starRingEnd ℂ c • g x :=
  Iff.rfl

/-- The domain of a conjugate-homogeneous map is closed under the ℂ-action. -/
theorem ConjHomogeneous.smul_mem {g : E →ₗ.[ℝ] F} (hg : ConjHomogeneous g)
    (c : ℂ) (x : g.domain) : c • (x : E) ∈ g.domain := by
  obtain ⟨hcx, -⟩ := hg c x
  exact hcx

/-- Pointwise value form of `ConjHomogeneous`, with a caller-supplied membership proof. -/
theorem ConjHomogeneous.apply_smul {g : E →ₗ.[ℝ] F} (hg : ConjHomogeneous g)
    (c : ℂ) (x : g.domain) (hcx : c • (x : E) ∈ g.domain) :
    g ⟨c • (x : E), hcx⟩ = starRingEnd ℂ c • g x := by
  obtain ⟨hcx', hval⟩ := hg c x
  exact hval

/-- THE TWIST GUARD SOURCE (verdict A5): the ℝ-restriction of a conjugate-linear partial map
is conjugate-homogeneous, derived from `map_smulₛₗ` alone — the single source of truth for
the direction of the twist. -/
theorem realRestrict_conjHomogeneous (f : E →ₛₗ.[starRingEnd ℂ] F) :
    ConjHomogeneous (realRestrict f) := by
  intro c x
  have hx : (x : E) ∈ f.domain := x.2
  have hcx : c • (x : E) ∈ f.domain := f.domain.smul_mem c hx
  exact ⟨hcx, f.map_smulₛₗ c ⟨(x : E), hx⟩⟩

/-! ### CC2 — the bridge: the sequence criterion implies closability -/

/-- THE BRIDGE (verdict A3 shape): if every sequence in the domain converging to `0` whose
image converges forces the image limit to be `0`, then the partial map is closable. Absent
from Mathlib even for id-linear maps. Proof: the topological closure of the graph is a graph,
by `Submodule.toLinearPMap_graph_eq`, whose hypothesis is exactly a sequential statement in
the first-countable (hence Fréchet–Urysohn) space `E × F`. -/
theorem isClosable_of_seq (g : E →ₗ.[ℝ] F)
    (h : ∀ (x : ℕ → g.domain) (v : F),
      Tendsto (fun n => (x n : E)) atTop (𝓝 0) →
      Tendsto (fun n => g (x n)) atTop (𝓝 v) → v = 0) :
    g.IsClosable := by
  have key : ∀ p : E × F, p ∈ g.graph.topologicalClosure → p.fst = 0 → p.snd = 0 := by
    intro p hp hp1
    have hp' : p ∈ closure (g.graph : Set (E × F)) := hp
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hp'
    have hmem : ∀ n, (u n).1 ∈ g.domain := fun n =>
      LinearPMap.mem_domain_of_mem_graph (f := g) (y := (u n).2) (hu_mem n)
    have hval : ∀ n, g ⟨(u n).1, hmem n⟩ = (u n).2 := fun n =>
      ((LinearPMap.image_iff (hmem n)).mpr (hu_mem n)).symm
    have h1 : Tendsto (fun n => ((⟨(u n).1, hmem n⟩ : g.domain) : E)) atTop (𝓝 0) := by
      have hfst : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
        (continuous_fst.tendsto p).comp hu_lim
      rw [hp1] at hfst
      exact hfst
    have h2 : Tendsto (fun n => g (⟨(u n).1, hmem n⟩ : g.domain)) atTop (𝓝 p.2) := by
      have hsnd : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) :=
        (continuous_snd.tendsto p).comp hu_lim
      exact hsnd.congr fun n => (hval n).symm
    exact h (fun n => ⟨(u n).1, hmem n⟩) p.2 h1 h2
  exact ⟨g.graph.topologicalClosure.toLinearPMap,
    (Submodule.toLinearPMap_graph_eq _ key).symm⟩

/-! ### CC3 — the transfer: conjugate-homogeneity survives closure -/

/-- Conjugate-homogeneity survives closure, UNCONDITIONALLY. Main branch: the twisted
continuous map `p ↦ (c • p.1, conj c • p.2)` maps the graph into itself (pointwise from
`ConjHomogeneous`), hence maps the closure of the graph into itself
(`image_closure_subset_closure_image`); translating back through
`graph_closure_eq_closure_graph` gives the statement for `g.closure`. Junk branch: a
non-closable map has `closure = itself` (`LinearPMap.closure_def'`). -/
theorem ConjHomogeneous.closure {g : E →ₗ.[ℝ] F} (hg : ConjHomogeneous g) :
    ConjHomogeneous g.closure := by
  by_cases hc : g.IsClosable
  · intro c x
    -- the point (x, g.closure x) lies in the closure of the graph of g
    have hx' : ((x : E), g.closure x) ∈ _root_.closure (g.graph : Set (E × F)) := by
      have hmem : ((x : E), g.closure x) ∈ g.graph.topologicalClosure := by
        rw [hc.graph_closure_eq_closure_graph]
        exact g.closure.mem_graph x
      exact hmem
    -- the twisted continuous map
    have hcont : Continuous (fun p : E × F => (c • p.1, starRingEnd ℂ c • p.2)) :=
      ((continuous_const_smul c).comp continuous_fst).prodMk
        ((continuous_const_smul _).comp continuous_snd)
    -- it maps the graph into itself
    have himg : (fun p : E × F => (c • p.1, starRingEnd ℂ c • p.2)) ''
        (g.graph : Set (E × F)) ⊆ (g.graph : Set (E × F)) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hp
      obtain ⟨y, hy1, hy2⟩ := hp
      obtain ⟨hcy, hval⟩ := hg c y
      show (c • p.1, starRingEnd ℂ c • p.2) ∈ (g.graph : Set (E × F))
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      refine ⟨⟨c • (y : E), hcy⟩, ?_, ?_⟩
      · show c • (y : E) = c • p.1
        rw [hy1]
      · show g ⟨c • (y : E), hcy⟩ = starRingEnd ℂ c • p.2
        rw [hval, hy2]
    -- hence it maps the closure of the graph into itself
    have hq : (c • (x : E), starRingEnd ℂ c • g.closure x) ∈ g.closure.graph := by
      rw [← hc.graph_closure_eq_closure_graph]
      have h1 : (c • (x : E), starRingEnd ℂ c • g.closure x) ∈
          (fun p : E × F => (c • p.1, starRingEnd ℂ c • p.2)) ''
            _root_.closure (g.graph : Set (E × F)) :=
        ⟨((x : E), g.closure x), hx', rfl⟩
      exact closure_mono himg (image_closure_subset_closure_image hcont h1)
    -- translate the graph membership back into the ∃-form
    rw [LinearPMap.mem_graph_iff] at hq
    obtain ⟨y, hy1, hy2⟩ := hq
    have hdom : c • (x : E) ∈ g.closure.domain := by
      have hy2' := y.2
      rw [hy1] at hy2'
      exact hy2'
    refine ⟨hdom, ?_⟩
    have hxy : (⟨c • (x : E), hdom⟩ : g.closure.domain) = y := Subtype.ext hy1.symm
    rw [hxy]
    exact hy2
  · rw [LinearPMap.closure_def' hc]
    exact hg

/-! ### CC4 — the involution transfer -/

/-- A partial map (endomorphism shape) has a symmetric graph when the graph is invariant
under the swap `(x, y) ↦ (y, x)`. This is the adjoint-free carrier of involutivity. -/
def GraphSymm (g : E →ₗ.[ℝ] E) : Prop :=
  ∀ p ∈ g.graph, Prod.swap p ∈ g.graph

/-- Graph symmetry survives closure: swap is continuous, so a swap-invariant graph has a
swap-invariant closure. Junk branch as in `ConjHomogeneous.closure`. -/
theorem GraphSymm.closure {g : E →ₗ.[ℝ] E} (hg : GraphSymm g) : GraphSymm g.closure := by
  by_cases hc : g.IsClosable
  · intro p hp
    rw [← hc.graph_closure_eq_closure_graph] at hp ⊢
    have hp' : p ∈ _root_.closure (g.graph : Set (E × E)) := hp
    have hsub : Prod.swap '' (g.graph : Set (E × E)) ⊆ (g.graph : Set (E × E)) := by
      rintro _ ⟨q, hq, rfl⟩
      exact hg q hq
    have h1 : Prod.swap p ∈ Prod.swap '' _root_.closure (g.graph : Set (E × E)) :=
      ⟨p, hp', rfl⟩
    exact closure_mono hsub (image_closure_subset_closure_image continuous_swap h1)
  · rw [LinearPMap.closure_def' hc]
    exact hg

/-- A graph-symmetric map maps its domain into its domain. -/
theorem GraphSymm.apply_mem {g : E →ₗ.[ℝ] E} (hs : GraphSymm g) (x : g.domain) :
    g x ∈ g.domain := by
  have h : (g x, (x : E)) ∈ g.graph := hs _ (g.mem_graph x)
  exact LinearPMap.mem_domain_of_mem_graph h

/-- FULL involutivity from graph symmetry: applying `g` twice returns the argument
(no adjoint anywhere — the swap of `(x, g x)` is `(g x, x)`, and it is in the graph). -/
theorem GraphSymm.involutive {g : E →ₗ.[ℝ] E} (hs : GraphSymm g) (x : g.domain) :
    ∃ h1 : g x ∈ g.domain, g ⟨g x, h1⟩ = (x : E) := by
  have h : (g x, (x : E)) ∈ g.graph := hs _ (g.mem_graph x)
  have h1 : g x ∈ g.domain := LinearPMap.mem_domain_of_mem_graph h
  exact ⟨h1, ((LinearPMap.image_iff h1).mpr h).symm⟩

/-- Trivial kernel from graph symmetry: if `g x = 0` then `x = 0` (as an element of `E`). -/
theorem GraphSymm.eq_zero_of_apply_eq_zero {g : E →ₗ.[ℝ] E} (hs : GraphSymm g)
    (x : g.domain) (hx : g x = 0) : (x : E) = 0 := by
  have h : (g x, (x : E)) ∈ g.graph := hs _ (g.mem_graph x)
  rw [hx] at h
  exact g.graph_fst_eq_zero_snd h rfl

/-- Range equals domain from graph symmetry (both inclusions from involutivity). -/
theorem GraphSymm.range_eq_domain {g : E →ₗ.[ℝ] E} (hs : GraphSymm g) :
    Set.range (fun x : g.domain => g x) = (g.domain : Set E) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact hs.apply_mem x
  · intro hy
    obtain ⟨h1, hval⟩ := hs.involutive ⟨y, hy⟩
    exact ⟨⟨g ⟨y, hy⟩, h1⟩, hval⟩

end QIQTH.ConjClosure
