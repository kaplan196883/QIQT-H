/-
  THE VON NEUMANN CAMPAIGN — VN2 (THE_VON_NEUMANN_PLAN.md) — the graph decomposition.

  **The von Neumann graph orthogonal decomposition**: for a CLOSED partial linear map `T`
  on a Hilbert space over any `RCLike` field `𝕜`, every `h : E` decomposes against the
  graph of `T`: there is an `x ∈ dom T` with
      `⟪a, h − x⟫ = ⟪T a, T x⟫`  for every `a ∈ dom T`.
  This is the inner-product shadow of the orthogonal decomposition
      `(h, 0) = (x, T x) + z`,  `z ⊥ graph T`,
  in the `L²` product `WithLp 2 (E × E)` — the single geometric input of von Neumann's
  `T†T` theorem (surjectivity of `1 + T†T`, VN3) and of the self-adjointness of the
  modular operator (VN4/VN5). ABSENT from Mathlib at this pin: the closest artifact,
  `Submodule.adjoint` (Analysis/InnerProductSpace/LinearPMap.lean), transports the graph
  into the same `L²` product but only to DEFINE the adjoint; no decomposition statement.

  DELIBERATELY adjoint-free, in statement AND proof: the consumer (VN4) instantiates at
  `𝕜 = ℝ` on the closure of the antilinear conjugation `S̄`, where the ℝ-adjoint would be
  the wrong object — only the closed graph and the Hilbert geometry are used.

  Route: `K :=` the graph of `T` pulled back through `WithLp.linearEquiv` into
  `WithLp 2 (E × E)` (a `comap`, so membership is definitional); `K` is closed because
  `ofLp` is continuous and `T.IsClosed`; `IsClosed → CompleteSpace K →
  K.HasOrthogonalProjection`; `Submodule.exists_add_mem_mem_orthogonal` applied to
  `toLp 2 (h, 0)`; the `K`-component is a graph element `(x, T x)`
  (`LinearPMap.mem_graph_iff`), the orthogonal component `z` has components
  `(h − x, −T x)`, and expanding `⟪(a, T a), z⟫ = 0` with `WithLp.prod_inner_apply`
  gives the pairing.

  This file is ABSTRACT and REUSABLE: Mathlib-only imports, no QIQTH dependency (a
  Mathlib-gap contribution). NOT here (deliberately): the composite `T†T` (VN3), any
  self-adjointness statement (VN1/VN5), any density hypothesis (not needed — closedness
  alone carries the decomposition).
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap

namespace QIQTH.VonNeumann

open LinearPMap WithLp
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **★★★ The von Neumann graph decomposition (VN2):** for a CLOSED partial linear map
`T` on a Hilbert space over any `RCLike` field, every vector `h` admits an `x` in the
domain of `T` with `⟪a, h − x⟫ = ⟪T a, T x⟫` for all `a` in the domain — the projection
of `(h, 0)` onto the (closed) graph of `T` inside the `L²` product `WithLp 2 (E × E)`,
read off in components. Adjoint-free by design: at `𝕜 = ℝ` this applies to the closure
of an ANTILINEAR map (where the ℝ-adjoint is the wrong object), which is exactly how the
modular-operator consumer uses it. -/
theorem exists_pairing_of_isClosed
    {T : E →ₗ.[𝕜] E} (hT : T.IsClosed) (h : E) :
    ∃ x : T.domain, ∀ a : T.domain, ⟪(a : E), h - (x : E)⟫_𝕜 = ⟪T a, T x⟫_𝕜 := by
  -- the graph of `T`, living inside the `L²` product (membership is definitional)
  set K : Submodule 𝕜 (WithLp 2 (E × E)) :=
    T.graph.comap (WithLp.linearEquiv 2 𝕜 (E × E) : WithLp 2 (E × E) →ₗ[𝕜] E × E)
    with hKdef
  have hmemK : ∀ w : WithLp 2 (E × E), w ∈ K ↔ ofLp w ∈ T.graph := fun _ => Iff.rfl
  -- `K` is closed: the `ofLp`-preimage of the closed graph
  have hK : IsClosed (K : Set (WithLp 2 (E × E))) := by
    have hset : (K : Set (WithLp 2 (E × E))) = ofLp ⁻¹' (T.graph : Set (E × E)) := rfl
    rw [hset]
    exact IsClosed.preimage (prod_continuous_ofLp 2 E E) hT
  haveI : CompleteSpace K := hK.completeSpace_coe
  -- decompose `(h, 0)` against `K` (orthogonal projection exists by completeness)
  obtain ⟨y, hyK, z, hzK, hv⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := K) (toLp 2 ((h, 0) : E × E))
  -- the `K`-component is a graph element `(x, T x)`
  obtain ⟨x, hx1, hx2⟩ := T.mem_graph_iff.mp ((hmemK y).mp hyK)
  -- component identities: `z = (h − x, −T x)`
  have hofLp : ofLp (toLp 2 ((h, 0) : E × E)) = ofLp (y + z) := congrArg ofLp hv
  have hfst : h = (ofLp y).1 + (ofLp z).1 := congrArg Prod.fst hofLp
  have hsnd : (0 : E) = (ofLp y).2 + (ofLp z).2 := congrArg Prod.snd hofLp
  have hz1 : (ofLp z).1 = h - (x : E) := by
    rw [hfst, ← hx1]
    abel
  have hz2 : (ofLp z).2 = -(T x) := by
    refine eq_neg_of_add_eq_zero_right ?_
    rw [hx2]
    exact hsnd.symm
  refine ⟨x, fun a => ?_⟩
  -- `(a, T a) ⊥ z`, expanded in components through the `L²` inner product
  have h0 : ⟪(a : E), (ofLp z).1⟫_𝕜 + ⟪T a, (ofLp z).2⟫_𝕜 = 0 := by
    have hmem : toLp 2 (((a : E), T a) : E × E) ∈ K := (hmemK _).mpr (T.mem_graph a)
    have hoz := (Submodule.mem_orthogonal K z).mp hzK _ hmem
    rw [WithLp.prod_inner_apply] at hoz
    exact hoz
  rw [hz1, hz2, inner_neg_right, ← sub_eq_add_neg] at h0
  exact sub_eq_zero.mp h0

end QIQTH.VonNeumann
