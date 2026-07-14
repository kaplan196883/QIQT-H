/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.TraceClass.Spectral
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The infinite-dimensional compact self-adjoint spectral theorem as an eigen-`HilbertBasis`

Every **compact self-adjoint** operator `T` on a (complex) Hilbert space admits an orthonormal
`HilbertBasis` of eigenvectors, with real eigenvalues. Mathlib supplies all the ingredients — the
compact spectral theorem `orthogonalComplement_iSup_eigenspaces_eq_bot` (density of the eigenspaces),
orthogonality of eigenspaces, per-eigenspace Hilbert bases (`exists_hilbertBasis`), and the
`Sigma`-orthonormal glue — but does **not** assemble the infinite-dimensional eigen-`HilbertBasis`
itself. That assembly is done here.

This **discharges** the carried eigenbasis hypothesis `hA` of `QIQTH.TraceClass`'s McKean–Singer
identity `traceE_eq_tsum_eigenvalues` for the compact self-adjoint case: given only
`IsCompactOperator T` and `IsSelfAdjoint T`, we produce an eigenbasis and hence
`traceE b T = ∑' i, μ i`.

## Main results

* `compactSelfAdjoint_hasEigenbasis` : a compact self-adjoint `T` has an orthonormal eigen-Hilbert
  basis `b` with real eigenvalues `μ`, `T (b i) = μ i • b i`.
* `compactSelfAdjoint_traceE_eq_tsum_eigenvalues` : combining the above with the McKean–Singer
  identity, `traceE b T = ∑' i, μ i` for some eigenbasis.

## Honest firewall

This is **pure functional analysis**. It removes the eigenbasis hypothesis *only* for **compact**
self-adjoint operators. The manifold input that the resolvent of the Laplacian `Δ` is compact
(Rellich–Kondrachov / elliptic regularity) is **not** proved here and remains the wall; nothing here
builds the manifold heat kernel or discharges the general `a₁ = R/6`. NOT the conjecture, NOT QG. No
axioms, no `sorry`.
-/

open scoped ComplexInnerProductSpace

namespace QIQTH.TraceClass

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The compact self-adjoint spectral theorem, packaged as an eigen-`HilbertBasis`.** A compact
self-adjoint operator `T` on a complex Hilbert space has an orthonormal `HilbertBasis` of
eigenvectors with real eigenvalues: there is an index type `κ`, a `HilbertBasis κ ℂ H` `b`, and real
eigenvalues `μ : κ → ℝ` with `T (b i) = μ i • b i` for all `i`.

The basis is `⨆`-assembled from per-eigenspace Hilbert bases: index `κ = Σ c : ℂ, ↥(W c)` where `W c`
indexes a Hilbert basis of the (closed, hence complete) `c`-eigenspace. Orthonormality across
eigenspaces is `OrthogonalFamily.orthonormal_sigma_orthonormal` applied to
`IsSymmetric.orthogonalFamily_eigenspaces`; density is the compact spectral theorem
`orthogonalComplement_iSup_eigenspaces_eq_bot`. Reality of the eigenvalues is
`IsSymmetric.conj_eigenvalue_eq_self`. -/
theorem compactSelfAdjoint_hasEigenbasis {T : H →L[ℂ] H}
    (hcomp : IsCompactOperator T) (hsa : IsSelfAdjoint T) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ H) (μ : κ → ℝ),
      ∀ i, T (b i) = ((μ i : ℝ) : ℂ) • b i := by
  classical
  -- Self-adjoint ⇒ symmetric (on the underlying linear map).
  have hsymm : (T : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  -- The eigenspaces.
  set E : ℂ → Submodule ℂ H := fun c => Module.End.eigenspace (T : H →ₗ[ℂ] H) c with hE
  -- Each eigenspace is closed, hence a complete space.
  have hcpl : ∀ c : ℂ, CompleteSpace (E c) := fun c =>
    (ContinuousLinearMap.isClosed_eigenspace T c).isComplete.completeSpace_coe
  -- A Hilbert basis `Bc c` of each eigenspace `E c`, indexed by `W c`.
  choose W Bc _hBc using fun c => by
    haveI := hcpl c
    exact exists_hilbertBasis ℂ (E c)
  -- The candidate orthonormal family in `H`.
  set v : (Σ c : ℂ, ↥(W c)) → H := fun a => (E a.1).subtypeₗᵢ (Bc a.1 a.2) with hv_def
  -- Orthonormal: `Sigma`-glue of the per-eigenspace orthonormal families across the orthogonal
  -- family of eigenspaces.
  have hv : Orthonormal ℂ v :=
    (hsymm.orthogonalFamily_eigenspaces).orthonormal_sigma_orthonormal
      (fun c => (Bc c).orthonormal)
  -- Density: the span of `v` has trivial orthogonal complement.
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    -- The direct sum of eigenspaces is contained in the closure of `span v`.
    have hkey : (⨆ c, E c) ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
      refine iSup_le (fun c => ?_)
      -- The eigenbasis of `E c`, pushed into `H`, lands inside `span v`.
      have hmap : (Submodule.span ℂ (Set.range (Bc c))).map ((E c).subtypeL : E c →ₗ[ℂ] H)
          ≤ Submodule.span ℂ (Set.range v) := by
        rw [Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨⟨c, a⟩, rfl⟩
      calc E c
          = (⊤ : Submodule ℂ (E c)).map ((E c).subtypeL : E c →ₗ[ℂ] H) := by
            rw [Submodule.toLinearMap_subtypeL, Submodule.map_subtype_top]
        _ = ((Submodule.span ℂ (Set.range (Bc c))).topologicalClosure).map
              ((E c).subtypeL : E c →ₗ[ℂ] H) := by rw [(Bc c).dense_span]
        _ ≤ ((Submodule.span ℂ (Set.range (Bc c))).map
              ((E c).subtypeL : E c →ₗ[ℂ] H)).topologicalClosure :=
            Submodule.topologicalClosure_map (E c).subtypeL _
        _ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure :=
            Submodule.topologicalClosure_mono hmap
    -- The compact spectral theorem: the eigenspaces are dense.
    have hbot : (⨆ c, E c)ᗮ = ⊥ :=
      ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcomp hsymm
    rw [← Submodule.orthogonal_closure (Submodule.span ℂ (Set.range v))]
    refine le_bot_iff.mp ?_
    calc ((Submodule.span ℂ (Set.range v)).topologicalClosure)ᗮ
        ≤ (⨆ c, E c)ᗮ := Submodule.orthogonal_le hkey
      _ = ⊥ := hbot
  -- Assemble the Hilbert basis.
  set b : HilbertBasis (Σ c : ℂ, ↥(W c)) ℂ H := HilbertBasis.mkOfOrthogonalEqBot hv hsp with hb_def
  have hcoe : ⇑b = v := by rw [hb_def]; exact HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp
  refine ⟨Σ c : ℂ, ↥(W c), b, fun a => a.1.re, fun i => ?_⟩
  -- `b i` is the eigenvector `↑(Bc i.1 i.2)`, lying in the `i.1`-eigenspace.
  have hbi : b i = (E i.1).subtypeₗᵢ (Bc i.1 i.2) := by rw [hcoe]
  have hmem : (b i) ∈ E i.1 := by rw [hbi]; exact Submodule.coe_mem _
  -- `b i` is a unit vector, hence nonzero.
  have hnorm : ‖b i‖ = 1 := by
    rw [hbi, LinearIsometry.norm_map]; exact (Bc i.1).orthonormal.norm_eq_one i.2
  have hne : b i ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm]; norm_num
  -- Hence `i.1` is an eigenvalue, so it is real.
  have hev : Module.End.HasEigenvalue (T : H →ₗ[ℂ] H) i.1 :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩
  have hre : ((i.1.re : ℝ) : ℂ) = i.1 :=
    Complex.conj_eq_iff_re.mp (hsymm.conj_eigenvalue_eq_self hev)
  -- The eigenvalue equation, with the real eigenvalue.
  have heig : T (b i) = i.1 • b i := by
    have h := Module.End.mem_eigenspace_iff.mp hmem
    simpa using h
  rw [heig]
  exact congrArg (· • b i) hre.symm

/-- **Trace = sum of eigenvalues for a compact self-adjoint operator, unconditionally.** Combining
`compactSelfAdjoint_hasEigenbasis` with `QIQTH.TraceClass.traceE_eq_tsum_eigenvalues`: a compact
self-adjoint `T` has an eigenbasis `b` with real eigenvalues `μ` for which
`traceE b T = ∑' i, μ i`. This removes the carried eigenbasis hypothesis of the McKean–Singer
identity for the compact self-adjoint case. -/
theorem compactSelfAdjoint_traceE_eq_tsum_eigenvalues {T : H →L[ℂ] H}
    (hcomp : IsCompactOperator T) (hsa : IsSelfAdjoint T) :
    ∃ (κ : Type u) (b : HilbertBasis κ ℂ H) (μ : κ → ℝ),
      (∀ i, T (b i) = ((μ i : ℝ) : ℂ) • b i) ∧ traceE b T = ∑' i, ((μ i : ℝ) : ℂ) := by
  obtain ⟨κ, b, μ, hA⟩ := compactSelfAdjoint_hasEigenbasis hcomp hsa
  exact ⟨κ, b, μ, hA, traceE_eq_tsum_eigenvalues b hA⟩

end QIQTH.TraceClass
