/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Tier-2 §2.2 — the min-cut bound on distinguishable RECORDS (capacity = area, from the code)

This is the **QG-facing** finite core of `docs/qg_roadmap/TIER_2_FINITE_QI_SUBSTRATE.md` §2.2: in a
finite holographic / tensor-network code, the number of **distinguishable records** across a
bipartition cut is bounded by the **min-cut "area"** (the product of bond dimensions crossing the
cut).  Finiteness alone gives only a *volume* law (Tier-0); the *area* law must EMERGE from the
code's factorization/redundancy structure — and it does, as a theorem ABOUT the code.

## The distinctive angle (why this is NOT just Ryu–Takayanagi again)

The existing `EmergentSpacetime.lean` graph-RT bounds an *entropy* by the min-cut.  This file bounds
the **rank / distinguishable-record count** — the zero-error effective Hilbert-space dimension seen
across the cut.  A rank bound is *strictly different* from an entropy bound: a reduced state can have
tiny entropy yet arbitrarily large support (long tails), so `S ≤ area` does NOT give `rank ≤ area`.
The record/capacity notion of QIQT-H (distinguishable records = dimension of the reduced support) is
exactly this rank, so the min-cut rank bound is the honest "capacity is area" statement.  It *implies*
`S ≤ log(rank) ≤ area·log d`, but not conversely.

## What is proved (all finite, axiom-free)

* `distinguishableRecords f := finrank K (range f)` — the record count of a bipartite flattening `f`
  (Schmidt rank / reduced-support dimension adapter point).
* `distinguishableRecords_le_of_factorization` — the linear-algebra core: if `f = r ∘ l` factors
  through a finite space `X`, then `distinguishableRecords f ≤ finrank X`.
* `cutSpace_finrank` — the cut index space `CutSpace K D C` has dimension `∏_{e∈C} D e` = the cut's
  bond capacity (its "area" in bond-dimension units).
* `distinguishableRecords_le_cut` — if the flattening factors through a cut `C` (the tensor-network
  semantic certificate `FactorsThroughCut`), the records are `≤` that cut's bond capacity.
* `mincut_bounds_distinguishable_records` — the §2.2 capstone: with a chosen min-cut `Cmin` among a
  finite family of separating cuts (each carrying the factorization certificate), the records are
  bounded by the **min-cut** bond capacity.
* `records_log_le_mincut_area` — the additive/log corollary: `log(records) ≤ (min-cut area)·log d`
  for a uniform bond dimension `d`, the "capacity ≤ area" form.

## Scope firewall (HONEST)

This is a finite STRUCTURAL theorem about a code: min-cut bounds distinguishable records, given the
tensor-network factorization certificate as a HYPOTHESIS (`FactorsThroughCut` — the network-specific
"split the contraction across the cut" fact, supplied per model).  It is **NOT** a derivation that
the physical world is holographic (the min-cut = geometric AREA identification is Tier-3, stays
OPEN), **NOT** max-flow/min-cut combinatorics (only a finite family of admissible cuts + a chosen
minimizer), **NOT** emergent spacetime, **NOT** QG.  No claim of numerical `G`, interacting matter,
or a continuum limit.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace QIQTH.RecordMincut

open scoped BigOperators

variable {K : Type*} [Field K]

/-- **Distinguishable-record count** of a bipartite flattening `f : U →ₗ[K] V`.
For a pure finite state, the flattening across `A | Aᶜ` is a linear map whose RANGE dimension is the
Schmidt rank = the dimension of the reduced-state support = the number of distinguishable records
seen across the cut.  This is the QIQT-H *capacity* notion (a rank, not an entropy). -/
noncomputable def distinguishableRecords
    {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f : U →ₗ[K] V) : ℕ :=
  Module.finrank K (LinearMap.range f)

/-- **The linear-algebra core.**  If a flattening `f` factors through a finite space `X`
(`f = r ∘ l`), then its record count is at most `dim X`.  (Range of `r ∘ l` sits inside range of `r`,
whose dimension is at most `dim X`.) -/
theorem distinguishableRecords_le_of_factorization
    {U X V : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup V] [Module K V]
    (f : U →ₗ[K] V) (l : U →ₗ[K] X) (r : X →ₗ[K] V) (h : f = r.comp l) :
    distinguishableRecords (K := K) f ≤ Module.finrank K X := by
  rw [distinguishableRecords, h]
  have hle : LinearMap.range (r.comp l) ≤ LinearMap.range r := by
    rintro y ⟨x, rfl⟩
    exact ⟨l x, rfl⟩
  exact (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le r)

variable {Edge : Type*} [DecidableEq Edge]

/-- **Cut index assignments** — one bond index per edge crossing the cut.  Its cardinality is
`∏_{e∈C} D e`, the cut's bond capacity.  (`abbrev` so the `Fintype`/`Module` instances resolve
through it transparently.) -/
abbrev CutAssignments (D : Edge → ℕ) (C : Finset Edge) : Type _ :=
  (e : C) → Fin (D e.1)

/-- **The cut vector space** — one basis vector per cut bond-index assignment.  This is the finite
"channel" the flattening must pass through. -/
abbrev CutSpace (K : Type*) [Field K] (D : Edge → ℕ) (C : Finset Edge) : Type _ :=
  CutAssignments D C → K

/-- **The bond capacity of a cut** `∏_{e∈C} D e` — the cut's "area" in bond-dimension units. -/
def cutBondCapacity (D : Edge → ℕ) (C : Finset Edge) : ℕ :=
  ∏ e ∈ C, D e

@[simp] theorem cutAssignments_card (D : Edge → ℕ) (C : Finset Edge) :
    Fintype.card (CutAssignments D C) = cutBondCapacity D C := by
  classical
  rw [show Fintype.card (CutAssignments D C) = ∏ e : C, Fintype.card (Fin (D e.1)) from
      Fintype.card_pi, cutBondCapacity]
  simp only [Fintype.card_fin]
  exact Finset.prod_coe_sort C D

@[simp] theorem cutSpace_finrank (D : Edge → ℕ) (C : Finset Edge) :
    Module.finrank K (CutSpace K D C) = cutBondCapacity D C := by
  classical
  rw [show Module.finrank K (CutSpace K D C) = Fintype.card (CutAssignments D C) from
      Module.finrank_fintype_fun_eq_card K, cutAssignments_card]

/-- **The tensor-network semantic certificate for a cut.**  The bipartite flattening `f` factors
through the cut index space `CutSpace K D C`.  This is proved, per model, by splitting the finite
contraction across the separating cut `C`:  `M_{a,b} = ∑_{s : CutAssignments C} L_{a,s} R_{s,b}`.
Carried as a HYPOTHESIS here — it is the only model-specific input. -/
def FactorsThroughCut
    {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (D : Edge → ℕ) (C : Finset Edge) (f : U →ₗ[K] V) : Prop :=
  ∃ (l : U →ₗ[K] CutSpace K D C) (r : CutSpace K D C →ₗ[K] V), f = r.comp l

/-- **Records are bounded by the bond capacity of any cut the flattening factors through.** -/
theorem distinguishableRecords_le_cut
    {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (D : Edge → ℕ) (C : Finset Edge) (f : U →ₗ[K] V)
    (hfac : FactorsThroughCut (K := K) D C f) :
    distinguishableRecords (K := K) f ≤ cutBondCapacity D C := by
  classical
  obtain ⟨l, r, h⟩ := hfac
  calc distinguishableRecords (K := K) f
      ≤ Module.finrank K (CutSpace K D C) :=
        distinguishableRecords_le_of_factorization (K := K) f l r h
    _ = cutBondCapacity D C := cutSpace_finrank (K := K) D C

/-- **A chosen minimizer among a finite family of admissible (separating) cuts.**  This replaces
max-flow/min-cut: the graph development supplies the finite family `cuts`; `Cmin` minimizes the bond
capacity over it. -/
structure IsMinCut (D : Edge → ℕ) (cuts : Finset (Finset Edge)) (Cmin : Finset Edge) : Prop where
  mem : Cmin ∈ cuts
  minimal : ∀ C ∈ cuts, cutBondCapacity D Cmin ≤ cutBondCapacity D C

/-- **Tier-2 §2.2 — the min-cut bounds distinguishable records.**

`f` is the bipartite flattening of the boundary state/code object across `A | Aᶜ`; `cuts` is the
finite family of graph cuts separating `A` from `Aᶜ`; each separating cut carries the tensor-network
factorization certificate.  Then the distinguishable-record capacity is bounded by the **min-cut**
bond capacity — the "capacity is area" law, as a theorem about the code. -/
theorem mincut_bounds_distinguishable_records
    {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (D : Edge → ℕ) (cuts : Finset (Finset Edge)) (Cmin : Finset Edge)
    (hmin : IsMinCut D cuts Cmin) (f : U →ₗ[K] V)
    (hfac : ∀ C ∈ cuts, FactorsThroughCut (K := K) D C f) :
    distinguishableRecords (K := K) f ≤ cutBondCapacity D Cmin :=
  distinguishableRecords_le_cut (K := K) D Cmin f (hfac Cmin hmin.mem)

/-- **The log / additive corollary — "capacity ≤ area".**  For a uniform bond dimension `d ≥ 1` on a
min-cut of `n` edges (`cutBondCapacity = d ^ n`), the log-record count is bounded by the min-cut
"area" `n` times `log d`:  `log (records) ≤ n · log d`.  (`records ≥ 1` carried, so `log` is
monotone-usable.) -/
theorem records_log_le_mincut_area
    {U V : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (D : Edge → ℕ) (cuts : Finset (Finset Edge)) (Cmin : Finset Edge)
    (hmin : IsMinCut D cuts Cmin) (f : U →ₗ[K] V)
    (hfac : ∀ C ∈ cuts, FactorsThroughCut (K := K) D C f)
    (d n : ℕ) (hcap : cutBondCapacity D Cmin = d ^ n)
    (hrec : 1 ≤ distinguishableRecords (K := K) f) :
    Real.log (distinguishableRecords (K := K) f) ≤ n * Real.log d := by
  have hbound := mincut_bounds_distinguishable_records (K := K) D cuts Cmin hmin f hfac
  rw [hcap] at hbound
  have hmono : Real.log (distinguishableRecords (K := K) f) ≤ Real.log ((d : ℝ) ^ n) := by
    apply Real.log_le_log
    · exact_mod_cast hrec
    · exact_mod_cast hbound
  calc Real.log (distinguishableRecords (K := K) f)
      ≤ Real.log ((d : ℝ) ^ n) := hmono
    _ = n * Real.log d := by rw [Real.log_pow]

end QIQTH.RecordMincut
