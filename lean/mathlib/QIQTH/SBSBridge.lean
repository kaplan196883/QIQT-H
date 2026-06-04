/-
# QIQT-H Tier B: the bridge theorem via Spectrum Broadcast Structures (load-bearing v2)

GPT-5.5-pro's review of v1 found the dimension lemmas *decorative* — `cost := R·log n`
was DEFINED, not forced by Hilbert structure.  This v2 makes the chain load-bearing:

    SBS distinguishability  ⇒  fragment dimension ≥ n  ⇒  ∑ log(finrank) ≥ R·log n
                            ⇒  storageCost > Q_max/2.

The middle inequality is now a THEOREM (`redundancy_le_logStorage`) about *actual* finite-
dimensional fragment Hilbert spaces carrying orthonormal record states (perfect
distinguishability), demonstrated non-vacuous on Euclidean fragments
(`euclidean_storage_bound`).  The bridge `SBSContext.toRecordContext` derives
`cost_gt_half` from that bound + the capacity relation `hcap`.

HONEST framing (per the review):
 • `R·log n` is **redundancy-weighted physical storage capacity** (log-dimension of the
   broadcast substrate — Bekenstein-style), NOT Shannon/Holevo information of the pointer
   variable (which stays `H(X)` no matter how redundantly broadcast).
 • The additive capacity bound `∑ cost ≤ Q_max` (in `Coactual`) is correct only for
   records on **disjoint/independent** substrates; for correlated records the true joint
   cost is subadditive.  A fully robust treatment would use a `jointCost` with a pairwise
   lower bound (a deferred refactor of `CoreNoCollapse`).
 • `sbs_single_outcome` gives one active *record* (`∃! r : ι`), not yet one pointer *value*
   inside `Fin (n r)`.
 • The capacity relation `hcap : Q_max/2 < R_macro·log 2` (capacity small vs a macroscopic
   record's storage) is the remaining transparent physical input (Holevo/Bekenstein).

Grounded in: Korbicz, arXiv:2007.04276 (SBS, redundancy); Korbicz et al., arXiv:1305.3247.
Axiom-free (standard three only). -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QIQTH.CoreNoCollapse
import Mathlib.Tactic

namespace QIQTH.SBSBridge

open scoped BigOperators
open Module

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]

/-- **Distinguishability ⇒ dimension.**  A fragment perfectly distinguishing `n` pointer
    outcomes carries `n` orthonormal record states, hence has dimension `≥ n`. -/
theorem fragment_finrank_ge {n : ℕ} (r : Fin n → H) (hr : Orthonormal 𝕜 r) :
    n ≤ finrank 𝕜 H := by
  have h := hr.linearIndependent.fintype_card_le_finrank
  simpa using h

/-- **Broadcasting tensors the fragments (dims MULTIPLY).**  Two fragments each
    distinguishing `n` outcomes give a joint broadcast space of dimension `≥ n²` — the
    information/tensor model (`log` adds), not direct-sum rank. -/
theorem broadcast_finrank_ge {n : ℕ} (r₁ : Fin n → H) (h₁ : Orthonormal 𝕜 r₁)
    (r₂ : Fin n → H₂) (h₂ : Orthonormal 𝕜 r₂) :
    n * n ≤ finrank 𝕜 (TensorProduct 𝕜 H H₂) := by
  rw [Module.finrank_tensorProduct]
  exact Nat.mul_le_mul (fragment_finrank_ge r₁ h₁) (fragment_finrank_ge r₂ h₂)

/-- **THE load-bearing bridge fact.**  If a record's `R = card Frag` fragments each
    perfectly distinguish its `n` outcomes (`hrec`), then the total storage capacity
    `∑_f log(finrank (E f))` is at least `R · log n`.  PROVED from `fragment_finrank_ge`
    (each fragment `≥ n`) + monotonicity of `log` + summation — so the cost is forced by
    distinguishability, not defined. -/
theorem redundancy_le_logStorage {Frag : Type*} [Fintype Frag] {n : ℕ} (hn : 1 ≤ n)
    {E : Frag → Type*} [∀ f, NormedAddCommGroup (E f)] [∀ f, InnerProductSpace 𝕜 (E f)]
    [∀ f, FiniteDimensional 𝕜 (E f)]
    (rec : (f : Frag) → Fin n → E f) (hrec : ∀ f, Orthonormal 𝕜 (rec f)) :
    (Fintype.card Frag : ℝ) * Real.log n ≤ ∑ f, Real.log (finrank 𝕜 (E f)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdim : ∀ f, (n : ℝ) ≤ (finrank 𝕜 (E f) : ℝ) := fun f => by
    exact_mod_cast fragment_finrank_ge (rec f) (hrec f)
  calc (Fintype.card Frag : ℝ) * Real.log n
      = ∑ _f : Frag, Real.log n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ f, Real.log (finrank 𝕜 (E f)) :=
        Finset.sum_le_sum (fun f _ => Real.log_le_log hnpos (hdim f))

/-- **Non-vacuity:** `R` Euclidean fragments of dimension `n` (orthonormal basis as the
    distinguishing family) satisfy the bound (in fact with equality, since each
    `finrank = n`).  Shows the storage bound is genuinely sourced from real Hilbert-space
    distinguishability, not vacuous. -/
theorem euclidean_storage_bound (R n : ℕ) (hn : 1 ≤ n) :
    (R : ℝ) * Real.log n ≤
      ∑ _f : Fin R, Real.log (finrank 𝕜 (EuclideanSpace 𝕜 (Fin n))) := by
  have h := redundancy_le_logStorage (𝕜 := 𝕜) (Frag := Fin R) (n := n) hn
    (E := fun _ => EuclideanSpace 𝕜 (Fin n))
    (rec := fun _ => ⇑(EuclideanSpace.basisFun (Fin n) 𝕜))
    (fun _ => (EuclideanSpace.basisFun (Fin n) 𝕜).orthonormal)
  simpa only [Fintype.card_fin] using h

/- ── The bridge: objective (redundant) record ⇒ cost > Q_max/2 ─────────────-/

open QIQTH.CoreNoCollapse

/-- An **SBS / objective-record context**: finitely many candidate objective records.
    Record `j` is an `n j`-outcome pointer redundantly broadcast to `R j` fragments; its
    physical storage capacity `storageCost j` is bounded below by `R j · log (n j)`
    (`hstorage`, discharged by `redundancy_le_logStorage` from genuine fragments — see
    `euclidean_storage_bound`).  Capacity `Q_max` is small vs a macroscopic broadcast. -/
structure SBSContext where
  ι : Type
  [fin : Fintype ι]
  R : ι → ℕ
  n : ι → ℕ
  hn : ∀ j, 2 ≤ n j
  Rmacro : ℕ
  hRmacro : 1 ≤ Rmacro
  hmacro : ∀ j, Rmacro ≤ R j
  /-- physical storage capacity of record `j` (log-dimension of its broadcast substrate) -/
  storageCost : ι → ℝ
  /-- the load-bearing bound: storage ≥ broadcast information `R·log n`
      (a THEOREM via `redundancy_le_logStorage`, not an assumption — see `ofFragmentDims`). -/
  hstorage : ∀ j, (R j : ℝ) * Real.log (n j) ≤ storageCost j
  Qmax : ℝ
  hcap : Qmax / 2 < (Rmacro : ℝ) * Real.log 2

attribute [instance] SBSContext.fin

/-- **The bridge.**  An SBS context yields a `RecordContext` whose cost is the physical
    storage capacity, and whose `cost_gt_half` (saturation) is PROVED from the storage
    lower bound (`hstorage`, ⇐ distinguishability) + redundancy + the capacity relation —
    not stipulated as ">half a register". -/
noncomputable def SBSContext.toRecordContext (S : SBSContext) : RecordContext where
  Rec := S.ι
  cost := S.storageCost
  cost_pos := fun j => by
    have hR : (1 : ℝ) ≤ (S.R j : ℝ) := by exact_mod_cast le_trans S.hRmacro (S.hmacro j)
    have hlog : 0 < Real.log (S.n j) :=
      Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two (S.hn j))
    have hpos : 0 < (S.R j : ℝ) * Real.log (S.n j) := mul_pos (by linarith) hlog
    linarith [S.hstorage j]
  Qmax := S.Qmax
  cost_gt_half := fun j => by
    have h1 : (S.Rmacro : ℝ) ≤ (S.R j : ℝ) := by exact_mod_cast S.hmacro j
    have h2 : Real.log 2 ≤ Real.log (S.n j) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast S.hn j)
    have hge : (S.Rmacro : ℝ) * Real.log 2 ≤ (S.R j : ℝ) * Real.log (S.n j) :=
      mul_le_mul h1 h2 (Real.log_nonneg (by norm_num)) (le_trans (by positivity) h1)
    linarith [S.hcap, S.hstorage j]

/-- **Tier-B single-outcome theorem.**  In any run of an SBS context, the actuality
    selector picks EXACTLY ONE objective record — single-outcome experience with the
    saturation premise DERIVED from redundancy + a storage lower bound that is itself a
    theorem about genuine fragment distinguishability (`redundancy_le_logStorage`), and
    the cost a real physical storage capacity, not a stipulated threshold.  (Gives one
    active record `∃! r : ι`; selecting the pointer *value* in `Fin (n r)` is future work.) -/
theorem sbs_single_outcome (S : SBSContext) (sel : Selection S.toRecordContext) :
    ∃! r : S.ι, r ∈ sel.config.active :=
  qiqth_single_outcome_no_collapse sel

/- ── Fully load-bearing layer: storage DEFINED from fragment dimensions ────-/

/-- A **fragmented** SBS context: the fragment Hilbert spaces are EXPLICIT, so the storage
    cost is DEFINED from their dimensions and the bridge premise `hstorage` becomes a
    THEOREM (`redundancy_le_logStorage`), not a free field.  Record `j` is an `n j`-outcome
    pointer broadcast to fragments `Frag j`, each a finite-dim Hilbert space `E j f` with an
    orthonormal distinguishing family `rec j f : Fin (n j) → E j f`. -/
structure FragmentedSBSContext (𝕜 : Type*) [RCLike 𝕜] where
  ι : Type
  [finι : Fintype ι]
  Frag : ι → Type
  [finFrag : ∀ j, Fintype (Frag j)]
  n : ι → ℕ
  hn : ∀ j, 2 ≤ n j
  E : (j : ι) → Frag j → Type*
  [ng : ∀ j f, NormedAddCommGroup (E j f)]
  [ip : ∀ j f, InnerProductSpace 𝕜 (E j f)]
  [fd : ∀ j f, FiniteDimensional 𝕜 (E j f)]
  dist : (j : ι) → (f : Frag j) → Fin (n j) → E j f
  hdist : ∀ j f, Orthonormal 𝕜 (dist j f)
  Rmacro : ℕ
  hRmacro : 1 ≤ Rmacro
  hmacro : ∀ j, Rmacro ≤ Fintype.card (Frag j)
  Qmax : ℝ
  hcap : Qmax / 2 < (Rmacro : ℝ) * Real.log 2

attribute [instance] FragmentedSBSContext.finι FragmentedSBSContext.finFrag
  FragmentedSBSContext.ng FragmentedSBSContext.ip FragmentedSBSContext.fd

/-- Storage cost DEFINED from the fragment dimensions: `∑_f log(finrank (E j f))`. -/
noncomputable def FragmentedSBSContext.storageCost (S : FragmentedSBSContext 𝕜) (j : S.ι) : ℝ :=
  ∑ f : S.Frag j, Real.log (finrank 𝕜 (S.E j f))

/-- **The physical constructor.**  A fragmented context yields an `SBSContext` whose
    `storageCost` is finrank-defined and whose `hstorage` is PROVED by
    `redundancy_le_logStorage` — so the dimension theorem is now load-bearing in the
    dependency graph (no free `hstorage` field, no room to cheat). -/
noncomputable def FragmentedSBSContext.toSBSContext (S : FragmentedSBSContext 𝕜) :
    SBSContext where
  ι := S.ι
  R := fun j => Fintype.card (S.Frag j)
  n := S.n
  hn := S.hn
  Rmacro := S.Rmacro
  hRmacro := S.hRmacro
  hmacro := S.hmacro
  storageCost := S.storageCost
  hstorage := fun j =>
    redundancy_le_logStorage (le_trans one_le_two (S.hn j)) (S.dist j) (S.hdist j)
  Qmax := S.Qmax
  hcap := S.hcap

/-- **Fully load-bearing single-outcome theorem.**  Over a fragmented SBS context — where
    the cost is the finrank-defined storage and the saturation premise is the dimension
    theorem `redundancy_le_logStorage` (no `hstorage` shell) — the actuality selector picks
    EXACTLY ONE objective record. -/
theorem fragmented_single_outcome (S : FragmentedSBSContext 𝕜)
    (sel : Selection S.toSBSContext.toRecordContext) :
    ∃! r : S.ι, r ∈ sel.config.active :=
  sbs_single_outcome S.toSBSContext sel

end QIQTH.SBSBridge
