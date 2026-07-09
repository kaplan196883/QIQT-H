/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# METRIC FROM STATE — geometry as the OUTPUT of an entangled state (M1 + M2)

This is the first increment of the METRIC-FROM-STATE campaign
(`docs/qg_roadmap/METRIC_FROM_STATE_PLAN.md`): deriving a spatial metric as the **output** of a finite
entangled state, moving the metric `g` from a hypothesis to a conclusion.

## The pipeline

    state ψ  ──►  cut-rank profile  ──►  adjacency graph G(ψ)  ──►  metric d_ψ = G(ψ).dist

The cut-rank of a region `A` is `q ^ (boundary A)`, where `boundary A` is the number of entanglement
bonds (edges) crossing the cut — an honest combinatorial "area" of `A`.  Two vertices are declared
**adjacent** exactly when their joint cut-rank is *strictly submultiplicative*,
`cutRank {u}·cutRank {v} > cutRank {u,v}` — i.e. when they carry positive Rényi-0 mutual information (no
matrix logs).  The key theorem (**M1**) is that this **DECODES the graph back**: `rankMIGraph S = G`.
Then (**M2**) the graph-geodesic distance is a genuine metric equal to `G.dist` — reusing the existing
axiom-free `EmergentSpacetime.graphDist_isFiniteMetric`.

## Anti-circularity (binding)

`boundary` is carried as the crossing-bond count with the geometric **defect identity**
`boundary {u} + boundary {v} = boundary {u,v} + 2·[u∼v]` (a property any edge-crossing count
satisfies).  The graph `G` is *recovered* from the cut-rank by a proved theorem, NOT by definition; the
profile is the *state's* property (an explicit state realizing it is the next brick, M3).  Nothing here
is indexed by `G`'s edges circularly — `boundary`/`q` are the data, `G` is decoded.

## Scope firewall (HONEST)

This derives a **finite spatial graph-metric from a cut-rank profile** (the state-side realization of
that profile is M3).  It is NOT a continuum Riemannian metric, NOT GR, and does NOT derive WHY a
physical state carries this entanglement (the dynamical source is the open wall).  Carried inputs (the
profile, connectivity) are HYPOTHESES, never axioms; the decoding is proved, not definitional.  NOT
numerical-`G`; NOT QG.
-/
import QIQTH.EmergentSpacetime
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace QIQTH.MetricFromState

open QIQTH.EmergentSpacetime

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The cut-rank profile of a state**, decoupled from any Hilbert-space realization.  `boundary A`
is the number of entanglement bonds crossing the cut `A | Aᶜ` (the combinatorial "area" of `A`), the
cut-rank is `q ^ boundary A`, and `defect` is the crossing-count identity that any edge-boundary
satisfies:  `boundary {u} + boundary {v} = boundary {u,v} + 2·[u∼v]`.  Realized by an explicit state
in the next brick (M3). -/
structure CutRankProfile (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- bond dimension `≥ 2`. -/
  q : ℕ
  hq : 2 ≤ q
  /-- number of entanglement bonds crossing the cut `A | Aᶜ` (combinatorial area of `A`). -/
  boundary : Finset V → ℕ
  /-- the crossing-count defect: the bond `{u,v}` (present iff `u∼v`) is counted in `boundary {u}` and
  `boundary {v}` but NOT in `boundary {u,v}` (both endpoints inside), hence the `2·[u∼v]` deficit. -/
  defect : ∀ u v, u ≠ v →
    boundary {u} + boundary {v} = boundary {u, v} + 2 * (if G.Adj u v then 1 else 0)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The cut-rank `q ^ boundary A` of a region. -/
def cutRank (S : CutRankProfile G) (A : Finset V) : ℕ := S.q ^ S.boundary A

lemma cutRank_pos (S : CutRankProfile G) (A : Finset V) : 1 ≤ cutRank S A :=
  Nat.one_le_pow _ _ (by have := S.hq; omega)

/-- **The mutual-information adjacency the state induces.**  `u` and `v` are adjacent exactly when
their cut-rank is strictly submultiplicative — positive Rényi-0 mutual information. -/
def rankMIGraph (S : CutRankProfile G) : SimpleGraph V where
  Adj u v := u ≠ v ∧ cutRank S {u} * cutRank S {v} > cutRank S {u, v}
  symm := fun u v ⟨hne, hgt⟩ => ⟨hne.symm, by rw [Finset.pair_comm, mul_comm]; exact hgt⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- **The decoding equivalence:** for `u ≠ v`, strict submultiplicativity of the cut-rank holds
exactly when `u ∼ v` in `G`.  Algebra: `cutRank{u}·cutRank{v} = cutRank{u,v}·q^(2·[u∼v])` (from the
crossing defect), and `q ≥ 2` makes `q^(2·[u∼v]) > 1 ⟺ [u∼v] = 1`. -/
theorem submult_iff_adj (S : CutRankProfile G) {u v : V} (hne : u ≠ v) :
    cutRank S {u} * cutRank S {v} > cutRank S {u, v} ↔ G.Adj u v := by
  have hkey : cutRank S {u} * cutRank S {v}
      = cutRank S {u, v} * S.q ^ (2 * (if G.Adj u v then 1 else 0)) := by
    simp only [cutRank, ← pow_add]; rw [S.defect u v hne]
  have hcpos : 0 < cutRank S {u, v} := cutRank_pos S _
  rw [gt_iff_lt, hkey]
  constructor
  · intro hlt
    have h1 : (1 : ℕ) < S.q ^ (2 * (if G.Adj u v then 1 else 0)) := by
      have hmul : cutRank S {u, v} * 1
          < cutRank S {u, v} * S.q ^ (2 * (if G.Adj u v then 1 else 0)) := by simpa using hlt
      exact lt_of_mul_lt_mul_left hmul (Nat.zero_le _)
    by_contra hadj
    simp only [hadj, if_false, mul_zero, pow_zero, lt_self_iff_false] at h1
  · intro hadj
    rw [if_pos hadj]
    have hq1 : (1 : ℕ) < S.q ^ (2 * 1) :=
      lt_of_lt_of_le (by have := S.hq; omega : (1:ℕ) < S.q) (Nat.le_self_pow (by norm_num) _)
    have := mul_lt_mul_of_pos_left hq1 hcpos
    simpa using this

/-- **M1 — the state DECODES its graph.**  From the crossing-count profile, the induced
mutual-information adjacency recovers `G` exactly: `rankMIGraph S = G`.  The graph is an OUTPUT of the
cut-rank data, proved (not definitional). -/
theorem rankMIGraph_eq (S : CutRankProfile G) : rankMIGraph S = G := by
  ext u v
  constructor
  · rintro ⟨hne, hgt⟩; exact (submult_iff_adj S hne).mp hgt
  · intro hadj
    exact ⟨G.ne_of_adj hadj, (submult_iff_adj S (G.ne_of_adj hadj)).mpr hadj⟩

/-- **M2 — the decoded metric.**  The graph-geodesic distance of the state-induced graph, reusing the
axiom-free `EmergentSpacetime.graphDist`. -/
noncomputable def decodedDist (S : CutRankProfile G) (x y : V) : ℝ :=
  graphDist (rankMIGraph S) x y

/-- The decoded distance IS the geodesic distance of `G` (since `rankMIGraph S = G`). -/
@[simp] theorem decodedDist_eq (S : CutRankProfile G) (x y : V) :
    decodedDist S x y = graphDist G x y := by
  simp only [decodedDist, rankMIGraph_eq]

/-- **M2 capstone — the state OUTPUTS a genuine finite metric.**  For a connected decoded graph, the
metric derived from the state's entanglement (`decodedDist`) is a genuine finite metric — geometry as
an output of the cut-rank profile, reusing `graphDist_isFiniteMetric`. -/
theorem decodedDist_isFiniteMetric (S : CutRankProfile G) (hconn : G.Connected) :
    IsFiniteMetric (decodedDist S) := by
  have h : decodedDist S = graphDist G := by
    funext x y; exact decodedDist_eq S x y
  rw [h]; exact graphDist_isFiniteMetric G hconn

/-! ## M3 — an EXPLICIT graph realizes the crossing-defect profile (defect PROVEN, not carried)

The cut-rank profile's `defect` field is not a vacuous hypothesis: it is satisfied by the genuine
edge-crossing count of any finite graph.  `crossingCard G A = ∑ v∈A, (neighborFinset v \ A).card` is
the number of entanglement bonds (edges) crossing the cut `A | Aᶜ` (directed boundary; each crossing
edge counted once at its `A`-endpoint).  We prove the defect
`crossingCard {u} + crossingCard {v} = crossingCard {u,v} + 2·[u∼v]` by partitioning each neighbor
set at `{u,v}` (no ℕ-subtraction), then package the explicit profile `explicitProfile G q` — for which
`rankMIGraph = G` becomes a theorem about a REAL graph's crossing-count area functional, not a carried
assumption. -/

variable [DecidableRel (· = · : V → V → Prop)]

/-- The crossing-edge count of `A` (combinatorial "area" of the cut `A | Aᶜ`). -/
def crossingCard (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  ∑ x ∈ A, (G.neighborFinset x \ A).card

variable {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma crossingCard_singleton (x : V) :
    crossingCard G ({x} : Finset V) = (G.neighborFinset x).card := by
  unfold crossingCard
  rw [Finset.sum_singleton, Finset.sdiff_singleton_eq_erase,
    Finset.erase_eq_of_notMem (by rw [SimpleGraph.mem_neighborFinset]; exact fun h => (G.ne_of_adj h) rfl)]

private lemma nbr_inter_pair_left (u v : V) :
    G.neighborFinset u ∩ ({u, v} : Finset V) = if G.Adj u v then ({v} : Finset V) else ∅ := by
  by_cases h : G.Adj u v
  · rw [if_pos h]; ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hux, rfl | rfl⟩
      · exact absurd rfl (G.ne_of_adj hux)
      · rfl
    · rintro rfl; exact ⟨h, Or.inr rfl⟩
  · rw [if_neg h]; ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro hux (rfl | rfl)
    · exact absurd rfl (G.ne_of_adj hux)
    · exact h hux

private lemma nbr_inter_pair_right (u v : V) :
    G.neighborFinset v ∩ ({u, v} : Finset V) = if G.Adj u v then ({u} : Finset V) else ∅ := by
  by_cases h : G.Adj u v
  · rw [if_pos h]; ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hvx, rfl | rfl⟩
      · rfl
      · exact absurd rfl (G.ne_of_adj hvx)
    · rintro rfl; exact ⟨G.symm h, Or.inl rfl⟩
  · rw [if_neg h]; ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro hvx (rfl | rfl)
    · exact h (G.symm hvx)
    · exact absurd rfl (G.ne_of_adj hvx)

/-- **The crossing-count defect** — the state's `defect` field, PROVEN for the genuine edge-crossing
count of any finite graph.  Partitions each neighbor set at `{u,v}` (no subtraction). -/
theorem crossingCard_pair_defect (u v : V) (huv : u ≠ v) :
    crossingCard G ({u} : Finset V) + crossingCard G ({v} : Finset V)
      = crossingCard G ({u, v} : Finset V) + 2 * (if G.Adj u v then 1 else 0) := by
  have hcp : crossingCard G ({u, v} : Finset V)
      = (G.neighborFinset u \ ({u, v} : Finset V)).card
        + (G.neighborFinset v \ ({u, v} : Finset V)).card := by
    unfold crossingCard; rw [Finset.sum_pair huv]
  have hIu : (G.neighborFinset u ∩ ({u, v} : Finset V)).card = (if G.Adj u v then 1 else 0) := by
    rw [nbr_inter_pair_left u v]; by_cases h : G.Adj u v <;> simp [h]
  have hIv : (G.neighborFinset v ∩ ({u, v} : Finset V)).card = (if G.Adj u v then 1 else 0) := by
    rw [nbr_inter_pair_right u v]; by_cases h : G.Adj u v <;> simp [h]
  calc crossingCard G ({u} : Finset V) + crossingCard G ({v} : Finset V)
      = (G.neighborFinset u).card + (G.neighborFinset v).card := by
        rw [crossingCard_singleton, crossingCard_singleton]
    _ = ((G.neighborFinset u \ ({u, v} : Finset V)).card
          + (G.neighborFinset u ∩ ({u, v} : Finset V)).card)
        + ((G.neighborFinset v \ ({u, v} : Finset V)).card
          + (G.neighborFinset v ∩ ({u, v} : Finset V)).card) := by
        rw [← Finset.card_sdiff_add_card_inter (G.neighborFinset u) ({u, v} : Finset V),
          ← Finset.card_sdiff_add_card_inter (G.neighborFinset v) ({u, v} : Finset V)]
    _ = ((G.neighborFinset u \ ({u, v} : Finset V)).card + (if G.Adj u v then 1 else 0))
        + ((G.neighborFinset v \ ({u, v} : Finset V)).card + (if G.Adj u v then 1 else 0)) := by
        rw [hIu, hIv]
    _ = crossingCard G ({u, v} : Finset V) + 2 * (if G.Adj u v then 1 else 0) := by
        rw [hcp]; ring

/-- **The explicit cut-rank profile of a graph** — bond dimension `q`, boundary = the genuine
edge-crossing count, defect PROVEN (`crossingCard_pair_defect`).  No carried profile hypothesis. -/
def explicitProfile (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq : 2 ≤ q) :
    CutRankProfile G where
  q := q
  hq := hq
  boundary := crossingCard G
  defect := crossingCard_pair_defect

/-- **M3 — the crossing-count area functional of a REAL graph decodes back to the graph.**  For the
explicit profile (edge-crossing boundary, defect proven), `rankMIGraph = G` — geometry-from-state is
non-vacuous: the cut-rank of an actual graph recovers that graph. -/
theorem explicitProfile_rankMIGraph_eq (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ} (hq : 2 ≤ q) :
    rankMIGraph (explicitProfile G hq) = G :=
  rankMIGraph_eq (explicitProfile G hq)

/-- **M3 capstone — a real graph's crossing-count cut-rank OUTPUTS its geodesic metric.**  For a
connected graph, the metric decoded from the explicit (edge-crossing) cut-rank profile is a genuine
finite metric equal to `G.dist`. -/
theorem explicitProfile_decodedDist_isFiniteMetric (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 2 ≤ q) (hconn : G.Connected) :
    IsFiniteMetric (decodedDist (explicitProfile G hq)) :=
  decodedDist_isFiniteMetric (explicitProfile G hq) hconn

/-! ## M5 — the AREA is a property of the CUT (region-complement symmetric)

The entanglement "area" `crossingCard G A` of a region equals that of its complement:
`crossingCard G A = crossingCard G Aᶜ`.  The cut `A | Aᶜ` — not the region — carries the area, exactly
as a Ryu–Takayanagi surface is shared by both sides.  Proven by double-counting the crossing edges
(`∑_{v∈A}∑_{w∈Aᶜ}[v∼w]`, symmetric under `Finset.sum_comm` + `G.adj_comm`).  HONEST: this is the
cut-symmetry of the area — NOT the (false-in-general) claim `area = graph min-cut`, which needs
RT-saturation; and the capacity BOUND `records ≤ q^area` genuinely needs the quantum flattening map
(M3b), not present here. -/
theorem crossingCard_symm (A : Finset V) : crossingCard G A = crossingCard G Aᶜ := by
  have hstep : ∀ B : Finset V,
      crossingCard G B = ∑ v ∈ B, ∑ w ∈ Bᶜ, (if G.Adj v w then 1 else 0) := by
    intro B
    unfold crossingCard
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hset : G.neighborFinset v \ B = Bᶜ.filter (fun w => G.Adj v w) := by
      ext w
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
        Finset.mem_compl]
      tauto
    rw [hset, Finset.card_filter]
  rw [hstep A, hstep Aᶜ, compl_compl, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  by_cases h : G.Adj y x
  · simp [h, (G.adj_comm y x).mp h]
  · have h' : ¬ G.Adj x y := fun hc => h ((G.adj_comm x y).mp hc)
    simp [h, h']

end QIQTH.MetricFromState
