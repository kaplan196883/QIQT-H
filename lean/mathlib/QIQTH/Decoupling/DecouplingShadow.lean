/-
  THE DECOUPLING SHADOW DS7 (THE_DECOUPLING_SHADOW_PLAN.md, DS1–DS7 COMPLETE) — the shadow
  package: the finite forced core of the dictionary.

  THE PARENT TOWER (one object, two surviving descriptions — the honest finite shadow of the
  Maldacena decoupling structure): the finite truncated code corner with its oscillators and
  records, carrying a refinement-natural area valuation. THE THREE THEOREMS:
  1. the free-oscillator sector SURVIVES the cutoff limit (operator level: the CCR stabilize at
     bounded occupations; state level: the thermal data converge to the Planck values);
  2. the refinement-natural area valuation IS `κ·Σ log D_k` (THE FORCED WEIGHT — the dictionary's
     local weight is rigid, no longer a constructed choice);
  3. given the normalization (the κ slot — where `4G` lives, input), the SATURATED area law
     survives: the code's β = 0 entropy equals the forced area over κ.

  DS7 CHECKPOINT — the two honest sentences (verbatim from the plan):

  HAVE: "The capacity-limit theorem forces the oscillator/free-field sector only in the
  bounded-occupation or positive-temperature sense; it does not force the screen geometry or
  Newton constant."

  HAVE NOT: "The tower-rigidity theorem forces the logarithmic capacity weight only under
  monoidal, monotone refinement naturality; without those hypotheses there are explicit finite
  counterexamples."

  ⚠ NOT quantum gravity solved; no wall crossed; NOT a full decoupling derivation — the join
  incidence geometry, the species/cell match, and the value of G remain parent data.
-/
import Mathlib
import QIQTH.Decoupling.TruncatedCCR
import QIQTH.Decoupling.ProductModes
import QIQTH.Rigidity.FiniteCornerValuation
import QIQTH.Dynamics

namespace QIQTH.Decoupling

open Filter QIQTH.Keystone
open scoped Matrix

/-- **The refinement-natural area valuation** — the tower's area assignment: monoidal under
    tensor product, monotone under ALL isometric embeddings (the STRONG hypotheses; the ν₂
    counterexample shows weaker refinement does not force the weight). -/
structure RefinementNaturalValuation where
  /-- the valuation on finite dimensions -/
  A : ℕ → ℝ
  /-- monoidal: additive under tensor product -/
  monoidal : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → A (m * n) = A m + A n
  /-- monotone under all isometric embeddings -/
  embed_monotone : ∀ m n : ℕ, 1 ≤ m → m ≤ n → A m ≤ A n

/-- **Package theorem 2 — THE FORCED WEIGHT**: every refinement-natural valuation is
    `κ·Σ log D_k` on product record corners. -/
theorem RefinementNaturalValuation.forced (V : RefinementNaturalValuation)
    {E : Type*} (L : LinkDims E) (C : Finset E) :
    ∃ κ : ℝ, 0 ≤ κ ∧ V.A (∏ k ∈ C, L.D k) = κ * ∑ k ∈ C, Real.log (L.D k) :=
  QIQTH.Rigidity.forced_weight_product V.A V.monoidal V.embed_monotone L C

/-- **Package theorem 1 — the free sector survives the cutoff limit** (the DS1–DS4 evidence
    bundled as one `Prop`; every field is a landed theorem — see `decouplingShadow_holds`). -/
structure FreeSectorEvidence : Prop where
  /-- operator level: the truncated CCR stabilize to the exact values at bounded occupations -/
  ccr_stabilizes : ∀ m n : ℕ, ∀ᶠ D in atTop,
    ∃ (hm : m + 1 < D) (hn : n + 1 < D),
      (QIQTH.CornerConstruction.lowering D * (QIQTH.CornerConstruction.lowering D)ᴴ
          - (QIQTH.CornerConstruction.lowering D)ᴴ * QIQTH.CornerConstruction.lowering D)
          ⟨m, Nat.lt_of_succ_lt hm⟩ ⟨n, Nat.lt_of_succ_lt hn⟩
        = if m = n then 1 else 0
  /-- state level: the occupation expectation converges to the Planck value -/
  planck_occupation : ∀ q : ℝ, 0 ≤ q → q < 1 →
    Tendsto (fun D : ℕ => meanN D q) atTop (nhds (q / (1 - q)))
  /-- state level: the truncation-defect expectation dies at fixed positive temperature -/
  defect_dies : ∀ q : ℝ, 0 ≤ q → q < 1 →
    Tendsto (fun D : ℕ => defectExpect D q) atTop (nhds 0)
  /-- entropy level: the truncated entropy converges to the Planck entropy -/
  entropy_planck : ∀ x : ℝ, 0 < x →
    Tendsto (fun D : ℕ => thermalEntropy D x) atTop
      (nhds (-Real.log (1 - Real.exp (-x))
        + x * (Real.exp (-x) / (1 - Real.exp (-x)))))
  /-- THE GUARD: along saturating schedules the defect expectation tends to 1, not 0 -/
  guard : ∀ x : ℕ → ℝ, (∀ D, 0 ≤ x D) →
    Tendsto (fun D : ℕ => x D * D) atTop (nhds 0) →
    Tendsto (fun D : ℕ => defectExpect D (Real.exp (-(x D)))) atTop (nhds 1)

/-- **The free-sector evidence HOLDS** — every field is a landed DS theorem. -/
theorem decouplingShadow_holds : FreeSectorEvidence where
  ccr_stabilizes := commutator_eventually_exact
  planck_occupation := fun _ h0 h1 => tendsto_meanN h0 h1
  defect_dies := fun _ h0 h1 => tendsto_defectExpect h0 h1
  entropy_planck := fun _ hx => tendsto_thermalEntropy_planck hx
  guard := guard_defect_survives

/-- **Package theorem 3 — the SATURATED area law survives** (conditional on the normalization —
    the κ slot is where `4G` lives, and stays input): the code's β = 0 region entropy equals the
    FORCED area over κ. -/
theorem saturated_entropy_eq_forced_area {M : Type*} [DecidableEq M]
    (L : LinkDims M) (ω : M → ℝ) (Rg : Finset M)
    (V : RefinementNaturalValuation) {κ : ℝ} (hκpos : 0 < κ)
    (hforced : V.A (∏ k ∈ Rg, L.D k) = κ * ∑ k ∈ Rg, Real.log (L.D k)) :
    QIQTH.Dynamics.Smicro L ω Rg 0 = V.A (∏ k ∈ Rg, L.D k) / κ := by
  rw [QIQTH.Dynamics.Smicro_zero, hforced]
  field_simp

end QIQTH.Decoupling
