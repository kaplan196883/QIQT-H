/-
  E3 (MICROTHEORY_EARNS_GRAVITY_PLAN.md) — `calibrated_entanglement_cut_area_law` (the wEnt formulation).

  The Strominger-shape join, in-model: the microstate COUNT and the geometric AREA as two computations that
  agree. The screen's links carry ENTANGLEMENT weights `wEnt` (Track C cut data — the same `cut` of
  `EmergentSpacetime`); the area is *INDUCED* from them, `screenArea := 4G·cut(wEnt,S)` — there is NO separate
  `areaWt` label anywhere. Under the local calibration `log D_e = wEnt e` (an EXPLICIT carried hypothesis — the
  physics), the microstate count obeys the area law with the right coefficient:
      log #microstates = screenArea / (4G),
  and the maximum-entropy (uniform) state REALIZES the count (`shannon_uniform_eq_log_card` — Jacobson's local
  equilibrium regime). The cut-indexing lemma (`screen_cut_eq`, verifier-required) pins the screen sum to Track
  C's directed cut with no double counting.

  ⚠ Honest labels (verifier-binding): genuine formal progress — ONE weight family does both jobs (capacity and
  geometry), the separate area label is deleted — but NOT a derivation of area from entanglement: the calibration
  `log D_e = wEnt e` carries the physical content (deleting it = the continuum trace + background independence,
  out of scope). The no-calibration guard stays in force: without it the count is unbounded at fixed area
  (`ScreenCode.codeCap_unbounded_at_fixed_area`). Finite/model level; `G > 0` required.
-/
import Mathlib
import QIQTH.EmergentSpacetime
import QIQTH.HolographicScreenCode
import QIQTH.RecordContract

namespace QIQTH.EarnGravity

open QIQTH.EmergentSpacetime

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The canonical two-layer screen graph: each link `i` crosses from `(i, true)` (inside) to `(i, false)`
    (outside) carrying its entanglement weight; nothing else crosses. -/
def screenW (links : Finset ι) (wEnt : ι → ℝ) : ι × Bool → ι × Bool → ℝ :=
  fun p q => if p.1 = q.1 ∧ p.1 ∈ links ∧ p.2 = true ∧ q.2 = false then wEnt p.1 else 0

/-- The inside region: the `true` layer. -/
def screenS : Finset (ι × Bool) := Finset.univ.filter (fun p => p.2 = true)

/-- **The cut-indexing lemma** (verifier-required; no double counting): Track C's directed cut of the canonical
    screen graph equals the plain link sum of the entanglement weights. -/
theorem screen_cut_eq (links : Finset ι) (wEnt : ι → ℝ) :
    cut (screenW links wEnt) (screenS (ι := ι)) = ∑ e ∈ links, wEnt e := by
  unfold cut screenS screenW
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, if_true, if_false, ite_self]
  have hinner : ∀ i : ι, (∑ q ∈ Finset.univ.filter (fun p : ι × Bool => p.2 = false),
      if i = q.1 ∧ i ∈ links ∧ q.2 = false then wEnt i else 0)
      = if i ∈ links then wEnt i else 0 := by
    intro i
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    by_cases hi : i ∈ links
    · simp [hi, Finset.sum_ite_eq, Finset.mem_univ]
    · simp [hi]
  simp [hinner, Finset.sum_ite_mem]
/-- The screen's microstate space: one `Fin (D e)` record fiber per link. -/
abbrev Microstates (links : Finset ι) (D : ι → ℕ) : Type _ := ∀ e : links, Fin (D e.val)

/-- The microstate count is the product of the link dimensions. -/
theorem card_microstates (links : Finset ι) (D : ι → ℕ) :
    Fintype.card (Microstates links D) = ∏ e ∈ links, D e := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact Finset.prod_coe_sort links D

/-- **The induced screen area** — DEFINED from the calibrated entanglement cut (no separate area label):
    `screenArea := 4G · cut(wEnt, S)`. -/
noncomputable def inducedScreenArea (G : ℝ) (links : Finset ι) (wEnt : ι → ℝ) : ℝ :=
  4 * G * cut (screenW links wEnt) (screenS (ι := ι))

/-- **E3 CAPSTONE — `calibrated_entanglement_cut_area_law`.** Under the local calibration `log D_e = wEnt e`
    (carried), the microstate count obeys the area law with the area INDUCED from the entanglement cut:
    `log #microstates = screenArea/(4G)`. Count and geometry: two computations, one calibrated weight family. -/
theorem calibrated_entanglement_cut_area_law (G : ℝ) (hG : 0 < G) (links : Finset ι)
    (wEnt : ι → ℝ) (D : ι → ℕ) (hD : ∀ e ∈ links, 0 < D e)
    (hcal : ∀ e ∈ links, Real.log (D e) = wEnt e) :
    Real.log (Fintype.card (Microstates links D)) = inducedScreenArea G links wEnt / (4 * G) := by
  have h4G : (4 : ℝ) * G ≠ 0 := by positivity
  have hlog : Real.log (∏ e ∈ links, (D e : ℝ)) = ∑ e ∈ links, Real.log (D e) :=
    Real.log_prod (fun e he => by exact_mod_cast (hD e he).ne')
  rw [card_microstates, inducedScreenArea, screen_cut_eq,
    mul_div_cancel_left₀ _ h4G, Nat.cast_prod, hlog]
  exact Finset.sum_congr rfl hcal

/-- **The uniform (maximum-entropy) state REALIZES the count** — Jacobson's local-equilibrium regime: the
    uniform record's Shannon entropy equals `screenArea/(4G)` exactly (`shannon_uniform_eq_log_card`). -/
theorem uniform_realizes_area_law (G : ℝ) (hG : 0 < G) (links : Finset ι)
    (wEnt : ι → ℝ) (D : ι → ℕ) (hD : ∀ e ∈ links, 0 < D e)
    (hcal : ∀ e ∈ links, Real.log (D e) = wEnt e) :
    haveI : Nonempty (Microstates links D) := ⟨fun e => ⟨0, hD e e.2⟩⟩
    QIQTH.BranchLedger.Shannon Finset.univ
        (fun _ : Microstates links D => (Fintype.card (Microstates links D) : ℝ)⁻¹)
      = inducedScreenArea G links wEnt / (4 * G) := by
  haveI : Nonempty (Microstates links D) := ⟨fun e => ⟨0, hD e e.2⟩⟩
  rw [QIQTH.RecordContract.shannon_uniform_eq_log_card]
  exact calibrated_entanglement_cut_area_law G hG links wEnt D hD hcal

end QIQTH.EarnGravity
