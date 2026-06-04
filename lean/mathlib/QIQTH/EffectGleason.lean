/-
# QIQT-H: finite-dimensional Effect (POVM) Gleason — Stage 1 / step G1

Target (`GLEASON_SCOPE.md`): the Busch / Caves–Fuchs–Manne–Renes finite-dimensional
effect-Gleason theorem — a normalized, nonnegative, (coexistent-)additive functional on
effects `0 ≤ E ≤ 1` is `μ E = tr(ρ E)` for a unique density matrix `ρ`.  This discharges
the finite-dim case of `TypicalityMackeyGleason.mackey_gleason_to_trace_density`, makes the
`GoldsteinStruyveFinDim` Born-uniqueness axioms retirable, and completes the Stage-1
"minimal breakthrough" of `PRIZE_ROADMAP.md` by discharging the `hsupp` hypothesis of
`GleasonSelector.born_is_forced` from first principles.

This installment lands **step G1's foundation**: the effect predicate, effect closure
(`0`, `1`, scaling, subtraction), `μ 0 = 0`, **monotonicity**, and the
scaling-additivity that drives the homogeneity argument.  The remaining G1 core (additive +
bounded ⇒ ℝ-homogeneous, via the Cauchy-on-`[0,1]` squeeze) and steps G2–G4 follow.

Axiom-free (standard three only). -/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace QIQTH.EffectGleason

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-- An **effect** is a positive-semidefinite matrix `E` with `1 - E` also PSD, i.e.
    `0 ≤ E ≤ 1` in the Löwner order — the yes-part of a POVM. -/
def IsEffect (E : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

theorem isEffect_zero : IsEffect (0 : Matrix (Fin d) (Fin d) ℂ) :=
  ⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one⟩

theorem isEffect_one : IsEffect (1 : Matrix (Fin d) (Fin d) ℂ) :=
  ⟨Matrix.PosSemidef.one, by simpa using Matrix.PosSemidef.zero⟩

/-- Effects are closed under scaling by `t ∈ [0,1]`:  `1 - t•E = (1-t)•1 + t•(1-E)` is a
    sum of PSD matrices. -/
theorem isEffect_smul {E : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : IsEffect (t • E) := by
  refine ⟨hE.1.smul h0, ?_⟩
  have hsplit : (1 : Matrix (Fin d) (Fin d) ℂ) - t • E
      = (1 - t) • (1 : Matrix (Fin d) (Fin d) ℂ) + t • (1 - E) := by
    rw [smul_sub]; module
  rw [hsplit]
  exact (Matrix.PosSemidef.one.smul (by linarith : (0:ℝ) ≤ 1 - t)).add (hE.2.smul h0)

/-- If `E ≤ F` (i.e. `F - E` is PSD) with both effects, then `F - E` is an effect:
    `1 - (F - E) = (1 - F) + E` is PSD. -/
theorem isEffect_sub {E F : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) (hF : IsEffect F)
    (hle : (F - E).PosSemidef) : IsEffect (F - E) := by
  refine ⟨hle, ?_⟩
  have : (1 : Matrix (Fin d) (Fin d) ℂ) - (F - E) = (1 - F) + E := by abel
  rw [this]
  exact hF.2.add hE.1

/-- **Cauchy on the unit interval (the homogeneity core).**  A function `g : ℝ → ℝ` that
    is additive and monotone on `[0,1]` (with `g 0 = 0`) is linear there: `g t = t · g 1`.
    Proof: induction gives `g(k/n) = (k/n)·g 1` (rational homogeneity); the `⌊t·n⌋` squeeze
    plus monotonicity then forces `|g t − t·g 1| ≤ g 1 / n` for all `n`, hence `= 0`.
    This is the elementary heart of effect-Gleason — additive + bounded ⇒ ℝ-homogeneous. -/
theorem cauchy_unit_interval (g : ℝ → ℝ) (h0 : g 0 = 0)
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 → g (a + b) = g a + g b)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → g a ≤ g b) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → g t = t * g 1 := by
  have hg1 : 0 ≤ g 1 := by have := hmono 0 1 le_rfl zero_le_one le_rfl; rwa [h0] at this
  -- rational homogeneity: g(j/N) = j · g(1/N) for j ≤ N
  have hstep : ∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, j ≤ N → g ((j : ℝ) / N) = (j : ℝ) * g (1 / N) := by
    intro N hN
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ k ih =>
        intro hk
        have hkN : k ≤ N := Nat.le_of_succ_le hk
        have e : ((k + 1 : ℕ) : ℝ) / N = (k : ℝ) / N + 1 / N := by push_cast; ring
        have hle1 : (k : ℝ) / N + 1 / N ≤ 1 := by
          rw [← e, div_le_one hN0]; exact_mod_cast hk
        rw [e, hadd ((k:ℝ)/N) (1/N) (by positivity) (by positivity) hle1, ih hkN,
          Nat.cast_succ]
        ring
  -- g(1/N) = g 1 / N
  have hinv : ∀ N : ℕ, 1 ≤ N → g (1 / N) = g 1 / N := by
    intro N hN
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    have h := hstep N hN N le_rfl
    rw [show ((N:ℝ)/N) = 1 by field_simp] at h
    rw [eq_div_iff (ne_of_gt hN0)]; linarith [h]
  -- rational homogeneity in final form: g(k/N) = (k/N)·g 1
  have hrat : ∀ N : ℕ, 1 ≤ N → ∀ k : ℕ, k ≤ N → g ((k:ℝ)/N) = ((k:ℝ)/N) * g 1 := by
    intro N hN k hk
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    rw [hstep N hN k hk, hinv N hN]; field_simp
  intro t ht0 ht1
  rcases eq_or_lt_of_le ht1 with rfl | htlt
  · rw [one_mul]
  · -- per-n squeeze bound
    have hbound : ∀ n : ℕ, 1 ≤ n → |g t - t * g 1| ≤ g 1 / n := by
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn
      set k := ⌊t * n⌋₊ with hkdef
      have htn0 : 0 ≤ t * n := by positivity
      have hk_le : (k : ℝ) ≤ t * n := Nat.floor_le htn0
      have hlt_k1 : t * n < k + 1 := Nat.lt_floor_add_one _
      have hk_lt_n : k < n := by rw [hkdef, Nat.floor_lt htn0]; nlinarith [htlt, hn0]
      have hk1n : k + 1 ≤ n := hk_lt_n
      have hkn : (k : ℝ) / n ≤ t := by rw [div_le_iff₀ hn0]; linarith [hk_le]
      have htk1 : t ≤ ((k:ℝ) + 1) / n := by rw [le_div_iff₀ hn0]; linarith [hlt_k1]
      have hkn0 : 0 ≤ (k:ℝ)/n := by positivity
      have hk1n1 : ((k:ℝ) + 1) / n ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hk1n
      -- bracket g t
      have hlo : ((k:ℝ)/n) * g 1 ≤ g t := by
        have := hmono ((k:ℝ)/n) t hkn0 hkn ht1
        rwa [hrat n hn k (le_of_lt hk_lt_n)] at this
      have hcast : (((k:ℝ)+1)/n) = ((k+1:ℕ):ℝ)/n := by push_cast; ring
      have hhi : g t ≤ (((k:ℝ)+1)/n) * g 1 := by
        have h := hmono t (((k:ℝ)+1)/n) ht0 htk1 hk1n1
        rw [hcast, hrat n hn (k+1) hk1n] at h
        rw [hcast]; exact h
      -- bracket t * g 1
      have htlo : ((k:ℝ)/n) * g 1 ≤ t * g 1 := by
        apply mul_le_mul_of_nonneg_right hkn hg1
      have hthi : t * g 1 ≤ (((k:ℝ)+1)/n) * g 1 := by
        apply mul_le_mul_of_nonneg_right htk1 hg1
      -- width of the bracket is g1/n
      have hwidth : (((k:ℝ)+1)/n) * g 1 - ((k:ℝ)/n) * g 1 = g 1 / n := by
        field_simp; ring
      rw [abs_le]; constructor <;> [nlinarith [hlo, hthi, hwidth]; nlinarith [hhi, htlo, hwidth]]
    -- |x| ≤ g1/n for all n ⇒ x = 0
    by_contra hne
    have hx : 0 < |g t - t * g 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (g 1 / |g t - t * g 1|)
    have hge0 : 0 ≤ g 1 / |g t - t * g 1| := by positivity
    have hn0 : (0:ℝ) < n := lt_of_le_of_lt hge0 hn
    have hn1 : 1 ≤ n := by
      have : 0 < n := by exact_mod_cast hn0
      omega
    have hb := hbound n hn1
    rw [div_lt_iff₀ hx] at hn
    rw [le_div_iff₀ hn0] at hb
    nlinarith [hb, hn]

/-- A **finite effect measure** (generalized probability measure on effects): normalized,
    nonnegative, and additive on coexistent effects.  This is the hypothesis of
    effect-Gleason; the theorem (future installments) is that `μ E = tr(ρ E)`. -/
structure EffectMeasure (d : ℕ) where
  μ : Matrix (Fin d) (Fin d) ℂ → ℝ
  normalized : μ 1 = 1
  nonneg : ∀ E, IsEffect E → 0 ≤ μ E
  additive : ∀ E F, IsEffect E → IsEffect F → IsEffect (E + F) → μ (E + F) = μ E + μ F

namespace EffectMeasure

variable (m : EffectMeasure d)

/-- `μ 0 = 0` — from `μ 1 = μ(1 + 0) = μ 1 + μ 0`. -/
theorem map_zero : m.μ 0 = 0 := by
  have h := m.additive 1 0 isEffect_one isEffect_zero (by rw [add_zero]; exact isEffect_one)
  rw [add_zero] at h
  have := m.normalized
  linarith

/-- **Monotonicity.**  If `E ≤ F` (`F - E` PSD) with both effects, then `μ E ≤ μ F`.
    From `μ F = μ E + μ(F - E)` and `μ(F - E) ≥ 0`. -/
theorem mono {E F : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) (hF : IsEffect F)
    (hle : (F - E).PosSemidef) : m.μ E ≤ m.μ F := by
  have hsub : IsEffect (F - E) := isEffect_sub hE hF hle
  have hEF : E + (F - E) = F := by abel
  have hadd := m.additive E (F - E) hE hsub (by rw [hEF]; exact hF)
  rw [hEF] at hadd
  have := m.nonneg (F - E) hsub
  linarith

/-- **Scaling additivity.**  For `s, s' ≥ 0` with `s•E`, `s'•E`, `(s+s')•E` all effects,
    `μ((s+s')•E) = μ(s•E) + μ(s'•E)`.  The seed of the homogeneity argument: the map
    `s ↦ μ(s•E)` is additive on `[0,1]` (next: Cauchy ⇒ `μ(s•E) = s·μ E`). -/
theorem map_smul_add {E : Matrix (Fin d) (Fin d) ℂ} {s s' : ℝ}
    (hsE : IsEffect (s • E)) (hs'E : IsEffect (s' • E)) (hsum : IsEffect ((s + s') • E)) :
    m.μ ((s + s') • E) = m.μ (s • E) + m.μ (s' • E) := by
  have hsplit : (s + s') • E = s • E + s' • E := by module
  rw [hsplit] at hsum ⊢
  exact m.additive (s • E) (s' • E) hsE hs'E hsum

/-- **G1 — ℝ-homogeneity (the load-bearing core).**  For an effect `E` and `t ∈ [0,1]`,
    `μ(t • E) = t · μ E`.  Apply `cauchy_unit_interval` to `g s := μ(s • E)`: additivity is
    `map_smul_add`, monotonicity is `mono` (since `(b-a)•E ⪰ 0`), `g 0 = μ 0 = 0`, and
    `g 1 = μ E`.  This is "additive + bounded ⇒ ℝ-homogeneous" — the elementary effect
    (Busch) Gleason step that the original projection Gleason needs spherical harmonics for. -/
theorem map_smul {E : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : m.μ (t • E) = t * m.μ E := by
  have key := cauchy_unit_interval (fun s => m.μ (s • E)) ?_ ?_ ?_ t h0 h1
  · simpa only [one_smul] using key
  · -- g 0 = μ 0 = 0
    simp only [zero_smul]; exact m.map_zero
  · -- additivity on [0,1]
    intro a b ha hb hab
    have haE : IsEffect (a • E) := isEffect_smul hE ha (by linarith)
    have hbE : IsEffect (b • E) := isEffect_smul hE hb (by linarith)
    have habE : IsEffect ((a + b) • E) := isEffect_smul hE (by linarith) hab
    exact m.map_smul_add haE hbE habE
  · -- monotonicity on [0,1]
    intro a b ha hab hb1
    have haE : IsEffect (a • E) := isEffect_smul hE ha (le_trans hab hb1)
    have hbE : IsEffect (b • E) := isEffect_smul hE (le_trans ha hab) hb1
    have hpsd : ((b • E) - (a • E)).PosSemidef := by
      have : (b • E) - (a • E) = (b - a) • E := by module
      rw [this]; exact hE.1.smul (by linarith)
    exact m.mono haE hbE hpsd

end EffectMeasure

end QIQTH.EffectGleason
