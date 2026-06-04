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

/-- The quadratic form `⟨x, H x⟩` of a Hermitian matrix is **real** (`im = 0`):
    `star(⟪x,Hx⟫) = ⟪x,Hx⟫` since `Hᴴ = H`. -/
theorem quadForm_im_zero {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← Complex.star_def]
  conv_lhs => rw [Matrix.star_dotProduct, star_star]
  rw [Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

/-- **Löwner-order bound for Hermitian matrices (G2 — absent from Mathlib).**  Every
    Hermitian `A` satisfies `A ⪯ c·1` with `c = ∑ᵢⱼ‖Aᵢⱼ‖`, i.e. `c•1 − A` is PSD.  Proved
    elementarily (no spectral theorem): for Hermitian `A` the quadratic form `⟨x,Ax⟩` is real
    (`quadForm_im_zero`) and `|⟨x,Ax⟩| ≤ (∑‖Aᵢⱼ‖)·∑‖xₖ‖²` via the triangle inequality and
    `‖xᵢ‖‖xⱼ‖ ≤ ∑‖x_k‖²`.  (PSD is the special case `posSemidef_sumNorm_sub` below.) -/
theorem posSemidef_sumNorm_sub_herm {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    (((∑ i, ∑ j, ‖A i j‖ : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef := by
  classical
  set c : ℝ := ∑ i, ∑ j, ‖A i j‖ with hc
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · -- IsHermitian
    show ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A)ᴴ
        = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hA]
    simp [Complex.conj_ofReal]
  · intro x
    have hexp : star x ⬝ᵥ (((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A) *ᵥ x)
        = (c : ℂ) * (star x ⬝ᵥ x) - star x ⬝ᵥ (A *ᵥ x) := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hexp]
    have hQre : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
      rw [dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
        Complex.sq_norm]
    have hQim : (star x ⬝ᵥ x).im = 0 := by
      have h := (Complex.le_def.mp (dotProduct_star_self_nonneg x)).2; simpa using h.symm
    have hRim : (star x ⬝ᵥ (A *ᵥ x)).im = 0 := quadForm_im_zero hA x
    have hRexp : star x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, star (x i) * (A i j * x j) := by
      simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    have hRre : (star x ⬝ᵥ (A *ᵥ x)).re ≤ c * (star x ⬝ᵥ x).re := by
      have hnorm : ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ c * (star x ⬝ᵥ x).re := by
        rw [hRexp, hQre, hc, Finset.sum_mul]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
        rw [Finset.sum_mul]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
        rw [norm_mul, norm_mul, norm_star]
        have hxij : ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖ ^ 2 := by
          have hi : ‖x i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
            Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity)
              (Finset.mem_univ i)
          have hj : ‖x j‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
            Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity)
              (Finset.mem_univ j)
          nlinarith [hi, hj, sq_nonneg (‖x i‖ - ‖x j‖), norm_nonneg (x i), norm_nonneg (x j)]
        calc ‖x i‖ * (‖A i j‖ * ‖x j‖) = ‖A i j‖ * (‖x i‖ * ‖x j‖) := by ring
          _ ≤ ‖A i j‖ * ∑ k, ‖x k‖ ^ 2 := mul_le_mul_of_nonneg_left hxij (norm_nonneg (A i j))
      exact le_trans (Complex.re_le_norm _) hnorm
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re, zero_mul, sub_zero]
      linarith [hRre]
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_im, zero_mul, add_zero]
      rw [hQim, hRim]; ring

/-- PSD special case of the Löwner-order bound: `A ⪯ (∑‖Aᵢⱼ‖)·1`. -/
theorem posSemidef_sumNorm_sub {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    (((∑ i, ∑ j, ‖A i j‖ : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef :=
  posSemidef_sumNorm_sub_herm hA.1

/-- Lower Löwner bound: for Hermitian `A`, `(∑‖Aᵢⱼ‖)·1 + A` is PSD (apply the upper bound
    to `−A`).  Gives `−c·1 ⪯ A`, the lower half of the two-sided bound. -/
theorem posSemidef_sumNorm_add_herm {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    (((∑ i, ∑ j, ‖A i j‖ : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + A).PosSemidef := by
  have hthis := posSemidef_sumNorm_sub_herm hA.neg
  rw [show (∑ i, ∑ j, ‖(-A) i j‖) = ∑ i, ∑ j, ‖A i j‖ by simp [Matrix.neg_apply],
    sub_neg_eq_add] at hthis
  exact hthis

/-- Existential form of the PSD Löwner-order bound (`A ⪯ c•1` for some `c ≥ 0`). -/
theorem exists_smul_one_sub_posSemidef {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef :=
  ⟨_, by positivity, posSemidef_sumNorm_sub hA⟩

/-- Real-smul equals complex-smul on a ℂ-matrix: `t • M = (↑t) • M`.  (Bridges the
    `ℝ`-scaling used by `map_smul`/`isEffect_smul` and the `ℂ`-scaling in the PSD bound.) -/
theorem coe_smul (t : ℝ) (M : Matrix (Fin d) (Fin d) ℂ) : t • M = (↑t : ℂ) • M := by
  ext i j; simp [Matrix.smul_apply, Complex.real_smul]

/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_smul {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (t : ℝ) :
    (t • H).IsHermitian := by
  rw [coe_smul]
  show ((↑t : ℂ) • H)ᴴ = (↑t : ℂ) • H
  rw [conjTranspose_smul, hH, Complex.star_def, Complex.conj_ofReal]

/-- Hermitian "real part" of a matrix: `(M + Mᴴ)/2`. -/
noncomputable def reHerm (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((2⁻¹ : ℝ) : ℂ) • (M + Mᴴ)

/-- Hermitian "imaginary part": `(M − Mᴴ)/(2i) = (−i/2)(M − Mᴴ)`. -/
noncomputable def imHerm (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (((2⁻¹ : ℝ) : ℂ) * (-Complex.I)) • (M - Mᴴ)

theorem reHerm_isHermitian (M : Matrix (Fin d) (Fin d) ℂ) : (reHerm M).IsHermitian := by
  show (reHerm M)ᴴ = reHerm M
  rw [reHerm, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, add_comm Mᴴ M]

theorem imHerm_isHermitian (M : Matrix (Fin d) (Fin d) ℂ) : (imHerm M).IsHermitian := by
  show (imHerm M)ᴴ = imHerm M
  rw [imHerm, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
    show star (((2⁻¹ : ℝ) : ℂ) * (-Complex.I)) = ((2⁻¹ : ℝ) : ℂ) * Complex.I by
      simp [Complex.star_def, Complex.conj_ofReal]]
  rw [show (Mᴴ - M) = -(M - Mᴴ) by abel, smul_neg, ← neg_smul]
  congr 1; ring

/-- `reHerm(i•M) = −imHerm M`. -/
theorem reHerm_I (M : Matrix (Fin d) (Fin d) ℂ) :
    reHerm (Complex.I • M) = -imHerm M := by
  have hconj : (Complex.I • M)ᴴ = (-Complex.I) • Mᴴ := by
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [reHerm, imHerm, hconj]
  match_scalars <;> (push_cast; ring)

/-- `imHerm(i•M) = reHerm M`. -/
theorem imHerm_I (M : Matrix (Fin d) (Fin d) ℂ) :
    imHerm (Complex.I • M) = reHerm M := by
  have hconj : (Complex.I • M)ᴴ = (-Complex.I) • Mᴴ := by
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [imHerm, reHerm]
  rw [hconj, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul]
  congr 1
  rw [mul_assoc, neg_mul, Complex.I_mul_I]; ring

/-- `M = reHerm M + i·imHerm M`. -/
theorem hermDecomp (M : Matrix (Fin d) (Fin d) ℂ) :
    reHerm M + Complex.I • imHerm M = M := by
  rw [reHerm, imHerm, smul_smul,
    show Complex.I * (((2⁻¹ : ℝ) : ℂ) * (-Complex.I)) = ((2⁻¹ : ℝ) : ℂ) by
      rw [mul_comm, mul_assoc]; rw [show (-Complex.I) * Complex.I = 1 by
        rw [neg_mul, Complex.I_mul_I]; ring]; ring,
    ← smul_add]
  rw [show (M + Mᴴ) + (M - Mᴴ) = (2 : ℂ) • M by module, smul_smul]
  norm_num

/-- **Effect closure under `(1/c)·`.**  If `A` is PSD and `A ⪯ c·1` (`c > 0`), then
    `(1/c)•A` is an effect: it is PSD, and `1 − (1/c)•A = (1/c)•(c·1 − A)` is PSD.  Lets us
    scale any PSD matrix bounded by `c·1` down into the effect cube — the engine of the cone
    extension `ν`. -/
theorem isEffect_inv_smul {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) {c : ℝ}
    (hc : 0 < c) (hbd : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef) :
    IsEffect ((1 / c) • A) := by
  refine ⟨hA.smul (by positivity), ?_⟩
  have h1 : (1 / c) • ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
    rw [coe_smul, smul_smul, ← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (ne_of_gt hc),
      Complex.ofReal_one, one_smul]
  have key : (1 : Matrix (Fin d) (Fin d) ℂ) - (1 / c) • A
      = (1 / c) • ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A) := by
    rw [smul_sub, h1]
  rw [key]; exact hbd.smul (by positivity)

/-- **Monotonicity of the Löwner bound.**  If `A ⪯ a·1` and `a ≤ b`, then `A ⪯ b·1`
    (`b·1 − A = (a·1 − A) + (b−a)·1`, a sum of PSD matrices). -/
theorem posSemidef_smul_one_sub_mono {A : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hbd : ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef) (hab : a ≤ b) :
    ((b : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef := by
  have hPSD : (((b - a : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by linarith)
  have key : (b : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A
      = ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A)
        + (b - a : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [coe_smul]; push_cast; module
  rw [key]; exact hbd.add hPSD

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

/-- **Cone extension** of `μ` to all PSD matrices: `ν A = c · μ((1/c)•A)` for any Löwner
    bound `A ⪯ c·1`.  Defined concretely with `c = ∑‖Aᵢⱼ‖` (the PSD-bound witness); the key
    theorem `coneExt_eq` shows the value is independent of the chosen bound `c`. -/
noncomputable def coneExt (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ i, ∑ j, ‖A i j‖) * m.μ ((1 / (∑ i, ∑ j, ‖A i j‖)) • A)

/-- **Well-definedness of `ν`.**  For any Löwner bound `A ⪯ c·1` (`c > 0`),
    `coneExt A = c · μ((1/c)•A)` — independent of which bound is used.  Proof: scaling
    `(1/c)•A = (a/c)•((1/a)•A)` and `map_smul` make `c·μ((1/c)•A)` constant in the bound. -/
theorem coneExt_eq {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 < c)
    (hbd : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef) :
    m.coneExt A = c * m.μ ((1 / c) • A) := by
  unfold coneExt
  set s : ℝ := ∑ i, ∑ j, ‖A i j‖ with hs
  have hindep : ∀ (a b : ℝ), 0 < a → 0 < b → a ≤ b →
      ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef →
      ((b : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef →
      a * m.μ ((1 / a) • A) = b * m.μ ((1 / b) • A) := by
    intro a b ha hb hab hbda _
    have hEa : IsEffect ((1 / a) • A) := isEffect_inv_smul hA ha hbda
    have hsm : (1 / b) • A = (a / b) • ((1 / a) • A) := by
      rw [smul_smul]; congr 1; field_simp
    have hmap := m.map_smul hEa (by positivity : (0:ℝ) ≤ a / b)
      (by rw [div_le_one hb]; exact hab)
    rw [← hsm] at hmap
    rw [hmap]; field_simp
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ s by rw [hs]; positivity) with hs0 | hspos
  · have hA0 : A = 0 := by
      have hsum0 : (∑ i, ∑ j, ‖A i j‖) = 0 := by rw [← hs]; exact hs0.symm
      ext i j
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)).mp hsum0 i (Finset.mem_univ i)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => norm_nonneg _)).mp h1 j (Finset.mem_univ j)
      simpa using norm_eq_zero.mp h2
    rw [hA0]; simp [m.map_zero]
  · have hsbd : ((s : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef := by
      rw [hs]; exact posSemidef_sumNorm_sub hA
    rcases le_total s c with hsc | hcs
    · exact hindep s c hspos hc hsc hsbd hbd
    · exact (hindep c s hc hspos hcs hbd hsbd).symm

/-- `ν 1 = 1` (normalization survives the cone extension). -/
theorem coneExt_one : m.coneExt 1 = 1 := by
  rw [m.coneExt_eq Matrix.PosSemidef.one one_pos (by simpa using Matrix.PosSemidef.zero)]
  simp [m.normalized]

/-- `ν` is nonnegative on PSD matrices. -/
theorem coneExt_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ m.coneExt A := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ by positivity) with h0 | hpos
  · unfold coneExt; rw [← h0]; simp
  · rw [m.coneExt_eq hA hpos (posSemidef_sumNorm_sub hA)]
    exact mul_nonneg (le_of_lt hpos) (m.nonneg _ (isEffect_inv_smul hA hpos (posSemidef_sumNorm_sub hA)))

/-- `ν(a·1) = a` for `a ≥ 0`. -/
theorem coneExt_smul_one {a : ℝ} (ha : 0 ≤ a) :
    m.coneExt ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) = a := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · rw [← h0, Complex.ofReal_zero, zero_smul]; simp [coneExt]
  · have hPSD : ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
      rw [← coe_smul]; exact Matrix.PosSemidef.one.smul ha
    have hbd : ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
        - (a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
      rw [sub_self]; exact Matrix.PosSemidef.zero
    rw [m.coneExt_eq hPSD hpos hbd]
    have h1 : (1 / a) • ((a : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
      rw [coe_smul, smul_smul, ← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (ne_of_gt hpos),
        Complex.ofReal_one, one_smul]
    rw [h1, m.normalized, mul_one]

/-- **Homogeneity of `ν`** for nonnegative scalars: `ν(t•A) = t·ν A` (`t ≥ 0`, `A` PSD). -/
theorem coneExt_smul {t : ℝ} (ht : 0 ≤ t) {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    m.coneExt (t • A) = t * m.coneExt A := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0, zero_smul, zero_mul]; simp [coneExt]
  · rcases eq_or_lt_of_le (show (0:ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ by positivity) with hc0 | hcpos
    · have hA0 : A = 0 := by
        have hsum0 : (∑ i, ∑ j, ‖A i j‖) = 0 := hc0.symm
        ext i j
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)).mp hsum0 i (Finset.mem_univ i)
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => norm_nonneg _)).mp h1 j (Finset.mem_univ j)
        simpa using norm_eq_zero.mp h2
      rw [hA0, smul_zero]; simp [coneExt]
    · set c : ℝ := ∑ i, ∑ j, ‖A i j‖ with hc
      have hbd : ((↑(t * c) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - t • A).PosSemidef := by
        rw [show ((↑(t * c) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - t • A)
            = t • ((↑c : ℂ) • 1 - A) by simp only [coe_smul]; push_cast; module]
        exact (posSemidef_sumNorm_sub hA).smul ht
      rw [m.coneExt_eq (hA.smul ht) (by positivity) hbd,
        m.coneExt_eq hA hcpos (posSemidef_sumNorm_sub hA),
        show (1 / (t * c)) • (t • A) = (1 / c) • A by
          rw [smul_smul]; congr 1; field_simp]
      ring

/-- **Additivity of `ν`** on PSD matrices.  Uses a common Löwner bound
    `c = ∑‖Aᵢⱼ‖ + ∑‖Bᵢⱼ‖ + 1` for `A`, `B`, and `A+B`, then the additivity of `μ` on the
    coexistent effects `(1/c)•A`, `(1/c)•B`. -/
theorem coneExt_add {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    m.coneExt (A + B) = m.coneExt A + m.coneExt B := by
  have hsA0 : (0:ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ := by positivity
  have hsB0 : (0:ℝ) ≤ ∑ i, ∑ j, ‖B i j‖ := by positivity
  set c : ℝ := (∑ i, ∑ j, ‖A i j‖) + (∑ i, ∑ j, ‖B i j‖) + 1 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hbA : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - A).PosSemidef :=
    posSemidef_smul_one_sub_mono (posSemidef_sumNorm_sub hA) (by rw [hcdef]; linarith)
  have hbB : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - B).PosSemidef :=
    posSemidef_smul_one_sub_mono (posSemidef_sumNorm_sub hB) (by rw [hcdef]; linarith)
  have htri : (∑ i, ∑ j, ‖(A + B) i j‖) ≤ c := by
    have h1 : (∑ i, ∑ j, ‖(A + B) i j‖) ≤ ∑ i, ∑ j, (‖A i j‖ + ‖B i j‖) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
        rw [Matrix.add_apply]; exact norm_add_le _ _))
    calc (∑ i, ∑ j, ‖(A + B) i j‖) ≤ ∑ i, ∑ j, (‖A i j‖ + ‖B i j‖) := h1
      _ = (∑ i, ∑ j, ‖A i j‖) + (∑ i, ∑ j, ‖B i j‖) := by simp only [Finset.sum_add_distrib]
      _ ≤ c := by rw [hcdef]; linarith
  have hbAB : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - (A + B)).PosSemidef :=
    posSemidef_smul_one_sub_mono (posSemidef_sumNorm_sub (hA.add hB)) htri
  rw [m.coneExt_eq (hA.add hB) hc hbAB, m.coneExt_eq hA hc hbA, m.coneExt_eq hB hc hbB,
    ← mul_add]
  congr 1
  rw [smul_add]
  exact m.additive _ _ (isEffect_inv_smul hA hc hbA) (isEffect_inv_smul hB hc hbB)
    (by rw [← smul_add]; exact isEffect_inv_smul (hA.add hB) hc hbAB)

/-- **Hermitian extension** of `μ`: `Λ H = ν(H + c·1) − c` for any `c ≥ 0` with `H + c·1 ⪰ 0`
    (using the two-sided Löwner bound).  Defined with `c = ∑‖Hᵢⱼ‖`; `hermExt_eq` shows
    independence of `c`. -/
noncomputable def hermExt (H : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  m.coneExt (((∑ i, ∑ j, ‖H i j‖ : ℝ) : ℂ) • 1 + H) - (∑ i, ∑ j, ‖H i j‖)

/-- **Well-definedness of `Λ`.**  `Λ H = ν(H + c·1) − c` for any valid bound `c`.  Proof:
    `(s+c)·1 + H` decomposes both as `(s·1+H) + c·1` and `(c·1+H) + s·1`; `coneExt_add` +
    `coneExt_smul_one` give `ν(s·1+H) + c = ν(c·1+H) + s`. -/
theorem hermExt_eq {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hbd : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + H).PosSemidef) :
    m.hermExt H = m.coneExt ((c : ℂ) • 1 + H) - c := by
  unfold hermExt
  set s : ℝ := ∑ i, ∑ j, ‖H i j‖ with hs
  have hs0 : (0:ℝ) ≤ s := by rw [hs]; positivity
  have hsbd : ((s : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + H).PosSemidef := by
    have hthis := posSemidef_sumNorm_sub_herm hH.neg
    rw [show (∑ i, ∑ j, ‖(-H) i j‖) = s by rw [hs]; simp [Matrix.neg_apply], sub_neg_eq_add]
      at hthis
    exact hthis
  have hcps : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
    rw [← coe_smul]; exact Matrix.PosSemidef.one.smul hc
  have hsps : ((s : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
    rw [← coe_smul]; exact Matrix.PosSemidef.one.smul hs0
  have hcone1 : m.coneExt (((s : ℂ) • 1 + H) + (c : ℂ) • 1) = m.coneExt ((s : ℂ) • 1 + H) + c := by
    rw [m.coneExt_add hsbd hcps, m.coneExt_smul_one hc]
  have hcone2 : m.coneExt (((c : ℂ) • 1 + H) + (s : ℂ) • 1) = m.coneExt ((c : ℂ) • 1 + H) + s := by
    rw [m.coneExt_add hbd hsps, m.coneExt_smul_one hs0]
  have key : ((s : ℂ) • 1 + H) + (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      = ((c : ℂ) • 1 + H) + (s : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by abel
  rw [key, hcone2] at hcone1
  linarith [hcone1]

/-- **Additivity of `Λ`** on Hermitian matrices.  Uses `hermExt_eq` with bounds `c₁`, `c₂`,
    `c₁+c₂`: `(c₁+c₂)·1 + (H₁+H₂) = (c₁·1+H₁) + (c₂·1+H₂)` and `coneExt_add`. -/
theorem hermExt_add {H₁ H₂ : Matrix (Fin d) (Fin d) ℂ} (h₁ : H₁.IsHermitian)
    (h₂ : H₂.IsHermitian) : m.hermExt (H₁ + H₂) = m.hermExt H₁ + m.hermExt H₂ := by
  set c₁ : ℝ := ∑ i, ∑ j, ‖H₁ i j‖ with hc₁
  set c₂ : ℝ := ∑ i, ∑ j, ‖H₂ i j‖ with hc₂
  have hc₁0 : (0:ℝ) ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : (0:ℝ) ≤ c₂ := by rw [hc₂]; positivity
  have hb₁ : ((c₁ : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + H₁).PosSemidef := by
    rw [hc₁]; exact posSemidef_sumNorm_add_herm h₁
  have hb₂ : ((c₂ : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + H₂).PosSemidef := by
    rw [hc₂]; exact posSemidef_sumNorm_add_herm h₂
  have hrw : ((↑(c₁ + c₂) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + (H₁ + H₂))
      = ((c₁ : ℂ) • 1 + H₁) + ((c₂ : ℂ) • 1 + H₂) := by push_cast; module
  have hbsum : ((↑(c₁ + c₂) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + (H₁ + H₂)).PosSemidef := by
    rw [hrw]; exact hb₁.add hb₂
  rw [m.hermExt_eq h₁ hc₁0 hb₁, m.hermExt_eq h₂ hc₂0 hb₂,
    m.hermExt_eq (h₁.add h₂) (by positivity) hbsum, hrw, m.coneExt_add hb₁ hb₂]
  ring

/-- On PSD matrices the Hermitian extension agrees with the cone extension: `Λ A = ν A`
    (take the bound `c = 0`). -/
theorem hermExt_eq_coneExt {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    m.hermExt A = m.coneExt A := by
  rw [m.hermExt_eq hA.1 (c := 0) le_rfl (by simpa using hA)]; simp

/-- `Λ ≥ 0` on PSD matrices (it equals `ν ≥ 0` there). -/
theorem hermExt_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ m.hermExt A := by
  rw [m.hermExt_eq_coneExt hA]; exact m.coneExt_nonneg hA

/-- `Λ 0 = 0`. -/
theorem hermExt_zero : m.hermExt (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  rw [m.hermExt_eq_coneExt Matrix.PosSemidef.zero]; simp [coneExt]

/-- `Λ(−H) = −Λ H` (from additivity and `Λ 0 = 0`). -/
theorem hermExt_neg {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    m.hermExt (-H) = -m.hermExt H := by
  have h := m.hermExt_add hH hH.neg
  rw [add_neg_cancel, m.hermExt_zero] at h
  linarith

/-- `Λ(t•H) = t·Λ H` for `t ≥ 0` (via `coneExt_smul` and `hermExt_eq` with bound `t·s`). -/
theorem hermExt_smul_nonneg {t : ℝ} (ht : 0 ≤ t) {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) : m.hermExt (t • H) = t * m.hermExt H := by
  set s : ℝ := ∑ i, ∑ j, ‖H i j‖ with hs
  have hs0 : (0:ℝ) ≤ s := by rw [hs]; positivity
  have hsps : ((s : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + H).PosSemidef := by
    rw [hs]; exact posSemidef_sumNorm_add_herm hH
  have heq : ((↑(t * s) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + t • H)
      = t • ((s : ℂ) • 1 + H) := by simp only [coe_smul]; push_cast; module
  have hts : ((↑(t * s) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + t • H).PosSemidef := by
    rw [heq]; exact hsps.smul ht
  rw [m.hermExt_eq (isHermitian_smul hH t) (by positivity) hts, m.hermExt_eq hH hs0 hsps, heq,
    m.coneExt_smul ht hsps]
  ring

/-- **ℝ-homogeneity of `Λ`** (all `t ∈ ℝ`): `Λ(t•H) = t·Λ H`.  With `hermExt_add`, `Λ` is
    ℝ-linear on Hermitian matrices.  `t < 0` reduces to `t ≥ 0` via `Λ(−H) = −Λ H`. -/
theorem hermExt_smul {t : ℝ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    m.hermExt (t • H) = t * m.hermExt H := by
  rcases le_total 0 t with ht | ht
  · exact m.hermExt_smul_nonneg ht hH
  · have e : t • H = -((-t) • H) := by rw [neg_smul, neg_neg]
    rw [e, m.hermExt_neg (isHermitian_smul hH (-t)),
      m.hermExt_smul_nonneg (by linarith : (0:ℝ) ≤ -t) hH]
    ring

/-- On an effect, the cone extension recovers `μ`: `ν E = μ E` (take the bound `c = 1`,
    since `E ≤ 1`). -/
theorem coneExt_eq_mu_of_isEffect {E : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) :
    m.coneExt E = m.μ E := by
  rw [m.coneExt_eq hE.1 (c := 1) one_pos (by simpa using hE.2)]; simp

/-- On an effect, the Hermitian extension recovers `μ`: `Λ E = μ E`. -/
theorem hermExt_eq_mu_of_isEffect {E : Matrix (Fin d) (Fin d) ℂ} (hE : IsEffect E) :
    m.hermExt E = m.μ E := by
  rw [m.hermExt_eq_coneExt hE.1, m.coneExt_eq_mu_of_isEffect hE]

/-- **ℂ-linear extension** of `μ` to all matrices: `Λ_ℂ M = Λ(reHerm M) + i·Λ(imHerm M)`. -/
noncomputable def cExt (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (m.hermExt (reHerm M) : ℂ) + Complex.I * (m.hermExt (imHerm M) : ℂ)

/-- `Λ_ℂ` is additive. -/
theorem cExt_add (M N : Matrix (Fin d) (Fin d) ℂ) :
    m.cExt (M + N) = m.cExt M + m.cExt N := by
  have hre : reHerm (M + N) = reHerm M + reHerm N := by
    simp only [reHerm, conjTranspose_add]; module
  have him : imHerm (M + N) = imHerm M + imHerm N := by
    simp only [imHerm, conjTranspose_add]; module
  simp only [cExt, hre, him, m.hermExt_add (reHerm_isHermitian M) (reHerm_isHermitian N),
    m.hermExt_add (imHerm_isHermitian M) (imHerm_isHermitian N)]
  push_cast; ring

/-- `Λ_ℂ` on a `ℂ`-real scalar: `Λ_ℂ((↑r)•M) = ↑r · Λ_ℂ M`. -/
theorem cExt_ofReal_smul (r : ℝ) (M : Matrix (Fin d) (Fin d) ℂ) :
    m.cExt ((r : ℂ) • M) = (r : ℂ) * m.cExt M := by
  have hre : reHerm ((r : ℂ) • M) = (r : ℝ) • reHerm M := by
    simp only [reHerm, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, coe_smul]
    module
  have him : imHerm ((r : ℂ) • M) = (r : ℝ) • imHerm M := by
    simp only [imHerm, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, coe_smul]
    module
  simp only [cExt, hre, him, m.hermExt_smul (reHerm_isHermitian M),
    m.hermExt_smul (imHerm_isHermitian M)]
  push_cast; ring

/-- `Λ_ℂ(i•M) = i·Λ_ℂ M` (complex-structure compatibility). -/
theorem cExt_I_smul (M : Matrix (Fin d) (Fin d) ℂ) :
    m.cExt (Complex.I • M) = Complex.I * m.cExt M := by
  simp only [cExt, reHerm_I, imHerm_I, m.hermExt_neg (imHerm_isHermitian M)]
  push_cast
  linear_combination (-(↑(m.hermExt (imHerm M)) : ℂ)) * Complex.I_sq

/-- **ℂ-linearity of `Λ_ℂ`**: `Λ_ℂ(c•M) = c·Λ_ℂ M` for all `c ∈ ℂ`.  With `cExt_add`, `Λ_ℂ`
    is a ℂ-linear functional on all matrices (the complexification of `Λ`). -/
theorem cExt_smul (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    m.cExt (c • M) = c * m.cExt M := by
  conv_lhs => rw [show c • M = (↑c.re : ℂ) • M + (↑c.im : ℂ) • (Complex.I • M) by
    rw [smul_smul, ← add_smul, Complex.re_add_im]]
  rw [m.cExt_add, m.cExt_ofReal_smul, m.cExt_ofReal_smul, m.cExt_I_smul,
    show c * m.cExt M = ((↑c.re : ℂ) + ↑c.im * Complex.I) * m.cExt M by rw [Complex.re_add_im]]
  ring

end EffectMeasure

end QIQTH.EffectGleason
