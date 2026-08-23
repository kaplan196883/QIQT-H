/-
  LeviWindowUniformAmpLipschitz — J4-1075: the WINDOW-UNIFORM `Levi(s,z)` bounded+Lipschitz bundle
  (constants independent of `s` across the whole sliver window `[t-ε,t]`) and its s-indexed product
  wrapper with an amplitude, folding `Levi(s,·)` into a single window-uniform Lipschitz-at-0 constant
  ready to feed `HCompNearCarryBfacFourTermAssembly.bfac_four_term_domain_restricted_bound` at each
  fixed `s`/`τ := t-s` in the sliver — the Sol-scoped fix for the invalid "multiply by a constant
  `M_Levi`" composition flagged by J4-1074.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM THIS FILE ADDRESSES.  `HCompNearCarryKPrimeBaseFieldCoV.lean`'s (J4-1010) BRICK 1
  has `Bfac(z) := Levi(s,z)·(hsMixed·A + grⱼ·∂ⱼA + grᵢ·∂ᵢA + ∂ⱼ∂ᵢA)`, with `Levi(s,z) := leviSeries E
  s z 0` and `s` the SAME variable as the OUTER Duhamel time in `gaussDdim (t-s) (U z x)` (confirmed
  by direct read of `HCompNearCarryKPrimeBaseFieldCoV.lean` line 108: `leviSeries (heatOp …) s z 0`,
  literal `s`, NOT `t-s`).  `HCompNearCarryBfacFourTermAssembly.lean` (J4-1073) bounds the bare
  4-term SUM `T1+T2+T3+T4` (no `Levi` factor) over the sliver window `s ∈ (t-ε,t)` at `O(√ε)`. J4-1074
  found that multiplying that SIGNED bound by a pointwise sup `M_Levi` on `|Levi|` is mathematically
  INVALID (`|∫f|≤B` does not give `|∫Levi·f|≤M·B` from a mere pointwise `|Levi|≤M`, absent an
  L¹/pointwise-domination argument) and scoped the fix: fold `Levi(s,z)` INTO each amplitude BEFORE
  bounding (mirroring `LeviAmpProductGlobalRegularity.lean`'s/J4-1028's OWN pattern for `T1`), using
  WINDOW-UNIFORM (not per-`s`) constants for `Levi`'s own bound/Lipschitz data, since
  `bfac_four_term_domain_restricted_bound`'s conclusion shape needs `s`-INDEPENDENT `L`,`M` constants
  to survive the outer sliver-window `s`-integration unchanged.

  ## THE KEY OBSERVATION (confirmed before Lean, `gpt-5.6-sol` high, GO-confirmed 2026-08-23).
  `LeviAmpProductGlobalRegularity.leviBase_global_bounded_lipschitz`'s per-`s` constants are, via its
  OWN proof (`LeviLipschitz.abs_F_le_diagonal`/`resolvent_lipschitz_pointwise`), CONCRETELY
      `M_F(s) = C_L · gaussDdim (2s) 0`   (bound, ANTITONE in `s`: `gaussDdimPeak_antitone_width`,
                                            J4-886, `HZMassCappedWindowClosed.lean`, reused verbatim),
      `L_F(s) = L_E + Kc·(2·√s)`          (Lipschitz modulus, MONOTONE INCREASING in `s`).
  So on a window `s ∈ [t-ε,t]` with `0 < ε < t` (bounded away from `s=0`), `M_F(s)` peaks at the
  window's LOWER endpoint `s=t-ε` and `L_F(s)` peaks at the UPPER endpoint `s=t` — giving GENUINE
  `s`-INDEPENDENT window-uniform constants `M_F(t-ε)`, `L_F(t)` that dominate `M_F(s)`, `L_F(s)` for
  EVERY `s` in the window.  This is the OPPOSITE window-endpoint pairing from a naive single-endpoint
  guess (the two constants peak at OPPOSITE ends), confirmed correct by Sol before any Lean was written.

  ## WHAT LANDS (ns `QIQTH.LeviWindowUniformAmpLipschitz`).
    • `leviBase_window_uniform_bounded_lipschitz` — ★★★★ the WINDOW-UNIFORM re-export: from the SAME
      five analytic carries (`hFdom`,`hVol`,`hE1`,`hIz`,`hSlice`), now quantified `∀ s ∈ Icc (t-ε) t`
      (genuinely needed at EVERY `s` in the window, not one fixed `s`), produces `∃ M_F L_F ≥ 0` with
      `∀ s ∈ Icc (t-ε) t, ∀ z, |Levi(s,z)| ≤ M_F` and `∀ s ∈ Icc (t-ε) t, ∀ z w, |Levi(s,z)-Levi(s,w)|
      ≤ L_F·dist z w` — SAME `M_F`, `L_F` for every `s` in the window.  Built DIRECTLY from
      `LeviLipschitz.abs_F_le_diagonal`/`resolvent_lipschitz_pointwise` (not by `obtain`-ing the
      opaque existential of `leviBase_global_bounded_lipschitz`, whose witnesses are NOT exposed
      concretely by that theorem's `∃`-statement — re-deriving directly from the concrete underlying
      facts avoids relying on unexposed proof-term formulas, the same "wrong API" pitfall J4-1073's
      own report flagged for a different composition).
    • `leviAmp_product_window_uniform_lipschitz` — ★★★★★ THE `s`-INDEXED WRAPPER: composes the
      window-uniform `Levi` bundle with any bounded+Lipschitz-at-0 amplitude `Amp` (`bounded_lipschitz_
      mul_global`, J4-1028) into a SINGLE window-uniform pair `(M', L')` such that ∀ `s` in the window,
      the product `AmpLevi_s(v) := Levi(s,v)·Amp(v)` is bounded by `M'` and Lipschitz-AT-0 by `L'`
      (`|AmpLevi_s(v) - AmpLevi_s(0)| ≤ L'·‖v‖`) — EXACTLY the `hAmp`/`L`/`hlip` hypothesis shape
      `HCompNearCarryBfacFourTermAssembly.bfac_four_term_domain_restricted_bound` demands, ready to be
      supplied at each fixed `s` (equivalently `τ := t-s`) in the sliver.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Precisely
  what remains OPEN, regardless of this file:
    (i)   This file does NOT thread `leviAmp_product_window_uniform_lipschitz`'s `(M',L')` THROUGH
          `HCompNearCarryBfacFourTermAssembly.bfac_four_term_domain_restricted_sliver_window_bound`'s
          Part-2 outer `s`-sliver-window integration (`pointwise_bound_sliver_window_inv_sqrt`) to
          produce a NEW `O(√ε)` capstone for the `Levi`-FOLDED four-term sum.  That composition needs,
          in addition, bounding the s-VARYING quantity `|AmpLevi_s(0)| = |Levi(s,0)·Amp(0)|` (which
          appears inside Part 1's conclusion) by the `s`-INDEPENDENT `M_F·|Amp 0|` via the nonneg-
          coefficient monotonicity substitution Sol confirmed is sound — genuinely NOT built here, and
          is the concrete next Lean increment (would re-derive a `bfac_four_term_LEVI_domain_restricted_
          sliver_window_bound`, mirroring J4-1073's own Part 1/Part 2 split, at comparable size).
    (ii)  `Bfac`'s literal `A`/`∂ⱼA`/`∂ᵢA`/`∂ⱼ∂ᵢA` globalization (J4-1069's frontier item 1) — untouched.
    (iii) `hfac`'s literal carry over the IFT-selected `S'`, `hxmem` (shared upstream gate), the far
          carry `fb` — all untouched, ENTIRELY SEPARATE, per J4-1073's own firewall.
    (iv)  Does NOT discharge `nb`, `hCConv`, `hcomp`, or any part of `VanVleckGatedSpatialSymmetry`.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  Non-vacuity: every hypothesis set is satisfiable by concrete
  test data (e.g. `E := 0`, `C_L := 0`, `Kc := 0`, `L_E := 0`, `Amp := 0`, `MA := 0`, `LA := 0`,
  `t := 1`, `ε := 1/2`), and no theorem's hypothesis set is equal to its conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.LeviLipschitz
import QIQTH.HZMassCappedWindowClosed
import QIQTH.LeviAmpProductGlobalRegularity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.HZMassCappedWindowClosed
open QIQTH.LeviAmpProductGlobalRegularity
open scoped Topology BigOperators Interval

namespace QIQTH.LeviWindowUniformAmpLipschitz

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the WINDOW-UNIFORM `Levi(s,z)` bounded+Lipschitz bundle.
    ############################################################################### -/

/-- **★★★★ `leviBase_window_uniform_bounded_lipschitz`.**  For the sliver window `s ∈ [t-ε,t]` with
    `0 < ε < t` (bounded away from `s=0`), a SINGLE pair `(M_F, L_F)` — INDEPENDENT of `s` — bounds
    `Levi(s,z) := leviSeries E s z 0` and its spatial Lipschitz modulus for EVERY `s` in the window:
    `M_F := C_L·gaussDdim(2(t-ε))(0)` (the bound-side sup, achieved at the window's LOWER endpoint,
    by `gaussDdimPeak_antitone_width`) and `L_F := L_E + Kc·(2√t)` (the Lipschitz-side sup, achieved
    at the window's UPPER endpoint, by `Real.sqrt` monotonicity).  Built directly from `LeviLipschitz.
    abs_F_le_diagonal`/`resolvent_lipschitz_pointwise` (the concrete underlying facts), not from the
    opaque existential of `leviBase_global_bounded_lipschitz`.  NOT `a₁ = R/6`. -/
theorem leviBase_window_uniform_bounded_lipschitz
    (E : ℝ → Point n → Point n → ℝ) (t ε C_L Kc L_E : ℝ)
    (hε : 0 < ε) (hεt : ε < t) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ s ∈ Set.Icc (t - ε) t, ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ s ∈ Set.Icc (t - ε) t, ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ M_F L_F : ℝ, 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n, |leviSeries E s z 0| ≤ M_F) ∧
      (∀ s ∈ Set.Icc (t - ε) t, ∀ z w : Point n,
          |leviSeries E s z 0 - leviSeries E s w 0| ≤ L_F * dist z w) := by
  have ht0 : 0 < t - ε := by linarith
  have h2te0 : 0 < 2 * (t - ε) := by linarith
  refine ⟨C_L * gaussDdim (2 * (t - ε)) (0 : Point n), L_E + Kc * (2 * Real.sqrt t),
    mul_nonneg hC_L (gaussDdim_nonneg' _ _),
    add_nonneg hL_E (mul_nonneg hKc (by positivity)), ?_, ?_⟩
  · intro s hs z
    have hspos : 0 < s := lt_of_lt_of_le ht0 hs.1
    have hb := abs_F_le_diagonal (leviSeries E) C_L s hspos hC_L (hFdom s hs) z
    have hmono : gaussDdim (2 * s) (0 : Point n) ≤ gaussDdim (2 * (t - ε)) (0 : Point n) :=
      gaussDdimPeak_antitone_width h2te0 (by linarith [hs.1])
    calc |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (0 : Point n) := hb
      _ ≤ C_L * gaussDdim (2 * (t - ε)) (0 : Point n) := mul_le_mul_of_nonneg_left hmono hC_L
  · intro s hs z w
    have hspos : 0 < s := lt_of_lt_of_le ht0 hs.1
    have hl := resolvent_lipschitz_pointwise E (leviSeries E) s Kc L_E z w hspos hKc
      (hVol s hs z) (hVol s hs w) (hE1 s hs z w) (hIz s hs z) (hIz s hs w) (hSlice s hs z w)
    have hsqrt_mono : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hs.2
    have hLmono : L_E + Kc * (2 * Real.sqrt s) ≤ L_E + Kc * (2 * Real.sqrt t) := by
      have h1 : Kc * (2 * Real.sqrt s) ≤ Kc * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left (by linarith [hsqrt_mono]) hKc
      linarith
    calc |leviSeries E s z 0 - leviSeries E s w 0|
        ≤ (L_E + Kc * (2 * Real.sqrt s)) * dist z w := hl
      _ ≤ (L_E + Kc * (2 * Real.sqrt t)) * dist z w := mul_le_mul_of_nonneg_right hLmono dist_nonneg

/-! ###############################################################################
    ### §B — the `s`-indexed product wrapper: window-uniform `Levi(s,·)·Amp(·)` Lipschitz-at-0.
    ############################################################################### -/

/-- **★★★★★ `leviAmp_product_window_uniform_lipschitz`.**  For any bounded+Lipschitz-at-0 amplitude
    `Amp` (`|Amp v| ≤ MA`, `|Amp v - Amp 0| ≤ LA·‖v‖`), a SINGLE window-uniform pair `(M', L')`
    bounds the product `Levi(s,·)·Amp(·)` and its Lipschitz-at-0 modulus for EVERY `s ∈ [t-ε,t]`:
    `M' := M_F·MA`, `L' := M_F·LA + MA·L_F` — reusing `bounded_lipschitz_mul_global`'s pairwise bound
    at `w := 0` (`dist v 0 = ‖v‖`).  This is EXACTLY the `hAmp`/`L`/`hlip` hypothesis shape
    `HCompNearCarryBfacFourTermAssembly.bfac_four_term_domain_restricted_bound` needs, ready to supply
    at each fixed `s`/`τ := t-s` in the sliver — the `s`-indexed wrapper the Sol-scoped fix called for.
    Does NOT thread this through the outer sliver-window `s`-integration (see firewall). NOT `a₁=R/6`. -/
theorem leviAmp_product_window_uniform_lipschitz
    (E : ℝ → Point n → Point n → ℝ) (t ε C_L Kc L_E : ℝ)
    (hε : 0 < ε) (hεt : ε < t) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ s ∈ Set.Icc (t - ε) t, ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ s ∈ Set.Icc (t - ε) t, ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2))
    (Amp : Point n → ℝ) (MA LA : ℝ) (hMA : 0 ≤ MA) (hLA : 0 ≤ LA)
    (hbdA : ∀ v : Point n, |Amp v| ≤ MA) (hlipA : ∀ v w : Point n, |Amp v - Amp w| ≤ LA * dist v w) :
    ∃ M' L' : ℝ, 0 ≤ M' ∧ 0 ≤ L' ∧
      (∀ s ∈ Set.Icc (t - ε) t, ∀ v : Point n, |leviSeries E s v 0 * Amp v| ≤ M') ∧
      (∀ s ∈ Set.Icc (t - ε) t, ∀ v : Point n,
          |leviSeries E s v 0 * Amp v - leviSeries E s (0 : Point n) 0 * Amp 0| ≤ L' * ‖v‖) := by
  obtain ⟨M_F, L_F, hMF, hLF, hFb, hFl⟩ :=
    leviBase_window_uniform_bounded_lipschitz E t ε C_L Kc L_E hε hεt hC_L hKc hL_E
      hFdom hVol hE1 hIz hSlice
  refine ⟨M_F * MA, M_F * LA + MA * L_F, mul_nonneg hMF hMA,
    add_nonneg (mul_nonneg hMF hLA) (mul_nonneg hMA hLF), ?_, ?_⟩
  · intro s hs v
    obtain ⟨hbnd, _⟩ :=
      bounded_lipschitz_mul_global (fun z => leviSeries E s z 0) Amp M_F L_F MA LA
        hMF hLF hMA hLA (hFb s hs) (hFl s hs) hbdA hlipA
    exact hbnd v
  · intro s hs v
    obtain ⟨_, hlip⟩ :=
      bounded_lipschitz_mul_global (fun z => leviSeries E s z 0) Amp M_F L_F MA LA
        hMF hLF hMA hLA (hFb s hs) (hFl s hs) hbdA hlipA
    have h0 := hlip v (0 : Point n)
    rwa [dist_zero_right] at h0

end QIQTH.LeviWindowUniformAmpLipschitz

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.LeviWindowUniformAmpLipschitz
#print axioms leviBase_window_uniform_bounded_lipschitz
#print axioms leviAmp_product_window_uniform_lipschitz
end AxiomChecks
