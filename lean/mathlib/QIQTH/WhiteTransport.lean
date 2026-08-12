/-
  WhiteTransport — J4-642: the h0/h1 TRANSPORT-WALL AUDIT — the conjugation-direction verdict.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★ THE CONJUGATION VERDICT (J4-642 finding; Sol-confirmed, gpt-5.6-sol high).
  The Sol-flagged "conjugation-direction identification" audit was carried out and found a GENUINE
  DIRECTION MISMATCH — and it sits at the *h0* level, not just h1:

  Under the Gauss-lemma hypotheses at `v` (inverse-metric radial compatibility `Σⱼ(gⁱʲ−δ)vⱼ = 0`,
  `gi` symmetric at `v`, the differentiated metric Gauss identity `Σ_a v_a·∂ᵢg_{aj} = δᵢⱼ − g_{ij}`,
  and `tr(gi·g) = n`), PURE FINITE-SUM ALGEBRA gives (§2, proved):
      (1) the metric-deviation cross term kills for EVERY field;
      (2) `Σ gⁱʲΓᵏᵢⱼvᵏ = (tr gi − n) − ½ρ`,  `ρ := Σ_a v_a Σᵢⱼ gⁱʲ ∂_a g_{ij}` (`radialLogDetSym`,
          the symbolic Jacobi form of `r∂_r log det g`);
      (3) hence the assembled coefficients collapse EXACTLY:
              `K₀ = ¼ρ·w₀ + r∂_r w₀`   and   `K₁ = ¼ρ·w₁ + w₁ + r∂_r w₁ − Δ_g w₀` .
  CONSEQUENCE (§3): the banked ansatz folds `w₀ = Θ^{−1/2}·u₀` with `Θ := vanVleck = (det g̃)^{−1/2}`,
  i.e. `w₀ = (det g̃)^{+1/4}`, whose radial chain rule is `r∂_r w₀ = +¼ρ·w₀` — so
      `K₀ = ½ρ·w₀ ≠ 0`   wherever `r∂_r log det g̃ ≠ 0` (generic curved chart, off-centre).
  The classical Minakshisundaram amplitude is `(det g̃)^{−1/4} = Θ^{+1/2}` (H³ cross-check:
  `r/sinh r = (det g̃)^{−1/4}`).  The ansatz fold `Θ^{−1/2}` carries the WRONG SIGN in the exponent
  relative to the repo's `vanVleck` convention; the `h0` binder consumed by
  `white_K1BudgetW_of_transport` is FALSE at curved Gauss-lemma data (proved here by an explicit
  globally-positive-definite exponential witness, §5), and the {h0,h1} binder pair is inconsistent
  wherever `K₀ ≠ 0` (h1 alone MAY vanish accidentally — not claimed false everywhere).

  ★ THE FIX (F1; the only one — `K₀` does not see the transport operator, so re-aiming `T` is dead):
  keep the coefficients `u = transportCoeff (transportOp Θ_w g gi)` — `transportOp`'s conjugator
  `Θ_w^{1/2} = (det g̃)^{−1/4}` is ALREADY the correct amplitude — and instantiate the ansatz with
  `Θ := (vanVleck G)⁻¹ = √det g̃`, so the fold `Θ^{−1/2}` becomes `(det g̃)^{−1/4}`.  Then (§4, proved):
      • `K₀ = ¼ρw₀ − ¼ρw₀ = 0`   (h0 = a theorem GIVEN the single radial-Jacobi chain-rule bridge
        `r∂_r w₀ = −¼ρ·w₀` — labelled `hamp`; NO Ricci/expMap representation needed: the Gauss
        lemma collapsed the old ParametrixResidualO1Total rep-mismatch checkpoint to ONE lemma);
      • `K₁ = a·(1+r∂_r)u₁ − Δ_g(a·u₀) = a·a⁻¹·Δ_g(a·u₀) − Δ_g(a·u₀) = 0`   (h1 = near-definitional
        from the banked ODE once the fold direction matches — exactly the Sol-predicted
        identification; `transportOp_inv_inv` bridges the double inverse to the banked operator,
        so the R/6 diagonal supplier is preserved).

  ⚠ HONEST SCOPE (binding).
    • The reduction theorems (§2) are unconditional finite-sum algebra at the point `v`.
    • The direction theorems (§3/§4) carry the radial chain rule for the fold (`hchain`/`hamp`) as
      a LABELLED hypothesis; for the actual whitened `Θ` its discharge is the radial Jacobi
      identity `r∂_r (det g)^p = p·ρ·(det g)^p` — `radialDeriv_rpow` (banked) supplies the rpow
      layer; the remaining owed content is Jacobi's determinant-derivative formula
      `r∂_r log det g = ρ` (the ONE remaining named h0 bridge lemma) plus the neighbourhood Gauss
      identities at the whitened chart.
    • With the CURRENT fold the ODE does not cancel `K₁` (schematically
      `K₁ = Θ⁻¹Δ_gΘ^{1/2} − Δ_gΘ^{−1/2} + ½ρΘ^{−1/2}u₁`); we do NOT claim it nonzero everywhere —
      the current witness is already dead via `K₀ ≠ 0`.
    • The K₁ identification gate at flat data (§6) is CONSISTENCY only (both conjugation
      directions coincide at `Θ ≡ 1`); the DISCRIMINATING gates are the h0 pair (§5: same curved
      witness, current fold `K₀ = 1 ≠ 0`, corrected fold `K₀ = 0`).
    • Nothing here modifies any banked theorem — this file only ADDS the audit verdict; the
      `WhiteOrder1` binders {h0, h1} remain as stated there (their curved-data discharge now
      routes through the F1 re-instantiation).  Flat tower and the diagonal `R/6` carrier are
      unaffected (`ρ(0) = 0`, fold `= 1` at the centre).
  `a₁ = R/6` remains CONDITIONAL: flat tower closed and non-vacuous; the curved side owes the F1
  re-instantiation of the whitened witness + the Jacobi bridge + the Jet-5 chart residue + the
  Duhamel carry + the fat-`K` carrier piles + capstone co-instantiation + the prior analytic
  piles.  This brick = the transport-wall AUDIT + the reduction/identification theorems + gates.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteOrder1

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.WhiteOrder1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialTransport
open QIQTH.VanVleck

namespace QIQTH.WhiteTransport

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. The symbolic radial log-det and elementary radial algebra. -/

/-- **The symbolic radial log-determinant** `ρ(v) = Σ_a v_a · Σᵢⱼ gⁱʲ(v)·∂_a g_{ij}(v)` — the
    Jacobi-formula form of `r∂_r log det g` carried purely in the `(g, gi)` symbol representation
    (no determinant, no `expMap`).  The Gauss-lemma reduction (§2) shows the ENTIRE `O(1/t)`
    geometry of the transport coefficients is this one scalar. -/
noncomputable def radialLogDetSym (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n) : ℝ :=
  ∑ a, v a * (∑ i, ∑ j, gi v i j * pd (fun y => g y i j) a v)

/-- Kronecker contraction: `Σⱼ δᵢⱼ·vⱼ = vᵢ`. -/
lemma sum_delta_mul (v : Point n) (i : Fin n) :
    (∑ j, (if i = j then (1 : ℝ) else 0) * v j) = v i := by
  simp [ite_mul]

/-- The Gauss identity in contraction form: `Σⱼ gⁱʲvⱼ = vⁱ`. -/
lemma gauss_contract {gi : Point n → Fin n → Fin n → ℝ} {v : Point n}
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0) (i : Fin n) :
    (∑ j, gi v i j * v j) = v i := by
  have h := hGauss i
  have hsplit : (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j)
      = (∑ j, gi v i j * v j) - (∑ j, (if i = j then (1 : ℝ) else 0) * v j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, sum_delta_mul] at h
  linarith

/-- First-slot Gauss contraction (via symmetry): `Σₖ vₖ·gᵏᵃ = vᵃ`. -/
lemma gauss_contract_left {gi : Point n → Fin n → Fin n → ℝ} {v : Point n}
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0) (a : Fin n) :
    (∑ k, v k * gi v k a) = v a := by
  have h : (∑ k, v k * gi v k a) = ∑ k, gi v a k * v k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym k a]; ring
  rw [h, gauss_contract hGauss a]

/-- **The radial Leibniz rule** `r∂_r(f·h) = f·(r∂_r h) + h·(r∂_r f)` at coordinate-differentiable
    data (termwise `pd_mul`). -/
theorem radialDeriv_mul (f h : Point n → ℝ) (v : Point n)
    (hf : ∀ i, PdiffAt f i v) (hh : ∀ i, PdiffAt h i v) :
    radialDeriv (fun y => f y * h y) v = f v * radialDeriv h v + h v * radialDeriv f v := by
  simp only [radialDeriv]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_mul f h i v (hf i) (hh i)]
  ring

/-- `r∂_r` of a constant field vanishes. -/
lemma radialDeriv_const (c : ℝ) (v : Point n) : radialDeriv (fun _ => c) v = 0 := by
  unfold radialDeriv
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [pd_const]
  ring

/-- `ρ` of a constant metric field vanishes (for ANY `gi`). -/
lemma radialLogDetSym_of_const (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (v : Point n) :
    radialLogDetSym (fun _ => G) gi v = 0 := by
  unfold radialLogDetSym
  refine Finset.sum_eq_zero fun a _ => ?_
  have hz : (∑ i, ∑ j, gi v i j * pd (fun _ => G i j) a v) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [pd_const]
    ring
  rw [hz]
  ring

/-! ### §2. The Gauss-lemma reduction of the two transport coefficients (pure algebra). -/

/-- **(1) The deviation cross term is killed by the Gauss lemma, for EVERY field**:
    `Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼf + vʲ∂ᵢf) = 0` given `Σⱼ(gⁱʲ−δ)vⱼ = 0` and `gi` symmetric at `v`.
    This is the MAJOR whitened-chart simplification the old checkpoint did not have: at a
    true-Gauss-lemma chart the deviation layer of the residual carries no content at all. -/
theorem deviation_term_vanishes (gi : Point n → Fin n → Fin n → ℝ) (f : Point n → ℝ)
    (v : Point n) (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0) :
    (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd f j v + v j * pd f i v)) = 0 := by
  have hcol : ∀ j, (∑ i, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v i) = 0 := by
    intro j
    have h : (∑ i, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v i)
        = ∑ i, (gi v j i - (if j = i then (1 : ℝ) else 0)) * v i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hδ : (if i = j then (1 : ℝ) else 0) = (if j = i then (1 : ℝ) else 0) := by
        by_cases h' : i = j
        · rw [if_pos h', if_pos h'.symm]
        · rw [if_neg h', if_neg (fun h'' => h' h''.symm)]
      rw [hsym i j, hδ]
    rw [h]
    exact hGauss j
  have hsplit : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd f j v + v j * pd f i v))
      = (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v i * pd f j v)
        + (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j * pd f i v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  have h1 : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v i * pd f j v) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show (∑ i, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v i * pd f j v)
        = (∑ i, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v i) * pd f j v from
      (Finset.sum_mul _ _ _).symm]
    rw [hcol j, zero_mul]
  have h2 : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j * pd f i v) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j * pd f i v)
        = (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) * pd f i v from
      (Finset.sum_mul _ _ _).symm]
    rw [hGauss i, zero_mul]
  rw [h1, h2, add_zero]

/-- **(2) The Christoffel contraction at a Gauss-lemma point**:
    `Σᵢⱼₖ gⁱʲ·Γᵏᵢⱼ·vᵏ = (Σᵢ gⁱⁱ − n) − ½·ρ` given the Gauss set at `v` (symmetry of `gi`, the
    inverse-metric radial compatibility, the DIFFERENTIATED metric Gauss identity
    `Σ_a v_a·∂ᵢg_{aj} = δᵢⱼ − g_{ij}`, and the trace normalization `Σᵢⱼ gⁱʲg_{ij} = n`).
    Finite-sum algebra on the `christoffel` definition — no analysis. -/
theorem gamma_contraction_gauss (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ)) :
    (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)
      = ((∑ i, gi v i i) - (n : ℝ)) - (1 / 2) * radialLogDetSym g gi v := by
  -- Step 1: collapse the k-contraction of Γ through the first-slot Gauss identity.
  have hchris : ∀ i j, (∑ k, christoffel g gi k i j v * v k)
      = (1 / 2) * (∑ a, v a * (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
          - pd (fun y => g y i j) a v)) := by
    intro i j
    simp only [christoffel]
    calc (∑ k, ((1 / 2) * ∑ a, gi v k a *
            (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
              - pd (fun y => g y i j) a v)) * v k)
        = ∑ k, ∑ a, (1 / 2) * (v k * gi v k a *
            (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
              - pd (fun y => g y i j) a v)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a, ∑ k, (1 / 2) * (v k * gi v k a *
            (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
              - pd (fun y => g y i j) a v)) := Finset.sum_comm
      _ = (1 / 2) * ∑ a, (∑ k, v k * gi v k a) *
            (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
              - pd (fun y => g y i j) a v) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = (1 / 2) * ∑ a, v a * (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
              - pd (fun y => g y i j) a v) := by
          refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
          rw [gauss_contract_left hsym hGauss a]
  -- Step 2: substitute and split each summand into the three metric-derivative pieces.
  have h1 : (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k)
      = ∑ i, ∑ j, gi v i j * (∑ k, christoffel g gi k i j v * v k) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∀ i j, gi v i j * (∑ k, christoffel g gi k i j v * v k)
      = (1 / 2) * (gi v i j * (∑ a, v a * pd (fun y => g y a j) i v)
          + gi v i j * (∑ a, v a * pd (fun y => g y a i) j v)
          - gi v i j * (∑ a, v a * pd (fun y => g y i j) a v)) := by
    intro i j
    rw [hchris i j]
    rw [show (∑ a, v a * (pd (fun y => g y a j) i v + pd (fun y => g y a i) j v
        - pd (fun y => g y i j) a v))
        = (∑ a, v a * pd (fun y => g y a j) i v) + (∑ a, v a * pd (fun y => g y a i) j v)
          - (∑ a, v a * pd (fun y => g y i j) a v) from by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring]
    ring
  rw [h1, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h2 i j]
  -- Step 3: pull the ½ out and split the double sum into the three pieces.
  have hhalf : (∑ i, ∑ j, (1 / 2) * (gi v i j * (∑ a, v a * pd (fun y => g y a j) i v)
        + gi v i j * (∑ a, v a * pd (fun y => g y a i) j v)
        - gi v i j * (∑ a, v a * pd (fun y => g y i j) a v)))
      = (1 / 2) * ((∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y a j) i v))
          + (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y a i) j v))
          - (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y i j) a v))) := by
    rw [show (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y a j) i v))
          + (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y a i) j v))
          - (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y i j) a v))
        = ∑ i, ∑ j, (gi v i j * (∑ a, v a * pd (fun y => g y a j) i v)
            + gi v i j * (∑ a, v a * pd (fun y => g y a i) j v)
            - gi v i j * (∑ a, v a * pd (fun y => g y i j) a v)) from by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hhalf]
  -- Step 4: evaluate the three pieces.
  have hP1 : (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y a j) i v))
      = (∑ i, gi v i i) - (n : ℝ) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by rw [hdGauss i j]]
    rw [show (∑ i, ∑ j, gi v i j * ((if i = j then (1 : ℝ) else 0) - g v i j))
        = (∑ i, ∑ j, gi v i j * (if i = j then (1 : ℝ) else 0))
          - (∑ i, ∑ j, gi v i j * g v i j) from by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring]
    have hδtr : (∑ i, ∑ j, gi v i j * (if i = j then (1 : ℝ) else 0)) = ∑ i, gi v i i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_ite]
    rw [hδtr, htr]
  have hP2 : (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y a i) j v))
      = (∑ i, gi v i i) - (n : ℝ) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by rw [hdGauss j i]]
    rw [show (∑ i, ∑ j, gi v i j * ((if j = i then (1 : ℝ) else 0) - g v j i))
        = (∑ i, ∑ j, gi v i j * (if j = i then (1 : ℝ) else 0))
          - (∑ i, ∑ j, gi v i j * g v j i) from by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring]
    have hδ2 : (∑ i, ∑ j, gi v i j * (if j = i then (1 : ℝ) else 0)) = ∑ i, gi v i i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_ite]
    have htr2 : (∑ i, ∑ j, gi v i j * g v j i) = (n : ℝ) := by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by rw [hsym i j]]
      rw [Finset.sum_comm]
      exact htr
    rw [hδ2, htr2]
  have hP3 : (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y i j) a v))
      = radialLogDetSym g gi v := by
    unfold radialLogDetSym
    calc (∑ i, ∑ j, gi v i j * (∑ a, v a * pd (fun y => g y i j) a v))
        = ∑ i, ∑ a, ∑ j, v a * (gi v i j * pd (fun y => g y i j) a v) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show (∑ j, gi v i j * (∑ a, v a * pd (fun y => g y i j) a v))
              = ∑ j, ∑ a, v a * (gi v i j * pd (fun y => g y i j) a v) from
            Finset.sum_congr rfl fun j _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun a _ => by ring]
          exact Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, v a * (gi v i j * pd (fun y => g y i j) a v) := Finset.sum_comm
      _ = ∑ a, v a * (∑ i, ∑ j, gi v i j * pd (fun y => g y i j) a v) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  rw [hP1, hP2, hP3]
  ring

/-- **★ THE K₀ GAUSS REDUCTION.**  At a Gauss-lemma point the assembled `O(1/t)` coefficient is
    EXACTLY the radial transport binomial:
        `K₀ = ¼·ρ·w₀ + r∂_r w₀`,   `ρ = radialLogDetSym`,  `w₀ = foldedCoeff Θ u 0`.
    The `(g,Γ)`-symbol content of `K₀` fully collapses into the single scalar `ρ` — the old
    rep-mismatch checkpoint (expMap Ricci facts vs `(g,Γ)` symbols) is bypassed at such charts. -/
theorem totalRadialO1_coeff_gauss_reduction (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ)) :
    totalRadialO1_coeff g gi Θ u v
      = (1 / 4) * radialLogDetSym g gi v * foldedCoeff Θ u 0 v
        + radialDeriv (foldedCoeff Θ u 0) v := by
  unfold totalRadialO1_coeff
  rw [gamma_contraction_gauss g gi v hsym hGauss hdGauss htr,
      deviation_term_vanishes gi (foldedCoeff Θ u 0) v hsym hGauss]
  have htrace : (∑ i, (gi v i i - 1)) = (∑ i, gi v i i) - (n : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [htrace]
  ring

/-- **★ THE K₁ GAUSS REDUCTION** — the level-1 mirror:
        `K₁ = ¼·ρ·w₁ + w₁ + r∂_r w₁ − Δ_g w₀`. -/
theorem totalRadialO1_coeff_level1_gauss_reduction (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ)) :
    totalRadialO1_coeff_level1 g gi Θ u v
      = (1 / 4) * radialLogDetSym g gi v * foldedCoeff Θ u 1 v
        + foldedCoeff Θ u 1 v + radialDeriv (foldedCoeff Θ u 1) v
        - laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
  unfold totalRadialO1_coeff_level1
  rw [gamma_contraction_gauss g gi v hsym hGauss hdGauss htr,
      deviation_term_vanishes gi (foldedCoeff Θ u 1) v hsym hGauss]
  have htrace : (∑ i, (gi v i i - 1)) = (∑ i, gi v i i) - (n : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [htrace]
  ring

/-! ### §3. ★ THE MISMATCH PIN — the CURRENT fold direction fails h0 at curved data. -/

/-- **The current-direction value**: if the fold obeys the CURRENT chain rule
    `r∂_r w₀ = +¼ρ·w₀` (what `w₀ = Θ^{−1/2} = (det g̃)^{+1/4}` satisfies for `Θ = vanVleck`,
    by `radialDeriv_rpow` + Jacobi), then `K₀ = ½·ρ·w₀` — NOT zero unless `ρ·w₀ = 0`. -/
theorem totalRadialO1_coeff_current_direction (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
    (hchain : radialDeriv (foldedCoeff Θ u 0) v
        = (1 / 4) * radialLogDetSym g gi v * foldedCoeff Θ u 0 v) :
    totalRadialO1_coeff g gi Θ u v
      = (1 / 2) * radialLogDetSym g gi v * foldedCoeff Θ u 0 v := by
  rw [totalRadialO1_coeff_gauss_reduction g gi Θ u v hsym hGauss hdGauss htr, hchain]
  ring

/-- **★ THE h0 MISMATCH PIN.**  Under the Gauss set + the current-fold chain rule, wherever the
    radial log-det derivative and the amplitude are nonzero, h0 FAILS:
    `totalRadialO1_coeff ≠ 0`.  At a generic curved chart `ρ ≠ 0` off-centre, so the h0 binder
    of `white_K1BudgetW_of_transport` is NOT dischargeable at the current whitened witness —
    the fold direction must be corrected (§4). -/
theorem h0_fails_current_direction (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
    (hchain : radialDeriv (foldedCoeff Θ u 0) v
        = (1 / 4) * radialLogDetSym g gi v * foldedCoeff Θ u 0 v)
    (hρ : radialLogDetSym g gi v ≠ 0) (hw0 : foldedCoeff Θ u 0 v ≠ 0) :
    totalRadialO1_coeff g gi Θ u v ≠ 0 := by
  rw [totalRadialO1_coeff_current_direction g gi Θ u v hsym hGauss hdGauss htr hchain]
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · norm_num at h''
    · exact hρ h''
  · exact hw0 h'

/-! ### §4. ★ THE CORRECTED DIRECTION — h0 and h1 become theorems. -/

/-- **★ h0 AT THE CORRECTED FOLD.**  If the fold obeys the CORRECTED chain rule
    `r∂_r w₀ = −¼ρ·w₀` (what `w₀ = (det g̃)^{−1/4}` satisfies, i.e. the ansatz instantiated at
    `Θ := (vanVleck G)⁻¹`), the assembled `O(1/t)` coefficient VANISHES at the Gauss point:
    `totalRadialO1_coeff = 0` — the k = 0 off-diagonal DeWitt transport equation, PROVED modulo
    the labelled chain rule `hamp` (whose discharge is the radial Jacobi identity). -/
theorem totalRadialO1_coeff_corrected_vanishes (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
    (hamp : radialDeriv (foldedCoeff Θ u 0) v
        = -((1 / 4) * radialLogDetSym g gi v * foldedCoeff Θ u 0 v)) :
    totalRadialO1_coeff g gi Θ u v = 0 := by
  rw [totalRadialO1_coeff_gauss_reduction g gi Θ u v hsym hGauss hdGauss htr, hamp]
  ring

/-- The double-inverse bridge: `transportOp` at `(Θ⁻¹)⁻¹` IS the banked `transportOp Θ`
    (so the matched-conjugation ODE of the K₁ identification, stated at the ansatz weight
    `Θ_ansatz := Θ_w⁻¹`, is the banked ODE at `Θ_w` — the R/6 diagonal supplier is preserved). -/
theorem transportOp_inv_inv (Θ : Point n → ℝ) (g gi : Point n → Fin n → Fin n → ℝ) :
    transportOp (fun y => ((Θ y)⁻¹)⁻¹) g gi = transportOp Θ g gi := by
  funext u x
  simp only [transportOp, inv_inv]

/-- **★★ THE h1 CONJUGATION IDENTIFICATION (the Sol-flagged step, landed).**  At a Gauss point,
    with the fold obeying the CORRECTED chain rule (`hamp`), the level-1 coefficient vanishes
    GIVEN the banked radial ODE `(1 + r∂_r)u₁ = T̂u₀` for the MATCHED conjugation
    `T̂ = transportOp (Θ⁻¹)` — i.e. `T̂ = a⁻¹·Δ_g(a·)` with `a = Θ^{−1/2}` the fold itself:
        `K₁ = a·(1+r∂_r)u₁ − Δ_g(a·u₀) = a·a⁻¹·Δ_g(a·u₀) − Δ_g(a·u₀) = 0` .
    The `±¼ρ·a·u₁` terms cancel between the `A`-layer and the Leibniz split of `r∂_r(a·u₁)`.
    All hypotheses are genuine (positivity, coordinate differentiability, the chain rule, the
    ODE); none is the conclusion. -/
theorem totalRadialO1_coeff_level1_corrected_vanishes (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
    (hΘpos : ∀ y, 0 < Θ y)
    (haa : ∀ i, PdiffAt (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) i v)
    (hu1d : ∀ i, PdiffAt (u 1) i v)
    (hamp : radialDeriv (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) v
        = -((1 / 4) * radialLogDetSym g gi v * (Θ v) ^ (-(1 : ℝ) / 2)))
    (hODE : u 1 v + radialDeriv (u 1) v
        = transportOp (fun y => (Θ y)⁻¹) g gi (u 0) v) :
    totalRadialO1_coeff_level1 g gi Θ u v = 0 := by
  -- the matched transport source IS `Θ^{1/2}·Δ_g(w₀)`
  have hT : transportOp (fun y => (Θ y)⁻¹) g gi (u 0) v
      = (Θ v) ^ ((1 : ℝ) / 2) * laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
    unfold transportOp
    have h1 : ((Θ v)⁻¹) ^ (-(1 / 2) : ℝ) = (Θ v) ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow (hΘpos v).le, Real.rpow_neg (hΘpos v).le, inv_inv]
    have h2 : (fun y => ((Θ y)⁻¹) ^ ((1 / 2) : ℝ) * u 0 y) = foldedCoeff Θ u 0 := by
      funext y
      unfold foldedCoeff
      rw [Real.inv_rpow (hΘpos y).le, ← Real.rpow_neg (hΘpos y).le, neg_div]
    rw [h1, h2]
  -- the folded level-1 coefficient and its radial Leibniz split
  have hw1 : foldedCoeff Θ u 1 = fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y := rfl
  have hrad : radialDeriv (foldedCoeff Θ u 1) v
      = (Θ v) ^ (-(1 : ℝ) / 2) * radialDeriv (u 1) v
        + u 1 v * radialDeriv (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) v := by
    rw [hw1]
    exact radialDeriv_mul _ _ v haa hu1d
  -- the `a·a⁻¹ = 1` conjugation algebra
  have hcancel : (Θ v) ^ (-(1 : ℝ) / 2) * (Θ v) ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (hΘpos v),
        show (-(1 : ℝ) / 2 + (1 : ℝ) / 2) = 0 by norm_num, Real.rpow_zero]
  -- the reduced ODE: `a·(u₁ + r∂_r u₁) = Δ_g w₀`
  have hkey : (Θ v) ^ (-(1 : ℝ) / 2) * (u 1 v + radialDeriv (u 1) v)
      = laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
    rw [hODE, hT, ← mul_assoc, hcancel, one_mul]
  -- assemble through the K₁ Gauss reduction
  have hw1v : foldedCoeff Θ u 1 v = (Θ v) ^ (-(1 : ℝ) / 2) * u 1 v := rfl
  rw [totalRadialO1_coeff_level1_gauss_reduction g gi Θ u v hsym hGauss hdGauss htr,
      hrad, hamp, hw1v]
  linear_combination hkey

/-- **The h1 identification INSTANTIATED at the actual transported coefficients**: for the
    witness family `u = transportCoeff T̂` with the matched `T̂ = transportOp (Θ⁻¹) g gi`, the
    ODE hypothesis is DISCHARGED by the banked `transportCoeff_succ_transport_eq` (J3/J4), so
    `K₁ = 0` given only the Gauss set + fold regularity + the labelled chain rule + genuine
    smoothness of the transport source.  At the F1-corrected whitened witness
    (`Θ := (vanVleck Ĝ)⁻¹`) the matched `T̂` is the BANKED `transportOp (vanVleck Ĝ)` by
    `transportOp_inv_inv` — the same operator that supplies the diagonal `R/6`. -/
theorem totalRadialO1_coeff_level1_transportCoeff_vanishes
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
    (hΘpos : ∀ y, 0 < Θ y)
    (haa : ∀ i, PdiffAt (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) i v)
    (hu1d : ∀ i, PdiffAt (transportCoeff (transportOp (fun y => (Θ y)⁻¹) g gi) 1) i v)
    (hamp : radialDeriv (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) v
        = -((1 / 4) * radialLogDetSym g gi v * (Θ v) ^ (-(1 : ℝ) / 2)))
    (hsm : ContDiff ℝ ⊤ (transportOp (fun y => (Θ y)⁻¹) g gi
        (transportCoeff (transportOp (fun y => (Θ y)⁻¹) g gi) 0))) :
    totalRadialO1_coeff_level1 g gi Θ
        (transportCoeff (transportOp (fun y => (Θ y)⁻¹) g gi)) v = 0 := by
  refine totalRadialO1_coeff_level1_corrected_vanishes g gi Θ _ v
    hsym hGauss hdGauss htr hΘpos haa hu1d hamp ?_
  have h := transportCoeff_succ_transport_eq (transportOp (fun y => (Θ y)⁻¹) g gi) 0 hsm v
  simpa using h

/-! ### §5. The DISCRIMINATING gates (cp466 discipline).

Witness: the globally smooth, positive-definite exponential metric `g = diag(1, e^{2(y₀−1)})`
on `ℝ²` with its exact global inverse, at the Gauss point `v = (1,0)`.  All Gauss hypotheses
hold there and `ρ = 2 ≠ 0`:
  • CURRENT fold (`Θ = vanVleck g`, `w₀ = e^{(y₀−1)/2}`): `K₀ = 1 ≠ 0` — a concrete
    COUNTEREXAMPLE to the h0 binder shape at Gauss-lemma data with the actual
    `vanVleck`/`transportCoeff` suppliers;
  • CORRECTED fold (`Θ = (vanVleck g)⁻¹`, `w₀ = e^{−(y₀−1)/2}`): `K₀ = 0` at the SAME point —
    the direction is genuinely discriminated (a flat witness cannot do this). -/

/-- The gate metric `g = diag(1, e^{2(y₀−1)})` — globally smooth and positive definite. -/
noncomputable def gW : Point 2 → Fin 2 → Fin 2 → ℝ := fun y i j =>
  if i = 1 ∧ j = 1 then Real.exp (2 * (y 0 - 1)) else if i = j then 1 else 0

/-- Its exact global inverse `gi = diag(1, e^{−2(y₀−1)})`. -/
noncomputable def giW : Point 2 → Fin 2 → Fin 2 → ℝ := fun y i j =>
  if i = 1 ∧ j = 1 then Real.exp (-(2 * (y 0 - 1))) else if i = j then 1 else 0

/-- The gate point `v = (1, 0)`. -/
noncomputable def vW : Point 2 := ![1, 0]

lemma vW_zero : vW 0 = 1 := rfl
lemma vW_one : vW 1 = 0 := rfl

/-- Entry values of `gW` (general point). -/
lemma gW_00 (y : Point 2) : gW y 0 0 = 1 := by
  unfold gW
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1 ∧ (0 : Fin 2) = 1)), if_pos rfl]
lemma gW_01 (y : Point 2) : gW y 0 1 = 0 := by
  unfold gW
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1 ∧ (1 : Fin 2) = 1)),
      if_neg (by decide : ¬((0 : Fin 2) = (1 : Fin 2)))]
lemma gW_10 (y : Point 2) : gW y 1 0 = 0 := by
  unfold gW
  rw [if_neg (by decide : ¬((1 : Fin 2) = 1 ∧ (0 : Fin 2) = 1)),
      if_neg (by decide : ¬((1 : Fin 2) = (0 : Fin 2)))]
lemma gW_11 (y : Point 2) : gW y 1 1 = Real.exp (2 * (y 0 - 1)) := by
  unfold gW
  rw [if_pos ⟨rfl, rfl⟩]

/-- Entry values of `giW` (general point). -/
lemma giW_00 (y : Point 2) : giW y 0 0 = 1 := by
  unfold giW
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1 ∧ (0 : Fin 2) = 1)), if_pos rfl]
lemma giW_01 (y : Point 2) : giW y 0 1 = 0 := by
  unfold giW
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1 ∧ (1 : Fin 2) = 1)),
      if_neg (by decide : ¬((0 : Fin 2) = (1 : Fin 2)))]
lemma giW_10 (y : Point 2) : giW y 1 0 = 0 := by
  unfold giW
  rw [if_neg (by decide : ¬((1 : Fin 2) = 1 ∧ (0 : Fin 2) = 1)),
      if_neg (by decide : ¬((1 : Fin 2) = (0 : Fin 2)))]
lemma giW_11 (y : Point 2) : giW y 1 1 = Real.exp (-(2 * (y 0 - 1))) := by
  unfold giW
  rw [if_pos ⟨rfl, rfl⟩]

lemma gW_vW_11 : gW vW 1 1 = 1 := by
  rw [gW_11, vW_zero]
  norm_num
lemma giW_vW_11 : giW vW 1 1 = 1 := by
  rw [giW_11, vW_zero]
  norm_num

/-- `∂₀` of the `(1,1)` entry at the gate point: `∂₀ e^{2(y₀−1)}(v) = 2`. -/
lemma pd_gW11_at_vW : pd (fun y : Point 2 => gW y 1 1) 0 vW = 2 := by
  have hfun : (fun y : Point 2 => gW y 1 1) = fun y => Real.exp (2 * (y 0 - 1)) :=
    funext fun y => gW_11 y
  rw [hfun]
  have hupd : (fun t : ℝ => Real.exp (2 * ((Function.update vW 0 t) 0 - 1)))
      = fun t : ℝ => Real.exp (2 * (t - 1)) := by
    funext t
    simp [Function.update_apply]
  have hder : HasDerivAt (fun t : ℝ => Real.exp (2 * (t - 1)))
      (Real.exp (2 * ((1 : ℝ) - 1)) * 2) 1 := by
    have hin : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul 2
    exact hin.exp
  simp only [pd, vW_zero, hupd]
  rw [hder.deriv]
  norm_num

/-- `∂₁` of the `(1,1)` entry vanishes everywhere (the entry depends only on `y₀`). -/
lemma pd_gW11_dir1 (x : Point 2) : pd (fun y : Point 2 => gW y 1 1) 1 x = 0 := by
  have hfun : (fun y : Point 2 => gW y 1 1) = fun y => Real.exp (2 * (y 0 - 1)) :=
    funext fun y => gW_11 y
  rw [hfun]
  have hupd : (fun t : ℝ => Real.exp (2 * ((Function.update x 1 t) 0 - 1)))
      = fun _ : ℝ => Real.exp (2 * (x 0 - 1)) := by
    funext t
    simp [Function.update_apply]
  simp only [pd, hupd]
  exact deriv_const _ _

/-- `pd` of the three constant entries vanishes (any direction, any point). -/
lemma pd_gW_00 (a : Fin 2) (x : Point 2) : pd (fun y : Point 2 => gW y 0 0) a x = 0 := by
  have hfun : (fun y : Point 2 => gW y 0 0) = fun _ => (1 : ℝ) := funext fun y => gW_00 y
  rw [hfun]
  exact pd_const 1 a x
lemma pd_gW_01 (a : Fin 2) (x : Point 2) : pd (fun y : Point 2 => gW y 0 1) a x = 0 := by
  have hfun : (fun y : Point 2 => gW y 0 1) = fun _ => (0 : ℝ) := funext fun y => gW_01 y
  rw [hfun]
  exact pd_const 0 a x
lemma pd_gW_10 (a : Fin 2) (x : Point 2) : pd (fun y : Point 2 => gW y 1 0) a x = 0 := by
  have hfun : (fun y : Point 2 => gW y 1 0) = fun _ => (0 : ℝ) := funext fun y => gW_10 y
  rw [hfun]
  exact pd_const 0 a x

/-- `pd` of the whole first row vanishes for EVERY column `j` (the row is constant in `y`). -/
lemma pd_gW_0j (j : Fin 2) (a : Fin 2) (x : Point 2) :
    pd (fun y : Point 2 => gW y 0 j) a x = 0 := by
  have hfun : (fun y : Point 2 => gW y 0 j)
      = fun _ => if (0 : Fin 2) = j then (1 : ℝ) else 0 := by
    funext y
    show (if (0 : Fin 2) = 1 ∧ j = 1 then Real.exp (2 * (y 0 - 1))
        else if (0 : Fin 2) = j then (1 : ℝ) else 0)
      = if (0 : Fin 2) = j then (1 : ℝ) else 0
    rw [if_neg (fun h => (by decide : ¬((0 : Fin 2) = 1)) h.1)]
  rw [hfun]
  exact pd_const _ a x

/-- `gW`/`giW` at the gate point are the identity matrix. -/
lemma gW_at_vW (i j : Fin 2) : gW vW i j = if i = j then (1 : ℝ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [gW_00, gW_01, gW_10, gW_vW_11]
lemma giW_at_vW (i j : Fin 2) : giW vW i j = if i = j then (1 : ℝ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [giW_00, giW_01, giW_10, giW_vW_11]

/-- **The Gauss hypothesis set holds at the gate witness** (symmetry, radial compatibility,
    differentiated Gauss, trace normalization). -/
theorem gate_gauss_hyps :
    (∀ i j, giW vW i j = giW vW j i)
    ∧ (∀ i, (∑ j, (giW vW i j - (if i = j then (1 : ℝ) else 0)) * vW j) = 0)
    ∧ (∀ i j, (∑ a, vW a * pd (fun y => gW y a j) i vW)
        = (if i = j then (1 : ℝ) else 0) - gW vW i j)
    ∧ ((∑ i, ∑ j, giW vW i j * gW vW i j) = ((2 : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    rw [giW_at_vW i j, giW_at_vW j i]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  · intro i
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [giW_at_vW i j]
    ring
  · intro i j
    have hsum : (∑ a, vW a * pd (fun y => gW y a j) i vW)
        = pd (fun y => gW y 0 j) i vW := by
      simp only [Fin.sum_univ_two, vW_zero, vW_one, one_mul, zero_mul, add_zero]
    rw [hsum, pd_gW_0j j i vW, gW_at_vW i j]
    ring
  · simp only [Fin.sum_univ_two]
    rw [gW_00, gW_01, gW_10, gW_vW_11, giW_00, giW_01, giW_10, giW_vW_11]
    norm_num

/-- **`ρ = 2` at the gate witness** — the radial log-det derivative is genuinely NONZERO
    (the curved discriminator a flat witness cannot supply). -/
theorem gate_rho_eq_two : radialLogDetSym gW giW vW = 2 := by
  unfold radialLogDetSym
  have hinner0 : (∑ i, ∑ j, giW vW i j * pd (fun y => gW y i j) 0 vW) = 2 := by
    simp only [Fin.sum_univ_two]
    rw [pd_gW_00 0 vW, pd_gW_01 0 vW, pd_gW_10 0 vW, pd_gW11_at_vW,
        giW_00, giW_01, giW_10, giW_vW_11]
    norm_num
  have hinner1 : (∑ i, ∑ j, giW vW i j * pd (fun y => gW y i j) 1 vW) = 0 := by
    simp only [Fin.sum_univ_two]
    rw [pd_gW_00 1 vW, pd_gW_01 1 vW, pd_gW_10 1 vW, pd_gW11_dir1 vW,
        giW_00, giW_01, giW_10, giW_vW_11]
    norm_num
  rw [show (∑ a, vW a * (∑ i, ∑ j, giW vW i j * pd (fun y => gW y i j) a vW))
      = vW 0 * (∑ i, ∑ j, giW vW i j * pd (fun y => gW y i j) 0 vW)
        + vW 1 * (∑ i, ∑ j, giW vW i j * pd (fun y => gW y i j) 1 vW) from
    Fin.sum_univ_two _]
  rw [hinner0, hinner1, vW_zero, vW_one]
  ring

/-- The determinant of the gate metric: `det gW(y) = e^{2(y₀−1)}` (hence `> 0` everywhere). -/
lemma det_gW (y : Point 2) : Matrix.det (gW y) = Real.exp (2 * (y 0 - 1)) := by
  rw [Matrix.det_fin_two]
  show gW y 0 0 * gW y 1 1 - gW y 0 1 * gW y 1 0 = _
  rw [gW_00, gW_01, gW_10, gW_11]
  ring

/-- The current-fold amplitude at the gate: `w₀ = Θ^{−1/2}·u₀ = e^{(y₀−1)/2}`
    (`Θ = vanVleck gW`, `u = transportCoeff T` — any `T`; `u₀ ≡ 1` definitionally). -/
lemma foldedCoeff_current_at_gate (T : (Point 2 → ℝ) → (Point 2 → ℝ)) :
    foldedCoeff (vanVleck gW) (transportCoeff T) 0
      = fun y => Real.exp ((y 0 - 1) * (1 / 2)) := by
  funext y
  unfold foldedCoeff
  have hu0 : transportCoeff T 0 y = 1 := by rw [transportCoeff_zero]
  rw [hu0, mul_one]
  unfold vanVleck
  rw [det_gW]
  have hsqrt : Real.sqrt (Real.exp (2 * (y 0 - 1))) = Real.exp (y 0 - 1) := by
    rw [show (2 : ℝ) * (y 0 - 1) = (y 0 - 1) + (y 0 - 1) by ring, Real.exp_add]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  rw [hsqrt, ← Real.exp_neg, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- The corrected-fold amplitude at the gate: with `Θ := (vanVleck gW)⁻¹`,
    `w₀ = e^{(y₀−1)·(−1/2)}`. -/
lemma foldedCoeff_corrected_at_gate (T : (Point 2 → ℝ) → (Point 2 → ℝ)) :
    foldedCoeff (fun y => (vanVleck gW y)⁻¹) (transportCoeff T) 0
      = fun y => Real.exp ((y 0 - 1) * (-(1 / 2))) := by
  funext y
  show ((vanVleck gW y)⁻¹) ^ (-(1 : ℝ) / 2) * transportCoeff T 0 y = _
  have hu0 : transportCoeff T 0 y = 1 := by rw [transportCoeff_zero]
  rw [hu0, mul_one]
  unfold vanVleck
  rw [inv_inv, det_gW]
  have hsqrt : Real.sqrt (Real.exp (2 * (y 0 - 1))) = Real.exp (y 0 - 1) := by
    rw [show (2 : ℝ) * (y 0 - 1) = (y 0 - 1) + (y 0 - 1) by ring, Real.exp_add]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  rw [hsqrt, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- Radial derivative of `y ↦ e^{(y₀−1)·c}` at the gate point equals `c`. -/
lemma radialDeriv_exp_gate (c : ℝ) :
    radialDeriv (fun y : Point 2 => Real.exp ((y 0 - 1) * c)) vW = c := by
  unfold radialDeriv
  simp only [Fin.sum_univ_two, vW_zero, vW_one, one_mul, zero_mul, add_zero]
  have hupd : (fun t : ℝ => Real.exp (((Function.update vW 0 t) 0 - 1) * c))
      = fun t : ℝ => Real.exp ((t - 1) * c) := by
    funext t
    simp [Function.update_apply]
  have hder : HasDerivAt (fun t : ℝ => Real.exp ((t - 1) * c))
      (Real.exp (((1 : ℝ) - 1) * c) * c) 1 := by
    have hin : HasDerivAt (fun t : ℝ => (t - 1) * c) c 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 1).mul_const c
    exact hin.exp
  simp only [pd, vW_zero, hupd]
  rw [hder.deriv]
  norm_num

/-- **★ GATE A — THE h0 COUNTEREXAMPLE (current direction).**  At the globally
    positive-definite Gauss witness, with the ACTUAL suppliers (`Θ = vanVleck gW`,
    `u = transportCoeff` of the banked transport operator), the assembled `O(1/t)` coefficient
    is `1` — the h0 equation `K₀ = 0` is FALSE at curved Gauss-lemma data with the current
    fold direction.  cp466-style unsatisfiability, caught BEFORE consumption. -/
theorem gate_current_h0_value :
    totalRadialO1_coeff gW giW (vanVleck gW)
      (transportCoeff (transportOp (vanVleck gW) gW giW)) vW = 1 := by
  obtain ⟨hsym, hGauss, hdGauss, htr⟩ := gate_gauss_hyps
  rw [totalRadialO1_coeff_gauss_reduction gW giW _ _ vW hsym hGauss hdGauss htr,
      gate_rho_eq_two, foldedCoeff_current_at_gate, radialDeriv_exp_gate]
  norm_num [vW_zero, Real.exp_zero]

/-- **GATE A′ — the counterexample as a `≠ 0` pin.** -/
theorem gate_current_h0_fails :
    totalRadialO1_coeff gW giW (vanVleck gW)
      (transportCoeff (transportOp (vanVleck gW) gW giW)) vW ≠ 0 := by
  rw [gate_current_h0_value]
  norm_num

/-- **★ GATE B — THE CORRECTED DIRECTION VANISHES at the SAME witness.**  With the F1 fold
    (`Θ := (vanVleck gW)⁻¹`) and the same coefficients, `K₀ = 0` at the same curved Gauss
    point: the pair {Gate A, Gate B} genuinely DISCRIMINATES the conjugation direction
    (a flat witness cannot — both folds coincide at `Θ ≡ 1`). -/
theorem gate_corrected_h0_vanishes :
    totalRadialO1_coeff gW giW (fun y => (vanVleck gW y)⁻¹)
      (transportCoeff (transportOp (vanVleck gW) gW giW)) vW = 0 := by
  obtain ⟨hsym, hGauss, hdGauss, htr⟩ := gate_gauss_hyps
  refine totalRadialO1_coeff_corrected_vanishes gW giW _ _ vW hsym hGauss hdGauss htr ?_
  rw [gate_rho_eq_two, foldedCoeff_corrected_at_gate, radialDeriv_exp_gate]
  norm_num [vW_zero, Real.exp_zero]

/-! ### §6. Flat inhabitance of the K₁-identification antecedents (consistency gate). -/

/-- The flat metric symbols `δ`. -/
noncomputable def flatδ (n : ℕ) : Point n → Fin n → Fin n → ℝ :=
  fun _ => fun i j => if i = j then (1 : ℝ) else 0

/-- The flat matched transport operator (`Θ ≡ 1`, so `Θ⁻¹ ≡ 1` — the two conjugation
    directions coincide; this is why the flat gate is consistency-only). -/
noncomputable def flatT (n : ℕ) : (Point n → ℝ) → Point n → ℝ :=
  transportOp (fun _ : Point n => ((1 : ℝ))⁻¹) (flatδ n) (flatδ n)

lemma flat_sym (v : Point n) : ∀ i j, flatδ n v i j = flatδ n v j i := by
  intro i j
  show (if i = j then (1 : ℝ) else 0) = (if j = i then (1 : ℝ) else 0)
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

lemma flat_gauss (v : Point n) :
    ∀ i, (∑ j, (flatδ n v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0 := by
  intro i
  refine Finset.sum_eq_zero fun j _ => ?_
  show ((if i = j then (1 : ℝ) else 0) - (if i = j then (1 : ℝ) else 0)) * v j = 0
  ring

lemma flat_dGauss (v : Point n) (i j : Fin n) :
    (∑ a, v a * pd (fun y => flatδ n y a j) i v)
      = (if i = j then (1 : ℝ) else 0) - flatδ n v i j := by
  have hz : ∀ a : Fin n, pd (fun y => flatδ n y a j) i v = 0 := fun a =>
    pd_const (if a = j then (1 : ℝ) else 0) i v
  have h0 : (∑ a, v a * pd (fun y => flatδ n y a j) i v) = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hz a, mul_zero]
  rw [h0]
  show (0 : ℝ) = (if i = j then (1 : ℝ) else 0) - (if i = j then (1 : ℝ) else 0)
  ring

lemma flat_tr (v : Point n) : (∑ i, ∑ j, flatδ n v i j * flatδ n v i j) = (n : ℝ) := by
  have hrow : ∀ i : Fin n, (∑ j, flatδ n v i j * flatδ n v i j) = 1 := by
    intro i
    show (∑ j, (if i = j then (1 : ℝ) else 0) * (if i = j then (1 : ℝ) else 0)) = 1
    simp [ite_mul, mul_ite]
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  simp

lemma flat_aa_pdiff (v : Point n) (i : Fin n) :
    PdiffAt (fun _ : Point n => ((1 : ℝ)) ^ (-(1 : ℝ) / 2)) i v :=
  PdiffAt_of_contDiff _ contDiff_const i v

/-- The flat matched source is the zero field. -/
lemma flat_Tu0 : flatT n (transportCoeff (flatT n) 0) = fun _ : Point n => (0 : ℝ) := by
  funext x
  show transportOp (fun _ : Point n => ((1 : ℝ))⁻¹) (flatδ n) (flatδ n)
    (transportCoeff (flatT n) 0) x = 0
  simp only [transportOp]
  have hf : (fun y => ((1 : ℝ)⁻¹) ^ ((1 / 2) : ℝ) * transportCoeff (flatT n) 0 y)
      = fun _ : Point n => (1 : ℝ) := by
    funext y
    have h1 : transportCoeff (flatT n) 0 y = 1 := by rw [transportCoeff_zero]
    rw [h1, mul_one]
    norm_num
  rw [hf, laplaceBeltrami_const]
  ring

/-- The flat `u₁` is the zero field. -/
lemma flat_u1 : transportCoeff (flatT n) 1 = fun _ : Point n => (0 : ℝ) := by
  funext x
  show transportCoeff (flatT n) (0 + 1) x = 0
  rw [transportCoeff_succ, flat_Tu0]
  unfold radialTransportSolve
  simp

lemma flat_u1_pdiff (v : Point n) (i : Fin n) :
    PdiffAt (transportCoeff (flatT n) 1) i v := by
  rw [flat_u1]
  exact PdiffAt_of_contDiff _ contDiff_const i v

lemma flat_amp (v : Point n) :
    radialDeriv (fun _ : Point n => ((1 : ℝ)) ^ (-(1 : ℝ) / 2)) v
      = -((1 / 4) * radialLogDetSym (flatδ n) (flatδ n) v
          * ((1 : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hρ : radialLogDetSym (flatδ n) (flatδ n) v = 0 :=
    radialLogDetSym_of_const (fun i j => if i = j then (1 : ℝ) else 0) (flatδ n) v
  rw [hρ, radialDeriv_const]
  ring

lemma flat_ode (v : Point n) :
    transportCoeff (flatT n) 1 v + radialDeriv (transportCoeff (flatT n) 1) v
      = flatT n (transportCoeff (flatT n) 0) v := by
  rw [flat_u1, flat_Tu0, radialDeriv_const]
  simp

/-- The K₁ identification conclusion fires at the flat witness. -/
lemma flat_K1_conc (v : Point n) :
    totalRadialO1_coeff_level1 (flatδ n) (flatδ n) (fun _ => (1 : ℝ))
      (transportCoeff (flatT n)) v = 0 :=
  totalRadialO1_coeff_level1_corrected_vanishes (flatδ n) (flatδ n)
    (fun _ => (1 : ℝ)) (transportCoeff (flatT n)) v
    (flat_sym v) (flat_gauss v) (fun i j => flat_dGauss v i j) (flat_tr v)
    (fun _ => one_pos) (fun i => flat_aa_pdiff v i) (fun i => flat_u1_pdiff v i)
    (flat_amp v) (flat_ode v)

/-- **GATE C — joint satisfiability of the K₁-identification antecedent set** (cp466
    inhabitance): at the flat data ALL hypotheses of
    `totalRadialO1_coeff_level1_corrected_vanishes` hold simultaneously (over every point `v`
    — no `K = {0}` collapse) and the conclusion fires.  ⚠ HONEST: consistency only — at
    `Θ ≡ 1` the two conjugation directions coincide, so this gate does NOT discriminate the
    direction; Gates A/B (§5, curved) do. -/
theorem gate_K1_identification_inhabited_flat (v : Point n) :
    ∃ (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ),
      (∀ i j, gi v i j = gi v j i)
      ∧ (∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
      ∧ (∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
          = (if i = j then (1 : ℝ) else 0) - g v i j)
      ∧ ((∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
      ∧ (∀ y, 0 < Θ y)
      ∧ (∀ i, PdiffAt (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) i v)
      ∧ (∀ i, PdiffAt (u 1) i v)
      ∧ (radialDeriv (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) v
          = -((1 / 4) * radialLogDetSym g gi v * (Θ v) ^ (-(1 : ℝ) / 2)))
      ∧ (u 1 v + radialDeriv (u 1) v = transportOp (fun y => (Θ y)⁻¹) g gi (u 0) v)
      ∧ totalRadialO1_coeff_level1 g gi Θ u v = 0 :=
  ⟨flatδ n, flatδ n, fun _ => (1 : ℝ), transportCoeff (flatT n),
   flat_sym v, flat_gauss v, fun i j => flat_dGauss v i j, flat_tr v,
   fun _ => one_pos, fun i => flat_aa_pdiff v i, fun i => flat_u1_pdiff v i,
   flat_amp v, flat_ode v, flat_K1_conc v⟩

end QIQTH.WhiteTransport

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WhiteTransport.deviation_term_vanishes
#print axioms QIQTH.WhiteTransport.gamma_contraction_gauss
#print axioms QIQTH.WhiteTransport.totalRadialO1_coeff_gauss_reduction
#print axioms QIQTH.WhiteTransport.totalRadialO1_coeff_level1_gauss_reduction
#print axioms QIQTH.WhiteTransport.totalRadialO1_coeff_current_direction
#print axioms QIQTH.WhiteTransport.h0_fails_current_direction
#print axioms QIQTH.WhiteTransport.totalRadialO1_coeff_corrected_vanishes
#print axioms QIQTH.WhiteTransport.transportOp_inv_inv
#print axioms QIQTH.WhiteTransport.totalRadialO1_coeff_level1_corrected_vanishes
#print axioms QIQTH.WhiteTransport.totalRadialO1_coeff_level1_transportCoeff_vanishes
#print axioms QIQTH.WhiteTransport.gate_gauss_hyps
#print axioms QIQTH.WhiteTransport.gate_rho_eq_two
#print axioms QIQTH.WhiteTransport.gate_current_h0_value
#print axioms QIQTH.WhiteTransport.gate_current_h0_fails
#print axioms QIQTH.WhiteTransport.gate_corrected_h0_vanishes
#print axioms QIQTH.WhiteTransport.gate_K1_identification_inhabited_flat
