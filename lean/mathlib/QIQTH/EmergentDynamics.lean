/-
  Emergent (linearized) dynamics — the graviton-wall attack. A CONDITIONAL FINITE SKELETON, NOT solved QG.

  ★ SCOPE (read first; GPT-5.5-pro-verified plan `GRAVITON_WALL_PLAN.md`). This attacks the mechanism gap — the
    graviton/dynamics wall — via the FGHMVR "entanglement first law ⟹ linearized Einstein" logic and a QIQT-H-native
    finite null-focusing route. It does **NOT** solve quantum gravity. Every theorem here is a finite/algebraic
    **conditional skeleton**; the decisive continuum physics (continuum ball modular Hamiltonians, RT/extremal-area
    emergence, Iyer–Wald geometry, the actual nonlinear/quantized graviton) is cited research (plan G8–G12). ★

  ★ THE SINGLE MOST IMPORTANT GUARD. Never turn the area–stress link `δA = 8πG·K` into a *derived* theorem from
    packing / first law / min-cut — that hypothesis is exactly where the Einstein-equation content enters (inventory
    §2: "the `δA/4G=2π∫δT_kk` step uses the Einstein equations"). It is always a CARRIED explicit hypothesis.

  Honest rails: NO `sorry`; std-3; NEVER claim QG solved / a real (nonlinear/quantized) graviton / background
  independence / the value of `G`. Linearized ≠ full. Toy ≠ background-independent. `G` relation ≠ `G` value.

  ── G1 — the FGHMVR logical skeleton (all-probes first law ⟺ residual = 0) ──
  The exact formal core of "the entanglement first law at *every* probe ⟺ the linearized field equation." Pure
  linear algebra: given a **separating** family of probe functionals `P B : E →ₗ[ℝ] ℝ` (`E` = the linearized-residual
  space) and a carried Iyer–Wald-shaped identity `δK − δS = ⟨P, residual⟩`, the first law `∀ B, δS B = δK B` holds
  iff the residual vanishes. ⚠ The `∀ B` all-probe family and the `iw` identity are EXPLICIT CARRIED hypotheses —
  the continuum CFT balls (plan G8) and Iyer–Wald geometry (plan G10) are NOT supplied here.
-/
import Mathlib

namespace QIQTH.GravDyn

/-- A family of probe functionals `P B : E →ₗ[ℝ] ℝ` is **separating** if only the zero residual is annihilated by
    every probe. (In FGHMVR `E` is the space of linearized Einstein residuals and the `P B` are the ball/Iyer–Wald
    pairings; separation is the "all ball integrals vanish ⟹ the field vanishes" property — supplied finitely in G2.) -/
def Separating {Ball E : Type*} [AddCommGroup E] [Module ℝ E] (P : Ball → E →ₗ[ℝ] ℝ) : Prop :=
  ∀ e : E, (∀ B : Ball, P B e = 0) → e = 0

/-- **G1a — first law at every probe ⟹ residual = 0.** With the carried Iyer–Wald identity
    `iw : ∀ B, δK B − δS B = P B residual`, if the first law `δS = δK` holds at every probe and the probe family is
    separating, the linearized residual vanishes. -/
theorem residual_eq_zero_of_firstLaw {Ball E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Ball → E →ₗ[ℝ] ℝ) (sep : Separating P) (residual : E) (δS δK : Ball → ℝ)
    (iw : ∀ B, δK B - δS B = P B residual) (fl : ∀ B, δS B = δK B) :
    residual = 0 := by
  apply sep
  intro B
  calc P B residual = δK B - δS B := (iw B).symm
    _ = δK B - δK B := by rw [fl B]
    _ = 0 := sub_self _

/-- **G1 — the FGHMVR skeleton: `(∀ B, δS B = δK B) ↔ residual = 0`.** The entanglement first law at every probe is
    equivalent to the vanishing of the linearized field-equation residual — the exact formal core of FGHMVR, as a
    conditional theorem over the carried separating-probe family + Iyer–Wald identity. Pure linear algebra; NOT a
    physical derivation of Einstein (the continuum ball/Iyer–Wald content is the carried hypothesis, plan G8/G10). -/
theorem allBall_firstLaw_iff_residual_zero {Ball E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Ball → E →ₗ[ℝ] ℝ) (sep : Separating P) (residual : E) (δS δK : Ball → ℝ)
    (iw : ∀ B, δK B - δS B = P B residual) :
    (∀ B, δS B = δK B) ↔ residual = 0 := by
  constructor
  · exact residual_eq_zero_of_firstLaw P sep residual δS δK iw
  · intro h B
    have hzero : δK B - δS B = 0 := by rw [iw B, h, map_zero]
    exact (sub_eq_zero.mp hzero).symm

/-! ## G2 — the finite decoder / Radon inversion (supplies `Separating` for G1) -/

/-- **G2 — the finite decoder / Radon inversion.** If a finite field `f : Cell → ℝ` is *reconstructible* from its
    probe measurements via a decoder — `∀ i, f i = ∑ p, decode i p · measure p f` — and every probe measurement of
    `f` vanishes, then `f = 0`. This is the finite model of "all ball integrals of `f` vanish ⟹ `f = 0`" (the
    separating property, made concrete on a finite cell/probe grid). -/
theorem eq_zero_of_decoder {Cell Probe : Type*} [Fintype Cell] [Fintype Probe]
    (measure : Probe → (Cell → ℝ) → ℝ) (decode : Cell → Probe → ℝ) (f : Cell → ℝ)
    (hdecode : ∀ i, f i = ∑ p, decode i p * measure p f)
    (hzero : ∀ p, measure p f = 0) : f = 0 := by
  funext i
  rw [hdecode i]
  simp [hzero]

/-- **G2 → G1 — the `Separating` instance G1 needs.** If a *linear* probe family `P : Probe → (Cell → ℝ) →ₗ[ℝ] ℝ`
    admits a decoder (`∀ f i, f i = ∑ p, decode i p · P p f`), then it is `Separating`. This supplies the separating
    hypothesis of `allBall_firstLaw_iff_residual_zero` concretely — the residual space is `Cell → ℝ`, the probes are
    the ball/Iyer–Wald pairings, and finite reconstruction closes the "all probes vanish ⟹ residual vanishes" step. -/
theorem separating_of_decoder {Cell Probe : Type*} [Fintype Cell] [Fintype Probe]
    (P : Probe → (Cell → ℝ) →ₗ[ℝ] ℝ) (decode : Cell → Probe → ℝ)
    (hdecode : ∀ (f : Cell → ℝ) (i : Cell), f i = ∑ p, decode i p * P p f) :
    Separating P := by
  intro f hf
  funext i
  rw [hdecode f i]
  simp [hf]

/-! ## G3 — the discrete null modular kernel  `Δ²K = T` (anchors to the existing `T_kk`) -/

/-- The **discrete null modular tail kernel** `K_c = ∑_{i=c}^N (i−c)·T_i` — the finite/discrete analogue of the null
    modular Hamiltonian `K_V = 2π∫(u−V)·T_kk`. Indices over `ℤ` to keep the subtraction genuine (no `Nat` truncation). -/
noncomputable def tailK (N : ℤ) (T : ℤ → ℝ) (c : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc c N, ((i : ℝ) - (c : ℝ)) * T i

/-- The **discrete second difference** `Δ²A_c = A_{c−1} − 2A_c + A_{c+1}`. -/
noncomputable def secondDiff (A : ℤ → ℝ) (c : ℤ) : ℝ := A (c - 1) - 2 * A c + A (c + 1)

/-- **G3 — the discrete null modular shape derivative `Δ²K = T`.** The second difference of the tail kernel recovers
    the local stress: `Δ²(tailK)_c = T_c` for `c < N` — the finite analogue of `δ²K_V/δV² = 2π T_kk`, connecting to
    the *existing* `T_kk` / `wedge_boostCharge_eq_neg_stressFlux`. ⚠ Sign/orientation and the KG/free-field
    instantiation of `T` are carried; this is the discrete kernel identity only, NOT a physical derivation. -/
theorem secondDiff_tailK_eq (N : ℤ) (T : ℤ → ℝ) (c : ℤ) (hcN : c < N) :
    secondDiff (tailK N T) c = T c := by
  have hcle : c ≤ N := le_of_lt hcN
  have e2 : Finset.Icc c N = insert c (Finset.Icc (c + 1) N) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hc_notin : c ∉ Finset.Icc (c + 1) N := by simp only [Finset.mem_Icc]; omega
  -- backward difference: `K_{d-1} − K_d = ∑_{i=d}^N T_i`
  have A : ∀ d : ℤ, d ≤ N → tailK N T (d - 1) - tailK N T d = ∑ i ∈ Finset.Icc d N, T i := by
    intro d _
    have ed : Finset.Icc (d - 1) N = insert (d - 1) (Finset.Icc d N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hd_notin : (d - 1) ∉ Finset.Icc d N := by simp only [Finset.mem_Icc]; omega
    unfold tailK
    rw [ed, Finset.sum_insert hd_notin,
      show (((d - 1 : ℤ) : ℝ) - ((d - 1 : ℤ) : ℝ)) = 0 by ring, zero_mul, zero_add,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast; ring
  have hAc : tailK N T (c - 1) - tailK N T c = ∑ i ∈ Finset.Icc c N, T i := A c hcle
  have hAc1 : tailK N T c - tailK N T (c + 1) = ∑ i ∈ Finset.Icc (c + 1) N, T i := by
    simpa using A (c + 1) (by omega)
  have hsplit : (∑ i ∈ Finset.Icc c N, T i) - (∑ i ∈ Finset.Icc (c + 1) N, T i) = T c := by
    rw [e2, Finset.sum_insert hc_notin]; ring
  unfold secondDiff
  have hcomb : tailK N T (c - 1) - 2 * tailK N T c + tailK N T (c + 1)
      = (tailK N T (c - 1) - tailK N T c) - (tailK N T c - tailK N T (c + 1)) := by ring
  rw [hcomb, hAc, hAc1]
  exact hsplit

/-! ## G4 — dynamic-screen refinement invariance (toy background independence) -/

/-- A **screen** assigns each edge an (independent) log-dimension and area weight; a region's boundary is a cut
    `C : Finset E`. (The refinement-facing view; cf. `ScreenCode.ScreenCut`.) -/
structure Screen (E : Type*) where
  logDim : E → ℝ
  areaWt : E → ℝ

/-- Code capacity of a cut. -/
noncomputable def codeCap {E : Type*} (S : Screen E) (C : Finset E) : ℝ := ∑ e ∈ C, S.logDim e
/-- The (independent) area charge of a cut. -/
noncomputable def screenArea {E : Type*} (S : Screen E) (C : Finset E) : ℝ := ∑ e ∈ C, S.areaWt e

/-- An **edge refinement** `S' ↦ S`: a map `π` from refined edges to coarse edges under which the coarse weights are
    the **fiberwise sums** of the refined weights. ⚠ This is the explicit *weight-preserving correspondence*
    GPT-5.5-pro requires — a bare edge surjection is NOT enough; the weights must add up over fibers. -/
structure EdgeRefinement {E E' : Type*} [Fintype E'] [DecidableEq E] (S : Screen E) (S' : Screen E') where
  π : E' → E
  logDim_add : ∀ e, S.logDim e = ∑ e' : E', if π e' = e then S'.logDim e' else 0
  areaWt_add : ∀ e, S.areaWt e = ∑ e' : E', if π e' = e then S'.areaWt e' else 0

/-- The **pulled-back cut**: the refined edges lying over the coarse cut `C` (the explicit cut/region correspondence). -/
def pullCut {E E' : Type*} [Fintype E'] [DecidableEq E] (π : E' → E) (C : Finset E) : Finset E' :=
  Finset.univ.filter (fun e' => π e' ∈ C)

/-- A weight that is a fiberwise sum of a finer weight is preserved by the pulled-back cut. -/
lemma weightSum_refine {E E' : Type*} [Fintype E'] [DecidableEq E]
    (w : E → ℝ) (w' : E' → ℝ) (π : E' → E) (C : Finset E)
    (hadd : ∀ e, w e = ∑ e' : E', if π e' = e then w' e' else 0) :
    (∑ e ∈ C, w e) = ∑ e' ∈ pullCut π C, w' e' := by
  simp_rw [hadd]
  rw [Finset.sum_comm]
  unfold pullCut
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun e' _ => Finset.sum_ite_eq C (π e') (fun _ => w' e'))

/-- **G4a — refinement preserves capacity and area** (under the pulled-back cut correspondence). -/
theorem refinement_preserves_area_and_capacity {E E' : Type*} [Fintype E'] [DecidableEq E]
    {S : Screen E} {S' : Screen E'} (r : EdgeRefinement S S') (C : Finset E) :
    codeCap S C = codeCap S' (pullCut r.π C) ∧ screenArea S C = screenArea S' (pullCut r.π C) :=
  ⟨weightSum_refine S.logDim S'.logDim r.π C r.logDim_add,
   weightSum_refine S.areaWt S'.areaWt r.π C r.areaWt_add⟩

/-- The local holographic packing constraint on a screen. -/
def Packing {E : Type*} (G : ℝ) (S : Screen E) : Prop := ∀ e, S.logDim e ≤ S.areaWt e / (4 * G)

/-- Packing on a screen gives the regional area law on any cut. -/
lemma codeCap_le_of_packing {E : Type*} (G : ℝ) {S : Screen E} (h : Packing G S) (D : Finset E) :
    codeCap S D ≤ screenArea S D / (4 * G) := by
  unfold codeCap screenArea
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun e _ => h e)

/-- **G4b — the regional area-law bound is invariant under refinement.** If the *fine* screen satisfies packing,
    the *coarse* region's area law holds — via the pulled-back cut. So the capacity theorem lives on the refinement
    class, not a single fixed graph. ⚠ **Toy** background independence only (supplied finite graph/cut data; the
    pulled-back cut is the required correspondence) — NOT continuum background independence. -/
theorem regional_bound_invariant_under_refinement {E E' : Type*} [Fintype E'] [DecidableEq E]
    {S : Screen E} {S' : Screen E'} (r : EdgeRefinement S S') (G : ℝ)
    (hpack' : Packing G S') (C : Finset E) :
    codeCap S C ≤ screenArea S C / (4 * G) := by
  obtain ⟨hcap, harea⟩ := refinement_preserves_area_and_capacity r C
  rw [hcap, harea]
  exact codeCap_le_of_packing G hpack' (pullCut r.π C)

/-- **G4c — a property preserved by single moves is preserved along move-paths.** For a connectivity-move relation
    on graph configurations, invariance under one move lifts to invariance along any `ReflTransGen` path — the toy
    "observables live on the quotient of graph configurations" statement. -/
theorem property_preserved_along_moves {Config : Type*} {Move : Config → Config → Prop} {P : Config → Prop}
    (hmove : ∀ X Y, Move X Y → P X → P Y) {X Y : Config}
    (h : Relation.ReflTransGen Move X Y) : P X → P Y := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hP => hmove _ _ hbc (ih hP)

/-! ## G5 — discrete RG dimensional transmutation (`Λ_s` non-circular) -/

/-- One-loop inverse-coupling flow `u_n = u0 + 2bε·n` (`u = 1/g²`). -/
noncomputable def uFlow (b ε u0 : ℝ) (n : ℕ) : ℝ := u0 + (2 * b * ε) * n
/-- The sliding scale `μ_n = μ0·e^{εn}`. -/
noncomputable def muFlow (ε μ0 : ℝ) (n : ℕ) : ℝ := μ0 * Real.exp (ε * n)
/-- The RG-invariant scale `Λ_RG = μ·e^{−u/2b}`. -/
noncomputable def LambdaRG (b u μ : ℝ) : ℝ := μ * Real.exp (-u / (2 * b))

/-- **G5 — dimensional transmutation: `Λ_RG` is RG-invariant.** Along the one-loop flow `(u_n, μ_n)` the combination
    `Λ_RG` is **constant**: `Λ_RG(b, u_n, μ_n) = Λ_RG(b, u0, μ0)`. So a *scale* is generated from the *dimensionless*
    data `{b, g0}` (via `u0 = 1/g0²`), not from `G`. ⚠ It still needs a reference unit; it does NOT compute the
    numerical value of `G` — a RELATION, not a value. -/
theorem LambdaRG_invariant (b ε u0 μ0 : ℝ) (n : ℕ) (hb : b ≠ 0) :
    LambdaRG b (uFlow b ε u0 n) (muFlow ε μ0 n) = LambdaRG b u0 μ0 := by
  have key : ε * (n : ℝ) + -(u0 + 2 * b * ε * (n : ℝ)) / (2 * b) = -u0 / (2 * b) := by
    field_simp; ring
  unfold LambdaRG uFlow muFlow
  rw [mul_assoc, ← Real.exp_add, key]

/-- The transmuted granularity scale `Λ_s = μ0·e^{−1/(2b g0²)}` — generated from dimensionless `{b, g0}`. -/
noncomputable def LambdaS (b g0 μ0 : ℝ) : ℝ := μ0 * Real.exp (-(1 / (2 * b * g0 ^ 2)))
/-- The induced Newton constant `G = 1/(N Λ²)` (cf. `InducedNewtonConstant`). -/
noncomputable def InducedG (N Λ : ℝ) : ℝ := 1 / (N * Λ ^ 2)

/-- `Λ_s > 0` for `μ0 > 0` (an exponential is positive). -/
theorem LambdaS_pos (b g0 μ0 : ℝ) (hμ : 0 < μ0) : 0 < LambdaS b g0 μ0 := by
  unfold LambdaS; positivity

/-- **G5 — the induced `G` from the transmuted scale is positive** (`G = 1/(N Λ_s²) > 0`). A RELATION `G = 1/(N Λ²)`,
    NOT the numerical value of `G`. -/
theorem InducedG_pos (N Λ : ℝ) (hN : 0 < N) (hΛ : 0 < Λ) : 0 < InducedG N Λ := by
  unfold InducedG; positivity

/-! ## G6 — the QIQT-H-native finite null-focusing theorem (CONDITIONAL BOOKKEEPING, NOT a derivation) -/

/-- The **discrete curvature proxy** `R_kk := Δ²(δA)`. ⚠ A discrete proxy, **NOT** the geometric Ricci
    contraction — it becomes a curvature only with extra geometry/sign/normalization (a carried input). -/
noncomputable def RkkDisc (δA : ℤ → ℝ) (c : ℤ) : ℝ := secondDiff δA c

/-- **G6 — the second difference of a first-law-linked area variation.** ⚠⚠ **CONDITIONAL BOOKKEEPING, NOT a
    derivation of Einstein.** Given the **carried** area–modular/stress link `hAK : ∀ d, δA d = κ·K d` (with
    `κ = 8πG`, the `Kboost` convention; this hypothesis is **exactly where the Einstein-equation content enters** —
    inventory §2 — and is **NEVER derived from packing/first-law/min-cut**, the single most important guard) and a
    kernel whose second difference is the stress (`Δ²K = T` at `c`), the second area variation obeys
    `Δ²(δA)_c = κ·T_c`. Pure algebra over the carried hypotheses. -/
theorem secondDiff_of_area_firstLaw (κ : ℝ) (δA K T : ℤ → ℝ) (c : ℤ)
    (hAK : ∀ d, δA d = κ * K d) (hKT : secondDiff K c = T c) :
    secondDiff δA c = κ * T c := by
  have h : secondDiff δA c = κ * secondDiff K c := by
    unfold secondDiff; rw [hAK (c - 1), hAK c, hAK (c + 1)]; ring
  rw [h, hKT]

/-- **G6 — finite null focusing from the modular tail (CONDITIONAL).** Instantiating with the G3 discrete null
    modular tail (`Δ²(tailK) = T_kk`): **given the carried area–stress link** `δA = κ·tailK N T` (`κ = 8πG`), the
    discrete curvature proxy equals `κ` times the local stress: `R_kk_c = κ·T_c` for `c < N`. The finite analogue of
    the null Einstein equation `R_kk = 8πG T_kk`, using the load-bearing local packing constraint (via the area law)
    — but **it does NOT derive Einstein**: the `δA = κ·tailK` link is the carried physics input, and `R_kk := Δ²(δA)`
    is a discrete proxy, not geometric Ricci. -/
theorem nullFocusing_of_areaLink (κ : ℝ) (N : ℤ) (T δA : ℤ → ℝ) (c : ℤ) (hcN : c < N)
    (hAK : ∀ d, δA d = κ * tailK N T d) :
    RkkDisc δA c = κ * T c := by
  unfold RkkDisc
  exact secondDiff_of_area_firstLaw κ δA (tailK N T) T c hAK (secondDiff_tailK_eq N T c hcN)

end QIQTH.GravDyn
