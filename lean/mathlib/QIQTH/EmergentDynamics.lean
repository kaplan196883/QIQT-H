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

/-! ## G7a — null contractions ⟹ metric proportionality (the linearized Einstein residual, pointwise) -/

/-- The 4D **Minkowski metric** `η = diag(−1,1,1,1)`. -/
def minkMetric : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

/-- A vector is **null** iff `−k₀² + k₁² + k₂² + k₃² = 0`. -/
def minkQuad (k : Fin 4 → ℝ) : ℝ := -(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2

/-- The quadratic form of a matrix `S`: `S(k,k) = ∑_{ij} S_ij k_i k_j`. -/
def quadForm (S : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : ℝ := ∑ i, ∑ j, S i j * k i * k j

/-- **G7a — a symmetric form vanishing on the null cone is proportional to the metric.** If a symmetric `S`
    satisfies `S(k,k) = 0` for every null `k`, then `S = φ·η` for some `φ`. Pure finite 4D linear algebra (nine
    explicit rational null vectors extract the entry constraints). This is the *pointwise* content behind the
    linearized Einstein residual `E_{ab} = φ g_{ab}`; removing `φ` (via Bianchi/conservation + a boundary condition)
    is G7b, and it reaches at most the **linearized** equation — NEVER the propagating/quantized graviton (G11/G12). -/
theorem symForm_proportional_to_minkowski_of_null_quad_zero
    (S : Matrix (Fin 4) (Fin 4) ℝ) (hSym : S.IsSymm)
    (hNull : ∀ k : Fin 4 → ℝ, minkQuad k = 0 → quadForm S k = 0) :
    ∃ φ : ℝ, S = φ • minkMetric := by
  have hs10 : S 1 0 = S 0 1 := by simpa [eq_comm] using hSym.apply 0 1
  have hs20 : S 2 0 = S 0 2 := by simpa [eq_comm] using hSym.apply 0 2
  have hs30 : S 3 0 = S 0 3 := by simpa [eq_comm] using hSym.apply 0 3
  have hs21 : S 2 1 = S 1 2 := by simpa [eq_comm] using hSym.apply 1 2
  have hs31 : S 3 1 = S 1 3 := by simpa [eq_comm] using hSym.apply 1 3
  have hs32 : S 3 2 = S 2 3 := by simpa [eq_comm] using hSym.apply 2 3
  have e01p_raw : S 0 0 + S 0 1 + S 1 0 + S 1 1 = 0 := by
    have h := hNull (![1, 1, 0, 0] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have e01m_raw : S 0 0 - S 0 1 - S 1 0 + S 1 1 = 0 := by
    have h := hNull (![1, -1, 0, 0] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have h01 : S 0 1 = 0 := by linarith [e01p_raw, e01m_raw, hs10]
  have hdiag1 : S 0 0 + S 1 1 = 0 := by linarith [e01p_raw, e01m_raw, hs10]
  have e02p_raw : S 0 0 + S 0 2 + S 2 0 + S 2 2 = 0 := by
    have h := hNull (![1, 0, 1, 0] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have e02m_raw : S 0 0 - S 0 2 - S 2 0 + S 2 2 = 0 := by
    have h := hNull (![1, 0, -1, 0] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have h02 : S 0 2 = 0 := by linarith [e02p_raw, e02m_raw, hs20]
  have hdiag2 : S 0 0 + S 2 2 = 0 := by linarith [e02p_raw, e02m_raw, hs20]
  have e03p_raw : S 0 0 + S 0 3 + S 3 0 + S 3 3 = 0 := by
    have h := hNull (![1, 0, 0, 1] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have e03m_raw : S 0 0 - S 0 3 - S 3 0 + S 3 3 = 0 := by
    have h := hNull (![1, 0, 0, -1] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have h03 : S 0 3 = 0 := by linarith [e03p_raw, e03m_raw, hs30]
  have hdiag3 : S 0 0 + S 3 3 = 0 := by linarith [e03p_raw, e03m_raw, hs30]
  have e12raw : 25 * S 0 0 + 15 * S 0 1 + 20 * S 0 2 + 15 * S 1 0 + 9 * S 1 1 + 12 * S 1 2 +
      20 * S 2 0 + 12 * S 2 1 + 16 * S 2 2 = 0 := by
    have h := hNull (![5, 3, 4, 0] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have h12 : S 1 2 = 0 := by linarith [e12raw, h01, h02, hs10, hs20, hs21, hdiag1, hdiag2]
  have e13raw : 25 * S 0 0 + 15 * S 0 1 + 20 * S 0 3 + 15 * S 1 0 + 9 * S 1 1 + 12 * S 1 3 +
      20 * S 3 0 + 12 * S 3 1 + 16 * S 3 3 = 0 := by
    have h := hNull (![5, 3, 0, 4] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have h13 : S 1 3 = 0 := by linarith [e13raw, h01, h03, hs10, hs30, hs31, hdiag1, hdiag3]
  have e23raw : 25 * S 0 0 + 15 * S 0 2 + 20 * S 0 3 + 15 * S 2 0 + 9 * S 2 2 + 12 * S 2 3 +
      20 * S 3 0 + 12 * S 3 2 + 16 * S 3 3 = 0 := by
    have h := hNull (![5, 0, 3, 4] : Fin 4 → ℝ) (by simp only [minkQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]; norm_num)
    simp [quadForm, Fin.sum_univ_four] at h; ring_nf at h ⊢; exact h
  have h23 : S 2 3 = 0 := by linarith [e23raw, h02, h03, hs20, hs30, hs32, hdiag2, hdiag3]
  refine ⟨S 1 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkMetric, Matrix.diagonal, Matrix.smul_apply] <;>
    linarith [h01, h02, h03, h12, h13, h23, hdiag1, hdiag2, hdiag3,
      hs10, hs20, hs30, hs21, hs31, hs32]

/-- **G7b (conditional) — with a boundary condition the linearized residual vanishes.** Given the metric form
    `S = φ•η` (from G7a) and the carried scalar condition `φ = 0`, the residual vanishes: `S = 0`. ⚠ Physically the
    `φ`-removal is: the linearized Bianchi identity `∇^a E_{ab}=0` forces `φ` **constant** (a cosmological-constant
    mode), then a boundary/trace condition sets it to zero. That Bianchi step is the **Iyer–Wald frontier (G10)** —
    carried here as the hypothesis `hφ0`; this theorem is only the trivial finite plug. **Linearized only, NOT a
    graviton** (G11/G12). -/
theorem residual_vanishes_of_metric_form (S : Matrix (Fin 4) (Fin 4) ℝ) (φ : ℝ)
    (hφS : S = φ • minkMetric) (hφ0 : φ = 0) : S = 0 := by
  rw [hφS, hφ0, zero_smul]

/-! ## G11a (partial) — the linearized graviton's two transverse-traceless polarizations (KINEMATIC only) -/

/-- The raised null wavevector `k^μ = (−1,0,0,1)` (for `k` along `z`, `η = diag(−1,1,1,1)`). -/
def kUp : Fin 4 → ℝ := ![-1, 0, 0, 1]

/-- `h` is **transverse** to the null `k` iff `∑_μ k^μ h_{μν} = 0` for all `ν`. -/
def Transverse (h : Matrix (Fin 4) (Fin 4) ℝ) : Prop := ∀ ν, ∑ μ, kUp μ * h μ ν = 0

/-- `h` is **traceless** iff `η^{μν} h_{μν} = −h₀₀ + h₁₁ + h₂₂ + h₃₃ = 0`. -/
def Traceless (h : Matrix (Fin 4) (Fin 4) ℝ) : Prop := -h 0 0 + h 1 1 + h 2 2 + h 3 3 = 0

/-- The `+` polarization tensor `e_x⊗e_x − e_y⊗e_y`. -/
def polPlus : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
/-- The `×` polarization tensor `e_x⊗e_y + e_y⊗e_x`. -/
def polCross : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 0]

theorem polPlus_isSymm : polPlus.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem polCross_isSymm : polCross.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem polPlus_transverse : Transverse polPlus := by
  intro ν; fin_cases ν <;> simp [kUp, polPlus, Fin.sum_univ_four]
theorem polCross_transverse : Transverse polCross := by
  intro ν; fin_cases ν <;> simp [kUp, polCross, Fin.sum_univ_four]
theorem polPlus_traceless : Traceless polPlus := by simp [Traceless, polPlus]
theorem polCross_traceless : Traceless polCross := by simp [Traceless, polCross]

/-- **G11a — the two graviton polarizations are linearly independent.** Together with symmetry/transverse/traceless
    above, this exhibits **two independent physical (transverse-traceless) polarizations** of the linearized
    metric perturbation for a null wavevector — the graviton's spin-2 polarization content in 4D. ⚠ This is the
    **kinematic** polarization count; that the TT space is *exactly* 2-dimensional is the standard massless-spin-2
    little-group result. It is **NOT** the quantized graviton / propagator / dynamics (G11/G12 remain frontier). -/
theorem graviton_polarizations_indep (a b : ℝ)
    (h : a • polPlus + b • polCross = 0) : a = 0 ∧ b = 0 := by
  constructor
  · have := congrFun (congrFun h 1) 1
    simpa [polPlus, polCross] using this
  · have := congrFun (congrFun h 1) 2
    simpa [polPlus, polCross] using this

/-- Spatial **rotation by `θ` about the propagation (`z`) axis** — acts in the `x,y` plane, identity on `t,z`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, Real.cos θ, -Real.sin θ, 0; 0, Real.sin θ, Real.cos θ, 0; 0, 0, 0, 1]

/-- **G11a — the graviton polarizations carry helicity ±2 (spin 2), part 1.** Under a rotation by `θ` about the
    propagation axis, `e₊` maps to `cos2θ·e₊ + sin2θ·e×` (the coefficients `cos²θ−sin²θ = cos2θ`,
    `2 sinθ cosθ = sin2θ`). The **double angle** `2θ` is the spin-2 / helicity-±2 signature — a photon (spin 1) would
    rotate by `θ`, a scalar by `0`. ⚠ KINEMATIC; not the quantized graviton. -/
theorem polPlus_helicity (θ : ℝ) :
    rot θ * polPlus * (rot θ).transpose
      = (Real.cos θ ^ 2 - Real.sin θ ^ 2) • polPlus + (2 * Real.sin θ * Real.cos θ) • polCross := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, polPlus, polCross, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

/-- **G11a — helicity ±2, part 2.** `e×` maps to `−sin2θ·e₊ + cos2θ·e×`. Together with `polPlus_helicity`, the
    polarization doublet `(e₊, e×)` transforms by the rotation `R(2θ)` — the spin-2 signature. -/
theorem polCross_helicity (θ : ℝ) :
    rot θ * polCross * (rot θ).transpose
      = (-(2 * Real.sin θ * Real.cos θ)) • polPlus + (Real.cos θ ^ 2 - Real.sin θ ^ 2) • polCross := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, polPlus, polCross, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

/-! ## G11a — helicity eigenstates: the circular polarizations `e_± = e₊ ± i·e×` (helicity ±2 as EXPLICIT eigenvalues)

  The real doublet `(e₊, e×)` mixes by `R(2θ)` under a rotation (`polPlus_helicity`/`polCross_helicity`). Diagonalizing
  that action gives the **circular-polarization basis** `e_± = e₊ ± i·e×`, the honest-to-goodness helicity eigenstates:
  each is an *eigenvector* of the rotation conjugation with eigenvalue `e^{∓2iθ}`. The `±2` in the exponent **is** the
  graviton's helicity ±2 — spin-2 stated as literal eigenvalues, not just a mixing angle. (`e_R` restricted to the `x,y`
  block is `[[1,i],[i,−1]] = v vᵀ` with `v = (1,i)`; the rotation sends `v ↦ e^{−iθ}v`, so `e_R ↦ e^{−2iθ}e_R`.)
  ⚠ KINEMATIC; not the quantized graviton. -/

/-- Complex `+` polarization (the ℂ-copy of `e₊`). -/
noncomputable def polPlusC : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
/-- Complex `×` polarization (the ℂ-copy of `e×`). -/
noncomputable def polCrossC : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 0]
/-- The **complexified rotation** by `θ` about the propagation axis. -/
noncomputable def rotC (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, Complex.cos (θ:ℂ), -Complex.sin (θ:ℂ), 0;
     0, Complex.sin (θ:ℂ), Complex.cos (θ:ℂ), 0; 0, 0, 0, 1]
/-- **Right-circular (helicity −2) polarization** `e_R = e₊ + i·e×`. -/
noncomputable def eR : Matrix (Fin 4) (Fin 4) ℂ := polPlusC + Complex.I • polCrossC
/-- **Left-circular (helicity +2) polarization** `e_L = e₊ − i·e×`. -/
noncomputable def eL : Matrix (Fin 4) (Fin 4) ℂ := polPlusC - Complex.I • polCrossC

/-- The complexified `+` polarization mixes like its real counterpart (I-free helicity lemma). -/
private theorem rotC_polPlusC (θ : ℝ) :
    rotC θ * polPlusC * (rotC θ).transpose
      = (Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2) • polPlusC
        + (2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ)) • polCrossC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, polPlusC, polCrossC, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

/-- The complexified `×` polarization mixes like its real counterpart (I-free helicity lemma). -/
private theorem rotC_polCrossC (θ : ℝ) :
    rotC θ * polCrossC * (rotC θ).transpose
      = (-(2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ))) • polPlusC
        + (Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2) • polCrossC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, polPlusC, polCrossC, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

/-- The eigenvalue bridge `e^{−2iθ} = (cos²θ − sin²θ) − (2 sinθ cosθ)i`. -/
private theorem exp_neg_two_mul_I (θ : ℝ) :
    Complex.exp (-(2 * (θ:ℂ)) * Complex.I)
      = (Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2)
        - (2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ)) * Complex.I := by
  have htwo : 2 * (θ : ℂ) = (θ : ℂ) + (θ : ℂ) := by ring
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, htwo, Complex.cos_add, Complex.sin_add]
  ring

/-- The eigenvalue bridge `e^{+2iθ} = (cos²θ − sin²θ) + (2 sinθ cosθ)i`. -/
private theorem exp_pos_two_mul_I (θ : ℝ) :
    Complex.exp ((2 * (θ:ℂ)) * Complex.I)
      = (Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2)
        + (2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ)) * Complex.I := by
  have htwo : 2 * (θ : ℂ) = (θ : ℂ) + (θ : ℂ) := by ring
  rw [Complex.exp_mul_I, htwo, Complex.cos_add, Complex.sin_add]
  ring

/-- **G11a — the right-circular polarization has helicity −2.** `e_R = e₊ + i·e×` is an eigenvector of the rotation
    conjugation with eigenvalue `e^{−2iθ}`: `R(θ) e_R R(θ)ᵀ = e^{−2iθ} e_R`. The `−2` is the helicity — the graviton's
    spin-2, stated as an explicit eigenvalue. ⚠ KINEMATIC; not the quantized graviton. -/
theorem eR_helicity (θ : ℝ) :
    rotC θ * eR * (rotC θ).transpose = Complex.exp (-(2 * (θ:ℂ)) * Complex.I) • eR := by
  calc
    rotC θ * eR * (rotC θ).transpose
        = rotC θ * (polPlusC + Complex.I • polCrossC) * (rotC θ).transpose := by rw [eR]
    _ = rotC θ * polPlusC * (rotC θ).transpose
          + Complex.I • (rotC θ * polCrossC * (rotC θ).transpose) := by
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = ((Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2) • polPlusC
          + (2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ)) • polCrossC)
          + Complex.I • (((-(2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ))) • polPlusC)
            + (Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2) • polCrossC) := by
            rw [rotC_polPlusC, rotC_polCrossC]
    _ = Complex.exp (-(2 * (θ:ℂ)) * Complex.I) • eR := by
            rw [exp_neg_two_mul_I, eR]
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [polPlusC, polCrossC, smul_add, smul_smul] <;>
              ring_nf <;> simp [pow_two, Complex.I_mul_I] <;> ring_nf

/-- **G11a — the left-circular polarization has helicity +2.** `e_L = e₊ − i·e×` is an eigenvector of the rotation
    conjugation with eigenvalue `e^{+2iθ}`: `R(θ) e_L R(θ)ᵀ = e^{+2iθ} e_L`. Together with `eR_helicity`, the two
    circular polarizations are the **helicity ±2 eigenstates** of the graviton — spin-2 in explicit eigenvalue form.
    ⚠ KINEMATIC; not the quantized graviton. -/
theorem eL_helicity (θ : ℝ) :
    rotC θ * eL * (rotC θ).transpose = Complex.exp ((2 * (θ:ℂ)) * Complex.I) • eL := by
  have heL' : eL = polPlusC + (-Complex.I) • polCrossC := by rw [eL]; simp [sub_eq_add_neg]
  calc
    rotC θ * eL * (rotC θ).transpose
        = rotC θ * (polPlusC + (-Complex.I) • polCrossC) * (rotC θ).transpose := by rw [heL']
    _ = rotC θ * polPlusC * (rotC θ).transpose
          + (-Complex.I) • (rotC θ * polCrossC * (rotC θ).transpose) := by
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = ((Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2) • polPlusC
          + (2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ)) • polCrossC)
          + (-Complex.I) • (((-(2 * Complex.sin (θ:ℂ) * Complex.cos (θ:ℂ))) • polPlusC)
            + (Complex.cos (θ:ℂ) ^ 2 - Complex.sin (θ:ℂ) ^ 2) • polCrossC) := by
            rw [rotC_polPlusC, rotC_polCrossC]
    _ = Complex.exp ((2 * (θ:ℂ)) * Complex.I) • eL := by
            rw [exp_pos_two_mul_I, heL']
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [polPlusC, polCrossC, smul_add, smul_smul] <;>
              ring_nf <;> simp [pow_two, Complex.I_mul_I] <;> ring_nf

/-! ## G11a — the gauge quotient: the physical graviton polarization space is EXACTLY 2-dimensional -/

/-- The down-index null wavevector `k_μ = (1,0,0,1)`. -/
def kDown : Fin 4 → ℝ := ![1, 0, 0, 1]

/-- A **pure-gauge shift** `δh_{μν} = k_μ ξ_ν + k_ν ξ_μ` (a linearized diffeomorphism, on-shell for null `k`). -/
noncomputable def gaugeShift (ξ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun μ ν => kDown μ * ξ ν + kDown ν * ξ μ)

/-- The gauge parameter that removes the unphysical part of a TT tensor: `ξ = (h₀₀/2, h₀₁, h₀₂, h₀₀/2)`. -/
noncomputable def gaugeXi (h : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ := ![h 0 0 / 2, h 0 1, h 0 2, h 0 0 / 2]

/-- **G11a — the TT decomposition (upper bound: physical space is spanned by the 2 polarizations).** Every symmetric
    transverse-traceless tensor decomposes as `h = h₁₁·e₊ + h₁₂·e× + (pure gauge)`. So modulo gauge, every physical
    polarization is a combination of `e₊` and `e×` — the graviton has **at most 2** physical degrees of freedom. -/
theorem tt_decomposition (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm)
    (hTrans : Transverse h) (hTrace : Traceless h) :
    h = h 1 1 • polPlus + h 1 2 • polCross + gaugeShift (gaugeXi h) := by
  have ht0 : h 3 0 = h 0 0 := by
    have t := hTrans (0 : Fin 4)
    simp [kUp, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at t
    linarith [t]
  have ht1 : h 3 1 = h 0 1 := by
    have t := hTrans (1 : Fin 4)
    simp [kUp, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at t
    linarith [t]
  have ht2 : h 3 2 = h 0 2 := by
    have t := hTrans (2 : Fin 4)
    simp [kUp, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at t
    linarith [t]
  have ht3 : h 3 3 = h 0 3 := by
    have t := hTrans (3 : Fin 4)
    simp [kUp, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at t
    linarith [t]
  have hs01 : h 1 0 = h 0 1 := by have s := hSym.apply (0 : Fin 4) (1 : Fin 4); linarith [s]
  have hs02 : h 2 0 = h 0 2 := by have s := hSym.apply (0 : Fin 4) (2 : Fin 4); linarith [s]
  have hs03 : h 3 0 = h 0 3 := by have s := hSym.apply (0 : Fin 4) (3 : Fin 4); linarith [s]
  have hs12 : h 2 1 = h 1 2 := by have s := hSym.apply (1 : Fin 4) (2 : Fin 4); linarith [s]
  have hs13 : h 3 1 = h 1 3 := by have s := hSym.apply (1 : Fin 4) (3 : Fin 4); linarith [s]
  have hs23 : h 3 2 = h 2 3 := by have s := hSym.apply (2 : Fin 4) (3 : Fin 4); linarith [s]
  have hTr : -h 0 0 + h 1 1 + h 2 2 + h 3 3 = 0 := by simpa [Traceless] using hTrace
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      polPlus, polCross, gaugeShift, gaugeXi, kDown,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, smul_eq_mul] <;>
    linarith [ht0, ht1, ht2, ht3, hs01, hs02, hs03, hs12, hs13, hs23, hTr]

/-- **G11a — independence mod gauge (lower bound: at least 2).** No nonzero combination of the polarizations is pure
    gauge. With `tt_decomposition`, this makes `{e₊, e×}` a **basis** of the physical polarization space (TT modulo
    gauge) — so the graviton has **exactly 2** physical polarizations. -/
theorem polarizations_not_gauge (a b : ℝ) (ξ : Fin 4 → ℝ)
    (h : a • polPlus + b • polCross = gaugeShift ξ) : a = 0 ∧ b = 0 := by
  have h11 := congrFun (congrFun h (1 : Fin 4)) (1 : Fin 4)
  have h12 := congrFun (congrFun h (1 : Fin 4)) (2 : Fin 4)
  constructor
  · simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      polPlus, polCross, gaugeShift, kDown, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_eq_mul] using h11
  · simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      polPlus, polCross, gaugeShift, kDown, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_eq_mul] using h12

end QIQTH.GravDyn
