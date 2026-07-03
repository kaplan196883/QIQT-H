/-
  THE JOIN INSTANCE (JOIN_INSTANCE_PLAN.md, JI1–JI7 COMPLETE) — delete `hJoin` by construction:
  the bridge at the finite level.

  The code tower (keystone THE COUNT) and the graviton tower (Q1–Q5) merged into ONE object: the
  dictionary instance links ↔ screen elements, with the code weights defined FROM the geometry, so
  the Q5 carried hypothesis `hJoin` becomes a THEOREM for the constructed instance.

  JI7 CHECKPOINT — the two honest sentences (verbatim from the plan):

  HAVE: "after JI1–JI6, `hJoin` is no longer a hypothesis for the constructed τ join or for
  nat-realizable finite-code joins, and the count normalization rewrites to `(A_J/4)·N·Λs²` with
  local capacity corollaries."

  HAVE NOT: "no theorem says arbitrary external real geometry has exact natural link dimensions,
  no asymptotic approximation is included, and no canonical `A0` split is asserted beyond the
  named apportionment data/policy."

  ⚠ NOT quantum gravity solved; no wall crossed. The join is deleted for the CONSTRUCTED instance
  (generic-exact at the τ level; realizable at the ℕ level under the named datum); the CCR-isometry
  obstruction is permanent (expectation-level forever); the continuum walls stay named.

  JI1 — the local area decomposition:
  • `localAreaVar` — the per-element linearized area share `δA_a = ½ w_a (h(e₁ᵃ,e₁ᵃ)+h(e₂ᵃ,e₂ᵃ))`,
    with `sum_localAreaVar` (the shares sum to the held `areaVar`);
  • `A0Split` — the NAMED apportionment of the global background area across the elements (honest
    DATA, per the binding verdict: there is no canonical per-link split of a global constant);
    `A0Split.uniform` as an optional constructor, never pretended-derived;
  • CAPSTONE `sum_localArea` — the algebraic core `∑_a (β_a + δA_a) = A₀ + areaVar S h`.
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.OperatorEmergence
import QIQTH.CalibratedAreaLaw
import QIQTH.InducedNewtonConstant
import QIQTH.Keystone

namespace QIQTH.JoinInstance

open QIQTH.AreaMap QIQTH.GravDyn

variable {ι : Type*}

/-- **The per-element linearized area share** `δA_a := ½ w_a (h(e₁ᵃ,e₁ᵃ) + h(e₂ᵃ,e₂ᵃ))` — the
    single element's contribution to the held discretized area response. -/
noncomputable def localAreaVar (S : ScreenSurface ι) (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  (1 / 2) * (S.w a * (quadForm h (S.e1 a) + quadForm h (S.e2 a)))

/-- The per-element shares sum to the held total area response. -/
theorem sum_localAreaVar (S : ScreenSurface ι) (h : Matrix (Fin 4) (Fin 4) ℝ) :
    ∑ a ∈ S.elems, localAreaVar S h a = areaVar S h := by
  rw [areaVar, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- **The named apportionment of the background area** across the screen elements — honest DATA
    (per the binding verdict: a global constant has no canonical per-link decomposition; any split
    is a CHOICE, carried as a structure field, never pretended-derived). -/
structure A0Split (S : ScreenSurface ι) (A0 : ℝ) where
  /-- the per-element background share -/
  share : ι → ℝ
  /-- the shares reassemble the background -/
  sum_share : ∑ a ∈ S.elems, share a = A0

/-- The uniform split — an optional CONSTRUCTOR (a policy, not a derivation). -/
noncomputable def A0Split.uniform (S : ScreenSurface ι) (A0 : ℝ) (hne : S.elems.Nonempty) :
    A0Split S A0 where
  share := fun _ => A0 / S.elems.card
  sum_share := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [Finset.card_ne_zero_of_mem hne.choose_spec]

/-- **The local area of an element**: background share plus linearized response. -/
noncomputable def localArea (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  β.share a + localAreaVar S h a

/-- **JI1 CAPSTONE — the algebraic core of the join:** the local areas reassemble the total,
    `∑_a (β_a + δA_a) = A₀ + areaVar S h` — exactly the right-hand side of the carried `hJoin`,
    now decomposed per link. -/
theorem sum_localArea (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    (h : Matrix (Fin 4) (Fin 4) ℝ) :
    ∑ a ∈ S.elems, localArea S β h a = A0 + areaVar S h := by
  simp only [localArea, Finset.sum_add_distrib, β.sum_share, sum_localAreaVar]

/-! ## JI2 — the generic τ join dictionary

The geometry-defined code: weights `wEnt a := A^loc_a/(4G)` and REAL trace-dimensions
`Dτ_a := exp(wEnt a)` (per the binding verdict: generic-exact at the τ level, NO integrality — the
calibration is `Real.log_exp`). CAPSTONE `hJoin_tau`: the Q5 carried `hJoin` equality is a THEOREM
for the constructed dictionary (direction geometry → code; links = the screen elements). -/

section TauDictionary

open QIQTH.EarnGravity QIQTH.OperatorEmergence

variable [Fintype ι] [DecidableEq ι]

/-- **The geometry-defined code weight**: the element's local area over `4G`. -/
noncomputable def tauWEnt (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  localArea S β h a / (4 * G)

/-- **The REAL trace-dimension of a link**: `Dτ_a := exp(wEnt a)` — a positive real, no
    integrality (the Type II lesson: trace-dimensions need not be natural numbers). -/
noncomputable def tauDim (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : ℝ :=
  Real.exp (tauWEnt S β G h a)

theorem tauDim_pos (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) : 0 < tauDim S β G h a :=
  Real.exp_pos _

/-- **The calibration is a THEOREM at the τ level** — `log Dτ_a = wEnt a`, by `Real.log_exp`;
    nothing is calibrated, no integrality is needed. -/
theorem hcal_tau (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) :
    Real.log (tauDim S β G h a) = tauWEnt S β G h a :=
  Real.log_exp _

/-- **JI2 CAPSTONE — the carried `hJoin` is a THEOREM for the constructed dictionary:** with the
    code weights defined FROM the geometry (links = the screen elements, `wEnt = A^loc/(4G)`), the
    code's induced screen area equals the background plus the linearized area response —
    `inducedScreenArea G S.elems wEnt = A₀ + areaVar S (classicalH pol α)`. This is exactly the Q5
    hypothesis shape, now supplied by construction (geometry → code; no smuggling: the theorem is
    about the instance BUILT from this geometric data). -/
theorem hJoin_tau (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) {G : ℝ} (hG : 0 < G)
    (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) :
    inducedScreenArea G S.elems (tauWEnt S β G (classicalH pol α))
      = A0 + areaVar S (classicalH pol α) := by
  rw [inducedScreenArea, screen_cut_eq,
    show ∑ a ∈ S.elems, tauWEnt S β G (classicalH pol α) a
        = (∑ a ∈ S.elems, localArea S β (classicalH pol α) a) / (4 * G) from by
      rw [Finset.sum_div]
      rfl,
    sum_localArea]
  field_simp

end TauDictionary

/-! ## JI3 — the τ₀ corner realization via clock-window mass

Per the binding qualifier: arbitrary positive τ-dimensions are legitimate because the CLOCK-WINDOW
MASS is a free positive real (`τ₀(p ⊗ 1_W) = rank·μ(W)`) — NOT because subcorners of one
already-fixed fiber + window take arbitrary values (they cannot: only rank-multiples of a fixed
real scale). Each realization below therefore carries its OWN explicit window witness
(`flatClock r` — the held keystone window of mass `r`). -/

section CornerRealization

open QIQTH.TypeIITrace QIQTH.Keystone QIQTH.Spectral.Multiplication

/-- **The general mass lemma**: at `t = 0` the held monomial trace against the flat window of mass
    `r` is the matter-state value times `r` — `τ₀(π(x)·q_r(L)) = ω(x)·r`. -/
theorem tauMonomial_flatClock_zero {A : Type*} (ω : A → ℂ) (x : A) (r : ℝ) :
    tauMonomial ω x 0 (flatClock r) = ω x * (r : ℂ) := by
  rw [tauMonomial]
  have hmod : Iexp ((flatClock r).modMul 0) = Iexp (flatClock r) := by
    rw [Iexp, Iexp]
    congr 1
    funext y
    rw [show ((flatClock r).modMul 0).f y = modSymbol 0 y * (flatClock r).f y from rfl,
      show modSymbol 0 y = 1 from by simp [modSymbol], one_mul]
  rw [hmod, Iexp_flatClock]

/-- **JI3 CAPSTONE — every positive real is a realized τ₀ corner value**, with the clock-window
    witness EXPLICIT (the rank-one matter corner dressed by its own mass-`r` window): for any
    normalized matter state, `∃ window F, τ₀(π(1)·F(L)) = r`. -/
theorem exists_tau0_corner_of_posReal {A : Type*} [One A] (ω : A → ℂ) (hω : ω 1 = 1)
    (r : ℝ) (_hr : 0 < r) :
    ∃ F : ExpTest, tauMonomial ω (1 : A) 0 F = (r : ℂ) :=
  ⟨flatClock r, by rw [tauMonomial_flatClock_zero, hω, one_mul]⟩

variable [Fintype ι] [DecidableEq ι]

/-- **The per-link witness for the instance's `Dτ` family**: each link's real trace-dimension is
    realized by ITS OWN window of mass `Dτ_a` (never as a subcorner of one fixed fiber+window). -/
theorem tau0_link_witness (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) {A : Type*} [One A] (ω : A → ℂ) (hω : ω 1 = 1) :
    tauMonomial ω (1 : A) 0 (flatClock (tauDim S β G h a))
      = ((tauDim S β G h a : ℝ) : ℂ) := by
  rw [tauMonomial_flatClock_zero, hω, one_mul]

/-- **The total witness**: the instance's TOTAL dimension `∏_a Dτ_a` realized by the window of the
    product mass — the whole dictionary's τ₀-dimension lives in the held core. -/
theorem tau0_total_witness (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) {A : Type*} [One A] (ω : A → ℂ) (hω : ω 1 = 1) :
    tauMonomial ω (1 : A) 0 (flatClock (∏ a ∈ S.elems, tauDim S β G h a))
      = ((∏ a ∈ S.elems, tauDim S β G h a : ℝ) : ℂ) := by
  rw [tauMonomial_flatClock_zero, hω, one_mul]

end CornerRealization

/-! ## JI4 — the τ count theorem: the generic exact replacement for `hJoin`

The instance's count `S_τ = log ∏_a Dτ_a` equals the weight sum equals `A_J/(4G)` — the code's
counting and the geometry's area agree as two computations of one number, for ARBITRARY geometric
data, with no carried join hypothesis (the join is the construction). -/

section TauCount

variable [Fintype ι] [DecidableEq ι]

/-- The instance's TOTAL τ-dimension: the product of the link trace-dimensions. -/
noncomputable def dimTau (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∏ a ∈ S.elems, tauDim S β G h a

theorem dimTau_pos (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) : 0 < dimTau S β G h :=
  Finset.prod_pos fun a _ => tauDim_pos S β G h a

/-- The instance's count: the log of its total τ-dimension. -/
noncomputable def Stau (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.log (dimTau S β G h)

/-- The count is the weight sum: `S_τ = Σ_a wEnt a` (log of a product of exponentials). -/
theorem Stau_eq_sum_wEnt (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) :
    Stau S β G h = ∑ a ∈ S.elems, tauWEnt S β G h a := by
  rw [Stau, dimTau, Real.log_prod]
  · exact Finset.sum_congr rfl fun a _ => hcal_tau S β G h a
  · exact fun a _ => (tauDim_pos S β G h a).ne'

/-- **JI4 CAPSTONE — the generic exact replacement for the carried `hJoin`:** the constructed
    instance's count equals the geometric area over `4G` for ARBITRARY graviton data —
    `S_τ(J) = (A₀ + areaVar S (classicalH pol α))/(4G) = A_J/(4G)`. The count and the geometry are
    two computations of one number; nothing is carried (the join IS the construction). -/
theorem Stau_eq_area_over_4G (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) {G : ℝ}
    (_hG : 0 < G) (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) :
    Stau S β G (QIQTH.OperatorEmergence.classicalH pol α)
      = (A0 + QIQTH.AreaMap.areaVar S (QIQTH.OperatorEmergence.classicalH pol α)) / (4 * G) := by
  rw [Stau_eq_sum_wEnt,
    show ∑ a ∈ S.elems, tauWEnt S β G (QIQTH.OperatorEmergence.classicalH pol α) a
        = (∑ a ∈ S.elems, localArea S β (QIQTH.OperatorEmergence.classicalH pol α) a) / (4 * G)
      from by rw [Finset.sum_div]; rfl,
    sum_localArea]

/-- The count through the Q5 interface: `S_τ(J) = inducedScreenArea/(4G)` — the exact shape of the
    old capstone's right-hand side, now with the join supplied by `hJoin_tau`. -/
theorem Stau_eq_inducedScreenArea_over_4G [Fintype ι] [DecidableEq ι] (S : ScreenSurface ι)
    {A0 : ℝ} (β : A0Split S A0) {G : ℝ} (hG : 0 < G)
    (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) :
    Stau S β G (QIQTH.OperatorEmergence.classicalH pol α)
      = QIQTH.EarnGravity.inducedScreenArea G S.elems
          (tauWEnt S β G (QIQTH.OperatorEmergence.classicalH pol α)) / (4 * G) := by
  rw [hJoin_tau S β hG pol α, Stau_eq_area_over_4G S β hG pol α]

end TauCount

/-! ## JI5 — the integer finite-code specialization

Per the binding verdict: the integer code exists ONLY under the NAMED realizability datum
(`NatRealizable` — the geometry-defined weights are logs of naturals). This is the exact old
finite-code case, NOT generic (generic exact integer realization for arbitrary real weights is
FALSE and stays cut). Where the datum holds, the old Q5 capstone is re-proved with NO `hJoin`
hypothesis — the join is supplied by `hJoin_tau`. -/

section NatCode

open QIQTH.EarnGravity QIQTH.OperatorEmergence

variable [Fintype ι] [DecidableEq ι]

/-- **The NAMED realizability datum**: an integer link-dimension family whose logs are exactly the
    geometry-defined weights. Honest DATA (a design condition on the geometry), never derived —
    arbitrary real weights are NOT logs of naturals. -/
structure NatRealizable (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0) (G : ℝ)
    (h : Matrix (Fin 4) (Fin 4) ℝ) where
  /-- the integer link dimensions -/
  D : ι → ℕ
  /-- positivity on the screen -/
  hD : ∀ a ∈ S.elems, 0 < D a
  /-- the realizability condition: the geometric weights are logs of the integer dimensions -/
  hlog : ∀ a ∈ S.elems, Real.log (D a) = tauWEnt S β G h a

/-- Where realizable, the REAL trace-dimension IS the integer dimension — the two levels of the
    construction agree: `Dτ_a = D_a`. -/
theorem NatRealizable.tauDim_eq (S : ScreenSurface ι) {A0 : ℝ} {β : A0Split S A0} {G : ℝ}
    {h : Matrix (Fin 4) (Fin 4) ℝ} (R : NatRealizable S β G h) {a : ι} (ha : a ∈ S.elems) :
    tauDim S β G h a = (R.D a : ℝ) := by
  rw [tauDim, ← R.hlog a ha, Real.exp_log]
  exact_mod_cast R.hD a ha

/-- **JI5 CAPSTONE — the old Q5 capstone with NO `hJoin` hypothesis:** for a nat-realizable
    geometry, the finite code's microstate count equals the coherent expectation of the TOTAL area
    operator over `4G` — `log #microstates = ⟨α|Â_tot(Σ)|α⟩/(4G)` — with the join SUPPLIED by
    `hJoin_tau` (the construction), not carried. -/
theorem code_count_eq_fock_area_expect_noJoin (S : ScreenSurface ι) {A0 : ℝ}
    (β : A0Split S A0) {G : ℝ} (hG : 0 < G) (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (α : Fin 2 → ℂ) (R : NatRealizable S β G (classicalH pol α)) :
    Real.log (Fintype.card (Microstates S.elems R.D))
      = ((areaTotExpr pol A0 S).cohExpect α).re / (4 * G) :=
  code_count_eq_fock_area_expect G hG S.elems
    (tauWEnt S β G (classicalH pol α)) R.D R.hD R.hlog pol A0 S α
    (hJoin_tau S β hG pol α)

end NatCode

/-! ## JI6 — the induced-G normalization + capacity corollaries

The consistency capstone: the join instance's count, expressed with the DERIVED Newton constant
`G = 1/(N·Λs²)` (the granularity/species primitives), is `(A_J/4)·N·Λs²` — the count-built
normalization and the induced-G normalization are the SAME formula in `{area, species, granularity}`.
Per the binding verdict: `A_J` is defined INTERNALLY (`A₀ + areaVar` — the instance's own total),
never a new emergence hypothesis; the content is that both constructions share `A_J`, `N`, `Λs`.
Corollaries: the per-link capacity in primitives, the patch-capacity bound, and the area cost of a
nat / a qubit of link entropy. -/

section InducedGNormalization

open QIQTH.InducedG QIQTH.OperatorEmergence QIQTH.AreaMap

variable [Fintype ι] [DecidableEq ι]

/-- **The instance's own total area** (INTERNAL — background plus the linearized response of the
    instance's classical field; never a hypothesis). -/
noncomputable def AJoin (S : ScreenSurface ι) (A0 : ℝ)
    (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) : ℝ :=
  A0 + areaVar S (classicalH pol α)

theorem inducedG_pos {N Λs : ℝ} (hN : 0 < N) (hΛ : 0 < Λs) : 0 < inducedG N Λs := by
  rw [inducedG]
  positivity

/-- **JI6 CAPSTONE — the count in the primitives:** with the DERIVED `G = 1/(N·Λs²)`, the join
    instance's count is `S_τ(J) = (A_J/4)·N·Λs²` — the two independent normalizations (the
    count-built one and the induced-G one) are one formula in `{area, species, granularity}`. -/
theorem Stau_eq_capacity_primitives (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    {N Λs : ℝ} (hN : 0 < N) (hΛ : 0 < Λs)
    (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) :
    Stau S β (inducedG N Λs) (classicalH pol α) = (AJoin S A0 pol α / 4) * (N * Λs ^ 2) := by
  rw [Stau_eq_area_over_4G S β (inducedG_pos hN hΛ) pol α, AJoin, inducedG]
  field_simp

/-- **The per-link capacity in primitives**: `wEnt a = (A^loc_a/4)·N·Λs²`. -/
theorem tauWEnt_eq_capacity_primitives (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    {N Λs : ℝ} (hN : 0 < N) (hΛ : 0 < Λs) (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι) :
    tauWEnt S β (inducedG N Λs) h a = (localArea S β h a / 4) * (N * Λs ^ 2) := by
  rw [tauWEnt, inducedG]
  have hNΛ : N * Λs ^ 2 ≠ 0 := by positivity
  field_simp

/-- **The patch-capacity bound**: a link whose local area fits in the patch area `P_a` carries at
    most `(P_a/4)·N·Λs²` nats. -/
theorem tauWEnt_le_patch_capacity (S : ScreenSurface ι) {A0 : ℝ} (β : A0Split S A0)
    {N Λs : ℝ} (hN : 0 < N) (hΛ : 0 < Λs) (h : Matrix (Fin 4) (Fin 4) ℝ) (a : ι)
    {P : ℝ} (hP : localArea S β h a ≤ P) :
    tauWEnt S β (inducedG N Λs) h a ≤ (P / 4) * (N * Λs ^ 2) := by
  rw [tauWEnt_eq_capacity_primitives S β hN hΛ h a]
  have hNΛ : 0 < N * Λs ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_right _ hNΛ.le
  linarith

/-- **The area cost of link entropy**: for a realizable link, `A^loc_a = 4·log D_a/(N·Λs²)` —
    each nat of link entropy costs area `4/(N·Λs²)`. -/
theorem localArea_eq_log_cost (S : ScreenSurface ι) {A0 : ℝ} {β : A0Split S A0}
    {N Λs : ℝ} (hN : 0 < N) (hΛ : 0 < Λs) {h : Matrix (Fin 4) (Fin 4) ℝ}
    (R : NatRealizable S β (inducedG N Λs) h) {a : ι} (ha : a ∈ S.elems) :
    localArea S β h a = 4 * Real.log (R.D a) / (N * Λs ^ 2) := by
  have hw := R.hlog a ha
  rw [tauWEnt_eq_capacity_primitives S β hN hΛ h a] at hw
  have hNΛ : N * Λs ^ 2 ≠ 0 := by positivity
  field_simp at hw ⊢
  linarith

/-- **The qubit costs `4·log 2/(N·Λs²)` of area**: a two-dimensional realizable link occupies
    exactly that local area. -/
theorem qubit_area_cost (S : ScreenSurface ι) {A0 : ℝ} {β : A0Split S A0}
    {N Λs : ℝ} (hN : 0 < N) (hΛ : 0 < Λs) {h : Matrix (Fin 4) (Fin 4) ℝ}
    (R : NatRealizable S β (inducedG N Λs) h) {a : ι} (ha : a ∈ S.elems)
    (h2 : R.D a = 2) :
    localArea S β h a = 4 * Real.log 2 / (N * Λs ^ 2) := by
  rw [localArea_eq_log_cost S hN hΛ R ha, h2]
  norm_num

end InducedGNormalization

end QIQTH.JoinInstance
