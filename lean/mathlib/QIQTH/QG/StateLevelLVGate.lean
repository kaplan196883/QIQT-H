/-
  GATE 3 — the STATE-LEVEL LV bound (QG_CAMPAIGN_PLAN.md; the follow-on forced by the diamond-tip gate).

  The first two gates killed every regulator reading of finite capacity (preferred-frame cutoffs: CPSUV;
  diamond-frame truncations + rapidity averaging: the tip gate). The survivor is the STATE/ALGEBRA-LEVEL
  reading: `Q_D` bounds the (renormalized) entropy of the diamond algebra in the covariant vacuum. THIS
  gate certifies that the surviving reading makes NO low-energy Lorentz-violation prediction — and names
  exactly the channels through which LV could still enter. GPT-5.5-pro-verified design (2026-07-02);
  literature anchor: covariant entropy bounds (Bousso; Casini relative-entropy/Bekenstein; QNEC) are
  state-region inequalities, not propagator regulators — they do not modify dispersion.

  (A) COVARIANCE OF THE CONSTRAINT SET — `admissible_smul_iff` / `constraintSet_invariant`: if entropy and
      capacity transport covariantly (`CovariantCapacity`), the admissible set `{ρ : ∀D, S_ren ≤ Q_D}` is
      G-invariant AS A SET (no frame enters the kinematics); `vacuum_admissible`. NOTE the honest limit:
      set covariance does NOT make every admissible state invariant (thermal/conditioned states may have a
      rest frame — that is spontaneous/state breaking, not a law-level LV prediction).
      The technical hinge is `Sren_cov_of_traceCovariant`: covariant transport of the core trace + an
      equivariant density assignment ⟹ entropy covariance (the trace-transport input is the same named
      follow-on as J3's `hmodVac` — deletable via the RvD tower).
  (B) NO DYNAMICAL MODIFICATION — `stateLevel_noDeltaC2`: the constraint restricts the STATE SPACE, not
      the action/propagator/loop measure (`hNoDyn : PiCap = Π₀`); with the covariant `Π₀(q) = P(q²)` the
      speed splitting vanishes identically (riding the certified `covariantSplit_eq_zero`). Substantive,
      not circular: the theorem certifies the capacity adds NO NEW LV channel — it does not claim to
      derive covariant dynamics from the entropy bound.
  (C) THE RESIDUAL CHANNELS, made precise:
      • `no_operationalLV_of_invariant` / `operationalLV_iff_not_invariant` — operational LV ⟺ the
        PREPARED state is non-invariant (given separating observables);
      • `conditioned_state_orbit` / `conditioned_invariant_iff_orbit_constant` — diamond-indexed
        conditioning/saturation `K D` imprints at most the diamond's own frame, covariantly: the
        conditioned state is invariant IFF the orbit map is constant (saturation is safe iff no
        non-invariant diamond/background is SELECTED);
      • `equivariant_enforcement_preserves_invariance` / `safe_enforced_step` — an enforcement mechanism
        keeps the vacuum invariant IFF it is equivariant: the DYNAMICAL-REALIZATION GAP is the ONLY place
        LV can still enter (a non-equivariant enforcer reopens everything);
      • the selector λ: covariant observable probabilities under the boost-invariant μ are ALREADY held
        (`LorentzSelectionStrong.upvm_covariant_probability`); biased/postselected λ would reopen LV.
  INSTANTIATION — `permutationCapacity`: a genuine finite non-vacuous instance (permutation-covariant
  regional Shannon entropy on finite probability vectors, capacity = log|D|), with the gate theorems
  applying verbatim.

  ⚠ Honest scope: gate-level algebra, not a QFT construction; the trace-transport and equivariant-enforcer
  inputs are NAMED carried hypotheses; the dynamical-realization gap remains the open frontier. NOT QG. Std-3.
-/
import Mathlib
import QIQTH.QG.CpsuvGate

namespace QIQTH.QG.StateLevelLV

/-! ## The invariance vocabulary -/

/-- A point fixed by the whole group action. -/
def InvariantPt (G : Type*) {X : Type*} [Group G] [MulAction G X] (x : X) : Prop :=
  ∀ g : G, g • x = x

/-! ## (A) The covariant capacity constraint -/

/-- **The covariant state-level capacity**: entropy and capacity data transporting covariantly under the
    symmetry group (the state-level reading of `Q_D = A/4ℓ_P²` — entropy of the diamond algebra, never a
    mode count). -/
structure CovariantCapacity (G State Diamond : Type*) [Group G] [MulAction G State]
    [MulAction G Diamond] where
  /-- the renormalized regional entropy -/
  Sren : State → Diamond → ℝ
  /-- the regional capacity -/
  Q : Diamond → ℝ
  /-- entropy transports covariantly -/
  Sren_cov : ∀ (g : G) (ρ : State) (D : Diamond), Sren (g • ρ) (g • D) = Sren ρ D
  /-- capacity is geometric (proper data), hence invariant -/
  Q_cov : ∀ (g : G) (D : Diamond), Q (g • D) = Q D

variable {G State Diamond : Type*} [Group G] [MulAction G State] [MulAction G Diamond]

/-- A state satisfying every diamond's capacity bound. -/
def Admissible (T : CovariantCapacity G State Diamond) (ρ : State) : Prop :=
  ∀ D, T.Sren ρ D ≤ T.Q D

/-- **GATE (A) — the constraint is frame-free:** a boosted state is admissible iff the state is. -/
theorem admissible_smul_iff (T : CovariantCapacity G State Diamond) (g : G) (ρ : State) :
    Admissible T (g • ρ) ↔ Admissible T ρ := by
  constructor
  · intro h D
    have := h (g • D)
    rwa [T.Sren_cov, T.Q_cov] at this
  · intro h D
    calc T.Sren (g • ρ) D = T.Sren (g • ρ) (g • (g⁻¹ • D)) := by rw [smul_inv_smul]
      _ = T.Sren ρ (g⁻¹ • D) := T.Sren_cov g ρ _
      _ ≤ T.Q (g⁻¹ • D) := h _
      _ = T.Q D := by
          have := T.Q_cov g (g⁻¹ • D)
          rw [smul_inv_smul] at this
          exact this.symm

/-- The admissible set. -/
def ConstraintSet (T : CovariantCapacity G State Diamond) : Set State :=
  {ρ | Admissible T ρ}

/-- **The constraint SET is invariant** — no frame enters the kinematics. -/
theorem constraintSet_invariant (T : CovariantCapacity G State Diamond) (g : G) :
    (fun ρ : State => g • ρ) '' ConstraintSet T = ConstraintSet T := by
  ext ρ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (admissible_smul_iff T g σ).mpr hσ
  · intro h
    exact ⟨g⁻¹ • ρ, (admissible_smul_iff T g⁻¹ ρ).mpr h, smul_inv_smul g ρ⟩

/-- The vacuum (zero renormalized entropy) is admissible for any nonnegative capacity. -/
theorem vacuum_admissible (T : CovariantCapacity G State Diamond) (Ω : State)
    (hS : ∀ D, T.Sren Ω D = 0) (hQ : ∀ D, 0 ≤ T.Q D) : Admissible T Ω :=
  fun D => (hS D) ▸ hQ D

/-- **The technical hinge (A)**: `S_ren ρ D := τ_D(elem ρ D)` is covariant GIVEN covariant transport of
    the core trace + an equivariant density assignment — the carried trace-transport input (the same
    named follow-on as J3's `hmodVac`; deletable via the RvD tower). -/
theorem Sren_cov_of_traceCovariant {X : Type*}
    (τ : Diamond → X → ℝ) (transport : G → Diamond → X → X) (elem : State → Diamond → X)
    (htrace : ∀ (g : G) (D : Diamond) (x : X), τ (g • D) (transport g D x) = τ D x)
    (helem : ∀ (g : G) (ρ : State) (D : Diamond),
      elem (g • ρ) (g • D) = transport g D (elem ρ D)) :
    ∀ (g : G) (ρ : State) (D : Diamond),
      τ (g • D) (elem (g • ρ) (g • D)) = τ D (elem ρ D) := by
  intro g ρ D
  rw [helem, htrace]

/-! ## (B) No dynamical modification ⟹ no speed splitting -/

/-- **GATE (B) CAPSTONE — the state-level capacity makes NO one-loop LV prediction.** The constraint
    restricts the state space, not the dynamics (`hNoDyn`); the two-point function is the unconstrained
    covariant one, `Π(q) = P(q_E²)`, so the temporal/spatial quadratic coefficients agree — `Δc² = 0`
    identically (riding the certified O(4) symmetry certificate). Substantive content: the capacity adds
    no new LV channel — exactly what every regulator reading failed. -/
theorem stateLevel_noDeltaC2 (PiCap : ℝ → ℝ → ℝ) (P : ℝ → ℝ)
    (hNoDyn : PiCap = fun q0 q1 => P (q0 ^ 2 + q1 ^ 2)) :
    iteratedDeriv 2 (fun s : ℝ => PiCap 0 s) 0 - iteratedDeriv 2 (fun t : ℝ => PiCap t 0) 0 = 0 := by
  subst hNoDyn
  exact QIQTH.QG.Cpsuv.covariantSplit_eq_zero P

/-! ## (C) The residual channels, made precise -/

/-- Covariant expectation data (`⟨A⟩_{gρ}` at boosted observables equals `⟨A⟩_ρ`). -/
structure CovariantExpectation (G State Obs R : Type*) [Group G] [MulAction G State]
    [MulAction G Obs] where
  /-- the expectation pairing -/
  expect : State → Obs → R
  /-- full covariance -/
  expect_cov : ∀ (g : G) (ρ : State) (A : Obs), expect (g • ρ) (g • A) = expect ρ A

variable {Obs R : Type*} [MulAction G Obs]

/-- An invariant state has covariant correlators. -/
theorem expect_invariant_of_invariant_state (T : CovariantExpectation G State Obs R)
    {ω : State} (hω : InvariantPt G ω) (g : G) (A : Obs) :
    T.expect ω (g • A) = T.expect ω A := by
  conv_lhs => rw [← hω g]
  exact T.expect_cov g ω A

/-- Operational Lorentz violation: some observable's expectation is frame-dependent. -/
def OperationalLV (T : CovariantExpectation G State Obs R) (ω : State) : Prop :=
  ∃ (g : G) (A : Obs), T.expect ω (g • A) ≠ T.expect ω A

/-- **An invariant prepared state shows NO operational LV** — the vacuum channel is closed. -/
theorem no_operationalLV_of_invariant (T : CovariantExpectation G State Obs R)
    {ω : State} (hω : InvariantPt G ω) : ¬ OperationalLV T ω := by
  rintro ⟨g, A, h⟩
  exact h (expect_invariant_of_invariant_state T hω g A)

/-- **The exact LV condition** (given separating observables): operational LV ⟺ the prepared state is
    NOT invariant. State-induced breaking (thermal rest frames, conditioned states) is the ONLY
    expectation-level channel — a statement about preparations, not laws. -/
theorem operationalLV_iff_not_invariant (T : CovariantExpectation G State Obs R)
    (Sep : ∀ {ρ σ : State}, (∀ A : Obs, T.expect ρ A = T.expect σ A) → ρ = σ)
    (ω : State) : OperationalLV T ω ↔ ¬ InvariantPt G ω := by
  constructor
  · rintro ⟨g, A, h⟩ hinv
    exact h (expect_invariant_of_invariant_state T hinv g A)
  · intro hninv
    by_contra hno
    apply hninv
    intro g
    apply Sep
    intro A
    have hval : T.expect ω (g⁻¹ • A) = T.expect ω A := by
      by_contra hA
      exact hno ⟨g⁻¹, A, hA⟩
    calc T.expect (g • ω) A = T.expect (g • ω) (g • (g⁻¹ • A)) := by rw [smul_inv_smul]
      _ = T.expect ω (g⁻¹ • A) := T.expect_cov g ω _
      _ = T.expect ω A := hval

/-- A diamond-indexed conditioning/enforcement family transporting covariantly. -/
def EquivariantFamily (K : Diamond → State → State) : Prop :=
  ∀ (g : G) (D : Diamond) (ρ : State), K (g • D) (g • ρ) = g • K D ρ

/-- Conditioning an INVARIANT state on a diamond moves along the diamond orbit: the imprint is at most
    the diamond's own (covariant) frame. -/
theorem conditioned_state_orbit {K : Diamond → State → State}
    (hK : EquivariantFamily (G := G) K) {Ω : State} (hΩ : InvariantPt G Ω)
    (g : G) (D : Diamond) : g • K D Ω = K (g • D) Ω := by
  rw [← hK g D Ω, hΩ g]

/-- **Saturation is safe iff no background is selected**: the conditioned state is invariant IFF the
    diamond-orbit map is constant. -/
theorem conditioned_invariant_iff_orbit_constant {K : Diamond → State → State}
    (hK : EquivariantFamily (G := G) K) {Ω : State} (hΩ : InvariantPt G Ω) (D : Diamond) :
    InvariantPt G (K D Ω) ↔ ∀ g : G, K (g • D) Ω = K D Ω := by
  constructor
  · intro h g
    rw [← conditioned_state_orbit hK hΩ g D]
    exact h g
  · intro h g
    rw [conditioned_state_orbit hK hΩ g D]
    exact h g

/-- **The enforcement channel**: an equivariant enforcement mechanism preserves the invariant vacuum —
    the dynamical-realization gap reopens LV ONLY through a non-equivariant enforcer. -/
theorem equivariant_enforcement_preserves_invariance {E : State → State}
    (hE : ∀ (g : G) (ρ : State), E (g • ρ) = g • E ρ) {ω : State}
    (hω : InvariantPt G ω) : InvariantPt G (E ω) := by
  intro g
  rw [← hE g ω, hω g]

/-- Equivariant dynamics + equivariant enforcement keep the invariant sector invariant, step by step. -/
theorem safe_enforced_step {Step Enf : State → State}
    (hS : ∀ (g : G) (ρ : State), Step (g • ρ) = g • Step ρ)
    (hE : ∀ (g : G) (ρ : State), Enf (g • ρ) = g • Enf ρ)
    {ω : State} (hω : InvariantPt G ω) : InvariantPt G (Enf (Step ω)) :=
  equivariant_enforcement_preserves_invariance hE
    (equivariant_enforcement_preserves_invariance hS hω)

/-! ## The finite instantiation: permutation-covariant regional entropy -/

section FiniteInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Permutations act on finite states (probability vectors) by relabeling. -/
local instance permStateSMul : SMul (Equiv.Perm ι) (ι → ℝ) := ⟨fun σ p => p ∘ σ.symm⟩

local instance permStateAction : MulAction (Equiv.Perm ι) (ι → ℝ) where
  one_smul p := rfl
  mul_smul σ τ p := rfl

/-- Permutations act on regions (finite index sets) by relabeling. -/
local instance permRegionSMul : SMul (Equiv.Perm ι) (Finset ι) := ⟨fun σ D => D.image σ⟩

local instance permRegionAction : MulAction (Equiv.Perm ι) (Finset ι) where
  one_smul D := by
    show D.image ⇑(1 : Equiv.Perm ι) = D
    simp
  mul_smul σ τ D := by
    show D.image ⇑(σ * τ) = (D.image ⇑τ).image ⇑σ
    rw [Finset.image_image, Equiv.Perm.coe_mul]

/-- The regional Shannon entropy `−∑_{i∈D} p_i log p_i`. -/
noncomputable def regionalEntropy (p : ι → ℝ) (D : Finset ι) : ℝ :=
  -∑ i ∈ D, p i * Real.log (p i)

/-- **The finite instantiation** — a genuine, non-vacuous `CovariantCapacity`: relabeling-covariant
    regional Shannon entropy with the size capacity `Q_D = log|D|`. The gate theorems
    (`admissible_smul_iff`, `constraintSet_invariant`, …) apply verbatim. -/
noncomputable def permutationCapacity :
    CovariantCapacity (Equiv.Perm ι) (ι → ℝ) (Finset ι) where
  Sren := regionalEntropy
  Q := fun D => Real.log (D.card)
  Sren_cov := by
    intro σ p D
    show regionalEntropy (p ∘ σ.symm) (D.image σ) = regionalEntropy p D
    rw [regionalEntropy, regionalEntropy,
      Finset.sum_image (fun i _ j _ h => σ.injective h)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by simp
  Q_cov := by
    intro σ D
    show Real.log ((D.image σ).card) = Real.log (D.card)
    rw [Finset.card_image_of_injective D σ.injective]

end FiniteInstance

end QIQTH.QG.StateLevelLV
