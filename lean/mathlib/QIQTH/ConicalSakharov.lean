/-
  CONICAL SAKHAROV — the Susskind–Uglum counterterm identity: entanglement entropy
  renormalizes `1/G` (duality campaign, brick D3d).

  Brick D3c (`QIQTH.ConicalHeatKernel`) proved, EXACTLY and machine-checked, the integer-cone
  heat-trace excess `zmodConeExcess n t = (1/12)(n − 1/n)` together with the replica coefficient
  `coneCoeff ν = (1/12)(ν − ν⁻¹)` and its derivative at the smooth point
  `d/dν coneCoeff|_{ν=1} = 1/6` (`ConicalHeatKernel.hasDerivAt_coneCoeff_one`) — the famous
  `c/6 = 1/6` (central charge `c = 1`) entanglement coefficient.  Bricks D3a/D3b
  (`QIQTH.HeatKernelThermal` / `QIQTH.ContinuumEntropy`) supplied the smooth thermal
  heat-kernel/continuum-entropy legs.

  THIS brick proves the exact ALGEBRAIC Susskind–Uglum content: the divergent one-loop
  conical/entanglement entropy is precisely the counterterm that renormalizes the induced
  Newton constant.  Writing `I = J_ε` for the (explicit, never-removed) proper-time/IR cutoff
  functional and `N` for the number of species:

      S_ent  =  (N·A·I)/12            (the divergent conical/entanglement entropy),
      δ(1/G) =  (N·I)/3               (the induced-Newton-constant counterterm, `a₁ = R/6`),

  and the SAME regulator `I` appears in both.  The exact algebraic facts are:

    • ★  `Sent = (A/4)·δ(1/G)`                       (the Susskind–Uglum identity),
    • ★  `(A/4)·(1/G)_bare + S_ent = (A/4)·(1/G)_ren`  (S_ent renormalizes `1/G`),
    • ★★ `4·G_ind·S_ent = A`, at EVERY finite cutoff  (the induced-only reading; ε → 0 NEVER
          taken — the divergences in `G_ind` and `S_ent` cancel, so the product is
          cutoff-INDEPENDENT).

  The `1/12` of `S_ent` is the honest descendant of D3c's `1/6`: the Gaussian one-loop
  determinant carries a `½` loop factor, and the replica entropy is
  `S = (½∫dt/t)·[(1 + n∂n) coneCoeff]|_{n=1}·N·A` with `(1 + n∂n) coneCoeff|_{1} = coneCoeff'(1)`
  (since `coneCoeff(1) = 0`), `= 1/6`; hence `½·(1/6) = 1/12` (`half_times_replica`).  SIGN
  (pro-caught): the orbifold/replica form is the `+n∂n` / `(1 − q∂q)` q-convention, NOT `−n∂n`.

  The D=4 specialization `I = 1/(4π ε²)` reproduces the held Sakharov ratio
  (`QIQTH.Sakharov.sakharov_ratio`): `S_ent = N·A/(48π ε²)`, `δ(1/G) = N/(12π ε²)`, and the
  numeric core `1/(48π) = (1/4)·(1/(12π))` now READ as the Susskind–Uglum ratio
  `S_ent : δ(1/G) = 1/4` at D=4.  The D=2 specialization `I = 2 log(L/ε)` gives the `c/6` log:
  `S_ent = (1/6) log(L/ε)` for the `c = 1` free scalar, tying the SAME cutoff functional to the
  D3a/D3b continuum-entropy legs.

  ────────────────────────────────────────────────────────────────────────────────────────
  MANDATORY FIREWALL (binding scope).  The cutoff functional `I = J_ε` is carried EXPLICIT
  throughout — this is a REGULATED counterterm identity, NOT a cutoff-free equality of
  infinities; `ε → 0` is NEVER taken.  CITED (entered as data, NOT built here): the Gaussian
  scalar-determinant one-loop form `log Z = ½∫(dt/t) Tr K`; the replica/entanglement
  identification `S = (1 − q∂q) log Z_q|_{q=1}`; the `n → 1` analytic continuation; the
  curved-space heat-kernel coefficient `a₁ = R/6` for the minimally-coupled scalar; the use of
  the SAME regulator in `S_ent` and `δ(1/G)`; integer cones + one-loop free scalar only; the
  replica-convention footnote (`ν = 2π/γ` vs `m = γ/2π`, and the `+n∂n` orbifold sign).  This
  is NOT the DY7 conjecture (its fourth rung), NOT the strong holographic principle, and NOT
  quantum gravity.  Susskind–Uglum 1994; Kabat–Strassler; the held `QIQTH.Sakharov.sakharov_ratio`
  is the D=4 numeric.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.ConicalHeatKernel
import QIQTH.SakharovRatio

noncomputable section

namespace QIQTH.ConicalSakharov

/-! ### PART A — the divergent conical/entanglement entropy and the induced counterterm

`I : ℝ` is the EXPLICIT proper-time/IR cutoff functional `J_ε` (never removed); `N : ℝ` the
number of species.  Both `Sent` and `dInvG` carry the SAME `I`. -/

/-- **The divergent conical/entanglement entropy** `S_ent = (N·A·I)/12`.  The `1/12 = ½ · 1/6`
    is the Gaussian loop factor `½` times D3c's replica coefficient
    `coneCoeff'(1) = 1/6` (`ConicalHeatKernel.hasDerivAt_coneCoeff_one`); see `half_times_replica`
    and the header. -/
def Sent (N A I : ℝ) : ℝ := N * A * I / 12

/-- **The induced-Newton-constant counterterm** `δ(1/G) = (N·I)/3` — the `a₁ = R/6` curved-space
    heat-kernel coefficient (minimally-coupled scalar), summed over `N` species, with the SAME
    cutoff functional `I` as `Sent`. -/
def dInvG (N I : ℝ) : ℝ := N * I / 3

/-- The induced Newton constant `G_ind = (δ(1/G))⁻¹` (the induced-only reading: no bare `1/G`). -/
def Gind (N I : ℝ) : ℝ := (dInvG N I)⁻¹

/-- The renormalized inverse Newton constant `(1/G)_ren = (1/G)_bare + δ(1/G)`. -/
def invGren (invGbare N I : ℝ) : ℝ := invGbare + dInvG N I

/-! ### PART B — the Susskind–Uglum counterterm identity -/

/-- **★ THE SUSSKIND–UGLUM IDENTITY** `S_ent = (A/4)·δ(1/G)`: the divergent conical/entanglement
    entropy equals the area over four times the induced-Newton-constant counterterm — the
    entanglement entropy IS the `A/4G` counterterm, with the SAME explicit cutoff `I`. -/
theorem ent_eq_area_quarter_dInvG (N A I : ℝ) :
    Sent N A I = (A / 4) * dInvG N I := by
  unfold Sent dInvG; ring

/-- **★ ENTANGLEMENT ENTROPY RENORMALIZES `1/G`**:
    `(A/4)·(1/G)_bare + S_ent = (A/4)·(1/G)_ren`.  Adding the divergent entanglement entropy to
    the bare gravitational `A/4·(1/G)` term is exactly the shift `(1/G)_bare → (1/G)_ren` of the
    induced Newton constant — the entropy is absorbed into `1/G`. -/
theorem bare_entropy_renormalizes (invGbare N A I : ℝ) :
    (A / 4) * invGbare + Sent N A I = (A / 4) * invGren invGbare N I := by
  unfold Sent invGren dInvG; ring

/-- **★★ THE CUTOFF-INDEPENDENT INDUCED PRODUCT** `4·G_ind·S_ent = A`.
    Both `G_ind = (δ(1/G))⁻¹` and `S_ent` diverge as `ε → 0`, but their product is EXACTLY the
    area `A` at EVERY finite cutoff `I` (the divergences cancel): `ε → 0` is never taken.  This
    is the exact one-loop-counterterm skeleton of the induced-only reading
    `S_micro = A/(4 G_ind)`. -/
theorem induced_product (N A I : ℝ) (h : dInvG N I ≠ 0) :
    4 * Gind N I * Sent N A I = A := by
  rw [Gind, ent_eq_area_quarter_dInvG]
  have hstep : 4 * (dInvG N I)⁻¹ * (A / 4 * dInvG N I)
      = A * ((dInvG N I)⁻¹ * dInvG N I) := by ring
  rw [hstep, inv_mul_cancel₀ h, mul_one]

/-! ### PART C — the honest origin of the `1/12` (the join to D3c) -/

/-- **The replica-coefficient origin of `1/12`** — `½ · (1/6) = 1/12`.  The Gaussian one-loop
    determinant carries the loop factor `½`; D3c's replica coefficient is
    `(1 + n∂n) coneCoeff|_{n=1} = coneCoeff'(1) = 1/6`
    (`ConicalHeatKernel.hasDerivAt_coneCoeff_one`, using `coneCoeff(1) = 0`).  Their product is
    the `1/12` of `Sent`.  (The `+n∂n` orbifold sign convention — pro-caught — is fixed as in
    D3c's `ν = n` derivative at `1`.) -/
theorem half_times_replica : (1 : ℝ) / 2 * (1 / 6) = 1 / 12 := by norm_num

/-- The `1/6` used above is exactly D3c's replica derivative
    `ConicalHeatKernel.hasDerivAt_coneCoeff_one : HasDerivAt coneCoeff (1/6) 1` — restated here
    to pin the numeric join formally. -/
theorem replica_deriv_is_one_sixth :
    HasDerivAt QIQTH.ConicalHeatKernel.coneCoeff (1 / 6) 1 :=
  QIQTH.ConicalHeatKernel.hasDerivAt_coneCoeff_one

/-! ### PART D — the D=4 specialization (the join to the held Sakharov ratio) -/

/-- The D=4 proper-time cutoff functional `I = 1/(4π ε²)`. -/
def dfour_I (ε : ℝ) : ℝ := 1 / (4 * Real.pi * ε ^ 2)

/-- `S_ent = N·A/(48π ε²)` at D=4 (the Susskind–Uglum entanglement-entropy density). -/
theorem sent_dfour (N A ε : ℝ) (hε : ε ≠ 0) :
    Sent N A (dfour_I ε) = N * A / (48 * Real.pi * ε ^ 2) := by
  have hπ := Real.pi_ne_zero
  unfold Sent dfour_I; field_simp; ring

/-- `δ(1/G) = N/(12π ε²)` at D=4 (the induced-Newton-constant counterterm). -/
theorem dInvG_dfour (N ε : ℝ) (hε : ε ≠ 0) :
    dInvG N (dfour_I ε) = N / (12 * Real.pi * ε ^ 2) := by
  have hπ := Real.pi_ne_zero
  unfold dInvG dfour_I; field_simp; ring

/-- **★ THE SUSSKIND–UGLUM RATIO AT D=4** `1/(48π) = (1/4)·(1/(12π))` — the held Sakharov numeric
    core (`QIQTH.Sakharov.sakharov_ratio`), now READ as `S_ent : δ(1/G) = 1/4` at D=4: the entropy
    coefficient `1/48π` is exactly `1/4` of the induced-`1/G` coefficient `1/12π`. -/
theorem susskind_uglum_ratio_dfour :
    (1 : ℝ) / (48 * Real.pi) = (1 / 4) * (1 / (12 * Real.pi)) := by
  have hπ := Real.pi_ne_zero
  field_simp; ring

/-- The held Sakharov ratio, restated to pin the D=4 join formally: with a shared UV factor
    `b/reg`, `S_ent/(A/G_ind) = 1/4`. -/
theorem sakharov_ratio_join (A b reg : ℝ) (hA : A ≠ 0) (hb : b ≠ 0) (hreg : reg ≠ 0) :
    (A * b / (48 * Real.pi * reg)) / (A * (b / (12 * Real.pi * reg))) = 1 / 4 :=
  QIQTH.Sakharov.sakharov_ratio A b reg hA hb hreg

/-! ### PART E — the D=2 specialization (the `c/6` log) -/

/-- The D=2 cutoff functional `I = 2 log(L/ε)` (interval length `L`, cutoff `ε`). -/
def dtwo_I (ε L : ℝ) : ℝ := 2 * Real.log (L / ε)

/-- **The `c/6` entanglement log** `S_ent = (1/6) log(L/ε)` for the `c = 1` free scalar
    (`N = A = 1`) — the SAME cutoff functional feeding D3a/D3b's continuum entropy, now with the
    D3c `c/6 = 1/6` coefficient. -/
theorem sent_dtwo (ε L : ℝ) :
    Sent 1 1 (dtwo_I ε L) = (1 / 6) * Real.log (L / ε) := by
  unfold Sent dtwo_I; ring

/-! ### PART F — the capstone -/

/-- **★★ THE CAPSTONE — `susskind_uglum_identity`** (brick D3d of the duality campaign).

    THE CONICAL LEG COUPLES TO `1/G`.  At the integer-cone / one-loop-free-scalar level, with
    the cutoff functional `I` carried EXPLICIT (ε → 0 never taken), the following hold exactly:

    1. **the counterterm identity** — `S_ent = (A/4)·δ(1/G)`: the divergent conical/entanglement
       entropy IS the area over four times the induced-Newton-constant counterterm;
    2. **the renormalization statement** — `(A/4)·(1/G)_bare + S_ent = (A/4)·(1/G)_ren`: the
       entanglement entropy renormalizes `1/G` with the SAME regulator;
    3. **the cutoff-independent product** — `4·G_ind·S_ent = A` (under `δ(1/G) ≠ 0`): the
       induced-only reading gives the exact area at EVERY finite cutoff (divergences cancel);
    4. **the D=4 ratio** — `1/(48π) = (1/4)·(1/(12π))`: the held Sakharov ratio, read as
       `S_ent : δ(1/G) = 1/4` at D=4.

    So the DY7 conjecture's `micro entropy = A/(4 G_ind)` has here its exact one-loop-counterterm
    skeleton, with the divergent cutoff carried explicit.

    FIREWALL: regulated counterterm identity, NOT a cutoff-free equality of infinities; the
    Gaussian determinant `½∫(dt/t)Tr K`, the replica identification, the `n → 1` continuation,
    the `a₁ = R/6` coefficient, the same-regulator assumption, integer-cone/one-loop-free-scalar
    scope, and the replica-convention/sign footnote are CITED — see the header.  Susskind–Uglum
    1994; Kabat–Strassler; the held `QIQTH.Sakharov.sakharov_ratio` the D=4 numeric.  This is
    NOT the DY7 conjecture (its fourth rung), NOT the strong holographic principle, NOT QG. -/
theorem susskind_uglum_identity (invGbare N A I : ℝ) (h : dInvG N I ≠ 0) :
    Sent N A I = (A / 4) * dInvG N I
    ∧ (A / 4) * invGbare + Sent N A I = (A / 4) * invGren invGbare N I
    ∧ 4 * Gind N I * Sent N A I = A
    ∧ (1 : ℝ) / (48 * Real.pi) = (1 / 4) * (1 / (12 * Real.pi)) :=
  ⟨ent_eq_area_quarter_dInvG N A I,
    bare_entropy_renormalizes invGbare N A I,
    induced_product N A I h,
    susskind_uglum_ratio_dfour⟩

end QIQTH.ConicalSakharov
