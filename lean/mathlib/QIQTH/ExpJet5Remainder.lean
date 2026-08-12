/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemainderB
import QIQTH.ExpJet5Prereq
import QIQTH.ExpJet4FundBounds

/-!
# Jet_5 quadratic remainder bound -- rung J5-5b (main assembly)

FAITHFUL one-Frechet-order-up mirror of `expJet4_remainder_quadratic_bound`.  Derives the
`O(‖r‖^2)` bound on the exact remainder `rho(t)` fed to `expJet5_residual_bound`'s `hr` obligation,
via the fifteen-block cancellation: the abstract reassembly `remMaster_identity` (opaque atoms) plus
the fifteen abstract block-shape bounds (`remBlk0_bound`, `remBlkTop_bound`, `remBlk211_bound` x6,
`remBlk22_bound` x3, `remBlk31_bound` x4), each fed the concrete tube Taylor / accuracy / Lipschitz /
value data.

## Honest firewall (binding)

Proves ONLY the quadratic-remainder assembly (brick (b) of J5-5).  Does NOT prove
`expMap_fderiv4_hasFDerivAt`, does NOT reach `exp in C^5`, `kappa = 1/6`, the heat-kernel parametrix,
or `a_1 = R/6` (CONDITIONAL).  All strictly-lower-order INPUTS (curve identities, first->second /
second->third / third->fourth variation residuals, Lipschitz and value bounds) are carried as
explicit numbered hypotheses, exactly as in the order-4 mirror.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 64000000
set_option maxRecDepth 65536
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 2000000

variable {n : ℕ}

set_option maxHeartbeats 64000000 in
/-- **Jet_5 quadratic remainder bound** (mirror of `expJet4_remainder_quadratic_bound`, one Frechet
    order up).  DERIVES the `O(‖r‖^2)` bound on the exact `rho(t)` fed to `expJet5_residual_bound`. -/
theorem expJet5_remainder_quadratic_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w r : Point n) (hwr : w = v + r)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qw : ℝ → (Point n × Point n))
    (Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm : ℝ → (Point n × Point n))
    (Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm : ℝ → (Point n × Point n))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n)) (h k l m : Point n)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p w t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQw0 : Qw 0 = 0)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQvhk : Qvhk = Qhk)
    (hQvhl : Qvhl = Qhl)
    (hQvhm : Qvhm = Qhm)
    (hQvkl : Qvkl = Qkl)
    (hQvkm : Qvkm = Qkm)
    (hQvlm : Qvlm = Qlm)
    (hQvhkl : Qvhkl = Qhkl)
    (hQvhkm : Qvhkm = Qhkm)
    (hQvhlm : Qvhlm = Qhlm)
    (hQvklm : Qvklm = Qklm)
    (Cd Ce Cq2 Cq3 Ccr : ℝ)
    (hCd0 : 0 ≤ Cd) (hCe0 : 0 ≤ Ce) (hCq20 : 0 ≤ Cq2) (hCq30 : 0 ≤ Cq3) (hCcr0 : 0 ≤ Ccr)
    (hQlipTop : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t - Qhklm t‖ ≤ Ce * ‖r‖)
    (hFPh : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFPk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFPl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t (expJetIota l) - Φ t (expJetIota l) - Qlr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFPm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t (expJetIota m) - Φ t (expJetIota m) - Qmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hVhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq2)
    (hVhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq2)
    (hVhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhm t‖ ≤ Cq2)
    (hVkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq2)
    (hVkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq2)
    (hVlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq2)
    (hVwhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t‖ ≤ Cq2)
    (hVwhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t‖ ≤ Cq2)
    (hVwhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhm t‖ ≤ Cq2)
    (hVwkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t‖ ≤ Cq2)
    (hVwkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkm t‖ ≤ Cq2)
    (hVwlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwlm t‖ ≤ Cq2)
    (hQLhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t - Qhk t‖ ≤ Ce * ‖r‖)
    (hQLhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t - Qhl t‖ ≤ Ce * ‖r‖)
    (hQLhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhm t - Qhm t‖ ≤ Ce * ‖r‖)
    (hQLkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t - Qkl t‖ ≤ Ce * ‖r‖)
    (hQLkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkm t - Qkm t‖ ≤ Ce * ‖r‖)
    (hQLlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwlm t - Qlm t‖ ≤ Ce * ‖r‖)
    (hFQhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t - Qhk t - Qhkr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t - Qhl t - Qhlr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhm t - Qhm t - Qhmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t - Qkl t - Qklr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkm t - Qkm t - Qkmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwlm t - Qlm t - Qlmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hVklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq3)
    (hVhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq3)
    (hVhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq3)
    (hVhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq3)
    (hVwklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwklm t‖ ≤ Cq3)
    (hVwhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhlm t‖ ≤ Cq3)
    (hVwhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkm t‖ ≤ Cq3)
    (hVwhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkl t‖ ≤ Cq3)
    (hQL3klm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwklm t - Qklm t‖ ≤ Ce * ‖r‖)
    (hQL3hlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhlm t - Qhlm t‖ ≤ Ce * ‖r‖)
    (hQL3hkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkm t - Qhkm t‖ ≤ Ce * ‖r‖)
    (hQL3hkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkl t - Qhkl t‖ ≤ Ce * ‖r‖)
    (hFQ3klm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwklm t - Qklm t - Qklmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQ3hlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhlm t - Qhlm t - Qhlmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQ3hkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkm t - Qhkm t - Qhkmr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hFQ3hkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkl t - Qhkl t - Qhklr t‖ ≤ Cd * ‖r‖ ^ 2)
    (hVQhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Cq3)
    (hVQhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Cq3)
    (hVQhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Cq3)
    (hVQklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Cq3)
    (hVQkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Cq3)
    (hVQlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Cq3)
    (hSQhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Ccr * ‖r‖)
    (hSQhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Ccr * ‖r‖)
    (hSQhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Ccr * ‖r‖)
    (hSQklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Ccr * ‖r‖)
    (hSQkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Ccr * ‖r‖)
    (hSQlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Ccr * ‖r‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))
           - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qw t)
         + (expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t
            - expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t
            - expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)‖
        ≤ C * ‖r‖ ^ 2 := by
  subst hwr
  -- flip the pair-curve identifications so the `Qv*` names are the ones eliminated
  -- (`subst h` with `h : a = b` and both sides fvars eliminates the RHS variable):
  replace hQvhk := hQvhk.symm; replace hQvhl := hQvhl.symm; replace hQvhm := hQvhm.symm
  replace hQvkl := hQvkl.symm; replace hQvkm := hQvkm.symm; replace hQvlm := hQvlm.symm
  replace hQvhkl := hQvhkl.symm; replace hQvhkm := hQvhkm.symm
  replace hQvhlm := hQvhlm.symm; replace hQvklm := hQvklm.symm
  subst hQvhk; subst hQvhl; subst hQvhm; subst hQvkl; subst hQvkm; subst hQvlm
  subst hQvhkl; subst hQvhkm; subst hQvhlm; subst hQvklm
  have hC₀ := expConst_nonneg g gi hC p
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  obtain ⟨Ld4f, hLipD4⟩ := expJet_fderiv4_lipschitzOnWith g gi hC p
  obtain ⟨Ld5f, hLipD5⟩ := expJet_fderiv5_lipschitzOnWith g gi hC p
  obtain ⟨Kvb, hKvb0, hKvbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kwb, _hKwb0, hKwbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p (v + r) hw
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hD3bd⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hD4bd⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar5, hKstar50, hD5bd⟩ := expJet_fderiv5_tube_bddAbove_unif g gi hC p
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := (Real.exp_pos _).le
  set Kstar : ℝ := max Kvb Kwb with hKstardef
  have hKstar0 : 0 ≤ Kstar := le_max_of_le_left hKvb0
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := (Real.exp_pos _).le
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := Ldf.coe_nonneg
  set L2 : ℝ := (Ld2f : ℝ) with hL2def
  have hL2_0 : 0 ≤ L2 := Ld2f.coe_nonneg
  set L3 : ℝ := (Ld3f : ℝ) with hL3def
  have hL3_0 : 0 ≤ L3 := Ld3f.coe_nonneg
  set L4 : ℝ := (Ld4f : ℝ) with hL4def
  have hL4_0 : 0 ≤ L4 := Ld4f.coe_nonneg
  set L5 : ℝ := (Ld5f : ℝ) with hL5def
  have hL5_0 : 0 ≤ L5 := Ld5f.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by rw [hC2def]; positivity
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by rw [hC3def]; positivity
  set nr : ℝ := ‖r‖ with hnrdef
  have hnr0 : 0 ≤ nr := norm_nonneg r
  set Bdir : ℝ := ‖h‖ + ‖k‖ + ‖l‖ + ‖m‖ with hBdirdef
  have hBdir0 : 0 ≤ Bdir := by rw [hBdirdef]; positivity
  set V : ℝ := eKs * Bdir with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  set Ddel : ℝ := C3 * Bdir with hDdeldef
  have hDdel0 : 0 ≤ Ddel := by rw [hDdeldef]; positivity
  set VFq : ℝ := Cq2 + Cq2 + Cq3 with hVFqdef
  have hVFq0 : 0 ≤ VFq := by rw [hVFqdef]; positivity
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  have hLipD2R : LipschitzOnWith L2.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL2def, Real.toNNReal_coe]; exact hLipD2
  have hLipD3R : LipschitzOnWith L3.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL3def, Real.toNNReal_coe]; exact hLipD3
  have hLipD4R : LipschitzOnWith L4.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL4def, Real.toNNReal_coe]; exact hLipD4
  have hLipD5R : LipschitzOnWith L5.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL5def, Real.toNNReal_coe]; exact hLipD5
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar :=
    fun t ht => (hKvbd t ht).trans (le_max_left Kvb Kwb)
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)‖ ≤ Kstar :=
    fun t ht => (hKwbd t ht).trans (le_max_right Kvb Kwb)
  have hK2v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd v hv t ht
  have hK3v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3 :=
    fun t ht => hD3bd v hv t ht
  have hK4v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4 := fun t ht => hD4bd v hv t ht
  have hK5v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)‖ ≤ Kstar5 := fun t ht => hD5bd v hv t ht
  have hK2w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd (v + r) hw t ht
  have hK3w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)‖ ≤ Kstar3 :=
    fun t ht => hD3bd (v + r) hw t ht
  have hK4w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)‖
        ≤ Kstar4 := fun t ht => hD4bd (v + r) hw t ht
  have hΦnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  have hΦ'norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p (v + r) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p (v + r) hw
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + r) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hw hC₀)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ≤ nr * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + r) 0) (expTube g gi hC p v 0) = nr := by
      rw [hY0w, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _), hnrdef]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdw t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L2 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L2 hL2_0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hD2tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L3 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D2F_second_order_taylor g gi hC p L3 hL3_0 hLipD3R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hD3tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L4 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D3F_second_order_taylor g gi hC p L4 hL4_0 hLipD4R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hD4tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
              (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L5 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D4F_second_order_taylor g gi hC p L5 hL5_0 hLipD5R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t - Φ t (expJetIota r)‖ ≤ C2 * nr ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v r hw hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  set M4 : ℝ := (Kstar4 * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖) * (eKs * ‖m‖)
    + Kstar3 * (eKs * ‖l‖) * (eKs * ‖m‖) * Cq2
    + Kstar3 * (eKs * ‖k‖) * (eKs * ‖m‖) * Cq2
    + Kstar3 * (eKs * ‖k‖) * (eKs * ‖l‖) * Cq2
    + Kstar3 * (eKs * ‖h‖) * (eKs * ‖m‖) * Cq2
    + Kstar3 * (eKs * ‖h‖) * (eKs * ‖l‖) * Cq2
    + Kstar3 * (eKs * ‖h‖) * (eKs * ‖k‖) * Cq2
    + Kstar2 * Cq2 * Cq2
    + Kstar2 * Cq2 * Cq2
    + Kstar2 * Cq2 * Cq2
    + Kstar2 * (eKs * ‖h‖) * Cq3
    + Kstar2 * (eKs * ‖k‖) * Cq3
    + Kstar2 * (eKs * ‖l‖) * Cq3
    + Kstar2 * (eKs * ‖m‖) * Cq3) * Real.exp Kstar with hM4def
  have hM40 : 0 ≤ M4 := by rw [hM4def]; positivity
  have hqwval := expJet4Fund_value_bound_Icc g gi hC p (v + r) Φ'
      Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m
      Kstar Kstar4 Kstar3 Kstar2 eKs Cq2 Cq2 Cq2 Cq2 Cq2 Cq2 Cq3 Cq3 Cq3 Cq3
      hKstar0 hKstar40 hKstar30 hKstar20 heKs0 hKstarw hK4w hK3w hK2w hΦ'norm
      hVwhk hVwhl hVwhm hVwkl hVwkm hVwlm hVwhkl hVwhkm hVwhlm hVwklm Qw hQw0 hQwd
  rw [← hM4def] at hqwval
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * nr := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + r) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hw Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + r) = -r by abel, norm_neg, ← hnrdef] at hb
    exact hb
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
  have hιm : ‖expJetIota (n := n) m‖ ≤ ‖m‖ :=
    ((expJetIota (n := n)).le_opNorm m).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg m))
  have hιr : ‖expJetIota (n := n) r‖ ≤ ‖r‖ :=
    ((expJetIota (n := n)).le_opNorm r).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg r))

  set CB0 : ℝ := L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce with hCB0def
  have hCB00 : 0 ≤ CB0 := by rw [hCB0def]; positivity
  set CBtop : ℝ := L5 * eKf ^ 2 * V ^ 4 + Kstar5 * C2 * V ^ 4
      + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3
      + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3
      + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2
      + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2
      + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd
      + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd
      + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2
      + 2 * Kstar4 * V ^ 3 * Cd with hCBtopdef
  have hCBtop0 : 0 ≤ CBtop := by rw [hCBtopdef]; positivity
  set CB211 : ℝ := L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2
      + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2
      + Kstar4 * eKs * Ce * V ^ 2
      + Kstar3 * V ^ 2 * Cd
      + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce
      + 2 * Kstar3 * V * Cq2 * Cd
      + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2
      + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V
      + 2 * Kstar3 * V * Cq2 * Cd with hCB211def
  have hCB2110 : 0 ≤ CB211 := by rw [hCB211def]; positivity
  set CB22 : ℝ := L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2
      + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2
      + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd
      + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq with hCB22def
  have hCB220 : 0 ≤ CB22 := by rw [hCB22def]; positivity
  set CB31 : ℝ := L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3
      + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V
      + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd
      + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd with hCB31def
  have hCB310 : 0 ≤ CB31 := by rw [hCB31def]; positivity
  refine ⟨CB0 + CBtop + CB211 + CB211 + CB211 + CB211 + CB211 + CB211 + CB22 + CB22 + CB22
      + CB31 + CB31 + CB31 + CB31,
    by linarith [hCB00, hCBtop0, hCB2110, hCB220, hCB310], ?_⟩
  intro t ht

  rw [expJet4Rhs_apply, expJet4Rhs_apply, expJet5Rhs_apply]
  have hd2n : ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))‖ ≤ Kstar2 := hK2v t ht
  have hd3n : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))‖ ≤ Kstar3 := hK3v t ht
  have hd4n : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))‖ ≤ Kstar4 := hK4v t ht
  have hd5n : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))‖ ≤ Kstar5 := hK5v t ht
  have hsep2 : ‖(expTube g gi hC p (v + r) t) - (expTube g gi hC p v t)‖ ≤ nr * eKf := hsep t ht
  have htay2 := (htay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL2_0)
  have htay3 := (hD2tay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL3_0)
  have htay4 := (hD3tay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL4_0)
  have htay5 := (hD4tay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL5_0)
  have hacc0 : ‖(expTube g gi hC p (v + r) t) - (expTube g gi hC p v t) - (Φ t (expJetIota r))‖ ≤ C2 * nr ^ 2 := hacc t ht
  have hPrn : ‖(Φ t (expJetIota r))‖ ≤ eKs * nr := by
    exact clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιr
  have hcyc5 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) :=
    fderiv5_geodesicField_symm_cyc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m))
  have hQa : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhr t) :=
    fderiv4_geodesicField_symm_cyc g gi hC (expTube g gi hC p v t) (Qhr t) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m))
  have hQb : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qkr t) (Φ t (expJetIota l)) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qkr t) :=
    (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Qkr t) (Φ t (expJetIota l)) (Φ t (expJetIota m))).trans
      (fderiv4_geodesicField_symm_cd g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkr t) (Φ t (expJetIota m)))
  have hQc : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlr t) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qlr t) :=
    fderiv4_geodesicField_symm_cd g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlr t) (Φ t (expJetIota m))
  have hhB : ‖h‖ ≤ Bdir := by rw [hBdirdef]; linarith [norm_nonneg k, norm_nonneg l, norm_nonneg m]
  have hkB : ‖k‖ ≤ Bdir := by rw [hBdirdef]; linarith [norm_nonneg h, norm_nonneg l, norm_nonneg m]
  have hlB : ‖l‖ ≤ Bdir := by rw [hBdirdef]; linarith [norm_nonneg h, norm_nonneg k, norm_nonneg m]
  have hmB : ‖m‖ ≤ Bdir := by rw [hBdirdef]; linarith [norm_nonneg h, norm_nonneg k, norm_nonneg l]
  have hPhV : ‖(Φ t (expJetIota h))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιh).trans
      (mul_le_mul_of_nonneg_left hhB heKs0)
  have hPkV : ‖(Φ t (expJetIota k))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιk).trans
      (mul_le_mul_of_nonneg_left hkB heKs0)
  have hPlV : ‖(Φ t (expJetIota l))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιl).trans
      (mul_le_mul_of_nonneg_left hlB heKs0)
  have hPmV : ‖(Φ t (expJetIota m))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιm).trans
      (mul_le_mul_of_nonneg_left hmB heKs0)
  have hPhwV : ‖(Φ' t (expJetIota h))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιh).trans
      (mul_le_mul_of_nonneg_left hhB heKs0)
  have hPkwV : ‖(Φ' t (expJetIota k))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιk).trans
      (mul_le_mul_of_nonneg_left hkB heKs0)
  have hPlwV : ‖(Φ' t (expJetIota l))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιl).trans
      (mul_le_mul_of_nonneg_left hlB heKs0)
  have hPmwV : ‖(Φ' t (expJetIota m))‖ ≤ V := by
    rw [hVdef]
    exact (clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιm).trans
      (mul_le_mul_of_nonneg_left hmB heKs0)
  have hδH : ‖(Φ' t (expJetIota h)) - (Φ t (expJetIota h))‖ ≤ Ddel * nr := by
    have he : (Φ' t (expJetIota h)) - (Φ t (expJetIota h)) = (Φ' t - Φ t) (expJetIota h) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he, hDdeldef]
    calc ‖(Φ' t - Φ t) (expJetIota h)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖h‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _) (by positivity)
      _ ≤ C3 * Bdir * nr := by
          rw [show C3 * nr * ‖h‖ = C3 * ‖h‖ * nr from by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhB hC3_0) hnr0
  have hδK : ‖(Φ' t (expJetIota k)) - (Φ t (expJetIota k))‖ ≤ Ddel * nr := by
    have he : (Φ' t (expJetIota k)) - (Φ t (expJetIota k)) = (Φ' t - Φ t) (expJetIota k) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he, hDdeldef]
    calc ‖(Φ' t - Φ t) (expJetIota k)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) k‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖k‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιk (norm_nonneg _) (by positivity)
      _ ≤ C3 * Bdir * nr := by
          rw [show C3 * nr * ‖k‖ = C3 * ‖k‖ * nr from by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkB hC3_0) hnr0
  have hδL : ‖(Φ' t (expJetIota l)) - (Φ t (expJetIota l))‖ ≤ Ddel * nr := by
    have he : (Φ' t (expJetIota l)) - (Φ t (expJetIota l)) = (Φ' t - Φ t) (expJetIota l) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he, hDdeldef]
    calc ‖(Φ' t - Φ t) (expJetIota l)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) l‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖l‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιl (norm_nonneg _) (by positivity)
      _ ≤ C3 * Bdir * nr := by
          rw [show C3 * nr * ‖l‖ = C3 * ‖l‖ * nr from by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlB hC3_0) hnr0
  have hδM : ‖(Φ' t (expJetIota m)) - (Φ t (expJetIota m))‖ ≤ Ddel * nr := by
    have he : (Φ' t (expJetIota m)) - (Φ t (expJetIota m)) = (Φ' t - Φ t) (expJetIota m) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he, hDdeldef]
    calc ‖(Φ' t - Φ t) (expJetIota m)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) m‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖m‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιm (norm_nonneg _) (by positivity)
      _ ≤ C3 * Bdir * nr := by
          rw [show C3 * nr * ‖m‖ = C3 * ‖m‖ * nr from by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmB hC3_0) hnr0
  have hFQhkV : ‖Qwhk t - Qhk t - Qhkr t‖ ≤ VFq := by
    rw [hVFqdef]
    calc ‖Qwhk t - Qhk t - Qhkr t‖ ≤ ‖Qwhk t - Qhk t‖ + ‖Qhkr t‖ := norm_sub_le _ _
      _ ≤ (‖Qwhk t‖ + ‖Qhk t‖) + ‖Qhkr t‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cq2 + Cq2) + Cq3 := add_le_add (add_le_add (hVwhk t ht) (hVhk t ht)) (hVQhkr t ht)
  have hFQhlV : ‖Qwhl t - Qhl t - Qhlr t‖ ≤ VFq := by
    rw [hVFqdef]
    calc ‖Qwhl t - Qhl t - Qhlr t‖ ≤ ‖Qwhl t - Qhl t‖ + ‖Qhlr t‖ := norm_sub_le _ _
      _ ≤ (‖Qwhl t‖ + ‖Qhl t‖) + ‖Qhlr t‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cq2 + Cq2) + Cq3 := add_le_add (add_le_add (hVwhl t ht) (hVhl t ht)) (hVQhlr t ht)
  have hFQhmV : ‖Qwhm t - Qhm t - Qhmr t‖ ≤ VFq := by
    rw [hVFqdef]
    calc ‖Qwhm t - Qhm t - Qhmr t‖ ≤ ‖Qwhm t - Qhm t‖ + ‖Qhmr t‖ := norm_sub_le _ _
      _ ≤ (‖Qwhm t‖ + ‖Qhm t‖) + ‖Qhmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cq2 + Cq2) + Cq3 := add_le_add (add_le_add (hVwhm t ht) (hVhm t ht)) (hVQhmr t ht)
  have hFQklV : ‖Qwkl t - Qkl t - Qklr t‖ ≤ VFq := by
    rw [hVFqdef]
    calc ‖Qwkl t - Qkl t - Qklr t‖ ≤ ‖Qwkl t - Qkl t‖ + ‖Qklr t‖ := norm_sub_le _ _
      _ ≤ (‖Qwkl t‖ + ‖Qkl t‖) + ‖Qklr t‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cq2 + Cq2) + Cq3 := add_le_add (add_le_add (hVwkl t ht) (hVkl t ht)) (hVQklr t ht)
  have hFQkmV : ‖Qwkm t - Qkm t - Qkmr t‖ ≤ VFq := by
    rw [hVFqdef]
    calc ‖Qwkm t - Qkm t - Qkmr t‖ ≤ ‖Qwkm t - Qkm t‖ + ‖Qkmr t‖ := norm_sub_le _ _
      _ ≤ (‖Qwkm t‖ + ‖Qkm t‖) + ‖Qkmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cq2 + Cq2) + Cq3 := add_le_add (add_le_add (hVwkm t ht) (hVkm t ht)) (hVQkmr t ht)
  have hFQlmV : ‖Qwlm t - Qlm t - Qlmr t‖ ≤ VFq := by
    rw [hVFqdef]
    calc ‖Qwlm t - Qlm t - Qlmr t‖ ≤ ‖Qwlm t - Qlm t‖ + ‖Qlmr t‖ := norm_sub_le _ _
      _ ≤ (‖Qwlm t‖ + ‖Qlm t‖) + ‖Qlmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cq2 + Cq2) + Cq3 := add_le_add (add_le_add (hVwlm t ht) (hVlm t ht)) (hVQlmr t ht)
  have hs1 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhk t) (Qlr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qlr t) (Φ t (expJetIota m)) (Qhk t) :=
    (fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qhk t) (Qlr t)).trans (fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qlr t) (Qhk t))
  have hs2 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhk t) (Qmr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qmr t) (Qhk t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qhk t) (Qmr t)
  have hs3 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhl t) (Qkr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qkr t) (Φ t (expJetIota m)) (Qhl t) :=
    (fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qhl t) (Qkr t)).trans (fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qkr t) (Qhl t))
  have hs4 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhl t) (Qmr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qmr t) (Qhl t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Qhl t) (Qmr t)
  have hs5 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhm t) (Qkr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qkr t) (Φ t (expJetIota l)) (Qhm t) :=
    (fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qhm t) (Qkr t)).trans (fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qkr t) (Qhm t))
  have hs6 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhm t) (Qlr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qlr t) (Qhm t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Qhm t) (Qlr t)
  have hs7 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhr t) (Qkl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota m)) (Qkl t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qhr t) (Qkl t)
  have hs8 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qkl t) (Qmr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qmr t) (Qkl t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Qkl t) (Qmr t)
  have hs9 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhr t) (Qkm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota l)) (Qkm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qhr t) (Qkm t)
  have hs10 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qkm t) (Qlr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qlr t) (Qkm t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Qkm t) (Qlr t)
  have hs11 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhr t) (Qlm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota k)) (Qlm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Qhr t) (Qlm t)
  have hs12 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qlmr t) (Qhk t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhk t) (Qlmr t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qlmr t) (Qhk t)
  have hs13 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qkmr t) (Qhl t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhl t) (Qkmr t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qkmr t) (Qhl t)
  have hs14 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qklr t) (Qhm t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhm t) (Qklr t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qklr t) (Qhm t)
  have hs15 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qklm t) (Qhr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhr t) (Qklm t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qklm t) (Qhr t)
  have hs16 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhlm t) (Qkr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qkr t) (Qhlm t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qhlm t) (Qkr t)
  have hs17 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhkm t) (Qlr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qlr t) (Qhkm t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qhkm t) (Qlr t)
  have hs18 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhkl t) (Qmr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qmr t) (Qhkl t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qhkl t) (Qmr t)
  have hcyc4_hk : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhk t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhk t))
  have hcyc4_hl : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhl t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhl t))
  have hcyc4_hm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhm t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qhm t))
  have hcyc4_kl : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qkl t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qkl t))
  have hcyc4_km : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qkm t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qkm t))
  have hcyc4_lm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qlm t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Qlm t))
  have hsA_klm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Qklm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Qklm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Qklm t)
  have hsA_hlm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Qhlm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qhlm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Qhlm t)
  have hsA_hkm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qhkm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhkm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qhkm t)
  have hsA_hkl : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhkl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhkl t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhkl t)
  exact remAssembly
    (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))
    (Qw t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ' t (expJetIota h)) (Φ' t (expJetIota k)) (Φ' t (expJetIota l)) (Φ' t (expJetIota m)) (Qhk t) (Qhl t) (Qhm t) (Qkl t) (Qkm t) (Qlm t) (Qhr t) (Qkr t) (Qlr t) (Qmr t) (Qwhk t) (Qwhl t) (Qwhm t) (Qwkl t) (Qwkm t) (Qwlm t) (Qhkl t) (Qhkm t) (Qhlm t) (Qklm t) (Qhkr t) (Qhlr t) (Qhmr t) (Qklr t) (Qkmr t) (Qlmr t) (Qwhkl t) (Qwhkm t) (Qwhlm t) (Qwklm t) (Qhklm t) (Qhklr t) (Qhkmr t) (Qhlmr t) (Qklmr t) (expTube g gi hC p v t) (expTube g gi hC p (v + r) t)
    nr eKf eKs L2 L3 L4 L5 C2 Kstar2 Kstar3 Kstar4 Kstar5 V Ddel Cd Ce Cq2 Cq3 Ccr VFq M4
    hnr0 heKf0 heKs0 hL2_0 hL3_0 hL4_0 hL5_0 hC2_0 hKstar20 hKstar30 hKstar40 hKstar50 hV0 hDdel0 hCd0 hCe0 hCq20 hCq30 hCcr0 hVFq0 hM40
    htay2 htay3 htay4 htay5 hacc0 hPrn hd2n hd3n hd4n hd5n
    hPhV hPkV hPlV hPmV hPhwV hPkwV hPlwV hPmwV
    (hVhk t ht) (hVhl t ht) (hVhm t ht) (hVkl t ht) (hVkm t ht) (hVlm t ht)
    (hVwhk t ht) (hVwhl t ht) (hVwhm t ht) (hVwkl t ht) (hVwkm t ht) (hVwlm t ht)
    (hVklm t ht) (hVhlm t ht) (hVhkm t ht) (hVhkl t ht)
    (hVwklm t ht) (hVwhlm t ht) (hVwhkm t ht) (hVwhkl t ht)
    (hVQhkr t ht) (hVQhlr t ht) (hVQhmr t ht) (hVQklr t ht) (hVQkmr t ht) (hVQlmr t ht)
    hδH hδK hδL hδM
    (hQlipTop t ht)
    (hQLhk t ht) (hQLhl t ht) (hQLhm t ht) (hQLkl t ht) (hQLkm t ht) (hQLlm t ht)
    (hQL3klm t ht) (hQL3hlm t ht) (hQL3hkm t ht) (hQL3hkl t ht)
    (hFPh t ht) (hFPk t ht) (hFPl t ht) (hFPm t ht)
    (hFQhk t ht) (hFQhl t ht) (hFQhm t ht) (hFQkl t ht) (hFQkm t ht) (hFQlm t ht)
    (hFQ3klm t ht) (hFQ3hlm t ht) (hFQ3hkm t ht) (hFQ3hkl t ht)
    (hSQhkr t ht) (hSQhlr t ht) (hSQhmr t ht) (hSQklr t ht) (hSQkmr t ht) (hSQlmr t ht)
    hFQhkV hFQhlV hFQhmV hFQklV hFQkmV hFQlmV
    (hqwval t ht)
    hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18
    hcyc5 hQa hQb hQc
    hcyc4_hk hcyc4_hl hcyc4_hm hcyc4_kl hcyc4_km hcyc4_lm
    hsA_klm hsA_hlm hsA_hkm hsA_hkl

end QIQTH.ExpMap
