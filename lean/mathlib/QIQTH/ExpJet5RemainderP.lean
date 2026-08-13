/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemainderB
import QIQTH.ExpJet5Prereq
import QIQTH.ExpJet4FundBounds
import QIQTH.ExpJet5RemAssemblyDir
import QIQTH.ExpJet5RemFactor

/-!
# Jet_5 quadratic remainder bound -- DIRECTIONAL wrapper `_P` (rung J5-5c)

Concrete directional wrapper `expJet5_remainder_quadratic_bound_P`: the one-Frechet-order-up mirror
of the order-4 `expJet4_remainder_quadratic_bound'`.  Same geometric setup as the non-directional
`expJet5_remainder_quadratic_bound` (tube membership, fderiv atoms, the eighteen `fderiv`-symmetry
facts), but every value / two-point / residual / Lipschitz feeder is carried with its OWN directional
scale (`‖Qhk t‖ ≤ Cq2·‖h‖·‖k‖`, `‖Qhkr t‖ ≤ Cq3·‖h‖·‖k‖`, ...).  Closes through the abstract
directional assembly `remAssembly_dir`, whose fifteen per-direction block constants are folded into
`C · ‖h‖·‖k‖·‖l‖·‖m‖` by the isolated pure-real ring lemma `factor_hklm`.

## Honest firewall (binding)

Proves ONLY the directional quadratic-remainder wrapper (`_P` layer).  Does NOT prove
`expJet5_remainder_quadratic_bound_unif`, `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the
heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).  All strictly-lower-order INPUTS are carried as
explicit numbered hypotheses, exactly as in the order-4 mirror.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 25600000
set_option maxRecDepth 65536
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 2000000

variable {n : ℕ}

set_option maxHeartbeats 25600000 in
/-- **Jet_5 directional quadratic remainder bound** (`_P`).  Mirror of
    `expJet4_remainder_quadratic_bound'`, one Frechet order up. -/
theorem expJet5_remainder_quadratic_bound_P (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hQlipTop : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qw t - Qhklm t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖)
    (hFPh : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhr t‖ ≤ Cd * ‖h‖ * ‖r‖ ^ 2)
    (hFPk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkr t‖ ≤ Cd * ‖k‖ * ‖r‖ ^ 2)
    (hFPl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota l) - Φ t (expJetIota l) - Qlr t‖ ≤ Cd * ‖l‖ * ‖r‖ ^ 2)
    (hFPm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota m) - Φ t (expJetIota m) - Qmr t‖ ≤ Cd * ‖m‖ * ‖r‖ ^ 2)
    (hVhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖)
    (hVhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖)
    (hVhm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhm t‖ ≤ Cq2 * ‖h‖ * ‖m‖)
    (hVkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖)
    (hVkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qkm t‖ ≤ Cq2 * ‖k‖ * ‖m‖)
    (hVlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qlm t‖ ≤ Cq2 * ‖l‖ * ‖m‖)
    (hVwhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖)
    (hVwhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖)
    (hVwhm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhm t‖ ≤ Cq2 * ‖h‖ * ‖m‖)
    (hVwkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖)
    (hVwkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkm t‖ ≤ Cq2 * ‖k‖ * ‖m‖)
    (hVwlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwlm t‖ ≤ Cq2 * ‖l‖ * ‖m‖)
    (hQLhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhk t - Qhk t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖r‖)
    (hQLhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhl t - Qhl t‖ ≤ Ce * ‖h‖ * ‖l‖ * ‖r‖)
    (hQLhm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhm t - Qhm t‖ ≤ Ce * ‖h‖ * ‖m‖ * ‖r‖)
    (hQLkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkl t - Qkl t‖ ≤ Ce * ‖k‖ * ‖l‖ * ‖r‖)
    (hQLkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkm t - Qkm t‖ ≤ Ce * ‖k‖ * ‖m‖ * ‖r‖)
    (hQLlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwlm t - Qlm t‖ ≤ Ce * ‖l‖ * ‖m‖ * ‖r‖)
    (hFQhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhk t - Qhk t - Qhkr t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖r‖ ^ 2)
    (hFQhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhl t - Qhl t - Qhlr t‖ ≤ Cd * ‖h‖ * ‖l‖ * ‖r‖ ^ 2)
    (hFQhm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhm t - Qhm t - Qhmr t‖ ≤ Cd * ‖h‖ * ‖m‖ * ‖r‖ ^ 2)
    (hFQkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkl t - Qkl t - Qklr t‖ ≤ Cd * ‖k‖ * ‖l‖ * ‖r‖ ^ 2)
    (hFQkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkm t - Qkm t - Qkmr t‖ ≤ Cd * ‖k‖ * ‖m‖ * ‖r‖ ^ 2)
    (hFQlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwlm t - Qlm t - Qlmr t‖ ≤ Cd * ‖l‖ * ‖m‖ * ‖r‖ ^ 2)
    (hVklm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qklm t‖ ≤ Cq3 * ‖k‖ * ‖l‖ * ‖m‖)
    (hVhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhlm t‖ ≤ Cq3 * ‖h‖ * ‖l‖ * ‖m‖)
    (hVhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhkm t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖m‖)
    (hVhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhkl t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖l‖)
    (hVwklm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwklm t‖ ≤ Cq3 * ‖k‖ * ‖l‖ * ‖m‖)
    (hVwhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhlm t‖ ≤ Cq3 * ‖h‖ * ‖l‖ * ‖m‖)
    (hVwhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkm t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖m‖)
    (hVwhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkl t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖l‖)
    (hQL3klm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwklm t - Qklm t‖ ≤ Ce * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖)
    (hQL3hlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhlm t - Qhlm t‖ ≤ Ce * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖)
    (hQL3hkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkm t - Qhkm t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖)
    (hQL3hkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkl t - Qhkl t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖)
    (hFQ3klm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwklm t - Qklm t - Qklmr t‖ ≤ Cd * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2)
    (hFQ3hlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhlm t - Qhlm t - Qhlmr t‖ ≤ Cd * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2)
    (hFQ3hkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkm t - Qhkm t - Qhkmr t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖ ^ 2)
    (hFQ3hkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkl t - Qhkl t - Qhklr t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖ ^ 2)
    (hVQhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhkr t‖ ≤ Cq3 * ‖h‖ * ‖k‖)
    (hVQhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhlr t‖ ≤ Cq3 * ‖h‖ * ‖l‖)
    (hVQhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhmr t‖ ≤ Cq3 * ‖h‖ * ‖m‖)
    (hVQklr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qklr t‖ ≤ Cq3 * ‖k‖ * ‖l‖)
    (hVQkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qkmr t‖ ≤ Cq3 * ‖k‖ * ‖m‖)
    (hVQlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qlmr t‖ ≤ Cq3 * ‖l‖ * ‖m‖)
    (hSQhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhkr t‖ ≤ Ccr * ‖h‖ * ‖k‖ * ‖r‖)
    (hSQhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhlr t‖ ≤ Ccr * ‖h‖ * ‖l‖ * ‖r‖)
    (hSQhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qhmr t‖ ≤ Ccr * ‖h‖ * ‖m‖ * ‖r‖)
    (hSQklr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qklr t‖ ≤ Ccr * ‖k‖ * ‖l‖ * ‖r‖)
    (hSQkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qkmr t‖ ≤ Ccr * ‖k‖ * ‖m‖ * ‖r‖)
    (hSQlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qlmr t‖ ≤ Ccr * ‖l‖ * ‖m‖ * ‖r‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))
           - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qw t)
         + (expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t
            - expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t
            - expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)‖
        ≤ C * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2 := by
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
  set Mc : ℝ := (Kstar4 * eKs ^ 4
      + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2
      + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2
      + Kstar2 * Cq2 ^ 2 + Kstar2 * Cq2 ^ 2 + Kstar2 * Cq2 ^ 2
      + Kstar2 * eKs * Cq3 + Kstar2 * eKs * Cq3 + Kstar2 * eKs * Cq3 + Kstar2 * eKs * Cq3)
      * Real.exp Kstar with hMcdef
  have hMc0 : 0 ≤ Mc := by rw [hMcdef]; positivity
  have hqwval := expJet4Fund_value_bound_Icc g gi hC p (v + r) Φ'
      Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m
      Kstar Kstar4 Kstar3 Kstar2 eKs
      (Cq2 * ‖h‖ * ‖k‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖k‖ * ‖l‖) (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖l‖ * ‖m‖)
      (Cq3 * ‖h‖ * ‖k‖ * ‖l‖) (Cq3 * ‖h‖ * ‖k‖ * ‖m‖) (Cq3 * ‖h‖ * ‖l‖ * ‖m‖) (Cq3 * ‖k‖ * ‖l‖ * ‖m‖)
      hKstar0 hKstar40 hKstar30 hKstar20 heKs0 hKstarw hK4w hK3w hK2w hΦ'norm
      hVwhk hVwhl hVwhm hVwkl hVwkm hVwlm hVwhkl hVwhkm hVwhlm hVwklm Qw hQw0 hQwd
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
  refine ⟨3*C2*Cq2^2*Kstar3 + 6*C2*Cq2*Kstar4*eKs^2 + 4*C2*Cq3*Kstar3*eKs + C2*Kstar2*Mc + C2*Kstar5*eKs^4 + 3*Ccr^2*Kstar2 + 6*Cd*Cq2*Kstar2 + 48*Cd*Cq2*Kstar3*eKs + 18*Cd*Cq3*Kstar2 + 3*Cd*Kstar2*VFq + 4*Cd*Kstar2*eKs + 6*Cd*Kstar3*eKs^2 + 16*Cd*Kstar4*eKs^3 + 6*C3^2*Cq2*Kstar3 + 6*C3^2*Kstar4*eKs^2 + 4*C3*Ce*Kstar2 + 12*C3*Ce*Kstar3*eKs + 12*C3*Cq2*Kstar4*eKs^2 + 4*C3*Cq3*Kstar3*eKs + 4*C3*Kstar5*eKs^4 + 6*Ce*Cq2*Kstar3*eKs + 4*Ce*Kstar3*eKs^2 + 6*Ce*Kstar4*eKs^3 + Ce*Kstar2*eKs + 3*Cq2^2*L3*eKf^2 + 6*Cq2*L4*eKf^2*eKs^2 + 4*Cq3*L3*eKf^2*eKs + L2*Mc*eKf^2 + L5*eKf^2*eKs^4, by positivity, ?_⟩
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
  have hqwM4 : ‖Qw t‖ ≤ Mc * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
    (hqwval t ht).trans (le_of_eq (by rw [hMcdef]; ring))
  have hPhV : ‖(Φ t (expJetIota h))‖ ≤ eKs * ‖h‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιh
  have hPkV : ‖(Φ t (expJetIota k))‖ ≤ eKs * ‖k‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιk
  have hPlV : ‖(Φ t (expJetIota l))‖ ≤ eKs * ‖l‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιl
  have hPmV : ‖(Φ t (expJetIota m))‖ ≤ eKs * ‖m‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιm
  have hPhwV : ‖(Φ' t (expJetIota h))‖ ≤ eKs * ‖h‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιh
  have hPkwV : ‖(Φ' t (expJetIota k))‖ ≤ eKs * ‖k‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιk
  have hPlwV : ‖(Φ' t (expJetIota l))‖ ≤ eKs * ‖l‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιl
  have hPmwV : ‖(Φ' t (expJetIota m))‖ ≤ eKs * ‖m‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιm
  have hδH : ‖(Φ' t (expJetIota h)) - (Φ t (expJetIota h))‖ ≤ C3 * ‖h‖ * nr := by
    have he : (Φ' t (expJetIota h)) - (Φ t (expJetIota h)) = (Φ' t - Φ t) (expJetIota h) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota h)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖h‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _) (by positivity)
      _ = C3 * ‖h‖ * nr := by ring
  have hδK : ‖(Φ' t (expJetIota k)) - (Φ t (expJetIota k))‖ ≤ C3 * ‖k‖ * nr := by
    have he : (Φ' t (expJetIota k)) - (Φ t (expJetIota k)) = (Φ' t - Φ t) (expJetIota k) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota k)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) k‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖k‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιk (norm_nonneg _) (by positivity)
      _ = C3 * ‖k‖ * nr := by ring
  have hδL : ‖(Φ' t (expJetIota l)) - (Φ t (expJetIota l))‖ ≤ C3 * ‖l‖ * nr := by
    have he : (Φ' t (expJetIota l)) - (Φ t (expJetIota l)) = (Φ' t - Φ t) (expJetIota l) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota l)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) l‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖l‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιl (norm_nonneg _) (by positivity)
      _ = C3 * ‖l‖ * nr := by ring
  have hδM : ‖(Φ' t (expJetIota m)) - (Φ t (expJetIota m))‖ ≤ C3 * ‖m‖ * nr := by
    have he : (Φ' t (expJetIota m)) - (Φ t (expJetIota m)) = (Φ' t - Φ t) (expJetIota m) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota m)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) m‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖m‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιm (norm_nonneg _) (by positivity)
      _ = C3 * ‖m‖ * nr := by ring
  have hFQhkV : ‖Qwhk t - Qhk t - Qhkr t‖ ≤ VFq * ‖h‖ * ‖k‖ := by
    have hb : ‖Qwhk t - Qhk t - Qhkr t‖
        ≤ (Cq2 * ‖h‖ * ‖k‖ + Cq2 * ‖h‖ * ‖k‖) + Cq3 * ‖h‖ * ‖k‖ := by
      calc ‖Qwhk t - Qhk t - Qhkr t‖ ≤ ‖Qwhk t - Qhk t‖ + ‖Qhkr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwhk t‖ + ‖Qhk t‖) + ‖Qhkr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖h‖ * ‖k‖ + Cq2 * ‖h‖ * ‖k‖) + Cq3 * ‖h‖ * ‖k‖ :=
            add_le_add (add_le_add (hVwhk t ht) (hVhk t ht)) (hVQhkr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQhlV : ‖Qwhl t - Qhl t - Qhlr t‖ ≤ VFq * ‖h‖ * ‖l‖ := by
    have hb : ‖Qwhl t - Qhl t - Qhlr t‖
        ≤ (Cq2 * ‖h‖ * ‖l‖ + Cq2 * ‖h‖ * ‖l‖) + Cq3 * ‖h‖ * ‖l‖ := by
      calc ‖Qwhl t - Qhl t - Qhlr t‖ ≤ ‖Qwhl t - Qhl t‖ + ‖Qhlr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwhl t‖ + ‖Qhl t‖) + ‖Qhlr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖h‖ * ‖l‖ + Cq2 * ‖h‖ * ‖l‖) + Cq3 * ‖h‖ * ‖l‖ :=
            add_le_add (add_le_add (hVwhl t ht) (hVhl t ht)) (hVQhlr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQhmV : ‖Qwhm t - Qhm t - Qhmr t‖ ≤ VFq * ‖h‖ * ‖m‖ := by
    have hb : ‖Qwhm t - Qhm t - Qhmr t‖
        ≤ (Cq2 * ‖h‖ * ‖m‖ + Cq2 * ‖h‖ * ‖m‖) + Cq3 * ‖h‖ * ‖m‖ := by
      calc ‖Qwhm t - Qhm t - Qhmr t‖ ≤ ‖Qwhm t - Qhm t‖ + ‖Qhmr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwhm t‖ + ‖Qhm t‖) + ‖Qhmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖h‖ * ‖m‖ + Cq2 * ‖h‖ * ‖m‖) + Cq3 * ‖h‖ * ‖m‖ :=
            add_le_add (add_le_add (hVwhm t ht) (hVhm t ht)) (hVQhmr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQklV : ‖Qwkl t - Qkl t - Qklr t‖ ≤ VFq * ‖k‖ * ‖l‖ := by
    have hb : ‖Qwkl t - Qkl t - Qklr t‖
        ≤ (Cq2 * ‖k‖ * ‖l‖ + Cq2 * ‖k‖ * ‖l‖) + Cq3 * ‖k‖ * ‖l‖ := by
      calc ‖Qwkl t - Qkl t - Qklr t‖ ≤ ‖Qwkl t - Qkl t‖ + ‖Qklr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwkl t‖ + ‖Qkl t‖) + ‖Qklr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖k‖ * ‖l‖ + Cq2 * ‖k‖ * ‖l‖) + Cq3 * ‖k‖ * ‖l‖ :=
            add_le_add (add_le_add (hVwkl t ht) (hVkl t ht)) (hVQklr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQkmV : ‖Qwkm t - Qkm t - Qkmr t‖ ≤ VFq * ‖k‖ * ‖m‖ := by
    have hb : ‖Qwkm t - Qkm t - Qkmr t‖
        ≤ (Cq2 * ‖k‖ * ‖m‖ + Cq2 * ‖k‖ * ‖m‖) + Cq3 * ‖k‖ * ‖m‖ := by
      calc ‖Qwkm t - Qkm t - Qkmr t‖ ≤ ‖Qwkm t - Qkm t‖ + ‖Qkmr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwkm t‖ + ‖Qkm t‖) + ‖Qkmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖k‖ * ‖m‖ + Cq2 * ‖k‖ * ‖m‖) + Cq3 * ‖k‖ * ‖m‖ :=
            add_le_add (add_le_add (hVwkm t ht) (hVkm t ht)) (hVQkmr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQlmV : ‖Qwlm t - Qlm t - Qlmr t‖ ≤ VFq * ‖l‖ * ‖m‖ := by
    have hb : ‖Qwlm t - Qlm t - Qlmr t‖
        ≤ (Cq2 * ‖l‖ * ‖m‖ + Cq2 * ‖l‖ * ‖m‖) + Cq3 * ‖l‖ * ‖m‖ := by
      calc ‖Qwlm t - Qlm t - Qlmr t‖ ≤ ‖Qwlm t - Qlm t‖ + ‖Qlmr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwlm t‖ + ‖Qlm t‖) + ‖Qlmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖l‖ * ‖m‖ + Cq2 * ‖l‖ * ‖m‖) + Cq3 * ‖l‖ * ‖m‖ :=
            add_le_add (add_le_add (hVwlm t ht) (hVlm t ht)) (hVQlmr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
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
  refine (remAssembly_dir
    (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))
    (Qw t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ' t (expJetIota h)) (Φ' t (expJetIota k)) (Φ' t (expJetIota l)) (Φ' t (expJetIota m)) (Qhk t) (Qhl t) (Qhm t) (Qkl t) (Qkm t) (Qlm t) (Qhr t) (Qkr t) (Qlr t) (Qmr t) (Qwhk t) (Qwhl t) (Qwhm t) (Qwkl t) (Qwkm t) (Qwlm t) (Qhkl t) (Qhkm t) (Qhlm t) (Qklm t) (Qhkr t) (Qhlr t) (Qhmr t) (Qklr t) (Qkmr t) (Qlmr t) (Qwhkl t) (Qwhkm t) (Qwhlm t) (Qwklm t) (Qhklm t) (Qhklr t) (Qhkmr t) (Qhlmr t) (Qklmr t) (expTube g gi hC p v t) (expTube g gi hC p (v + r) t)
    nr eKf eKs L2 L3 L4
    L5 C2 Kstar2 Kstar3 Kstar4 Kstar5
    (Mc * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) (eKs * ‖h‖) (eKs * ‖k‖) (eKs * ‖l‖) (eKs * ‖m‖)
    (C3 * ‖h‖) (C3 * ‖k‖) (C3 * ‖l‖) (C3 * ‖m‖) (Cd * ‖h‖) (Cd * ‖k‖)
    (Cd * ‖l‖) (Cd * ‖m‖) (Cq2 * ‖h‖ * ‖k‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖k‖ * ‖l‖)
    (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖) (Ce * ‖h‖ * ‖l‖) (Ce * ‖h‖ * ‖m‖) (Ce * ‖k‖ * ‖l‖)
    (Ce * ‖k‖ * ‖m‖) (Ce * ‖l‖ * ‖m‖) (Cd * ‖h‖ * ‖k‖) (Cd * ‖h‖ * ‖l‖) (Cd * ‖h‖ * ‖m‖) (Cd * ‖k‖ * ‖l‖)
    (Cd * ‖k‖ * ‖m‖) (Cd * ‖l‖ * ‖m‖) (Cq3 * ‖h‖ * ‖k‖) (Cq3 * ‖h‖ * ‖l‖) (Cq3 * ‖h‖ * ‖m‖) (Cq3 * ‖k‖ * ‖l‖)
    (Cq3 * ‖k‖ * ‖m‖) (Cq3 * ‖l‖ * ‖m‖) (Ccr * ‖h‖ * ‖k‖) (Ccr * ‖h‖ * ‖l‖) (Ccr * ‖h‖ * ‖m‖) (Ccr * ‖k‖ * ‖l‖)
    (Ccr * ‖k‖ * ‖m‖) (Ccr * ‖l‖ * ‖m‖) (VFq * ‖h‖ * ‖k‖) (VFq * ‖h‖ * ‖l‖) (VFq * ‖h‖ * ‖m‖) (VFq * ‖k‖ * ‖l‖)
    (VFq * ‖k‖ * ‖m‖) (VFq * ‖l‖ * ‖m‖) (Cq3 * ‖k‖ * ‖l‖ * ‖m‖) (Cq3 * ‖h‖ * ‖l‖ * ‖m‖) (Cq3 * ‖h‖ * ‖k‖ * ‖m‖) (Cq3 * ‖h‖ * ‖k‖ * ‖l‖)
    (Ce * ‖k‖ * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖ * ‖l‖) (Cd * ‖k‖ * ‖l‖ * ‖m‖) (Cd * ‖h‖ * ‖l‖ * ‖m‖)
    (Cd * ‖h‖ * ‖k‖ * ‖m‖) (Cd * ‖h‖ * ‖k‖ * ‖l‖)
    hnr0 heKf0 heKs0 hL2_0
    hL3_0 hL4_0 hL5_0 hC2_0
    hKstar20 hKstar30 hKstar40 hKstar50
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hMc0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg heKs0 (norm_nonneg h)) (mul_nonneg heKs0 (norm_nonneg k))
    (mul_nonneg heKs0 (norm_nonneg l)) (mul_nonneg heKs0 (norm_nonneg m)) (mul_nonneg hC3_0 (norm_nonneg h)) (mul_nonneg hC3_0 (norm_nonneg k))
    (mul_nonneg hC3_0 (norm_nonneg l)) (mul_nonneg hC3_0 (norm_nonneg m)) (mul_nonneg hCd0 (norm_nonneg h)) (mul_nonneg hCd0 (norm_nonneg k))
    (mul_nonneg hCd0 (norm_nonneg l)) (mul_nonneg hCd0 (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg h)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCq20 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg k)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCe0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg k)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCq30 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg h)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg k)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l))
    htay2 htay3 htay4 htay5
    hacc0 hPrn hd2n hd3n
    hd4n hd5n hqwM4 (hQlipTop t ht)
    hPhV hPkV hPlV hPmV
    hPhwV hPkwV hPlwV hPmwV
    hδH hδK hδL hδM
    (hFPh t ht) (hFPk t ht) (hFPl t ht) (hFPm t ht)
    (hVhk t ht) (hVhl t ht) (hVhm t ht) (hVkl t ht)
    (hVkm t ht) (hVlm t ht) (hVwhk t ht) (hVwhl t ht)
    (hVwhm t ht) (hVwkl t ht) (hVwkm t ht) (hVwlm t ht)
    (hQLhk t ht) (hQLhl t ht) (hQLhm t ht) (hQLkl t ht)
    (hQLkm t ht) (hQLlm t ht) (hFQhk t ht) (hFQhl t ht)
    (hFQhm t ht) (hFQkl t ht) (hFQkm t ht) (hFQlm t ht)
    (hVQhkr t ht) (hVQhlr t ht) (hVQhmr t ht) (hVQklr t ht)
    (hVQkmr t ht) (hVQlmr t ht) (hSQhkr t ht) (hSQhlr t ht)
    (hSQhmr t ht) (hSQklr t ht) (hSQkmr t ht) (hSQlmr t ht)
    hFQhkV hFQhlV hFQhmV hFQklV
    hFQkmV hFQlmV (hVklm t ht) (hVhlm t ht)
    (hVhkm t ht) (hVhkl t ht) (hVwklm t ht) (hVwhlm t ht)
    (hVwhkm t ht) (hVwhkl t ht) (hQL3klm t ht) (hQL3hlm t ht)
    (hQL3hkm t ht) (hQL3hkl t ht) (hFQ3klm t ht) (hFQ3hlm t ht)
    (hFQ3hkm t ht) (hFQ3hkl t ht)
    hs1 hs2 hs3 hs4 hs5 hs6
    hs7 hs8 hs9 hs10 hs11 hs12
    hs13 hs14 hs15 hs16 hs17 hs18
    hcyc5 hQa hQb hQc hcyc4_hk hcyc4_hl
    hcyc4_hm hcyc4_kl hcyc4_km hcyc4_lm hsA_klm hsA_hlm
    hsA_hkm hsA_hkl).trans ?_
  rw [factor_hklm eKf eKs L2 L3 L4 L5 C2 Kstar2 Kstar3 Kstar4 Kstar5 C3 Cd Cq2 Cq3 Ce Ccr VFq Mc Ce ‖h‖ ‖k‖ ‖l‖ ‖m‖]
  exact le_of_eq (by ring)

end QIQTH.ExpMap
