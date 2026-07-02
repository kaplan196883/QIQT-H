/-
  J4 (HYPOTHESIS_DELETION_PLAN.md) — the formal Deser system: consistency PROPAGATION, honestly.

  BINDING (consult): NO "DeserTower" whose fields posit conservation at every order — that is relabeling,
  forbidden. The honest all-order content is FORMAL-BIANCHI CONSISTENCY PROPAGATION:
  • `FormalDeserSystem` — order-indexed linear operator `L n` and divergence `div n` (order-dependent because
    NONLINEAR PRODUCTS SHIFT MOMENTA: the order-n harmonic lives at total momentum `n•k` — the binding
    harmonic bookkeeping), the PROVEN linear Bianchi `div n ∘ L n = 0`, the order-n source `S n` depending
    only on lower orders (`S_depends_lt`), and ONE carried coefficient field `formalBianchi_step`: the
    divergence of the order-n source is a lower-order-residual combination
    `div n (S n h) = Σ_{j<n} B_{n,j}(L j (h j) − S j h)` — the coefficient-Bianchi content, CARRIED until the
    nonlinear Einstein coefficients are formalized (a named structure field, never an axiom, and NOT a
    per-order conservation posit: it is an IDENTITY in the history, holding whether or not anything solves).
  • `DeserTowerUpTo` — the tower solves through order N (a definition, not data).
  • `next_source_conserved` — THE PROPAGATION THEOREM: if the tower solves through order N, the order-(N+1)
    source is conserved. Conservation is DERIVED, never posited.
  • `extend_of_solver` — given a solver (right inverse of `L n` on conserved sources), the tower extends.
  • `einsteinDeserSystem` — the instantiation with the HELD linearized symbols: `L n = einsteinSymbol (n•k)`,
    `div n = kContract (n•k)`, and the `bianchi` field DISCHARGED by the held `bianchi_einsteinSymbol`
    (the N=1/base-step content, now proven at every harmonic).

  HYPOTHESIS STATUS: the would-be per-order conservation tower (one hypothesis per order) SHRINKS to the
  single coefficient identity `formalBianchi_step`; the linear Bianchi input is DELETED (a held theorem).

  ⚠ Honest scope: this is consistency PROPAGATION — the statement that the Deser bootstrap is formally
  unobstructed GIVEN the coefficient-Bianchi identity; order 2 remains the concrete Deser theorem
  (`DeserRung.deser_selfcoupling_consistent`); the nonlinear Einstein coefficients (and hence a proof of
  `formalBianchi_step` for real gravity) are the cited frontier. NOT a nonlinear completion; NOT QG.
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.LinearizedEinstein
import QIQTH.DeserRung

namespace QIQTH.FormalDeser

open QIQTH.LinEinstein

/-! ## The abstract formal Deser system -/

/-- **The formal Deser system.** Order-indexed linear data with the PROVEN linear Bianchi, a lower-order
    source, and the ONE carried coefficient-Bianchi field. `formalBianchi_step` is an identity in the history
    `h` (it holds whether or not anything solves) — NOT a per-order conservation posit. -/
structure FormalDeserSystem (Field Source Constraint : Type*)
    [AddCommGroup Field] [AddCommGroup Source] [AddCommGroup Constraint] where
  /-- the order-n linearized operator (order-dependent: harmonics shift momenta) -/
  L : ℕ → Field →+ Source
  /-- the order-n divergence -/
  div : ℕ → Source →+ Constraint
  /-- the PROVEN linear Bianchi identity at every order -/
  bianchi : ∀ n f, div n (L n f) = 0
  /-- the order-n nonlinear source built from the history -/
  S : ℕ → (ℕ → Field) → Source
  /-- the source at order n depends only on strictly lower orders -/
  S_depends_lt : ∀ n (h h' : ℕ → Field), (∀ j, j < n → h j = h' j) → S n h = S n h'
  /-- the coefficient-Bianchi maps (lower-order residual → constraint) -/
  bianchiCoeff : ℕ → ℕ → (ℕ → Field) → Source →+ Constraint
  /-- CARRIED (named, one field): the formal-Bianchi identity — the divergence of the order-n source is a
      combination of LOWER-ORDER RESIDUALS (the coefficient-Bianchi content of the nonlinear theory) -/
  formalBianchi_step : ∀ n (h : ℕ → Field),
    div n (S n h) = ∑ j ∈ Finset.range n, bianchiCoeff n j h (L j (h j) - S j h)

variable {Field Source Constraint : Type*}
  [AddCommGroup Field] [AddCommGroup Source] [AddCommGroup Constraint]

/-- **The Deser tower through order `N`**: the order-`j` equation `L j (h j) = S j h` holds for all `j ≤ N`.
    A definition, not data — nothing here posits anything. -/
def FormalDeserSystem.DeserTowerUpTo (D : FormalDeserSystem Field Source Constraint)
    (h : ℕ → Field) (N : ℕ) : Prop :=
  ∀ j, j ≤ N → D.L j (h j) = D.S j h

/-- **J4 PROPAGATION THEOREM — the next source is AUTOMATICALLY conserved.** If the tower solves through
    order `N`, then `div (S_{N+1}) = 0`: every lower-order residual vanishes, so the formal-Bianchi identity
    collapses. Conservation is DERIVED at each order, never posited. -/
theorem FormalDeserSystem.next_source_conserved (D : FormalDeserSystem Field Source Constraint)
    (h : ℕ → Field) (N : ℕ) (htower : D.DeserTowerUpTo h N) :
    D.div (N + 1) (D.S (N + 1) h) = 0 := by
  rw [D.formalBianchi_step (N + 1) h]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [sub_eq_zero.mpr (htower j hjN), map_zero]

/-- **A solver**: a right inverse of `L n` on CONSERVED sources (the gauge-fixed propagator content —
    solvability of the linearized equation with conserved source). -/
structure Solver (D : FormalDeserSystem Field Source Constraint) where
  /-- solve the order-n linear equation -/
  solve : ℕ → Source → Field
  /-- right-inverse property on conserved sources -/
  hsolve : ∀ n s, D.div n s = 0 → D.L n (solve n s) = s

/-- **J4 EXTENSION THEOREM — the tower extends one order.** Given a solver, a tower through order `N`
    extends to order `N+1` by solving for the (automatically conserved) next source; lower orders are
    untouched (`S_depends_lt`). The Deser bootstrap is formally unobstructed. -/
theorem FormalDeserSystem.extend_of_solver (D : FormalDeserSystem Field Source Constraint)
    (σ : Solver D) (h : ℕ → Field) (N : ℕ) (htower : D.DeserTowerUpTo h N) :
    D.DeserTowerUpTo (Function.update h (N + 1) (σ.solve (N + 1) (D.S (N + 1) h))) (N + 1) := by
  intro j hj
  set h' := Function.update h (N + 1) (σ.solve (N + 1) (D.S (N + 1) h)) with hh'
  have hlow : ∀ i, i < j → h' i = h i := by
    intro i hi
    rw [hh', Function.update_apply, if_neg (by omega)]
  have hSj : D.S j h' = D.S j h :=
    D.S_depends_lt j h' h fun i hi => hlow i hi
  rcases Nat.lt_or_ge j (N + 1) with hlt | hge
  · have hjN : j ≤ N := Nat.lt_succ_iff.mp hlt
    have hval : h' j = h j := by
      rw [hh', Function.update_apply, if_neg (by omega)]
    rw [hval, hSj]
    exact htower j hjN
  · have hjeq : j = N + 1 := le_antisymm hj hge
    subst hjeq
    have hval : h' (N + 1) = σ.solve (N + 1) (D.S (N + 1) h) := by
      rw [hh', Function.update_self]
    rw [hval, hSj]
    exact σ.hsolve (N + 1) _ (D.next_source_conserved h N htower)

/-! ## The instantiation with the HELD linearized symbols -/

/-- `einsteinSymbol (n•k)` as an additive map (the held additivity). -/
noncomputable def einsteinL (k : Fin 4 → ℝ) (n : ℕ) :
    Matrix (Fin 4) (Fin 4) ℝ →+ Matrix (Fin 4) (Fin 4) ℝ :=
  AddMonoidHom.mk' (einsteinSymbol ((n : ℝ) • k)) (einsteinSymbol_add ((n : ℝ) • k))

/-- `kContract (n•k)` as an additive map. -/
noncomputable def einsteinDiv (k : Fin 4 → ℝ) (n : ℕ) :
    Matrix (Fin 4) (Fin 4) ℝ →+ (Fin 4 → ℝ) :=
  AddMonoidHom.mk' (fun e ν => kContract ((n : ℝ) • k) e ν)
    (fun e f => funext fun ν => kContract_add ((n : ℝ) • k) e f ν)

/-- **J4 INSTANTIATION — the Einstein formal Deser system at momentum `k`.** `L n = einsteinSymbol (n•k)`,
    `div n = kContract (n•k)` (the order-n harmonic at its CORRECT total momentum — the binding bookkeeping),
    with the `bianchi` field DISCHARGED by the held `bianchi_einsteinSymbol` at every harmonic (the N=1/base
    step, now a theorem at all orders). The nonlinear source data (`S`, `bianchiCoeff`, `formalBianchi_step`)
    stays the CARRIED input — the honest frontier (the nonlinear Einstein coefficients). -/
noncomputable def einsteinDeserSystem (k : Fin 4 → ℝ)
    (S : ℕ → (ℕ → Matrix (Fin 4) (Fin 4) ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (hS : ∀ (n : ℕ) (h h' : ℕ → Matrix (Fin 4) (Fin 4) ℝ), (∀ j, j < n → h j = h' j) → S n h = S n h')
    (bc : ℕ → ℕ → (ℕ → Matrix (Fin 4) (Fin 4) ℝ) →
      (Matrix (Fin 4) (Fin 4) ℝ →+ (Fin 4 → ℝ)))
    (hstep : ∀ (n : ℕ) (h : ℕ → Matrix (Fin 4) (Fin 4) ℝ),
      (fun ν => kContract ((n : ℝ) • k) (S n h) ν)
        = ∑ j ∈ Finset.range n, bc n j h (einsteinSymbol ((j : ℝ) • k) (h j) - S j h)) :
    FormalDeserSystem (Matrix (Fin 4) (Fin 4) ℝ) (Matrix (Fin 4) (Fin 4) ℝ) (Fin 4 → ℝ) where
  L := einsteinL k
  div := einsteinDiv k
  bianchi := fun n f => funext fun ν => bianchi_einsteinSymbol ((n : ℝ) • k) f ν
  S := S
  S_depends_lt := hS
  bianchiCoeff := bc
  formalBianchi_step := hstep

/-- **End-to-end**: in the Einstein instantiation, a tower through order `N` forces the order-(N+1) source to
    be conserved at its harmonic — `kContract ((N+1)•k) (S_{N+1}) = 0` — by the propagation theorem riding
    the held Bianchi identity. -/
theorem einstein_next_source_conserved (k : Fin 4 → ℝ)
    (S : ℕ → (ℕ → Matrix (Fin 4) (Fin 4) ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (hS : ∀ (n : ℕ) (h h' : ℕ → Matrix (Fin 4) (Fin 4) ℝ), (∀ j, j < n → h j = h' j) → S n h = S n h')
    (bc : ℕ → ℕ → (ℕ → Matrix (Fin 4) (Fin 4) ℝ) →
      (Matrix (Fin 4) (Fin 4) ℝ →+ (Fin 4 → ℝ)))
    (hstep : ∀ (n : ℕ) (h : ℕ → Matrix (Fin 4) (Fin 4) ℝ),
      (fun ν => kContract ((n : ℝ) • k) (S n h) ν)
        = ∑ j ∈ Finset.range n, bc n j h (einsteinSymbol ((j : ℝ) • k) (h j) - S j h))
    (h : ℕ → Matrix (Fin 4) (Fin 4) ℝ) (N : ℕ)
    (htower : (einsteinDeserSystem k S hS bc hstep).DeserTowerUpTo h N) (ν : Fin 4) :
    kContract (((N + 1 : ℕ) : ℝ) • k) (S (N + 1) h) ν = 0 := by
  have := (einsteinDeserSystem k S hS bc hstep).next_source_conserved h N htower
  exact congrFun this ν

end QIQTH.FormalDeser
