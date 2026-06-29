#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
QIQT-H — the MINIMAL REALISATION (toy model, SymPy-verified)
============================================================

A *realisation* of QIQT-H is a generative theory whose regional data, encoded into a
finite-capacity microstate space, satisfies the framework's machine-checked boundary
conditions (see QIQT_Foundations_Paper.md §1.1a, "boundary theory / realisations").

The MINIMAL one is: **a single fermionic CAR mode (= one qubit) isometrically embedded
into a finite microstate memory C^N**.  It is the smallest object that exercises *every*
boundary condition, and — being one exact-CAR mode — it fits a finite sector exactly.

This script CONSTRUCTS that toy and VERIFIES, symbolically and exactly, each boundary
condition QIQT-H imposes.  Each check names the corresponding Lean theorem.

Run:  python scripts/qiqth_minimal_realisation.py
"""

import sympy as sp
from sympy import Matrix, Rational, sqrt, log, eye, zeros, simplify

# ----------------------------------------------------------------------------------------
# 0. The microstate memory and its capacity bound  (P4 / FQ: finite capacity)
# ----------------------------------------------------------------------------------------
N = 4                      # dim of the regional microstate space 𝓗_R = C^N (finite capacity)
area = log(N)              # areaTerm = A/4ℓ_P² ; here saturating: log dim 𝓗_R = area
print(f"[0] microstate memory  𝓗_R = C^{N}   (finite capacity; log dim = area = log {N})")

def dagger(M):             # conjugate transpose (entries here are real/rational)
    return M.conjugate().T

ok = True
def check(name, cond, lean):
    global ok
    status = "OK " if cond else "FAIL"
    if not cond:
        ok = False
    print(f"    [{status}] {name:<46} ~ {lean}")

# ----------------------------------------------------------------------------------------
# 1. The field code: ONE fermionic CAR mode  C = C^2  (a qubit)
#    a = lowering, a† = raising ; {a,a†} = 1 on C^2  (exact finite CAR — fits exactly)
# ----------------------------------------------------------------------------------------
a    = Matrix([[0, 1],
               [0, 0]])           # a   : |1> -> |0>
adag = dagger(a)                  # a†  : |0> -> |1>
def anti(X, Y):                   # graded bracket, ε = +1 (anticommutator / CAR)
    return X*Y + Y*X
print("\n[1] field code  C = C^2  (one CAR fermion mode)")
check("CAR  {a,a†} = 1",        anti(a, adag) == eye(2),       "no_finiteDim_CCR (CAR fits; CCR can't)")
check("nilpotent {a,a} = 0",    anti(a, a)   == zeros(2,2),    "encoded_anticomm (ε=1, c=0)")

# ----------------------------------------------------------------------------------------
# 2. The isometric encoding  V : C^2 ↪ C^N   and the CORNER  P = V V†
#    (V = first two columns of the identity: a partial isometry into the memory)
# ----------------------------------------------------------------------------------------
V = zeros(N, 2)
V[0, 0] = 1
V[1, 1] = 1
P = V * dagger(V)                 # code projector / corner unit
def encode(A):                    # ι_V(A) = V A V†   (lands in the corner P·End(C^N)·P)
    return V * A * dagger(V)
print("\n[2] isometry  V : C^2 ↪ C^{}   and corner  P = V V†".format(N))
check("isometry  V† V = 1_2",   dagger(V)*V == eye(2),         "finrank_le_of_codeIsometry")
check("P idempotent  P² = P",   P*P == P,                      "codeProjector_mul_self")
check("P self-adjoint  P† = P", dagger(P) == P,                "codeProjector_conjTranspose")
check("encode(1) = P (NOT 1_N)", (encode(eye(2)) == P) and (P != eye(N)),
      "encode_one  (corner unit, not ambient 1_𝓗 — the audit tripwire)")

# ----------------------------------------------------------------------------------------
# 3. Faithful read-back: encoded record statistics = bare ones   (encoded_npoint / M2)
#    Tr( (VρV†)·(VOV†) ) = Tr(ρ O)   for a code state ρ and observable O
# ----------------------------------------------------------------------------------------
rho = Matrix([[Rational(2,3), 0],
              [0, Rational(1,3)]])        # a code density (Tr = 1)
O   = Matrix([[1, 0], [0, -1]])          # a record observable (e.g. occupation parity)
lhs = (encode(rho) * encode(O)).trace()
rhs = (rho * O).trace()
print("\n[3] faithful read-back through the corner")
check("Tr(VρV†·VOV†) = Tr(ρO)", simplify(lhs - rhs) == 0,      "encoded_record_expectation / encoded_npoint")

# ----------------------------------------------------------------------------------------
# 4. The CAR algebra transports into the CORNER (with unit P, not 1_N)   (encoded_anticomm)
#    {ι(a), ι(a†)} = ι({a,a†}) = ι(1) = P
# ----------------------------------------------------------------------------------------
corner_anti = anti(encode(a), encode(adag))
print("\n[4] CAR transports into the corner")
check("{ι(a),ι(a†)} = P",       corner_anti == P,              "encoded_anticomm  (= ⟨f,g⟩·P)")
check("{ι(a),ι(a†)} ≠ 1_N",     corner_anti != eye(N),         "encoded_CAR_ambient_forces_full (guard)")

# ----------------------------------------------------------------------------------------
# 5. Born from typicality: equiprobable measure over an equal-amplitude fine-graining
#    ψ = Σ_i f_i ,  f_i orthonormal, equal amplitude.  ‖ψ_k‖²/‖ψ‖² = count_k/|I| = |c_k|²
#    (Zurek amplitude→count bridge ; born_from_equiprobability)
# ----------------------------------------------------------------------------------------
m = 6                                   # |I| equal-amplitude atoms  (orthonormal basis of C^m)
sec = [0, 0, 0, 1, 1, 2]                # readout sec : I -> K = {0,1,2}  (a coarse-graining)
Kset = sorted(set(sec))
psi = Matrix([Rational(1) for _ in range(m)])             # ψ = Σ_i e_i  (equal amplitude 1 each)
norm2 = (dagger(psi)*psi)[0]                              # ‖ψ‖² = m
born_uniform = {}                                          # uniform-measure marginal  = count/|I|
born_amp     = {}                                          # squared sector amplitude  = ‖ψ_k‖²/‖ψ‖²
for k in Kset:
    cnt = sum(1 for s in sec if s == k)
    psi_k = Matrix([Rational(1) if sec[i] == k else 0 for i in range(m)])
    born_uniform[k] = Rational(cnt, m)
    born_amp[k]     = ((dagger(psi_k)*psi_k)[0]) / norm2
print("\n[5] Born from equiprobable typicality (Zurek amplitude→count)")
check("uniform marginal = |c_k|² ∀k", all(simplify(born_uniform[k]-born_amp[k]) == 0 for k in Kset),
      "uniform_marginal_eq_sectorAmp_sq / born_from_equiprobability")
check("Born weights sum to 1",       simplify(sum(born_uniform.values()) - 1) == 0,
      "sum_uniform_outcomeMarginal")
print(f"        Born law  p(k) = |c_k|²  =  {{ {', '.join(f'{k}:{born_uniform[k]}' for k in Kset)} }}")

# ----------------------------------------------------------------------------------------
# 6. The holographic AREA FLOOR:  S_vN(ρ) ≤ log dim C ≤ log dim 𝓗_R = area
#    (area_floor_vonNeumann ; the derived theorem, not a postulate)
# ----------------------------------------------------------------------------------------
def vonNeumann(rho_diag):               # rho diagonal with eigenvalues p_i
    return sum(-p*log(p) for p in rho_diag if p != 0)
S_vN = vonNeumann([Rational(2,3), Rational(1,3)])
S_max = vonNeumann([Rational(1,2), Rational(1,2)])        # maximally mixed qubit = log 2 (saturates dim C)
print("\n[6] area floor  S_vN(ρ) ≤ log dim C ≤ log dim 𝓗_R = area")
check("S_vN(ρ) ≤ log dim C = log 2", sp.N(S_vN) <= sp.N(log(2)) + 1e-12, "area_floor_vonNeumann")
check("log dim C ≤ area = log N",    sp.N(log(2)) <= sp.N(area) + 1e-12, "encoded_field_entropy_le_area")
check("max S_vN = log 2 (saturates)",simplify(S_max - log(2)) == 0,      "HolographicCapacityExact (saturating sector)")

# ----------------------------------------------------------------------------------------
# 7. The PHOTON honesty: a truncated bosonic mode CANNOT have exact CCR; the defect is explicit
#    N-level lowering a_N : a e_k = √k e_{k-1} ;  [a,a†] = 1 − N·|N-1⟩⟨N-1|   (D3b)
# ----------------------------------------------------------------------------------------
def truncated_lowering(n):
    M = zeros(n, n)
    for k in range(1, n):
        M[k-1, k] = sqrt(k)              # a e_k = √k e_{k-1}
    return M
print("\n[7] photon honesty: truncated boson — exact CCR impossible, defect explicit")
for n in (2, 3, 4):
    aN = truncated_lowering(n)
    comm = aN*dagger(aN) - dagger(aN)*aN          # [a,a†]
    top = zeros(n, n); top[n-1, n-1] = 1          # |N-1⟩⟨N-1|
    defect_form = eye(n) - n*top                  # 1 − N·|top⟩⟨top|
    tr0 = (comm).trace()
    check(f"N={n}: [a,a†] = 1 − {n}·|top⟩⟨top|", simplify(comm - defect_form) == zeros(n,n),
          "truncated_ladder_commutator")
    check(f"N={n}: Tr[a,a†] = 0 (≠ {n} = dim)",  simplify(tr0) == 0,
          "no_finiteDim_CCR (exact CCR impossible)")

# ----------------------------------------------------------------------------------------
print("\n" + "="*78)
print("RESULT:", "ALL BOUNDARY CONDITIONS SATISFIED — this toy is a realisation of QIQT-H."
      if ok else "SOME CHECK FAILED.")
print("="*78)
print("""
Minimal realisation = one CAR fermion mode (a qubit code C^2) isometrically embedded
into a finite microstate memory C^N.  It satisfies, exactly:
  finite capacity (P4) · faithful corner encoding · CAR in the corner (unit P, not 1_N)
  · Born from equiprobable typicality · area floor S_vN ≤ log dim ≤ area
  · and it respects the photon no-go (a truncated boson carries the explicit −N defect).
What it does NOT do (and a realisation need not, at this minimal level): supply interactions,
gauge dynamics, a spacetime metric, or the value of G — those are the generative frontiers.
""")
import sys
sys.exit(0 if ok else 1)
