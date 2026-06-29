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
# 8. TOY (a) — LOCALITY (microcausality, P3): disjoint regions' observables commute, and the
#    encoding preserves it.  Two modes as a tensor bipartition C^2 ⊗ C^2 = C^4.  Since encode is
#    a ⋆-homomorphism, [ι(O_A), ι(O_B)] = ι([O_A, O_B]) = ι(0) = 0 whenever the bare ones commute.
# ----------------------------------------------------------------------------------------
def kron(X, Y):
    rx, cx = X.shape; ry, cy = Y.shape
    Mk = zeros(rx*ry, cx*cy)
    for i in range(rx):
        for j in range(cx):
            Mk[i*ry:(i+1)*ry, j*cy:(j+1)*cy] = X[i, j] * Y
    return Mk

print("\n[8] TOY (a) — locality: disjoint regions commute, preserved by the encoding")
I2 = eye(2)
OA = Matrix([[0, 1], [1, 0]])           # an A-region observable (X)
OB = Matrix([[1, 0], [0, -1]])          # a B-region observable (Z)
OA_full = kron(OA, I2)                  # O_A ⊗ 1   (region A of the C^2⊗C^2 bipartition)
OB_full = kron(I2, OB)                  # 1 ⊗ O_B   (region B)
comm_bare = OA_full*OB_full - OB_full*OA_full
check("[O_A⊗1, 1⊗O_B] = 0 (bare)", comm_bare == zeros(4, 4), "microcausality (P3)")
Mmem = 6                                 # embed the two-mode code C^4 into a bigger memory C^6
V2 = zeros(Mmem, 4)
for i in range(4):
    V2[i, i] = 1
def enc2(A):
    return V2 * A * dagger(V2)
comm_corner = enc2(OA_full)*enc2(OB_full) - enc2(OB_full)*enc2(OA_full)
check("[ι(O_A), ι(O_B)] = 0 (corner)", comm_corner == zeros(Mmem, Mmem),
      "encode_mul (homomorphism preserves locality)")
check("= ι([O_A,O_B]) = ι(0)", comm_corner == enc2(comm_bare), "encoded_npoint")

# ----------------------------------------------------------------------------------------
# 9. TOY (b) — TENSOR-NETWORK / RT side (Track B): a 3-node weighted graph.  cut = the AREA
#    primitive (NOT a metric), with purity S(A)=S(Aᶜ) and subadditivity; the Ryu–Takayanagi
#    inequality S_vN(ρ_A) ≤ cut(A); and min-cut violating the triangle inequality.
# ----------------------------------------------------------------------------------------
print("\n[9] TOY (b) — 3-node tensor network: cut=area, S_vN ≤ cut, min-cut ≠ metric")
verts = [0, 1, 2]
wedge = {(0, 1): sp.Integer(1), (1, 2): sp.Integer(1), (0, 2): sp.Integer(4)}   # symmetric weights
def W(i, j):
    return sp.Integer(0) if i == j else wedge[(min(i, j), max(i, j))]
def cut(S):                              # cut(S) = Σ_{i∈S} Σ_{j∉S} w(i,j)   (the B2 area primitive)
    Sc = [v for v in verts if v not in S]
    return sum(W(i, j) for i in S for j in Sc)
check("cut purity  cut(S) = cut(Sᶜ)",
      all(cut([v]) == cut([u for u in verts if u != v]) for v in verts), "cut_compl  (S(A)=S(Aᶜ))")
check("cut subadditivity (disjoint)", cut([0]) + cut([1]) >= cut([0, 1]), "cut_union_le")
check("cut nonneg", all(cut(S) >= 0 for S in ([0], [1], [2], [0, 1], [0, 2], [1, 2])), "cut_nonneg")

def mincut(i, j):                        # min over bipartitions separating i from j
    best = None
    for bits in range(1, 2**3 - 1):
        S = [v for v in verts if (bits >> v) & 1]
        if i in S and j not in S:
            c = cut(S)
            best = c if best is None else min(best, c)
    return best
lam = {(0, 1): mincut(0, 1), (1, 2): mincut(1, 2), (0, 2): mincut(0, 2)}
check("min-cut violates triangle (λ02 > λ01+λ12)", lam[(0, 2)] > lam[(0, 1)] + lam[(1, 2)],
      "minCut_area_not_metric")

S_A  = vonNeumann([Rational(2, 3), Rational(1, 3)])     # region-A reduced entropy (one bond, dim 2)
cutA = log(2)                                            # cut(A) = log(bond dimension) = log 2
check("RT inequality  S_vN(ρ_A) ≤ cut(A) = log 2", sp.N(S_A) <= sp.N(cutA) + 1e-12,
      "entropy_le_cut")
print(f"        min-cuts: λ(0,1)={lam[(0,1)]}, λ(1,2)={lam[(1,2)]}, λ(0,2)={lam[(0,2)]}"
      f"   →   {lam[(0,2)]} > {lam[(0,1)]+lam[(1,2)]}  (so min-cut is NOT a metric)")

# ----------------------------------------------------------------------------------------
# 10. TOY (c) — the THERMAL half in finite form (as far as finite objects reach toward GR).
#     A finite modular/Gibbs state has a genuine temperature (finite KMS, D6); the entanglement
#     first law δS = δ⟨K⟩ is exact; and with the modular Hamiltonian ∝ area (K = η·A_op, the
#     BW/edge identification) it gives δS = η δA — the entropy–area VARIATION Jacobson needs.
#     This is the half a finite microstate count, equipped with a modular flow, CAN supply.
#     It still does NOT give the Einstein equations: those need the continuum smooth-background
#     Raychaudhuri step δA ↔ T_kk, which no finite toy can reach (the honest checkpoint).
# ----------------------------------------------------------------------------------------
print("\n[10] TOY (c) — thermal half: finite modular/Gibbs + KMS + first law → δS = η δA")

# (i) finite modular flow + KMS (D6): φ(A·σ_{-i}(B)) = φ(B A), σ_{-i}(B) = ρ B ρ⁻¹, φ(X)=Tr(ρX)
rho_g = sp.diag(Rational(1,2), Rational(1,3), Rational(1,6))      # a faithful finite Gibbs state
rho_gi = rho_g.inv()
Amat = Matrix([[0,1,0],[2,0,1],[0,3,0]])
Bmat = Matrix([[1,0,2],[0,1,0],[1,0,0]])
kms_lhs = (rho_g*Amat*(rho_g*Bmat*rho_gi)).trace()
kms_rhs = (rho_g*Bmat*Amat).trace()
check("finite KMS  φ(A·σ₋ᵢ(B)) = φ(B A)", simplify(kms_lhs - kms_rhs) == 0, "finite_KMS (D6)")

# (ii) entanglement first law δS = δ⟨K⟩, exact, around a reference Gibbs state (eigenbasis)
p1, p2, d1, d2, s, eta, a1, a2, a3 = sp.symbols('p1 p2 d1 d2 s eta a1 a2 a3', positive=True)
p3sym = 1 - p1 - p2                                # normalization Σp=1
pvec = [p1, p2, p3sym]
dvec = [d1, d2, -d1 - d2]                           # traceless perturbation Σδ=0
S_of   = lambda x: -sum((pvec[i] + x*dvec[i]) * sp.log(pvec[i] + x*dvec[i]) for i in range(3))
Keig   = [-sp.log(pvec[i]) for i in range(3)]       # modular Hamiltonian K = -log ρ_ref
Kexp_of= lambda x: sum(Keig[i] * (pvec[i] + x*dvec[i]) for i in range(3))
dS = sp.diff(S_of(s), s).subs(s, 0)
dK = sp.diff(Kexp_of(s), s).subs(s, 0)
check("entanglement first law  δS = δ⟨K⟩", simplify(dS - dK) == 0, "DifferentialAreaLaw (first law)")

# (iii) area identification K = η·A_op  ⟹  δS = η δA  (the entropy–area variation Jacobson uses)
aeig    = [a1, a2, a3]                              # area-operator eigenvalues
dKarea  = sp.diff(sum(eta*aeig[i]*(pvec[i] + s*dvec[i]) for i in range(3)), s).subs(s, 0)
dArea   = sp.diff(sum(aeig[i]*(pvec[i] + s*dvec[i]) for i in range(3)), s).subs(s, 0)
check("δ⟨K⟩ = η δA  (K = η·area)",       simplify(dKarea - eta*dArea) == 0, "δS = η δA (area identification)")
print("        finite temperature + δS = η δA reached;  Einstein still needs the continuum")
print("        smooth-background Raychaudhuri step δA ↔ T_kk — NOT finite-toy-reachable.")

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
Two extensions confirm the program stays consistent under composition:
  (a) LOCALITY — disjoint regions' observables commute, and the corner encoding preserves it
      ([ι(O_A),ι(O_B)] = ι([O_A,O_B]) = 0), the microcausality (P3) boundary condition;
  (b) TENSOR-NETWORK / RT — a 3-node graph whose cut is the area primitive (purity S(A)=S(Aᶜ),
      subadditivity), with the RT inequality S_vN(ρ_A) ≤ cut(A) and min-cut violating the triangle
      inequality (so it is an AREA, never a distance).
  (c) THERMAL HALF — a finite modular/Gibbs state has a genuine temperature (finite KMS), the
      entanglement first law δS = δ⟨K⟩ is exact, and with the modular Hamiltonian ∝ area it gives
      δS = η δA (the entropy–area variation Jacobson needs). This is as far as a finite microstate
      count, equipped with a modular flow, reaches toward GR.
What it does NOT do (and a realisation need not, at this minimal level): supply interactions,
gauge dynamics, or the value of G — and crucially it does NOT yield the Einstein field equations.
Those need the continuum smooth-background Raychaudhuri step δA ↔ T_kk, which no finite toy can
reach: a gravitational realisation (e.g. the free Klein–Gordon field on a smooth background,
`qiqt_gr_ppwave_showcase`) is required. The finite toys realise the kinematic + thermal boundary
conditions; GR is a property of the richer continuum realisation, not of these.
""")
import sys
sys.exit(0 if ok else 1)
