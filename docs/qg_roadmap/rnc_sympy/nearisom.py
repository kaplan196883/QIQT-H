import sympy as sp
print("="*70)
print("PART 2: hco <= hVdisp  (near-isometry / coercivity from quadratic disp)")
print("="*70)
# Point n = sup norm ||.||_inf.  rncRadialSq z = sum z_i^2 = ||z||_2^2.
# hVdisp: ||V z + z||_inf <= C_W ||z||_inf^2.
# Goal hco: (1/2)||z||_2^2 <= ||V z||_2^2.
# Norm equiv (dim n): ||z||_inf <= ||z||_2 <= sqrt(n)||z||_inf.
# V z = -z + r,  r = V z + z.  ||V z||_2 >= ||z||_2 - ||r||_2.
# ||r||_2 <= sqrt(n) ||r||_inf <= sqrt(n) C_W ||z||_inf^2 <= sqrt(n) C_W ||z||_2^2 (since ||z||_inf<=||z||_2)
# ||V z||_2 >= ||z||_2 (1 - sqrt(n) C_W ||z||_2).
# want ||V z||_2 >= (1/sqrt2) ||z||_2  <=> 1 - sqrt(n)C_W ||z||_2 >= 1/sqrt2
#   <=> ||z||_2 <= (1 - 1/sqrt2)/(sqrt(n) C_W)  =: r_star
r2, Cw, n = sp.symbols('r2 C_W n', positive=True)
rstar = (1 - 1/sp.sqrt(2))/(sp.sqrt(n)*Cw)
print("critical radius r* (in ||.||_2):", rstar, "=", sp.nsimplify(1-1/sp.sqrt(2)),"/(sqrt(n) C_W)")
print("  1 - 1/sqrt2 =", float(1-1/sp.sqrt(2)))
# check: at ||z||_2 = r_star, factor (1 - sqrt(n)Cw r_star) = 1/sqrt2, squared = 1/2. tight.
factor = 1 - sp.sqrt(n)*Cw*rstar
print("  factor at r*:", sp.simplify(factor), " squared:", sp.simplify(factor**2), "(=1/2 tight)")
# A cleaner sufficient condition often used: sqrt(n) C_W ||z||_2 <= 1/4  => factor>=3/4 => sq=9/16>1/2. looser but simpler.
print()
print("SIMPLER sufficient radius: sqrt(n)*C_W*||z||_2 <= 1/4 gives factor 3/4, (3/4)^2=9/16 >= 1/2. OK, cleaner.")
print("  => r_simple = 1/(4 sqrt(n) C_W). Use this for a clean Lean constant.")
# Verify (3/4)^2 = 9/16 >= 1/2
print("  (3/4)^2 =", sp.Rational(9,16), ">= 1/2 :", sp.Rational(9,16)>=sp.Rational(1,2))
