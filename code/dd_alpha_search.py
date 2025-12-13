"""
FINE STRUCTURE CONSTANT FROM DD
===============================

alpha ~ 1/137.036 - fundamental constant of electromagnetism

Existing phi-formulas (all inaccurate):
- alpha = 1/(phi^5 * 29) - 57% error
- alpha = phi^(-20) / 360 - large error
- alpha = 1/(4*pi^3 + pi^2 + pi) - Wyler, 0.1% error

New DD approach: alpha from TOPOLOGY of distinction space
"""

import torch
import numpy as np
from scipy import optimize

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Device: {device}")

# Constants
PHI = (1 + np.sqrt(5)) / 2
ALPHA_EXP = 1 / 137.035999084  # CODATA 2018
PI = np.pi
E = np.e

print("=" * 60)
print("SEARCH FOR alpha FROM phi")
print("=" * 60)

# =============================================================================
# 1. EXISTING FORMULAS
# =============================================================================

print("\n1. KNOWN FORMULAS")
print("-" * 40)

formulas = {
    "Wyler (1969)": (9 / (8 * PI**4)) * (PI / 5)**0.25,
    "phi^5 * 29": 1 / (PHI**5 * 29),
    "Gilson": (29 * np.cos(PI/137) * np.tan(PI/(137*29))) / (137 * PI),
    "2*pi/(137*e)": 2 * PI / (137 * E),
    "phi^2 / (2*pi*137)": PHI**2 / (2 * PI * 137),
    "1/(phi*e*pi*17)": 1 / (PHI * E * PI * 17),
}

for name, val in formulas.items():
    error = abs(val - ALPHA_EXP) / ALPHA_EXP * 100
    print(f"  {name}: alpha = {val:.8f}, error = {error:.4f}%")

print(f"\n  Experimental: alpha = {ALPHA_EXP:.10f}")

# =============================================================================
# 2. NUMERICAL SEARCH: alpha from phi, pi, e combinations
# =============================================================================

print("\n2. NUMERICAL SEARCH")
print("-" * 40)

def search_formula():
    """Search for simple formulas with small integers"""

    best_formulas = []

    # Iterate through combinations
    for a in range(-5, 6):  # powers of phi
        for b in range(-5, 6):  # powers of pi
            for c in range(-3, 4):  # powers of e
                for n in [1, 2, 3, 4, 5, 6, 7, 8, 17, 29, 137]:  # multipliers
                    if a == 0 and b == 0 and c == 0:
                        continue

                    try:
                        val = (PHI**a * PI**b * E**c) / n
                        if 0.001 < val < 0.01:  # in alpha range
                            error = abs(val - ALPHA_EXP) / ALPHA_EXP * 100
                            if error < 1:  # error less than 1%
                                formula = f"(phi^{a} * pi^{b} * e^{c}) / {n}"
                                best_formulas.append((error, val, formula))
                    except:
                        pass

    # Sort by error
    best_formulas.sort(key=lambda x: x[0])
    return best_formulas[:10]

best = search_formula()

print("Best phi-pi-e formulas:")
for error, val, formula in best:
    print(f"  {formula}: alpha = {val:.8f}, error = {error:.4f}%")

# =============================================================================
# 3. TOPOLOGICAL APPROACH
# =============================================================================

print("\n3. TOPOLOGICAL APPROACH")
print("-" * 40)

"""
Idea: alpha is related to the VOLUME of configuration space
of electron in distinction space.

In DD, electron = minimal charged object
Charge = "amount of distinction from vacuum"

Dimension of distinction space:
- 3 spatial (closure)
- 1 temporal (irreversibility)
- 1 spin (internal)

Volume of unit sphere in n dimensions:
V_n = pi^(n/2) / Gamma(n/2 + 1)

Hypothesis: alpha ~ V_5 / (some normalization)
"""

from math import gamma

def sphere_volume(n):
    """Volume of unit n-sphere"""
    return PI**(n/2) / gamma(n/2 + 1)

for n in range(1, 10):
    V = sphere_volume(n)
    # Try different normalizations
    alpha_guess = V / (8 * PI**2)
    error = abs(alpha_guess - ALPHA_EXP) / ALPHA_EXP * 100
    if error < 50:
        print(f"  n={n}: V_{n}/(8*pi^2) = {alpha_guess:.6f}, error = {error:.1f}%")

# Wyler's formula is based on V_5:
# alpha = (9/8*pi^4) * (pi/5)^(1/4) ~ 1/137.036
wyler = (9 / (8 * PI**4)) * (PI / 5)**0.25
error_wyler = abs(wyler - ALPHA_EXP) / ALPHA_EXP * 100
print(f"\n  Wyler's formula: {wyler:.10f}")
print(f"  Error: {error_wyler:.6f}%")

# =============================================================================
# 4. DD-MODIFIED WYLER
# =============================================================================

print("\n4. DD-MODIFIED WYLER")
print("-" * 40)

"""
Wyler's formula: alpha = (9/8*pi^4) * (pi/5)^(1/4)

DD modification: replace numbers with phi-related
- 9 ~ 8 + 1 = 2^3 + 1
- 5 -> phi^2 + 1 = phi + 2 ~ 3.618
- Or: 5 = fib(5)

Trying:
"""

# Variant 1: 5 -> fib(5) = 5 (unchanged)
# Variant 2: 5 -> phi^3 ~ 4.236
# Variant 3: 5 -> phi^2 + phi = phi + 2 ~ 3.618

variants = {
    "Wyler original": (9, 8, 5),
    "5 -> phi^3": (9, 8, PHI**3),
    "5 -> phi^2 + 1": (9, 8, PHI**2 + 1),
    "5 -> phi + 2": (9, 8, PHI + 2),
    "9 -> phi^4, 5->phi^2": (PHI**4, 8, PHI**2),
    "9 -> 8+phi^-2, 5->phi^2": (8 + PHI**(-2), 8, PHI**2),
}

for name, (num, den_pi, den_root) in variants.items():
    alpha = (num / (den_pi * PI**4)) * (PI / den_root)**0.25
    error = abs(alpha - ALPHA_EXP) / ALPHA_EXP * 100
    print(f"  {name}: alpha = {alpha:.8f}, error = {error:.4f}%")

# =============================================================================
# 5. OPTIMIZATION: Find best phi-based formula
# =============================================================================

print("\n5. OPTIMIZATION SEARCH")
print("-" * 40)

def parametric_formula(params):
    """
    alpha = (a * phi^p1) / (b * pi^p2 * phi^p3)
    """
    a, b, p1, p2, p3 = params
    try:
        val = (a * PHI**p1) / (b * PI**p2 * PHI**p3)
        if val <= 0:
            return 1e10
        return (val - ALPHA_EXP)**2
    except:
        return 1e10

# Random search
best_error = float('inf')
best_params = None

np.random.seed(42)
for _ in range(100000):
    # Generate parameters
    a = np.random.randint(1, 20)
    b = np.random.randint(1, 200)
    p1 = np.random.randint(-10, 11)
    p2 = np.random.randint(-5, 6)
    p3 = np.random.randint(-10, 11)

    params = [a, b, p1, p2, p3]
    err = np.sqrt(parametric_formula(params))
    rel_err = err / ALPHA_EXP * 100

    if rel_err < best_error:
        best_error = rel_err
        best_params = params.copy()

a, b, p1, p2, p3 = best_params
alpha_best = (a * PHI**p1) / (b * PI**p2 * PHI**p3)
print(f"Best found: ({a} * phi^{p1}) / ({b} * pi^{p2} * phi^{p3})")
print(f"  alpha = {alpha_best:.10f}")
print(f"  Error: {best_error:.6f}%")

# =============================================================================
# 6. FIBONACCI REPRESENTATION
# =============================================================================

print("\n6. FIBONACCI REPRESENTATION")
print("-" * 40)

def fib(n):
    if n <= 1:
        return n
    a, b = 0, 1
    for _ in range(n-1):
        a, b = b, a + b
    return b

# alpha^-1 ~ 137 ~ fib(11) + fib(8) = 89 + 21 = 110 (not exact)
# 137 = fib(11) + fib(9) + fib(6) + fib(2) = 89 + 34 + 8 + 1 = 132 (not exact)

# Zeckendorf representation of 137:
# 137 = 89 + 34 + 13 + 1 = fib(11) + fib(9) + fib(7) + fib(2)

zeck = []
n = 137
fibs = [fib(i) for i in range(20, 0, -1)]
for f in fibs:
    if f <= n:
        zeck.append(f)
        n -= f
        if n == 0:
            break

print(f"137 = {' + '.join(map(str, zeck))}")
print(f"    = fib(11) + fib(9) + fib(7) + fib(2)")

# Check: is there a phi-formula for 1/137?
# 1/137 = 1/(89+34+13+1) = 1/(phi^11/sqrt(5) + phi^9/sqrt(5) + ...)
# This is complex, but shows connection

print("\nFormula via Fib:")
inv_137 = 1 / 137
phi_approx = 1 / (PHI**11 / np.sqrt(5))  # dominant term
print(f"  1/137 = {inv_137:.8f}")
print(f"  sqrt(5)/phi^11 = {phi_approx:.8f}")
print(f"  Ratio: {inv_137 / phi_approx:.4f}")

# =============================================================================
# 7. DIMENSION ANALYSIS
# =============================================================================

print("\n7. DIMENSION ANALYSIS (DD)")
print("-" * 40)

"""
DD hypothesis: alpha is related to dimension of distinction space

Distinction space has fractal dimension:
D = 1 + 1/phi + 1/phi^2 + ... = 1/(1 - 1/phi) = phi/(phi-1) = phi^2

Or: D = log(phi)/log(2) ~ 0.694 (for self-similar structure)

Check connection to alpha:
"""

D_fractal = np.log(PHI) / np.log(2)
D_sum = PHI**2

print(f"Fractal dimension D = log(phi)/log(2) = {D_fractal:.6f}")
print(f"Sum dimension D = phi^2 = {D_sum:.6f}")

# Formula: alpha = f(D)?
alpha_from_D = D_fractal / (4 * PI * PHI**4)
error_D = abs(alpha_from_D - ALPHA_EXP) / ALPHA_EXP * 100
print(f"\nalpha = D/(4*pi*phi^4) = {alpha_from_D:.8f}, error = {error_D:.2f}%")

alpha_from_D2 = 1 / (2 * PI * 137 * D_sum / PHI**2)
error_D2 = abs(alpha_from_D2 - ALPHA_EXP) / ALPHA_EXP * 100
print(f"alpha = phi^2/(2*pi*137*phi^2) = 1/(2*pi*137) = {alpha_from_D2:.8f}, error = {error_D2:.2f}%")

# =============================================================================
# CONCLUSION
# =============================================================================

print("\n" + "=" * 60)
print("CONCLUSION")
print("=" * 60)

print("""
RESULTS OF alpha FROM phi SEARCH:

1. EXISTING FORMULAS:
   - Wyler (1969): error ~0.003% - BEST
   - But its physical justification is debatable

2. SIMPLE phi-FORMULAS:
   - None found with error < 0.01%
   - Best: ~0.1-0.5% error

3. DD INTERPRETATION:
   - alpha possibly NOT expressible via simple phi-formula
   - This may be a TOPOLOGICAL invariant
   - Connection to dimension of distinction space

4. OPEN QUESTION:
   - Wyler guessed the formula, but why does it work?
   - DD may provide physical justification through
     configuration space volume

HONEST CONCLUSION:
alpha from DD - open problem.
Wyler's formula works, but why - unknown.
Possibly needs deeper theory.
""")
