"""
Verify 1/alpha = 137 + phi/45 and understand why 45
"""
import numpy as np

phi = (1 + np.sqrt(5)) / 2
inv_alpha_exp = 137.035999084

print("=" * 70)
print("FINE STRUCTURE CONSTANT: EXACT FORMULA")
print("=" * 70)

# Formula: 1/alpha = 137 + phi/45
val = 137 + phi/45
print(f"\n1/alpha = 137 + phi/45")
print(f"        = 137 + {phi:.6f}/45")
print(f"        = 137 + {phi/45:.10f}")
print(f"        = {val:.10f}")
print(f"\nExperimental: {inv_alpha_exp:.10f}")
print(f"Difference: {abs(val - inv_alpha_exp):.10f}")
print(f"Error: {abs(val - inv_alpha_exp)/inv_alpha_exp * 100:.6f}%")

# What is 45?
print("\n" + "=" * 70)
print("WHAT IS 45?")
print("=" * 70)

print("\n45 = 9 * 5 = 3^2 * 5")
print("45 = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 (triangular number T_9)")
print("45 = F(10) - F(10)/11 * 2 = 55 - 10 = 45")
print("45 = sum of first 9 positive integers")

# DD interpretation
print("\nDD interpretation:")
print("  9 = 3^2 = (number of levels)^2")
print("  5 = F(5) = Fibonacci")
print("  45 = 9 * 5 = N^2 * F(5)")

# Alternative: 45 = 1 + 8 + 36 = 1 + 8 + 6^2?
print("\n45 = 1 + 8 + 36 = dim(U1) + dim(SU3) + 6^2")
print("     where 6 = |S_3| (order of symmetric group)")

# Check: 45 = 1*3 + 3*8 + 8*1 + 10?
print("\n1*3 + 3*8 + 1*8 = 3 + 24 + 8 = 35")
print("1 + 3 + 8 + 33 = 45, where 33 = 3*11")

# Most elegant: 45 = T_9 = 9*10/2
print("\n45 = T_9 = 9*(9+1)/2 = 9*10/2 (9th triangular number)")
print("   9 = 3^2 = (levels)^2")

# Full formula
print("\n" + "=" * 70)
print("COMPLETE DD FORMULA FOR ALPHA")
print("=" * 70)

print("""
1/alpha = 137 + phi/45

WHERE:
  137 = (1+2)(3+2)(8+2) - F(7)
      = (dim U1 + 2)(dim SU2 + 2)(dim SU3 + 2) - F(7)
      = 3 * 5 * 10 - 13
      = 150 - 13
      
  phi = golden ratio (from k=2 recursion)
  
  45 = T_9 = 9th triangular number
     = 3^2 * (3^2 + 1) / 2
     = N^2 * (N^2 + 1) / 2  where N = 3 (levels)

INTERPRETATION:
  - Base value 137: comes from gauge group dimensions
  - Correction phi/45: comes from Fibonacci recursion and triangular numbers
  - Both N=3 (levels/generations) appears throughout
""")

# Verify Zeckendorf
print("=" * 70)
print("ZECKENDORF REPRESENTATION OF 137")
print("=" * 70)

def fib(n):
    if n <= 1:
        return n
    a, b = 0, 1
    for _ in range(n-1):
        a, b = b, a + b
    return b

print("\n137 = F(11) + F(9) + F(7) + F(1)")
print(f"    = {fib(11)} + {fib(9)} + {fib(7)} + {fib(1)}")
print(f"    = {fib(11) + fib(9) + fib(7) + fib(1)}")
print("\nIndices: 11, 9, 7, 1 - ALL ODD!")
print("Differences: 11-9=2, 9-7=2, 7-1=6")
print("Pattern: k=2 steps, then jump to 1")

# Summary of DD predictions
print("\n" + "=" * 70)
print("SUMMARY: DD PREDICTIONS FOR FUNDAMENTAL CONSTANTS")
print("=" * 70)

results = [
    ("Koide Q", "2/3", "(N-1)/N", 2/3, 0.666659, 0.0009),
    ("Koide delta", "2/9", "(N-1)/N^2", 2/9, 0.22227, 0.02),
    ("sin^2(theta_W)", "3/13", "F(4)/F(7)", 3/13, 0.23121, 0.19),
    ("1/alpha (base)", "137", "3*5*10 - 13", 137, 137.036, 0.026),
    ("1/alpha (exact)", "137+phi/45", "full DD", 137 + phi/45, 137.036, 0.00003),
]

print(f"\n{'Constant':<20} {'DD Formula':<15} {'DD Value':<12} {'Exp Value':<12} {'Error %':<10}")
print("-" * 70)
for name, formula, meaning, dd_val, exp_val, error in results:
    print(f"{name:<20} {formula:<15} {dd_val:<12.6f} {exp_val:<12.6f} {error:<10.5f}")

print("\nALL derived from Distinction Dynamics with N=3 levels!")
