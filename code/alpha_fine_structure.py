"""
Fine structure constant alpha from DD
"""
import numpy as np

print("=" * 70)
print("FINE STRUCTURE CONSTANT FROM DD")
print("=" * 70)

# Experimental value
alpha_exp = 1/137.035999084  # CODATA 2018
inv_alpha_exp = 1/alpha_exp

print(f"\nExperimental values:")
print(f"alpha = {alpha_exp:.12f}")
print(f"1/alpha = {inv_alpha_exp:.6f}")

# Fibonacci numbers
def fib(n):
    if n <= 1:
        return n
    a, b = 0, 1
    for _ in range(n-1):
        a, b = b, a + b
    return b

phi = (1 + np.sqrt(5)) / 2

print("\n" + "=" * 70)
print("SEARCHING FOR FORMULAS")
print("=" * 70)

# Simple Fibonacci
print("\nFibonacci numbers near 137:")
for i in range(15):
    f = fib(i)
    if 100 < f < 200:
        print(f"F({i}) = {f}")

# F(11) = 89, F(12) = 144
# 137 is between them

# Check combinations
print("\nFibonacci combinations:")

# 137 = 144 - 8 + 1 = F(12) - F(6) + F(1)
print(f"F(12) - F(6) + F(1) = {fib(12) - fib(6) + fib(1)} (want 137)")
print(f"F(12) - F(6) + F(2) = {fib(12) - fib(6) + fib(2)}")

# 137 = 89 + 55 - 8 + 1 = F(11) + F(10) - F(6) + F(1)
val = fib(11) + fib(10) - fib(6) + fib(1)
print(f"F(11) + F(10) - F(6) + F(1) = {val}")

# 137 = 144 - 7 = F(12) - 7
print(f"F(12) - 7 = {fib(12) - 7}")

# Check if 137 = sum of Fibonacci?
# Zeckendorf representation: 137 = 89 + 34 + 13 + 1 = F(11) + F(9) + F(7) + F(1)
zeck = fib(11) + fib(9) + fib(7) + fib(1)
print(f"\nZeckendorf: 137 = F(11) + F(9) + F(7) + F(1) = 89 + 34 + 13 + 1 = {zeck}")

# Interesting: 11, 9, 7, 1 - odd indices!
print("Indices: 11, 9, 7, 1 - all ODD!")

# phi related
print("\n" + "=" * 70)
print("PHI FORMULAS")
print("=" * 70)

# Try phi^k combinations
print("\nphi powers:")
for k in range(1, 12):
    print(f"phi^{k} = {phi**k:.6f}")

# phi^9 = 76.01
# phi^10 = 122.99
# phi^10 + phi^4 = 122.99 + 6.85 = 129.84

# Check: 1/alpha ~ phi^something?
print(f"\nlog_phi(137) = {np.log(137)/np.log(phi):.6f}")
# About 10.2

# Try: 1/alpha = phi^10 + phi^3 + phi^0?
val = phi**10 + phi**3 + 1
print(f"phi^10 + phi^3 + 1 = {val:.6f}")

val = phi**10 + phi**4
print(f"phi^10 + phi^4 = {val:.6f}")

val = phi**10 + phi**5 - phi
print(f"phi^10 + phi^5 - phi = {val:.6f}")

# Closer look
# 137 - phi^10 = 137 - 122.99 = 14.01 ~ phi^5 = 11.09? No
# 137 - phi^10 = 14.01 ~ 14 = 2*7 = 2*F(5+1)

# Check: 137.036 more precisely
target = 137.035999084

# Try: phi^10 + phi^4 + something
base = phi**10 + phi**4
diff = target - base
print(f"\n137.036 - phi^10 - phi^4 = {diff:.6f}")
print(f"phi^2 = {phi**2:.6f}")
print(f"phi^3 = {phi**3:.6f}")

# Try: a*phi^10 + b*phi^k
print("\nSearching a*phi^10 + b*phi^k...")
for a in [1]:
    for b in range(-5, 6):
        for k in range(0, 10):
            val = a * phi**10 + b * phi**k
            if abs(val - target) < 0.1:
                print(f"{a}*phi^10 + {b}*phi^{k} = {val:.6f}, error = {abs(val-target):.6f}")

# Different approach: DD formula
print("\n" + "=" * 70)
print("DD STRUCTURAL FORMULAS")
print("=" * 70)

# Idea: alpha involves all three levels
# Level 1: U(1), dim=1
# Level 2: SU(2), dim=3
# Level 3: SU(3), dim=8
# Total dim = 12

# Weinberg: sin^2 = 3/13 uses 3 and 13
# Maybe alpha uses similar structure?

# 137 = 11 * 12 + 5 = 11 * (1+3+8) + F(5)
print(f"11 * 12 + 5 = {11*12 + 5}")

# 137 = 12 * 11 + 5
print(f"12 * 11 + 5 = {12*11 + 5}")

# 137 = 10 * 13 + 7
print(f"10 * 13 + 7 = {10*13 + 7}")

# 137 = F(11) + F(9) + F(7) + F(1) (Zeckendorf)
# = 89 + 34 + 13 + 1

# Note: 11-9=2, 9-7=2, but 7-1=6
# Hmm, not k=2 pattern

# Try: 137 = 128 + 8 + 1 = 2^7 + 2^3 + 2^0
print(f"\n2^7 + 2^3 + 2^0 = {2**7 + 2**3 + 2**0}")

# 137 in binary: 10001001
# Bits at positions 0, 3, 7
# 7-3=4, 3-0=3 ... 

# Connection to 3 generations?
# 137 = 3^4 + 3^3 + 3^2 + 3 + 2 = 81 + 27 + 9 + 3 + 2 = 122? No

# Try: 137 = something with dimensions
# dim(U1)=1, dim(SU2)=3, dim(SU3)=8
# 1*3*8 = 24
# 1+3+8 = 12
# 1*3 + 3*8 + 8*1 = 3 + 24 + 8 = 35
# (1+3+8)^2 - (1^2+3^2+8^2) = 144 - 74 = 70

# Hmm, let's try the product formula
# (1+1)(3+1)(8+1) = 2*4*9 = 72
# (1+2)(3+2)(8+2) = 3*5*10 = 150 - close!

print(f"\n(1+2)(3+2)(8+2) = 3*5*10 = {3*5*10}")
print(f"(1+1)(3+2)(8+2) = 2*5*10 = {2*5*10}")

# 137 = 140 - 3 = (2*5*14) - 3
# 137 = 150 - 13 = 3*5*10 - F(7)

print(f"3*5*10 - 13 = {3*5*10 - 13}")  # = 137!

print("\n" + "=" * 70)
print("CANDIDATE FORMULA")
print("=" * 70)
print("1/alpha = (1+2)(3+2)(8+2) - F(7)")
print("        = 3 * 5 * 10 - 13")
print("        = 150 - 13")
print("        = 137")
print(f"\nPredicted: 1/alpha = 137")
print(f"Experimental: 1/alpha = {inv_alpha_exp:.6f}")
print(f"Error: {abs(137 - inv_alpha_exp)/inv_alpha_exp * 100:.4f}%")

# More precise?
# Maybe: 1/alpha = 3*5*10 - 13 + correction?
# 137.036 - 137 = 0.036
# 0.036 ~ 1/28 ~ 1/(4*7)?

print("\n" + "=" * 70)
print("REFINED FORMULA")
print("=" * 70)

# Try: 1/alpha = 137 + pi/87 ?
val = 137 + np.pi/87
print(f"137 + pi/87 = {val:.6f}, error = {abs(val-inv_alpha_exp)/inv_alpha_exp*100:.4f}%")

# Try: 1/alpha = 137 + 1/28
val = 137 + 1/28
print(f"137 + 1/28 = {val:.6f}, error = {abs(val-inv_alpha_exp)/inv_alpha_exp*100:.4f}%")

# Try: 1/alpha = 137 + 1/27 = 137 + 1/3^3
val = 137 + 1/27
print(f"137 + 1/27 = {val:.6f}, error = {abs(val-inv_alpha_exp)/inv_alpha_exp*100:.4f}%")

# Try: 1/alpha = 137 + phi/45
val = 137 + phi/45
print(f"137 + phi/45 = {val:.6f}, error = {abs(val-inv_alpha_exp)/inv_alpha_exp*100:.4f}%")

# What is 0.036?
print(f"\n0.036 = {0.036:.6f}")
print(f"1/phi^4 = {1/phi**4:.6f}")
print(f"2/55 = {2/55:.6f}")
print(f"2/F(10) = {2/fib(10):.6f}")

# 0.036 ~ 2/55 = 2/F(10)?
val = 137 + 2/fib(10)
print(f"\n137 + 2/F(10) = 137 + 2/55 = {val:.6f}")
print(f"Error: {abs(val-inv_alpha_exp)/inv_alpha_exp*100:.4f}%")
