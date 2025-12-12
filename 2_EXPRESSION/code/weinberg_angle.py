"""
Weinberg angle from DD hierarchy
"""
import numpy as np

print("=" * 70)
print("WEINBERG ANGLE FROM DISTINCTION DYNAMICS")
print("=" * 70)

# Experimental value
sin2_exp = 0.23121  # sin^2(theta_W) at Z-pole
cos2_exp = 1 - sin2_exp
theta_exp = np.arcsin(np.sqrt(sin2_exp))

print(f"\nExperimental values:")
print(f"sin^2(theta_W) = {sin2_exp:.6f}")
print(f"cos^2(theta_W) = {cos2_exp:.6f}")
print(f"theta_W = {np.degrees(theta_exp):.4f} deg")

# DD hierarchy:
# Level 1: Monad -> U(1)  dim = 1
# Level 2: Dyad  -> SU(2) dim = 3
# Level 3: Triad -> SU(3) dim = 8

print("\n" + "=" * 70)
print("DD HIERARCHY DIMENSIONS")
print("=" * 70)
print("Level 1 (Monad): U(1)  -> dim = 1")
print("Level 2 (Dyad):  SU(2) -> dim = 3")
print("Level 3 (Triad): SU(3) -> dim = 8")

# Hypothesis 1: sin^2 = dim(U1) / (dim(U1) + dim(SU2)) = 1/4
hyp1 = 1 / (1 + 3)
print(f"\nHypothesis 1: sin^2 = 1/(1+3) = 1/4 = {hyp1:.6f}")
print(f"Error: {abs(hyp1 - sin2_exp)/sin2_exp * 100:.2f}%")

# Hypothesis 2: sin^2 = 1/dim(SU2) = 1/3
hyp2 = 1/3
print(f"\nHypothesis 2: sin^2 = 1/3 = {hyp2:.6f}")
print(f"Error: {abs(hyp2 - sin2_exp)/sin2_exp * 100:.2f}%")

# Hypothesis 3: Related to Koide Q = 2/3?
# sin^2 = 1 - Q = 1 - 2/3 = 1/3 (same as hyp2)

# Hypothesis 4: Level ratio
# sin^2 = Level1 / (Level1 + Level2) in some sense
# But levels are 1, 2, 3...

# Hypothesis 5: sin^2 = 3/13 (sum of dims = 1+3+8 = 12, so 3/13?)
hyp5 = 3/13
print(f"\nHypothesis 5: sin^2 = 3/13 = {hyp5:.6f}")
print(f"Error: {abs(hyp5 - sin2_exp)/sin2_exp * 100:.2f}%")

# Hypothesis 6: phi related?
phi = (1 + np.sqrt(5)) / 2
hyp6 = 1/phi**3
print(f"\nHypothesis 6: sin^2 = 1/phi^3 = {hyp6:.6f}")
print(f"Error: {abs(hyp6 - sin2_exp)/sin2_exp * 100:.2f}%")

# Hypothesis 7: sin^2 = (3-phi)/phi^2?
hyp7 = (3 - phi) / phi**2
print(f"\nHypothesis 7: sin^2 = (3-phi)/phi^2 = {hyp7:.6f}")
print(f"Error: {abs(hyp7 - sin2_exp)/sin2_exp * 100:.2f}%")

# Hypothesis 8: 1 - 1/phi^2 - 1/phi^4 ?
hyp8 = 1 - 1/phi**2 - 1/phi**4
print(f"\nHypothesis 8: sin^2 = 1 - 1/phi^2 - 1/phi^4 = {hyp8:.6f}")
print(f"Error: {abs(hyp8 - sin2_exp)/sin2_exp * 100:.2f}%")

# Hypothesis 9: (2/9)^2 * something?
delta = 2/9
hyp9 = 9 * delta**2
print(f"\nHypothesis 9: sin^2 = 9*(2/9)^2 = 4/9 = {hyp9:.6f}")
print(f"Error: {abs(hyp9 - sin2_exp)/sin2_exp * 100:.2f}%")

# Let's think differently: coupling constants
# g' (U1) and g (SU2)
# sin(theta_W) = g' / sqrt(g^2 + g'^2)
# At GUT scale, g' = g * sqrt(3/5) for SU(5)
# sin^2 = 3/8 = 0.375 at GUT scale

print("\n" + "=" * 70)
print("GUT PREDICTION")
print("=" * 70)
gut_sin2 = 3/8
print(f"SU(5) GUT: sin^2(theta_W) = 3/8 = {gut_sin2:.6f} (at GUT scale)")
print(f"Running to Z-pole gives ~0.231")

# DD interpretation of 3/8:
# 3 = levels of distinction (triad closes)
# 8 = dim(SU3)
print(f"\n3/8 = 3 (levels) / 8 (dim SU3)")

# Alternative: 3/8 = 3/(3+5) where 5 = dim(SU2) + 2?
# Or: 3/8 relates to S3 having 6 elements, and 6/8 = 3/4 is cos^2?

# Let's check: what gives exactly 0.23121?
# sin^2 = x => x = 0.23121
# Try: x = (1 - sqrt(something))/2 or similar

print("\n" + "=" * 70)
print("SEARCHING FOR EXACT FORMULA")
print("=" * 70)

# Check if sin^2 = a/b for small integers
for a in range(1, 20):
    for b in range(a+1, 50):
        val = a/b
        if abs(val - sin2_exp) < 0.001:
            print(f"{a}/{b} = {val:.6f}, error = {abs(val-sin2_exp)/sin2_exp*100:.3f}%")

# Check phi combinations
print("\nPhi combinations:")
for i in range(-5, 6):
    for j in range(-5, 6):
        if i == 0 and j == 0:
            continue
        try:
            val = phi**i + phi**j
            if 0 < val < 1 and abs(val - sin2_exp) < 0.01:
                print(f"phi^{i} + phi^{j} = {val:.6f}, error = {abs(val-sin2_exp)/sin2_exp*100:.2f}%")
        except:
            pass

# Check 1/phi^k
print("\n1/phi^k:")
for k in range(1, 10):
    val = 1/phi**k
    print(f"1/phi^{k} = {val:.6f}, error from sin^2 = {abs(val-sin2_exp)/sin2_exp*100:.2f}%")
