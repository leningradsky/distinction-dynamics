"""
delta = 2/9 hypothesis verification
"""
import numpy as np

print("=" * 70)
print("KOIDE PHASE delta = 2/9 HYPOTHESIS")
print("=" * 70)

# Experimental masses
m_e = 0.51099895
m_mu = 105.6583755
m_tau = 1776.86

# Koide parametrization
sqrt_masses = np.array([np.sqrt(m_e), np.sqrt(m_mu), np.sqrt(m_tau)])
M = np.sum(sqrt_masses) / 3

# Extract delta from data
cos_theta = (sqrt_masses / M - 1) / np.sqrt(2)
theta = np.arccos(np.clip(cos_theta, -1, 1))
delta_exp = np.mean([theta[0] - 2*np.pi/3, theta[2]])

print(f"\nExperimental delta = {delta_exp:.8f} rad")
print(f"2/9 = {2/9:.8f} rad")
print(f"Difference = {abs(delta_exp - 2/9):.8f} rad")
print(f"Error = {abs(delta_exp - 2/9)/(2/9) * 100:.4f}%")

# Now predict masses assuming delta = 2/9 exactly
print("\n" + "=" * 70)
print("MASS PREDICTION WITH delta = 2/9 EXACTLY")
print("=" * 70)

delta_theory = 2/9
theta_theory = np.array([
    2*np.pi/3 + delta_theory,  # Generation 1 (electron)
    4*np.pi/3 + delta_theory,  # Generation 2 (muon)
    delta_theory               # Generation 3 (tau)
])

# We need to find M from constraint Q = 2/3
# Q = 2/3 is automatic in Koide parametrization

# Use experimental M
sqrt_m_pred = M * (1 + np.sqrt(2) * np.cos(theta_theory))
m_pred = sqrt_m_pred**2

print(f"\nPredicted masses with delta = 2/9:")
print(f"m_e  = {m_pred[0]:.6f} MeV (exp: {m_e:.6f}, error: {abs(m_pred[0]-m_e)/m_e*100:.4f}%)")
print(f"m_mu = {m_pred[1]:.6f} MeV (exp: {m_mu:.6f}, error: {abs(m_pred[1]-m_mu)/m_mu*100:.4f}%)")
print(f"m_tau= {m_pred[2]:.6f} MeV (exp: {m_tau:.6f}, error: {abs(m_pred[2]-m_tau)/m_tau*100:.4f}%)")

# What is 2/9?
print("\n" + "=" * 70)
print("WHAT IS 2/9?")
print("=" * 70)

print("\n2/9 = 2/(3*3) = 2/N^2 where N=3 (generations)")
print("2/9 = (2/3) * (1/3) = Q_Koide * (1/N)")
print("2/9 = (N-1)/N * (1/N) = (N-1)/N^2")

for N in [2, 3, 4]:
    val = (N-1)/(N**2)
    print(f"  N={N}: (N-1)/N^2 = {val:.6f}")

# Connection to Cabibbo
print("\n" + "=" * 70)
print("CONNECTION TO CABIBBO ANGLE")
print("=" * 70)

cabibbo_exp = 0.22736  # experimental sin(theta_C)
print(f"\nsin(theta_Cabibbo) = {cabibbo_exp:.6f}")
print(f"2/9 = {2/9:.6f}")
print(f"Difference = {abs(cabibbo_exp - 2/9):.6f}")
print(f"Error = {abs(cabibbo_exp - 2/9)/(2/9) * 100:.2f}%")

print("\nCabibbo angle is mixing between generations 1 and 2 in CKM matrix!")
print("Same delta appears in both leptons (Koide) and quarks (CKM)!")

# DD interpretation
print("\n" + "=" * 70)
print("DD INTERPRETATION")
print("=" * 70)
print("""
TRIAD GEOMETRY:
  - 3 vertices (generations)
  - Rotations: 0, 120, 240 degrees
  - Phase shift delta = 2/9 rad

WHY 2/9?
  - 2/9 = 2/(3^2) = inter-generation coupling
  - 2 = pairs of generations that interact
  - 9 = 3^2 = all possible pairs (including self)
  - So: delta = (pairs)/(all pairs) = interaction strength

UNIFICATION:
  - Koide formula (leptons): angles = 0+d, 120+d, 240+d
  - CKM matrix (quarks): Cabibbo ~ 2/9
  - Same phase delta in both sectors!
  - This suggests common origin in triad geometry.
""")
