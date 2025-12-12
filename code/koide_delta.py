"""
What is delta = 12.73 degrees in Koide formula?
"""
import numpy as np

delta = 0.222270  # radians, from Koide fit

print("=" * 70)
print("WHAT IS KOIDE PHASE delta = 12.73 deg?")
print("=" * 70)

print(f"\ndelta = {delta:.6f} rad = {np.degrees(delta):.4f} deg")

# Check various ratios
print("\nCHECKING RATIOS:")

phi = (1 + np.sqrt(5)) / 2
print(f"phi = {phi:.6f}")
print(f"1/phi = {1/phi:.6f}")
print(f"1/phi^2 = {1/phi**2:.6f}")

print(f"\ndelta/pi = {delta/np.pi:.6f}")
print(f"delta/(2*pi) = {delta/(2*np.pi):.6f}")
print(f"delta/(pi/3) = {delta/(np.pi/3):.6f}")  # 60 deg

# Interesting: delta ~ 2/9 radians?
print(f"\n2/9 = {2/9:.6f}")
print(f"delta - 2/9 = {delta - 2/9:.6f}")

# Or delta ~ 1/(sqrt(2)*pi)?
print(f"\n1/(sqrt(2)*pi) = {1/(np.sqrt(2)*np.pi):.6f}")

# Or related to Cabibbo angle?
cabibbo = 0.227  # radians (about 13 degrees)
print(f"\nCabibbo angle = {cabibbo:.6f} rad = {np.degrees(cabibbo):.2f} deg")
print(f"delta - Cabibbo = {delta - cabibbo:.6f}")

# Check: is delta = arctan(1/4)?
print(f"\narctan(1/4) = {np.arctan(0.25):.6f} rad = {np.degrees(np.arctan(0.25)):.2f} deg")

# Check: is delta = arcsin(me/mmu)?
print(f"\narcsin(sqrt(m_e/m_mu)) = {np.arcsin(np.sqrt(0.511/105.66)):.6f} rad")

# Most interesting: delta related to 2/3?
print(f"\n2/(3*pi) = {2/(3*np.pi):.6f}")
print(f"delta - 2/(3*pi) = {delta - 2/(3*np.pi):.6f}")

# phi related?
print(f"\n1/(phi*pi) = {1/(phi*np.pi):.6f}")
print(f"2/(phi^2*pi) = {2/(phi**2*np.pi):.6f}")
print(f"(phi-1)/pi = {(phi-1)/np.pi:.6f}")

# Very close!
print(f"\n(phi-1)/pi = {(phi-1)/np.pi:.6f}")
print(f"delta = {delta:.6f}")
print(f"Difference = {abs(delta - (phi-1)/np.pi):.6f}")
print(f"Error = {abs(delta - (phi-1)/np.pi)/delta * 100:.2f}%")

print("\n" + "=" * 70)
print("HYPOTHESIS: delta = (phi - 1) / pi = 1 / (phi * pi)")
print("=" * 70)
print(f"This would mean: delta encodes phi in Koide formula!")
print(f"phi appears both in k=2 recursion AND in generation masses!")

# Verify
delta_theory = (phi - 1) / np.pi
print(f"\ndelta_theory = {delta_theory:.6f} rad = {np.degrees(delta_theory):.4f} deg")
print(f"delta_exp    = {delta:.6f} rad = {np.degrees(delta):.4f} deg")
print(f"Error = {abs(delta - delta_theory)/delta * 100:.2f}%")
