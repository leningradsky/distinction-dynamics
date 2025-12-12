"""
DD DEEP ANALYSIS: Quantum entanglement and phi
==============================================

Searching for phi in:
1. Entanglement entropy spectra
2. Qubit gate optimal angles
3. Variational quantum eigensolver
"""

import torch
import numpy as np
import time

device = torch.device('cuda')
PHI = (1 + np.sqrt(5)) / 2
print(f"Device: {torch.cuda.get_device_name(0)}")
print("=" * 60)

# =============================================================================
# 1. ENTANGLEMENT SPECTRUM ANALYSIS
# =============================================================================

print("\n1. ENTANGLEMENT SPECTRUM")
print("-" * 40)

def random_state_entanglement(n_qubits=10, n_samples=10000):
    """
    Analysis of entanglement spectrum of random states

    For random state in H_A x H_B, reduced density matrix
    rho_A has spectrum with specific statistics (Marchenko-Pastur for large systems)
    """

    dim_A = 2 ** (n_qubits // 2)
    dim_B = 2 ** (n_qubits - n_qubits // 2)

    entropies = []
    schmidt_ratios = []

    for _ in range(n_samples):
        # Random pure state
        psi = torch.randn(dim_A * dim_B, device=device) + 1j * torch.randn(dim_A * dim_B, device=device)
        psi = psi / torch.norm(psi)

        # Reshape to matrix
        psi_matrix = psi.reshape(dim_A, dim_B)

        # SVD for Schmidt decomposition
        U, S, Vh = torch.linalg.svd(psi_matrix, full_matrices=False)

        # Schmidt coefficients (squared = eigenvalues of rho_A)
        schmidt = S ** 2
        schmidt = schmidt / schmidt.sum()  # normalize

        # Von Neumann entropy
        entropy = -torch.sum(schmidt * torch.log2(schmidt + 1e-10)).item()
        entropies.append(entropy)

        # Ratio of two largest Schmidt coefficients
        if len(schmidt) >= 2:
            r = (schmidt[0] / schmidt[1]).item()
            if r > 1:
                r = 1/r
            schmidt_ratios.append(r)

    return np.mean(entropies), np.std(entropies), np.mean(schmidt_ratios)

start = time.time()
mean_S, std_S, mean_ratio = random_state_entanglement(n_qubits=12, n_samples=5000)
elapsed = time.time() - start

print(f"Random states (12 qubits, 5000 samples)")
print(f"Mean entanglement entropy: {mean_S:.4f} bits")
print(f"Std: {std_S:.4f}")
print(f"Mean Schmidt ratio (lambda1/lambda2): {mean_ratio:.4f}")
print(f"1/phi = {1/PHI:.4f}")
print(f"Time: {elapsed:.1f}s")

# =============================================================================
# 2. QUANTUM GATE ANGLES
# =============================================================================

print("\n2. OPTIMAL QUANTUM GATE ANGLES")
print("-" * 40)

def find_optimal_angles(n_trials=100000):
    """
    Search for optimal angles for quantum gates, check connection to phi

    Universal gates: Rx(theta), Ry(phi), Rz(lambda)
    """

    # Generate random angles
    theta = torch.rand(n_trials, device=device) * 2 * np.pi

    # Rotation matrices
    def Rx(t):
        c, s = torch.cos(t/2), torch.sin(t/2)
        return torch.stack([
            torch.stack([c, -1j*s], dim=-1),
            torch.stack([-1j*s, c], dim=-1)
        ], dim=-2)

    # For simplicity, check: at which angles gates give "nice" results

    # Criterion: |psi|^2 contains phi-proportions
    # Initial state |0>
    psi0 = torch.tensor([1.0, 0.0], dtype=torch.complex64, device=device)

    # Apply Ry(theta)
    c = torch.cos(theta/2)
    s = torch.sin(theta/2)

    # |psi> = cos(theta/2)|0> + sin(theta/2)|1>
    # Probabilities: cos^2(theta/2), sin^2(theta/2)

    p0 = c**2
    p1 = s**2

    # Search for angles where p0/p1 = phi or 1/phi
    ratio = p0 / (p1 + 1e-10)

    # Find closest to phi
    diff_phi = torch.abs(ratio - PHI)
    diff_inv_phi = torch.abs(ratio - 1/PHI)

    best_phi_idx = torch.argmin(diff_phi)
    best_inv_phi_idx = torch.argmin(diff_inv_phi)

    theta_phi = theta[best_phi_idx].item()
    theta_inv_phi = theta[best_inv_phi_idx].item()

    # Theoretically:
    # p0/p1 = phi => cos^2(t/2)/sin^2(t/2) = phi => cot^2(t/2) = phi
    # => t/2 = arccot(sqrt(phi)) = arctan(1/sqrt(phi))
    theta_theory = 2 * np.arctan(1/np.sqrt(PHI))

    return theta_phi, theta_inv_phi, theta_theory

t_phi, t_inv_phi, t_theory = find_optimal_angles()

print(f"Angle for p0/p1 = phi: {np.degrees(t_phi):.2f} deg")
print(f"Angle for p0/p1 = 1/phi: {np.degrees(t_inv_phi):.2f} deg")
print(f"Theory (2*arctan(1/sqrt(phi))): {np.degrees(t_theory):.2f} deg")
print(f"Golden angle (360/phi^2): {360/PHI**2:.2f} deg")

# =============================================================================
# 3. VARIATIONAL QUANTUM EIGENSOLVER (VQE) FOR H2
# =============================================================================

print("\n3. VQE GROUND STATE SEARCH")
print("-" * 40)

def vqe_h2_simple(n_params=1000):
    """
    Simplified VQE for H2 molecule

    Hamiltonian (in Pauli basis):
    H = g0*I + g1*Z0 + g2*Z1 + g3*Z0Z1 + g4*X0X1 + g5*Y0Y1

    Using Hardware Efficient Ansatz
    """

    # Coefficients for H2 at equilibrium distance (from literature)
    # This is simplified version
    g = torch.tensor([
        -0.4804,  # I
        +0.3435,  # Z0
        -0.4347,  # Z1
        +0.5716,  # Z0Z1
        +0.0910,  # X0X1
        +0.0910   # Y0Y1
    ], device=device)

    # Ansatz: |psi(theta)> = Ry(theta)|00>
    # This is too simple ansatz, but sufficient for demonstration

    thetas = torch.linspace(0, 2*np.pi, n_params, device=device)

    energies = []

    for theta in thetas:
        # |psi> = cos(t/2)|00> + sin(t/2)|11> (Bell-like state)
        c = torch.cos(theta/2)
        s = torch.sin(theta/2)

        # <Z0> = <Z1> = cos^2 - sin^2 = cos(theta)
        # <Z0Z1> = 1 (always for this ansatz)
        # <X0X1> = <Y0Y1> = sin(theta) (for Bell state)

        exp_Z = torch.cos(theta)
        exp_ZZ = torch.tensor(1.0, device=device)
        exp_XX = torch.sin(theta)
        exp_YY = torch.sin(theta)

        E = g[0] + g[1]*exp_Z + g[2]*exp_Z + g[3]*exp_ZZ + g[4]*exp_XX + g[5]*exp_YY
        energies.append(E.item())

    energies = np.array(energies)
    min_idx = np.argmin(energies)

    optimal_theta = thetas[min_idx].item()
    min_energy = energies[min_idx]

    return optimal_theta, min_energy, thetas.cpu().numpy(), energies

theta_opt, E_min, thetas, energies = vqe_h2_simple()

print(f"Optimal angle: {np.degrees(theta_opt):.2f} deg")
print(f"Ground state energy: {E_min:.4f} Ha")
print(f"Golden angle: {np.degrees(2*np.arctan(1/np.sqrt(PHI))):.2f} deg")

# Check connection to phi
ratio = theta_opt / (2*np.arctan(1/np.sqrt(PHI)))
print(f"Ratio to golden angle: {ratio:.4f}")

# =============================================================================
# 4. QUANTUM CHAOS: LEVEL STATISTICS
# =============================================================================

print("\n4. QUANTUM CHAOS DIAGNOSTICS")
print("-" * 40)

def quantum_kicked_rotor(n_states=512, n_samples=100, K=5.0):
    """
    Kicked Rotor - canonical model of quantum chaos

    H = p^2/2 + K*cos(x) * sum_n delta(t-n)

    Floquet operator: U = exp(-i*p^2/2) * exp(-i*K*cos(x))
    """

    N = n_states

    # Momentum basis
    p = torch.arange(-N//2, N//2, device=device, dtype=torch.float32)

    # Free evolution
    T_free = torch.exp(-1j * np.pi * p**2 / N).to(torch.complex64)

    # Kick
    x = torch.arange(N, device=device, dtype=torch.float32) * 2 * np.pi / N
    V_kick = torch.exp(-1j * K * torch.cos(x)).to(torch.complex64)

    all_ratios = []

    for _ in range(n_samples):
        # Random phase (ensemble)
        phase = torch.rand(1, device=device).item() * 2 * np.pi
        V_kick_shifted = torch.exp(-1j * K * torch.cos(x + phase)).to(torch.complex64)

        # Floquet operator in position basis
        # U = FFT^-1 * T_free * FFT * V_kick

        # Create matrix
        U = torch.zeros(N, N, dtype=torch.complex64, device=device)

        for j in range(N):
            # |j> in position basis
            state = torch.zeros(N, dtype=torch.complex64, device=device)
            state[j] = 1.0

            # Kick
            state = state * V_kick_shifted

            # FFT (to momentum basis)
            state = torch.fft.fft(state) / np.sqrt(N)

            # Free evolution
            state = state * T_free

            # Inverse FFT
            state = torch.fft.ifft(state) * np.sqrt(N)

            U[:, j] = state

        # Eigenvalues (phases)
        eigvals = torch.linalg.eigvals(U)
        phases = torch.angle(eigvals)
        phases_sorted = torch.sort(phases)[0]

        # Level spacings
        spacings = phases_sorted[1:] - phases_sorted[:-1]
        spacings = torch.abs(spacings)
        spacings = spacings[spacings > 1e-10]

        if len(spacings) > 1:
            ratios = spacings[:-1] / spacings[1:]
            ratios = torch.minimum(ratios, 1/ratios)
            all_ratios.extend(ratios.cpu().numpy())

    return np.mean(all_ratios)

start = time.time()
r_chaos = quantum_kicked_rotor(n_states=256, n_samples=50, K=10.0)
elapsed = time.time() - start

print(f"Kicked Rotor (K=10, chaotic regime)")
print(f"Mean level spacing ratio: {r_chaos:.4f}")
print(f"COE prediction: 0.5307")
print(f"1/phi: {1/PHI:.4f}")
print(f"Time: {elapsed:.1f}s")

# =============================================================================
# 5. GOLDEN MEAN IN QUASIPERIODIC SYSTEMS
# =============================================================================

print("\n5. AUBRY-ANDRE MODEL (quasiperiodic)")
print("-" * 40)

def aubry_andre_spectrum(N=1000, lambda_values=None):
    """
    Aubry-Andre model: tight-binding with quasiperiodic potential

    H = -t * sum_i (|i><i+1| + h.c.) + lambda * sum_i cos(2*pi*alpha*i + phi) |i><i|

    where alpha = (sqrt(5)-1)/2 = 1/phi (golden mean)

    Localization transition at lambda = 2t
    """

    if lambda_values is None:
        lambda_values = [0.5, 1.0, 2.0, 3.0]  # from delocalized to localized

    alpha = 1 / PHI  # Golden mean!
    t = 1.0
    phi = 0.0

    results = {}

    for lam in lambda_values:
        # Hamiltonian
        H = torch.zeros(N, N, device=device)

        # Hopping
        for i in range(N-1):
            H[i, i+1] = -t
            H[i+1, i] = -t

        # Periodic boundary
        H[0, N-1] = -t
        H[N-1, 0] = -t

        # Quasiperiodic potential
        for i in range(N):
            H[i, i] = lam * np.cos(2 * np.pi * alpha * i + phi)

        # Spectrum
        eigvals = torch.linalg.eigvalsh(H)
        eigvals_sorted = torch.sort(eigvals)[0]

        # Level spacing statistics
        spacings = eigvals_sorted[1:] - eigvals_sorted[:-1]
        spacings = spacings[spacings > 1e-10]

        if len(spacings) > 1:
            ratios = spacings[:-1] / spacings[1:]
            ratios = torch.minimum(ratios, 1/ratios)
            mean_r = ratios.mean().item()
        else:
            mean_r = 0

        # IPR (Inverse Participation Ratio) for localization
        _, eigvecs = torch.linalg.eigh(H)
        ipr = torch.mean(torch.sum(torch.abs(eigvecs)**4, dim=0)).item()

        results[lam] = {'ratio': mean_r, 'ipr': ipr}

    return results

results = aubry_andre_spectrum()

print(f"Aubry-Andre model (alpha = 1/phi)")
print(f"Localization transition at lambda = 2")
print()
for lam, data in results.items():
    phase = "Extended" if lam < 2 else "Critical" if lam == 2 else "Localized"
    print(f"  lambda={lam}: ratio={data['ratio']:.4f}, IPR={data['ipr']:.6f} ({phase})")

# =============================================================================
# SUMMARY
# =============================================================================

print("\n" + "=" * 60)
print("SUMMARY: PHI IN QUANTUM SYSTEMS")
print("=" * 60)
print(f"""
1. Entanglement spectrum: Schmidt ratio ~ {mean_ratio:.3f}

2. Optimal gate angles: golden angle = {np.degrees(2*np.arctan(1/np.sqrt(PHI))):.1f} deg
   appears naturally in probability ratios

3. VQE: optimal angle depends on Hamiltonian,
   phi appears in specific cases

4. Quantum chaos: level statistics ~ 0.53
   (related to RMT, not directly to phi)

5. Aubry-Andre: phi IS the quasiperiodic frequency!
   - Alpha = 1/phi defines the model
   - Localization transition at lambda=2

KEY INSIGHT: phi appears in quasiperiodic/aperiodic systems
because it is the "most irrational" number - hardest to
approximate by rationals, giving maximal aperiodicity.
""")
