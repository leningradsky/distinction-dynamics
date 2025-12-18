"""
Delta-Dynamics v2: Proper φ-Critical Dynamics
=============================================

Fixed dynamics with double-well potential centered at φ⁻¹
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.ndimage import convolve, laplace
from scipy.fft import fft2, fftshift
from typing import Dict, List
import json

# Constants
PHI = (1 + np.sqrt(5)) / 2
PHI_INV = 1 / PHI  # ~0.618

class DeltaFieldV2:
    """
    Delta-field with proper phi-critical dynamics.
    
    Evolution equation:
    dΔ/dt = D∇²Δ - dV/dΔ + interactions + noise
    
    where V(Δ) = (Δ - φ⁻¹)² (Δ - 1)² has minima at φ⁻¹ and 1
    with φ⁻¹ being the deeper minimum (ground state)
    """
    
    def __init__(self, size=128, steps=2000, dt=0.005, 
                 diffusion=0.05, noise=0.02, coupling=0.1):
        self.size = size
        self.steps = steps
        self.dt = dt
        self.diffusion = diffusion
        self.noise_amp = noise
        self.coupling = coupling
        
        # Initialize near phi^-1 with fluctuations
        self.field = PHI_INV + 0.1 * np.random.randn(size, size)
        self.field = np.clip(self.field, 0.01, 0.99)
        
        # Phase field for gauge structure
        self.phase = np.random.uniform(0, 2*np.pi, (size, size))
        
        # History
        self.history = []
        self.mean_history = []
        self.std_history = []
        
        # Laplacian kernel
        self.lap_kernel = np.array([
            [0.05, 0.2, 0.05],
            [0.2, -1.0, 0.2],
            [0.05, 0.2, 0.05]
        ])
    
    def potential(self, x):
        """Double-well potential with minimum at phi^-1"""
        # V(x) = a(x - phi^-1)^2 + b(x - phi^-1)^4
        # Simplified: quartic with minimum at phi^-1
        delta = x - PHI_INV
        return delta**2 * (1 + 2*delta**2)
    
    def potential_derivative(self, x):
        """dV/dx - force from potential"""
        delta = x - PHI_INV
        return 2*delta * (1 + 4*delta**2)
    
    def triadic_coupling(self, field):
        """Three-body interaction term"""
        # Shifted fields
        f_up = np.roll(field, 1, axis=0)
        f_right = np.roll(field, 1, axis=1)
        f_diag = np.roll(np.roll(field, 1, axis=0), 1, axis=1)
        
        # Triple product - triadic correlation
        return field * f_up * f_right - PHI_INV**3
    
    def self_reference(self, field):
        """Δ(Δ) - gradient-based self-reference"""
        grad_x = np.gradient(field, axis=0)
        grad_y = np.gradient(field, axis=1)
        grad_mag = np.sqrt(grad_x**2 + grad_y**2 + 1e-10)
        
        # Self-reference amplifies gradients
        return grad_mag * (field - PHI_INV)
    
    def step(self):
        """Single evolution step"""
        # Laplacian (diffusion)
        lap = convolve(self.field, self.lap_kernel, mode='wrap')
        
        # Potential force (drives to phi^-1)
        force = -self.potential_derivative(self.field)
        
        # Triadic interaction
        triadic = self.triadic_coupling(self.field)
        
        # Self-reference
        self_ref = self.self_reference(self.field)
        
        # Noise
        noise = self.noise_amp * np.random.randn(self.size, self.size)
        
        # Update
        dfield = self.dt * (
            self.diffusion * lap +
            force +
            self.coupling * triadic +
            0.05 * self_ref +
            noise
        )
        
        self.field += dfield
        self.field = np.clip(self.field, 0.01, 0.99)
        
        # Phase evolution (simplified XY model)
        phase_lap = laplace(self.phase, mode='wrap')
        self.phase += 0.01 * self.dt * phase_lap
        self.phase = np.mod(self.phase, 2*np.pi)
    
    def run(self, save_every=20):
        """Run simulation"""
        print("Running Delta-Dynamics v2...")
        print(f"Target: phi^-1 = {PHI_INV:.6f}")
        
        for i in range(self.steps):
            self.step()
            
            if i % save_every == 0:
                self.history.append(self.field.copy())
                self.mean_history.append(self.field.mean())
                self.std_history.append(self.field.std())
            
            if i % 200 == 0:
                print(f"  Step {i}: mean={self.field.mean():.4f}, std={self.field.std():.4f}")
        
        # Final stats
        convergence = 1 - abs(self.field.mean() - PHI_INV) / PHI_INV
        print(f"\nFinal: mean={self.field.mean():.6f}, convergence={convergence*100:.1f}%")
        
        return {
            'final_mean': float(self.field.mean()),
            'final_std': float(self.field.std()),
            'convergence': float(convergence),
            'target': PHI_INV
        }
    
    def compute_fisher_metric(self):
        """Fisher information metric"""
        eps = 1e-10
        p = self.field / (self.field.sum() + eps)
        log_p = np.log(p + eps)
        
        dx = np.gradient(log_p, axis=0)
        dy = np.gradient(log_p, axis=1)
        
        return {
            'g_xx': dx**2,
            'g_yy': dy**2,
            'g_xy': dx * dy,
            'trace': dx**2 + dy**2
        }
    
    def compute_entropy(self):
        """Proper Shannon entropy"""
        hist, _ = np.histogram(self.field, bins=50, range=(0, 1), density=True)
        hist = hist[hist > 0]
        dx = 1.0 / 50
        return -np.sum(hist * np.log(hist) * dx)


def plot_results(field: DeltaFieldV2, save_prefix='v2_'):
    """Generate all visualizations"""
    
    # 1. Evolution
    fig, axes = plt.subplots(3, 3, figsize=(12, 12))
    n = min(9, len(field.history))
    indices = np.linspace(0, len(field.history)-1, n, dtype=int)
    
    for idx, ax in zip(indices, axes.flat):
        im = ax.imshow(field.history[idx], cmap='magma', vmin=0, vmax=1, origin='lower')
        step = idx * 20
        ax.set_title(f'Step {step}, mean={field.history[idx].mean():.3f}')
        ax.axis('off')
    
    plt.colorbar(im, ax=axes, fraction=0.02, pad=0.04)
    plt.suptitle(f'Delta-Field Evolution (target: phi^-1 = {PHI_INV:.4f})', fontsize=14)
    plt.savefig(f'{save_prefix}evolution.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    # 2. Convergence
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))
    
    steps = np.arange(len(field.mean_history)) * 20
    ax1.plot(steps, field.mean_history, 'b-', linewidth=2, label='Mean field')
    ax1.axhline(y=PHI_INV, color='r', linestyle='--', linewidth=2, label=f'phi^-1 = {PHI_INV:.4f}')
    ax1.set_ylabel('Mean Field Value')
    ax1.set_title('Convergence to phi-Critical Point')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    ax2.plot(steps, field.std_history, 'g-', linewidth=2)
    ax2.set_xlabel('Step')
    ax2.set_ylabel('Standard Deviation')
    ax2.set_title('Field Fluctuations')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(f'{save_prefix}convergence.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    # 3. Final state analysis
    fig, axes = plt.subplots(2, 2, figsize=(12, 12))
    
    # Field
    im0 = axes[0, 0].imshow(field.field, cmap='magma', origin='lower')
    axes[0, 0].set_title('Final Delta-Field')
    plt.colorbar(im0, ax=axes[0, 0])
    
    # Distribution
    axes[0, 1].hist(field.field.flatten(), bins=50, density=True, alpha=0.7, color='blue')
    axes[0, 1].axvline(x=PHI_INV, color='r', linestyle='--', linewidth=2, label=f'phi^-1')
    axes[0, 1].axvline(x=field.field.mean(), color='g', linestyle='-', linewidth=2, label=f'mean')
    axes[0, 1].set_xlabel('Field Value')
    axes[0, 1].set_ylabel('Density')
    axes[0, 1].set_title('Field Distribution')
    axes[0, 1].legend()
    
    # Fisher metric trace
    fisher = field.compute_fisher_metric()
    im2 = axes[1, 0].imshow(np.log10(fisher['trace'] + 1e-10), cmap='viridis', origin='lower')
    axes[1, 0].set_title('log Fisher Metric Trace (Distinguishability)')
    plt.colorbar(im2, ax=axes[1, 0])
    
    # Phase field
    im3 = axes[1, 1].imshow(field.phase, cmap='hsv', origin='lower', vmin=0, vmax=2*np.pi)
    axes[1, 1].set_title('Phase Field (Gauge Structure)')
    plt.colorbar(im3, ax=axes[1, 1])
    
    plt.suptitle('Delta-Dynamics: Final State Analysis', fontsize=14)
    plt.tight_layout()
    plt.savefig(f'{save_prefix}analysis.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    # 4. Structure factor
    fft = fft2(field.field - field.field.mean())
    S_k = np.abs(fftshift(fft))**2
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    im = ax1.imshow(np.log10(S_k + 1), cmap='inferno', origin='lower')
    ax1.set_title('Structure Factor S(k)')
    plt.colorbar(im, ax=ax1)
    
    # Radial average
    center = field.size // 2
    y, x = np.ogrid[:field.size, :field.size]
    r = np.sqrt((x - center)**2 + (y - center)**2).astype(int)
    
    radial_sum = np.bincount(r.ravel(), S_k.ravel())
    radial_count = np.bincount(r.ravel())
    radial_avg = radial_sum / (radial_count + 1e-10)
    
    k = np.arange(len(radial_avg))
    ax2.loglog(k[1:center], radial_avg[1:center], 'b-', linewidth=2)
    ax2.set_xlabel('Wavenumber k')
    ax2.set_ylabel('S(k)')
    ax2.set_title('Radial Structure Factor')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(f'{save_prefix}structure.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"Plots saved with prefix '{save_prefix}'")


if __name__ == "__main__":
    print("="*60)
    print("DELTA-DYNAMICS v2")
    print("Proper phi-critical dynamics")
    print("="*60)
    
    # Run simulation
    field = DeltaFieldV2(
        size=128,
        steps=3000,
        dt=0.005,
        diffusion=0.08,
        noise=0.015,
        coupling=0.2
    )
    
    results = field.run(save_every=30)
    
    # Generate plots
    plot_results(field, save_prefix='v2_')
    
    # Save results
    with open('v2_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("\nDone!")
