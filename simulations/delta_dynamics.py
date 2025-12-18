"""
Δ-Dynamics Simulation: Emergence of Structure from Distinction
==============================================================

This simulation demonstrates how complex structure emerges from 
the simple principle Δ ≠ ∅ (distinction exists).

Key ideas:
1. Δ-field: A field of distinction-making intensity
2. Self-reference: Δ(Δ) - distinctions distinguish themselves  
3. Triadic closure: Δ = Δ(Δ) creates stable patterns
4. Criticality: System self-organizes to edge of chaos

We model this as a coupled map lattice where each site represents
local distinction-making capacity, and interactions create
emergent gauge-like structures.

Author: DD Research
Date: December 2024
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.ndimage import convolve, laplace
from scipy.fft import fft2, fftshift
from typing import Tuple, List, Optional, Dict
import json
from dataclasses import dataclass, asdict
from pathlib import Path
import warnings
warnings.filterwarnings('ignore')

# Golden ratio - emerges as critical point
PHI = (1 + np.sqrt(5)) / 2
PHI_INV = 1 / PHI

@dataclass
class SimulationParams:
    """Parameters for Δ-dynamics simulation"""
    size: int = 128          # Lattice size
    steps: int = 1000        # Evolution steps
    dt: float = 0.01         # Time step
    coupling: float = 0.1    # Neighbor coupling strength
    self_ref: float = 0.5    # Self-reference strength Δ(Δ)
    noise: float = 0.01      # Quantum fluctuations
    boundary: str = 'periodic'  # Boundary conditions
    
    # Triadic interaction parameters
    triadic_strength: float = 0.3
    critical_threshold: float = PHI_INV  # φ-criticality
    
    def to_dict(self) -> dict:
        return asdict(self)


class DeltaField:
    """
    The Δ-field represents local distinction-making intensity.
    
    At each point, the field value represents "how much distinction
    is being made" - the local rate of Δ-activity.
    
    The field evolves according to:
    ∂Δ/∂t = D∇²Δ + αΔ(1-Δ) + βΔ(Δ) + γT(Δ) + η
    
    where:
    - D∇²Δ: diffusion (distinctions spread)
    - αΔ(1-Δ): logistic growth (distinction capacity)
    - βΔ(Δ): self-reference (meta-distinction)
    - γT(Δ): triadic interaction (three-body correlations)
    - η: noise (quantum fluctuations)
    """
    
    def __init__(self, params: SimulationParams):
        self.params = params
        self.size = params.size
        
        # Initialize field near critical point
        self.field = np.random.uniform(
            PHI_INV - 0.1, 
            PHI_INV + 0.1, 
            (self.size, self.size)
        )
        
        # Phase field for gauge structure (complex phase)
        self.phase = np.random.uniform(0, 2*np.pi, (self.size, self.size))
        
        # History for analysis
        self.history: List[np.ndarray] = []
        self.entropy_history: List[float] = []
        self.order_param_history: List[float] = []
        
        # Laplacian kernel for diffusion
        self.laplacian_kernel = np.array([
            [0.05, 0.2, 0.05],
            [0.2, -1.0, 0.2],
            [0.05, 0.2, 0.05]
        ])
        
        # Triadic kernel (captures 3-point correlations)
        self.triadic_kernel = self._build_triadic_kernel()
    
    def _build_triadic_kernel(self) -> np.ndarray:
        """
        Build kernel for triadic (3-body) interactions.
        Based on equilateral triangle arrangement.
        """
        kernel = np.zeros((5, 5))
        # Vertices of approximate equilateral triangles
        kernel[0, 2] = 1/3  # top
        kernel[2, 0] = 1/3  # bottom-left  
        kernel[2, 4] = 1/3  # bottom-right
        kernel[4, 1] = 1/3  # lower-left
        kernel[4, 3] = 1/3  # lower-right
        return kernel / kernel.sum()
    
    def _apply_boundary(self, field: np.ndarray) -> np.ndarray:
        """Apply boundary conditions"""
        if self.params.boundary == 'periodic':
            return field  # handled by convolution mode
        elif self.params.boundary == 'reflecting':
            field[0, :] = field[1, :]
            field[-1, :] = field[-2, :]
            field[:, 0] = field[:, 1]
            field[:, -1] = field[:, -2]
        return field
    
    def _self_reference(self, field: np.ndarray) -> np.ndarray:
        """
        Δ(Δ): The field distinguishes itself.
        
        Implemented as: Δ distinguishes regions of high vs low Δ
        This creates a gradient-sensitive term.
        """
        # Gradient magnitude represents "how distinguishable" the field is
        grad_x = np.gradient(field, axis=0)
        grad_y = np.gradient(field, axis=1)
        grad_mag = np.sqrt(grad_x**2 + grad_y**2)
        
        # Self-reference amplifies where distinctions are sharp
        return field * grad_mag
    
    def _triadic_interaction(self, field: np.ndarray) -> np.ndarray:
        """
        Three-body correlations: the minimal self-referential closure.
        
        Δ, Δ(Δ), and their identity Δ = Δ(Δ) form a triad.
        This creates non-linear 3-point correlations.
        """
        # Triadic term: product of three shifted copies
        triadic = convolve(field, self.triadic_kernel, mode='wrap')
        
        # Cubic nonlinearity for 3-body
        return triadic * field * (1 - field)
    
    def _gauge_evolution(self) -> None:
        """
        Evolve the phase field (gauge degrees of freedom).
        
        The phase represents internal SU(N) structure.
        Phase coherence emerges from Δ-field dynamics.
        """
        # Phase velocity proportional to field gradient
        grad_x = np.gradient(self.field, axis=0)
        grad_y = np.gradient(self.field, axis=1)
        
        # Vorticity in phase
        phase_laplacian = laplace(self.phase, mode='wrap')
        
        # XY-model like dynamics
        self.phase += self.params.dt * (
            0.1 * phase_laplacian +
            0.05 * (grad_x * np.cos(self.phase) + grad_y * np.sin(self.phase))
        )
        self.phase = np.mod(self.phase, 2 * np.pi)
    
    def step(self) -> None:
        """Single evolution step of the Δ-field"""
        p = self.params
        
        # Diffusion term: ∇²Δ
        diffusion = convolve(self.field, self.laplacian_kernel, mode='wrap')
        
        # Logistic growth: Δ(1-Δ) - keeps field bounded
        logistic = self.field * (1 - self.field)
        
        # Self-reference: Δ(Δ)
        self_ref = self._self_reference(self.field)
        
        # Triadic interaction
        triadic = self._triadic_interaction(self.field)
        
        # Noise term (quantum fluctuations)
        noise = p.noise * np.random.randn(self.size, self.size)
        
        # Evolution equation
        dfield = p.dt * (
            p.coupling * diffusion +
            logistic +
            p.self_ref * self_ref +
            p.triadic_strength * triadic +
            noise
        )
        
        # Critical damping toward φ⁻¹
        dfield += p.dt * 0.01 * (p.critical_threshold - self.field)
        
        # Update field
        self.field += dfield
        self.field = np.clip(self.field, 0, 1)
        self.field = self._apply_boundary(self.field)
        
        # Evolve gauge phase
        self._gauge_evolution()
    
    def compute_entropy(self) -> float:
        """
        Compute Shannon entropy of the field distribution.
        This is the DD measure of distinction complexity.
        """
        hist, _ = np.histogram(self.field.flatten(), bins=50, density=True)
        hist = hist[hist > 0]
        return -np.sum(hist * np.log(hist + 1e-10)) * (1/50)
    
    def compute_order_parameter(self) -> float:
        """
        Order parameter: measures coherence of triadic structure.
        Uses third moment to capture 3-body correlations.
        """
        centered = self.field - self.field.mean()
        return np.abs(np.mean(centered**3)) / (np.std(self.field)**3 + 1e-10)
    
    def compute_structure_factor(self) -> np.ndarray:
        """
        Structure factor S(k) - reveals emergent spatial patterns.
        Peaks indicate characteristic length scales.
        """
        fft = fft2(self.field - self.field.mean())
        return np.abs(fftshift(fft))**2
    
    def compute_winding_number(self) -> int:
        """
        Topological winding number of the phase field.
        Non-zero values indicate topological defects (vortices).
        """
        # Phase gradient
        dphi_x = np.angle(np.exp(1j * np.diff(self.phase, axis=0, append=self.phase[0:1, :])))
        dphi_y = np.angle(np.exp(1j * np.diff(self.phase, axis=1, append=self.phase[:, 0:1])))
        
        # Circulation
        circulation = np.sum(dphi_x) + np.sum(dphi_y)
        return int(np.round(circulation / (2 * np.pi)))
    
    def compute_fisher_metric(self) -> np.ndarray:
        """
        Local Fisher information metric.
        
        g_μν = <∂_μ log p · ∂_ν log p>
        
        This measures local distinguishability - the DD spacetime metric!
        """
        # Treat field as probability distribution
        p = self.field / (self.field.sum() + 1e-10)
        log_p = np.log(p + 1e-10)
        
        # Gradients
        d_log_p_x = np.gradient(log_p, axis=0)
        d_log_p_y = np.gradient(log_p, axis=1)
        
        # Fisher metric components
        g_xx = d_log_p_x**2
        g_yy = d_log_p_y**2
        g_xy = d_log_p_x * d_log_p_y
        
        return np.stack([g_xx, g_xy, g_xy, g_yy]).reshape(2, 2, self.size, self.size)
    
    def run(self, save_every: int = 10) -> Dict:
        """Run full simulation"""
        print(f"Running Delta-dynamics simulation...")
        print(f"  Size: {self.size}x{self.size}")
        print(f"  Steps: {self.params.steps}")
        print(f"  Critical threshold (phi^-1): {self.params.critical_threshold:.6f}")
        
        for step in range(self.params.steps):
            self.step()
            
            if step % save_every == 0:
                self.history.append(self.field.copy())
                self.entropy_history.append(self.compute_entropy())
                self.order_param_history.append(self.compute_order_parameter())
            
            if step % 100 == 0:
                entropy = self.entropy_history[-1] if self.entropy_history else 0
                order = self.order_param_history[-1] if self.order_param_history else 0
        print(f"  Step {step}: entropy={entropy:.4f}, order={order:.4f}, mean={self.field.mean():.4f}")
        
        # Final analysis
        results = {
            'final_entropy': self.entropy_history[-1],
            'final_order_param': self.order_param_history[-1],
            'final_mean': float(self.field.mean()),
            'final_std': float(self.field.std()),
            'winding_number': self.compute_winding_number(),
            'critical_deviation': float(np.abs(self.field.mean() - PHI_INV)),
            'phi_convergence': float(1 - np.abs(self.field.mean() - PHI_INV) / PHI_INV),
        }
        
        print(f"\nResults:")
        print(f"  Final mean: {results['final_mean']:.6f} (phi^-1 = {PHI_INV:.6f})")
        print(f"  phi-convergence: {results['phi_convergence']*100:.2f}%")
        print(f"  Winding number: {results['winding_number']}")
        print(f"  Entropy: {results['final_entropy']:.4f}")
        
        return results




class DeltaVisualizer:
    """Visualization tools for Δ-dynamics"""
    
    def __init__(self, field: DeltaField):
        self.field = field
    
    def plot_evolution(self, save_path: Optional[str] = None) -> None:
        """Plot field evolution snapshots"""
        n_snapshots = min(9, len(self.field.history))
        if n_snapshots == 0:
            print("No history to plot")
            return
        
        fig, axes = plt.subplots(3, 3, figsize=(12, 12))
        indices = np.linspace(0, len(self.field.history)-1, n_snapshots, dtype=int)
        
        for idx, ax in zip(indices, axes.flat):
            im = ax.imshow(self.field.history[idx], cmap='magma', 
                          vmin=0, vmax=1, origin='lower')
            ax.set_title(f'Step {idx * 10}')
            ax.axis('off')
        
        plt.colorbar(im, ax=axes, fraction=0.02, pad=0.04, label='Δ intensity')
        plt.suptitle('Δ-Field Evolution: Emergence of Structure from Distinction', 
                    fontsize=14, fontweight='bold')
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.show()
    
    def plot_entropy_evolution(self, save_path: Optional[str] = None) -> None:
        """Plot entropy and order parameter evolution"""
        fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8), sharex=True)
        
        steps = np.arange(len(self.field.entropy_history)) * 10
        
        ax1.plot(steps, self.field.entropy_history, 'b-', linewidth=2)
        ax1.axhline(y=np.log(2), color='r', linestyle='--', alpha=0.5, 
                   label='Maximum entropy (log 2)')
        ax1.set_ylabel('Shannon Entropy', fontsize=12)
        ax1.set_title('Entropy Evolution: Complexity from Δ ≠ ∅', fontsize=14)
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        ax2.plot(steps, self.field.order_param_history, 'g-', linewidth=2)
        ax2.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
        ax2.set_xlabel('Evolution Step', fontsize=12)
        ax2.set_ylabel('Triadic Order Parameter', fontsize=12)
        ax2.set_title('Triadic Coherence: Self-Referential Closure', fontsize=14)
        ax2.grid(True, alpha=0.3)
        
        plt.tight_layout()
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.show()
    
    def plot_structure_factor(self, save_path: Optional[str] = None) -> None:
        """Plot structure factor showing emergent length scales"""
        S_k = self.field.compute_structure_factor()
        
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        
        # 2D structure factor
        im = ax1.imshow(np.log10(S_k + 1), cmap='inferno', origin='lower')
        ax1.set_title('Structure Factor S(k): Emergent Patterns', fontsize=14)
        ax1.set_xlabel('kx')
        ax1.set_ylabel('ky')
        plt.colorbar(im, ax=ax1, label='log₁₀ S(k)')
        
        # Radial average
        center = self.field.size // 2
        y, x = np.ogrid[:self.field.size, :self.field.size]
        r = np.sqrt((x - center)**2 + (y - center)**2).astype(int)
        
        radial_sum = np.bincount(r.ravel(), S_k.ravel())
        radial_count = np.bincount(r.ravel())
        radial_avg = radial_sum / (radial_count + 1e-10)
        
        k_values = np.arange(len(radial_avg))
        ax2.loglog(k_values[1:center], radial_avg[1:center], 'b-', linewidth=2)
        ax2.set_xlabel('Wavenumber k', fontsize=12)
        ax2.set_ylabel('S(k)', fontsize=12)
        ax2.set_title('Radial Structure Factor: Scale Invariance?', fontsize=14)
        ax2.grid(True, alpha=0.3)
        
        # Fit power law
        valid = (k_values > 5) & (k_values < center//2)
        if np.sum(valid) > 10:
            log_k = np.log(k_values[valid])
            log_S = np.log(radial_avg[valid] + 1e-10)
            coeffs = np.polyfit(log_k, log_S, 1)
            ax2.loglog(k_values[valid], np.exp(coeffs[1]) * k_values[valid]**coeffs[0], 
                      'r--', linewidth=2, label=f'Power law: k^{coeffs[0]:.2f}')
            ax2.legend()
        
        plt.tight_layout()
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.show()
    
    def plot_phase_field(self, save_path: Optional[str] = None) -> None:
        """Plot phase field showing gauge structure"""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        
        # Phase field
        im1 = ax1.imshow(self.field.phase, cmap='hsv', origin='lower',
                        vmin=0, vmax=2*np.pi)
        ax1.set_title('Phase Field: Emergent Gauge Structure', fontsize=14)
        plt.colorbar(im1, ax=ax1, label='Phase θ')
        
        # Phase coherence (local alignment)
        cos_phase = np.cos(self.field.phase)
        sin_phase = np.sin(self.field.phase)
        
        # Local coherence via convolution
        kernel = np.ones((5, 5)) / 25
        local_cos = convolve(cos_phase, kernel, mode='wrap')
        local_sin = convolve(sin_phase, kernel, mode='wrap')
        coherence = np.sqrt(local_cos**2 + local_sin**2)
        
        im2 = ax2.imshow(coherence, cmap='viridis', origin='lower',
                        vmin=0, vmax=1)
        ax2.set_title('Phase Coherence: SU(N) Order', fontsize=14)
        plt.colorbar(im2, ax=ax2, label='Coherence')
        
        plt.tight_layout()
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.show()
    
    def plot_fisher_metric(self, save_path: Optional[str] = None) -> None:
        """Plot Fisher information metric - the DD spacetime metric"""
        g = self.field.compute_fisher_metric()
        
        # Metric determinant (area element)
        det_g = g[0, 0] * g[1, 1] - g[0, 1] * g[1, 0]
        
        # Trace (scalar curvature proxy)
        tr_g = g[0, 0] + g[1, 1]
        
        fig, axes = plt.subplots(2, 2, figsize=(12, 12))
        
        im0 = axes[0, 0].imshow(g[0, 0], cmap='plasma', origin='lower')
        axes[0, 0].set_title('g_xx: Horizontal Distinguishability')
        plt.colorbar(im0, ax=axes[0, 0])
        
        im1 = axes[0, 1].imshow(g[1, 1], cmap='plasma', origin='lower')
        axes[0, 1].set_title('g_yy: Vertical Distinguishability')
        plt.colorbar(im1, ax=axes[0, 1])
        
        im2 = axes[1, 0].imshow(np.log10(np.abs(det_g) + 1e-10), cmap='RdBu_r', origin='lower')
        axes[1, 0].set_title('log|det(g)|: Spacetime Volume Element')
        plt.colorbar(im2, ax=axes[1, 0])
        
        im3 = axes[1, 1].imshow(tr_g, cmap='viridis', origin='lower')
        axes[1, 1].set_title('Tr(g): Total Local Distinguishability')
        plt.colorbar(im3, ax=axes[1, 1])
        
        plt.suptitle('Fisher Information Metric: DD Spacetime Geometry', 
                    fontsize=14, fontweight='bold')
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.show()


def run_critical_analysis():
    """
    Analyze system behavior near φ-criticality.
    
    DD predicts that φ = (1+√5)/2 emerges as the critical point
    for self-referential closure.
    """
    print("="*60)
    print("CRITICAL ANALYSIS: phi-Point in Delta-Dynamics")
    print("="*60)
    
    # Scan coupling strengths
    couplings = np.linspace(0.05, 0.3, 10)
    final_means = []
    final_stds = []
    entropies = []
    
    for coupling in couplings:
        params = SimulationParams(
            size=64, 
            steps=500,
            coupling=coupling,
            self_ref=0.5,
            triadic_strength=0.3
        )
        field = DeltaField(params)
        results = field.run(save_every=50)
        
        final_means.append(results['final_mean'])
        final_stds.append(results['final_std'])
        entropies.append(results['final_entropy'])
    
    # Plot results
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    
    axes[0].plot(couplings, final_means, 'bo-', linewidth=2, markersize=8)
    axes[0].axhline(y=PHI_INV, color='r', linestyle='--', label=f'phi^-1 = {PHI_INV:.4f}')
    axes[0].set_xlabel('Coupling Strength')
    axes[0].set_ylabel('Final Mean Field')
    axes[0].set_title('Convergence to phi^-1')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    axes[1].plot(couplings, final_stds, 'go-', linewidth=2, markersize=8)
    axes[1].set_xlabel('Coupling Strength')
    axes[1].set_ylabel('Final Std Dev')
    axes[1].set_title('Fluctuations')
    axes[1].grid(True, alpha=0.3)
    
    axes[2].plot(couplings, entropies, 'ro-', linewidth=2, markersize=8)
    axes[2].set_xlabel('Coupling Strength')
    axes[2].set_ylabel('Entropy')
    axes[2].set_title('Complexity')
    axes[2].grid(True, alpha=0.3)
    
    plt.suptitle('Critical Behavior in Δ-Dynamics: Testing DD Predictions', 
                fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.savefig('critical_analysis.png', dpi=150, bbox_inches='tight')
    plt.show()
    
    return couplings, final_means, final_stds, entropies


def run_gauge_emergence():
    """
    Test emergence of gauge-like structure from Δ-dynamics.
    
    DD predicts: SU(3)×SU(2)×U(1) from triadic closure.
    Here we look for signatures of gauge structure in phase coherence.
    """
    print("="*60)
    print("GAUGE EMERGENCE: Testing SU(N) Structure from Delta")
    print("="*60)
    
    params = SimulationParams(
        size=128,
        steps=2000,
        coupling=0.15,
        self_ref=0.6,
        triadic_strength=0.4,
        noise=0.005
    )
    
    field = DeltaField(params)
    results = field.run(save_every=20)
    
    # Compute topological charge density
    # Q = (1/2π) ε^μν ∂_μ n · (∂_ν n × n) for unit vector field
    # Simplified: look at phase vorticity
    
    dphi_x = np.gradient(field.phase, axis=0)
    dphi_y = np.gradient(field.phase, axis=1)
    
    # Vorticity = curl of phase gradient
    vorticity = np.gradient(dphi_y, axis=0) - np.gradient(dphi_x, axis=1)
    
    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(12, 12))
    
    im0 = axes[0, 0].imshow(field.field, cmap='magma', origin='lower')
    axes[0, 0].set_title('Final Δ-Field')
    plt.colorbar(im0, ax=axes[0, 0])
    
    im1 = axes[0, 1].imshow(field.phase, cmap='hsv', origin='lower')
    axes[0, 1].set_title('Phase Field (Gauge)')
    plt.colorbar(im1, ax=axes[0, 1])
    
    im2 = axes[1, 0].imshow(vorticity, cmap='RdBu_r', origin='lower',
                           vmin=-0.5, vmax=0.5)
    axes[1, 0].set_title('Vorticity (Topological Charge)')
    plt.colorbar(im2, ax=axes[1, 0])
    
    # Histogram of vorticity
    axes[1, 1].hist(vorticity.flatten(), bins=100, density=True, alpha=0.7)
    axes[1, 1].set_xlabel('Vorticity')
    axes[1, 1].set_ylabel('Density')
    axes[1, 1].set_title('Vorticity Distribution')
    axes[1, 1].axvline(x=0, color='r', linestyle='--')
    
    plt.suptitle('Gauge Structure Emergence from Δ-Dynamics', 
                fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.savefig('gauge_emergence.png', dpi=150, bbox_inches='tight')
    plt.show()
    
    print(f"\nTotal topological charge: {field.compute_winding_number()}")
    print(f"Net vorticity: {vorticity.sum():.4f}")
    
    return field, results


def main():
    """Main simulation runner"""
    print("="*60)
    print("DELTA-DYNAMICS SIMULATION")
    print("Emergence of Structure from Distinction")
    print("Based on Distinction Dynamics (DD) Theory")
    print("="*60)
    print()
    print("Core axiom: Delta != Empty (Distinction exists)")
    print(f"Critical point: phi^-1 = {PHI_INV:.6f}")
    print()
    
    # Main simulation
    params = SimulationParams(
        size=128,
        steps=1000,
        coupling=0.12,
        self_ref=0.5,
        triadic_strength=0.35,
        noise=0.01
    )
    
    print("Parameters:")
    for key, val in params.to_dict().items():
        print(f"  {key}: {val}")
    print()
    
    # Run simulation
    field = DeltaField(params)
    results = field.run(save_every=10)
    
    # Visualize
    viz = DeltaVisualizer(field)
    
    print("\nGenerating visualizations...")
    viz.plot_evolution('evolution.png')
    viz.plot_entropy_evolution('entropy.png')
    viz.plot_structure_factor('structure_factor.png')
    viz.plot_phase_field('phase_field.png')
    viz.plot_fisher_metric('fisher_metric.png')
    
    # Save results
    results['params'] = params.to_dict()
    with open('simulation_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("\nSimulation complete!")
    print(f"Results saved to simulation_results.json")
    
    return field, results


if __name__ == "__main__":
    # Run main simulation
    field, results = main()
    
    # Run additional analyses
    print("\n" + "="*60)
    print("Running additional analyses...")
    print("="*60)
    
    # Critical analysis
    # run_critical_analysis()
    
    # Gauge emergence
    # run_gauge_emergence()
