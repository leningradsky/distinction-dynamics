"""
DDCE Simulator — Distinction-Driven Cosmological Expansion
==========================================================

Numerical simulation of the DD cosmological model:

    dΔ/dt = a + bF + cM
    dF/dt = α₁Δ - α₂F + α₃M
    dM/dt = β₁Δ - β₂M + β₃F  
    dV/dt = k(Δ + F + M)

Author: Andrey Shkursky
Date: December 2025
"""

import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import Tuple, Optional
import json


@dataclass
class DDCEParameters:
    """Parameters for DDCE dynamical system."""
    
    # Distinction generation rates
    a: float = 0.01      # Physical entropy (slow)
    b: float = 0.1       # Biological adaptation
    c: float = 1.0       # Cognitive recursion (fast)
    
    # β-function coefficients (law evolution)
    alpha1: float = 0.5  # Δ → F coupling
    alpha2: float = 0.1  # F stabilization
    alpha3: float = 0.3  # M → F coupling
    
    # γ-function coefficients (meta-law evolution)  
    beta1: float = 0.4   # Δ → M coupling
    beta2: float = 0.1   # M stabilization
    beta3: float = 0.2   # F → M coupling
    
    # Cosmological coupling
    k: float = 0.1       # Volume response to complexity
    
    def to_dict(self):
        return self.__dict__
    
    @classmethod
    def from_dict(cls, d):
        return cls(**d)


class DDCESystem:
    """
    DDCE Dynamical System Simulator.
    
    State vector: [Δ, F, M, V]
    - Δ: Distinction complexity
    - F: Reaction laws (physics)
    - M: Meta-reactions (consciousness/science)
    - V: Cosmic volume
    """
    
    def __init__(self, params: Optional[DDCEParameters] = None):
        self.params = params or DDCEParameters()
        self.history = None
        
    def derivatives(self, t: float, state: np.ndarray) -> np.ndarray:
        """Compute derivatives of the DDCE system."""
        Delta, F, M, V = state
        p = self.params
        
        # Ensure non-negative values
        Delta = max(Delta, 0)
        F = max(F, 0)
        M = max(M, 0)
        V = max(V, 0)
        
        # dΔ/dt = a + bF + cM
        dDelta = p.a + p.b * F + p.c * M
        
        # dF/dt = α₁Δ - α₂F + α₃M (β-function)
        dF = p.alpha1 * Delta - p.alpha2 * F + p.alpha3 * M
        
        # dM/dt = β₁Δ - β₂M + β₃F (γ-function)
        dM = p.beta1 * Delta - p.beta2 * M + p.beta3 * F
        
        # dV/dt = k(Δ + F + M)
        dV = p.k * (Delta + F + M)
        
        return np.array([dDelta, dF, dM, dV])
    
    def compute_lagrangian(self, state: np.ndarray, state_dot: np.ndarray) -> float:
        """
        Compute Lagrangian L = T - U
        
        T = ½(Δ̇² + Ḟ² + Ṁ² + V̇²)
        U = -α₁ΔF - α₃FM - β₁ΔM - k(Δ+F+M)V
        """
        Delta, F, M, V = state
        dDelta, dF, dM, dV = state_dot
        p = self.params
        
        # Kinetic energy
        T = 0.5 * (dDelta**2 + dF**2 + dM**2 + dV**2)
        
        # Potential energy
        U = (-p.alpha1 * Delta * F 
             - p.alpha3 * F * M 
             - p.beta1 * Delta * M 
             - p.k * (Delta + F + M) * V)
        
        return T - U
    
    def compute_action(self) -> float:
        """Compute total action S = ∫L dt over the simulated trajectory."""
        if self.history is None:
            raise ValueError("Run simulate() first")
            
        t = self.history['t']
        states = self.history['states']
        
        action = 0.0
        for i in range(len(t) - 1):
            dt = t[i+1] - t[i]
            state = states[i]
            state_dot = self.derivatives(t[i], state)
            L = self.compute_lagrangian(state, state_dot)
            action += L * dt
            
        return action
    
    def compute_complexity(self, state: np.ndarray) -> float:
        """Compute distinction complexity C = Δ + F + M."""
        Delta, F, M, V = state
        return Delta + F + M
    
    def compute_hubble(self, state: np.ndarray, state_dot: np.ndarray) -> float:
        """
        Compute effective Hubble parameter H = V̇/V.
        In 3D: V ~ a³, so H = ȧ/a = V̇/(3V).
        """
        V = state[3]
        dV = state_dot[3]
        if V > 0:
            return dV / (3 * V)
        return 0.0
    
    def compute_lambda_eff(self, state: np.ndarray) -> float:
        """Compute effective cosmological constant Λ_eff = k(Δ + F + M)."""
        Delta, F, M, V = state
        return self.params.k * (Delta + F + M)
    
    def simulate(self, 
                 initial_state: Tuple[float, float, float, float] = (0.1, 0.1, 0.01, 1.0),
                 t_span: Tuple[float, float] = (0, 100),
                 n_points: int = 1000) -> dict:
        """
        Run DDCE simulation.
        
        Args:
            initial_state: (Δ₀, F₀, M₀, V₀)
            t_span: (t_start, t_end)
            n_points: Number of output points
            
        Returns:
            Dictionary with simulation results
        """
        t_eval = np.linspace(t_span[0], t_span[1], n_points)
        
        solution = solve_ivp(
            self.derivatives,
            t_span,
            initial_state,
            method='RK45',
            t_eval=t_eval,
            dense_output=True
        )
        
        # Compute derived quantities
        states = solution.y.T
        complexities = [self.compute_complexity(s) for s in states]
        lambda_effs = [self.compute_lambda_eff(s) for s in states]
        
        hubbles = []
        for i, (t, state) in enumerate(zip(solution.t, states)):
            state_dot = self.derivatives(t, state)
            hubbles.append(self.compute_hubble(state, state_dot))
        
        self.history = {
            't': solution.t,
            'states': states,
            'Delta': solution.y[0],
            'F': solution.y[1],
            'M': solution.y[2],
            'V': solution.y[3],
            'C': np.array(complexities),
            'Lambda_eff': np.array(lambda_effs),
            'H': np.array(hubbles),
            'success': solution.success
        }
        
        return self.history
    
    def analyze_growth_rates(self) -> dict:
        """Analyze exponential growth rates of state variables."""
        if self.history is None:
            raise ValueError("Run simulate() first")
            
        results = {}
        for var in ['Delta', 'F', 'M', 'V', 'C']:
            y = self.history[var]
            t = self.history['t']
            
            # Fit log(y) = λt + c to get growth rate λ
            mask = y > 0
            if np.sum(mask) > 10:
                log_y = np.log(y[mask])
                t_masked = t[mask]
                
                # Linear regression
                coeffs = np.polyfit(t_masked, log_y, 1)
                lambda_rate = coeffs[0]
                
                results[var] = {
                    'growth_rate': lambda_rate,
                    'doubling_time': np.log(2) / lambda_rate if lambda_rate > 0 else np.inf
                }
                
        return results
    
    def plot_evolution(self, save_path: Optional[str] = None):
        """Plot evolution of all state variables."""
        if self.history is None:
            raise ValueError("Run simulate() first")
            
        fig, axes = plt.subplots(2, 3, figsize=(15, 10))
        t = self.history['t']
        
        # Plot state variables
        axes[0, 0].semilogy(t, self.history['Delta'], 'b-', linewidth=2)
        axes[0, 0].set_xlabel('Time')
        axes[0, 0].set_ylabel('Δ (Distinctions)')
        axes[0, 0].set_title('Distinction Growth')
        axes[0, 0].grid(True, alpha=0.3)
        
        axes[0, 1].semilogy(t, self.history['F'], 'g-', linewidth=2)
        axes[0, 1].set_xlabel('Time')
        axes[0, 1].set_ylabel('F (Laws)')
        axes[0, 1].set_title('Law Evolution')
        axes[0, 1].grid(True, alpha=0.3)
        
        axes[0, 2].semilogy(t, self.history['M'], 'r-', linewidth=2)
        axes[0, 2].set_xlabel('Time')
        axes[0, 2].set_ylabel('M (Meta-laws)')
        axes[0, 2].set_title('Meta-law Evolution')
        axes[0, 2].grid(True, alpha=0.3)
        
        axes[1, 0].semilogy(t, self.history['V'], 'purple', linewidth=2)
        axes[1, 0].set_xlabel('Time')
        axes[1, 0].set_ylabel('V (Volume)')
        axes[1, 0].set_title('Cosmic Volume')
        axes[1, 0].grid(True, alpha=0.3)
        
        axes[1, 1].semilogy(t, self.history['C'], 'orange', linewidth=2)
        axes[1, 1].set_xlabel('Time')
        axes[1, 1].set_ylabel('C = Δ + F + M')
        axes[1, 1].set_title('Total Complexity')
        axes[1, 1].grid(True, alpha=0.3)
        
        axes[1, 2].plot(t, self.history['H'], 'brown', linewidth=2)
        axes[1, 2].set_xlabel('Time')
        axes[1, 2].set_ylabel('H = V̇/(3V)')
        axes[1, 2].set_title('Hubble Parameter')
        axes[1, 2].grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"Saved plot to {save_path}")
        
        plt.show()
        return fig
    
    def plot_phase_space(self, save_path: Optional[str] = None):
        """Plot phase space trajectories."""
        if self.history is None:
            raise ValueError("Run simulate() first")
            
        fig = plt.figure(figsize=(12, 5))
        
        # F vs Δ
        ax1 = fig.add_subplot(1, 2, 1)
        ax1.plot(self.history['Delta'], self.history['F'], 'b-', linewidth=1.5)
        ax1.scatter([self.history['Delta'][0]], [self.history['F'][0]], 
                   c='green', s=100, zorder=5, label='Start')
        ax1.scatter([self.history['Delta'][-1]], [self.history['F'][-1]], 
                   c='red', s=100, zorder=5, label='End')
        ax1.set_xlabel('Δ (Distinctions)')
        ax1.set_ylabel('F (Laws)')
        ax1.set_title('Phase Space: F vs Δ')
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        # M vs F
        ax2 = fig.add_subplot(1, 2, 2)
        ax2.plot(self.history['F'], self.history['M'], 'r-', linewidth=1.5)
        ax2.scatter([self.history['F'][0]], [self.history['M'][0]], 
                   c='green', s=100, zorder=5, label='Start')
        ax2.scatter([self.history['F'][-1]], [self.history['M'][-1]], 
                   c='red', s=100, zorder=5, label='End')
        ax2.set_xlabel('F (Laws)')
        ax2.set_ylabel('M (Meta-laws)')
        ax2.set_title('Phase Space: M vs F')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            
        plt.show()
        return fig


class DDCEScenarios:
    """Predefined DDCE scenarios for different cosmic epochs."""
    
    @staticmethod
    def no_life() -> DDCEParameters:
        """Universe without life: only physical entropy."""
        return DDCEParameters(
            a=0.01, b=0.0, c=0.0,  # No biological/cognitive contribution
            alpha1=0.1, alpha2=0.05, alpha3=0.0,
            beta1=0.0, beta2=0.1, beta3=0.0,
            k=0.05
        )
    
    @staticmethod
    def early_life() -> DDCEParameters:
        """Early life: biological adaptation begins."""
        return DDCEParameters(
            a=0.01, b=0.1, c=0.0,  # No cognitive yet
            alpha1=0.2, alpha2=0.1, alpha3=0.0,
            beta1=0.1, beta2=0.1, beta3=0.1,
            k=0.07
        )
    
    @staticmethod
    def cognitive_emergence() -> DDCEParameters:
        """Cognitive beings emerge: M becomes significant."""
        return DDCEParameters(
            a=0.01, b=0.1, c=0.5,  # Cognitive contribution
            alpha1=0.3, alpha2=0.1, alpha3=0.2,
            beta1=0.2, beta2=0.1, beta3=0.15,
            k=0.1
        )
    
    @staticmethod
    def technological_civilization() -> DDCEParameters:
        """Advanced civilization: M dominates."""
        return DDCEParameters(
            a=0.01, b=0.1, c=2.0,  # Strong cognitive contribution
            alpha1=0.5, alpha2=0.1, alpha3=0.5,
            beta1=0.4, beta2=0.1, beta3=0.3,
            k=0.15
        )
    
    @staticmethod
    def singularity() -> DDCEParameters:
        """Technological singularity: exponential M growth."""
        return DDCEParameters(
            a=0.01, b=0.1, c=10.0,  # Extreme cognitive
            alpha1=1.0, alpha2=0.05, alpha3=1.0,
            beta1=0.8, beta2=0.05, beta3=0.5,
            k=0.2
        )


def compare_scenarios():
    """Compare different DDCE scenarios."""
    scenarios = {
        'No Life': DDCEScenarios.no_life(),
        'Early Life': DDCEScenarios.early_life(),
        'Cognitive': DDCEScenarios.cognitive_emergence(),
        'Civilization': DDCEScenarios.technological_civilization(),
        'Singularity': DDCEScenarios.singularity()
    }
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    for name, params in scenarios.items():
        system = DDCESystem(params)
        history = system.simulate(t_span=(0, 50))
        
        axes[0, 0].semilogy(history['t'], history['V'], label=name, linewidth=2)
        axes[0, 1].semilogy(history['t'], history['C'], label=name, linewidth=2)
        axes[1, 0].plot(history['t'], history['H'], label=name, linewidth=2)
        axes[1, 1].semilogy(history['t'], history['Lambda_eff'], label=name, linewidth=2)
    
    axes[0, 0].set_xlabel('Time')
    axes[0, 0].set_ylabel('V (Volume)')
    axes[0, 0].set_title('Cosmic Volume by Scenario')
    axes[0, 0].legend()
    axes[0, 0].grid(True, alpha=0.3)
    
    axes[0, 1].set_xlabel('Time')
    axes[0, 1].set_ylabel('C (Complexity)')
    axes[0, 1].set_title('Total Complexity')
    axes[0, 1].legend()
    axes[0, 1].grid(True, alpha=0.3)
    
    axes[1, 0].set_xlabel('Time')
    axes[1, 0].set_ylabel('H (Hubble)')
    axes[1, 0].set_title('Hubble Parameter')
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    
    axes[1, 1].set_xlabel('Time')
    axes[1, 1].set_ylabel('Λ_eff')
    axes[1, 1].set_title('Effective Cosmological Constant')
    axes[1, 1].legend()
    axes[1, 1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('ddce_scenarios.png', dpi=150, bbox_inches='tight')
    plt.show()
    
    # Print growth rates
    print("\n=== Growth Rate Analysis ===")
    for name, params in scenarios.items():
        system = DDCESystem(params)
        system.simulate(t_span=(0, 50))
        rates = system.analyze_growth_rates()
        print(f"\n{name}:")
        for var, data in rates.items():
            print(f"  {var}: λ = {data['growth_rate']:.4f}, T₂ = {data['doubling_time']:.2f}")


def main():
    """Main demonstration."""
    print("=" * 60)
    print("DDCE Simulator — Distinction-Driven Cosmological Expansion")
    print("=" * 60)
    
    # Default simulation
    print("\n1. Running default DDCE simulation...")
    system = DDCESystem()
    history = system.simulate(t_span=(0, 100))
    
    print(f"   Simulation successful: {history['success']}")
    print(f"   Final state:")
    print(f"     Δ = {history['Delta'][-1]:.2e}")
    print(f"     F = {history['F'][-1]:.2e}")
    print(f"     M = {history['M'][-1]:.2e}")
    print(f"     V = {history['V'][-1]:.2e}")
    print(f"     C = {history['C'][-1]:.2e}")
    
    # Growth rate analysis
    print("\n2. Analyzing growth rates...")
    rates = system.analyze_growth_rates()
    for var, data in rates.items():
        print(f"   {var}: λ = {data['growth_rate']:.4f}, doubling time = {data['doubling_time']:.2f}")
    
    # Compute action
    print("\n3. Computing action integral...")
    action = system.compute_action()
    print(f"   S = ∫L dt = {action:.4e}")
    
    # Plot
    print("\n4. Generating plots...")
    system.plot_evolution(save_path='ddce_evolution.png')
    system.plot_phase_space(save_path='ddce_phase_space.png')
    
    # Compare scenarios
    print("\n5. Comparing cosmic scenarios...")
    compare_scenarios()
    
    print("\n" + "=" * 60)
    print("DDCE Simulation Complete")
    print("=" * 60)


if __name__ == "__main__":
    main()
