"""
DD-Agent v0.1 — Distinction Dynamics Model of Consciousness
============================================================

Implementation of the DD-agent equations:

    dΔ₀/dt = F⁽⁰⁾(Δ₀) + S(t)           # Sensory layer
    dΔ₁/dt = F⁽¹⁾(Δ₁, Δ₀) + H₁         # Cognitive layer  
    dΔ₂/dt = M⁽²⁾(Δ₂, Δ₁, H₂)          # Meta layer
    dF⁽¹⁾/dt = M⁽²⁾(∇_Δ V)             # Adaptation
    Hₖ(t) = αHₖ(t-1) + (1-α)Δₖ(t)      # Memory
    E(t) = ||dΔ/dt||                    # Emotion

Author: Andrey Shkursky
Date: December 2025
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Optional, Callable, Tuple
from enum import Enum
import matplotlib.pyplot as plt


class DistinctionLevel(Enum):
    """Levels of distinction in DD hierarchy."""
    SENSORY = 0      # Δ₀: raw distinctions
    COGNITIVE = 1    # Δ₁: interpreted distinctions
    META = 2         # Δ₂: distinctions of distinctions


@dataclass
class DDAgentConfig:
    """Configuration for DD-Agent."""
    
    # Dimensions
    dim_sensory: int = 10      # Dimension of Δ₀
    dim_cognitive: int = 20    # Dimension of Δ₁
    dim_meta: int = 5          # Dimension of Δ₂
    
    # Memory parameters
    alpha: float = 0.95        # Memory decay rate
    
    # Emotion parameters
    emotion_smoothing: float = 0.1
    
    # Goal parameters
    goal_weight: float = 1.0
    
    # Time step
    dt: float = 0.01
    
    # Trauma parameters
    trauma_sensitivity: float = 1.0  # β in trauma model


@dataclass
class DDAgentState:
    """State of DD-Agent at a given time."""
    
    # Distinction states
    Delta_0: np.ndarray  # Sensory distinctions
    Delta_1: np.ndarray  # Cognitive distinctions
    Delta_2: np.ndarray  # Meta distinctions
    
    # Memory states
    H_0: np.ndarray      # Sensory memory
    H_1: np.ndarray      # Cognitive memory
    H_2: np.ndarray      # Meta memory
    
    # Reaction function parameters (simplified as weight matrices)
    F_1_weights: np.ndarray  # Cognitive reaction weights
    
    # Goal state
    Delta_star: np.ndarray   # Target cognitive state
    
    # Derived quantities
    emotion: float = 0.0     # E(t) = ||dΔ/dt||
    value: float = 0.0       # V(Δ) = -||Δ - Δ*||²
    
    def copy(self) -> 'DDAgentState':
        return DDAgentState(
            Delta_0=self.Delta_0.copy(),
            Delta_1=self.Delta_1.copy(),
            Delta_2=self.Delta_2.copy(),
            H_0=self.H_0.copy(),
            H_1=self.H_1.copy(),
            H_2=self.H_2.copy(),
            F_1_weights=self.F_1_weights.copy(),
            Delta_star=self.Delta_star.copy(),
            emotion=self.emotion,
            value=self.value
        )


class DDAgent:
    """
    DD-Agent: A distinction-dynamics model of consciousness.
    
    The agent processes signals through three layers:
    1. Sensory (Δ₀): Raw distinctions from environment
    2. Cognitive (Δ₁): Interpreted, contextualized distinctions
    3. Meta (Δ₂): Distinctions about how we distinguish
    
    Key features:
    - Memory (H): Exponentially decaying trace of distinctions
    - Emotion (E): Magnitude of change in distinctions
    - Goals (Δ*): Target state driving adaptation
    - Adaptation (M): Meta-operator that modifies F
    """
    
    def __init__(self, config: Optional[DDAgentConfig] = None):
        self.config = config or DDAgentConfig()
        self.state = self._initialize_state()
        self.history: List[DDAgentState] = []
        self.time = 0.0
        
    def _initialize_state(self) -> DDAgentState:
        """Initialize agent state with random small values."""
        cfg = self.config
        
        return DDAgentState(
            Delta_0=np.random.randn(cfg.dim_sensory) * 0.1,
            Delta_1=np.random.randn(cfg.dim_cognitive) * 0.1,
            Delta_2=np.random.randn(cfg.dim_meta) * 0.1,
            H_0=np.zeros(cfg.dim_sensory),
            H_1=np.zeros(cfg.dim_cognitive),
            H_2=np.zeros(cfg.dim_meta),
            F_1_weights=np.random.randn(cfg.dim_cognitive, cfg.dim_sensory) * 0.1,
            Delta_star=np.zeros(cfg.dim_cognitive),  # No goal initially
            emotion=0.0,
            value=0.0
        )
    
    def F_0(self, Delta_0: np.ndarray) -> np.ndarray:
        """
        Sensory reaction function F⁽⁰⁾.
        Simple nonlinear transformation of raw input.
        """
        return np.tanh(Delta_0)
    
    def F_1(self, Delta_1: np.ndarray, Delta_0: np.ndarray) -> np.ndarray:
        """
        Cognitive reaction function F⁽¹⁾.
        Maps sensory input to cognitive distinctions using learned weights.
        """
        # Linear transformation + nonlinearity
        raw = self.state.F_1_weights @ Delta_0
        # Add recurrent component
        recurrent = 0.1 * Delta_1
        return np.tanh(raw + recurrent)
    
    def M_2(self, Delta_2: np.ndarray, Delta_1: np.ndarray, 
            H_2: np.ndarray, grad_V: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """
        Meta-operator M⁽²⁾.
        
        Returns:
            - dDelta_2: Change in meta-distinctions
            - dF_1: Change in cognitive reaction weights
        """
        # Meta-distinction dynamics
        # Δ₂ responds to discrepancy between Δ₁ and its memory
        discrepancy = Delta_1[:self.config.dim_meta] - H_2
        dDelta_2 = 0.1 * discrepancy + 0.05 * np.tanh(Delta_2)
        
        # Adaptation of F₁ weights
        # Gradient descent on value function
        # dF/dt = M(∇V) where ∇V points toward goal
        learning_rate = 0.01 * self.config.trauma_sensitivity
        
        # Outer product learning rule (simplified Hebbian)
        dF_1 = learning_rate * np.outer(grad_V, self.state.Delta_0)
        
        return dDelta_2, dF_1
    
    def compute_value(self, Delta_1: np.ndarray) -> float:
        """Compute value function V(Δ) = -||Δ - Δ*||²."""
        diff = Delta_1 - self.state.Delta_star
        return -np.dot(diff, diff)
    
    def compute_value_gradient(self, Delta_1: np.ndarray) -> np.ndarray:
        """Compute gradient of value function ∇V = -2(Δ - Δ*)."""
        return -2 * (Delta_1 - self.state.Delta_star)
    
    def compute_emotion(self, dDelta: np.ndarray) -> float:
        """Compute emotion E(t) = ||dΔ/dt||."""
        return np.linalg.norm(dDelta)
    
    def update_memory(self):
        """Update memory states: Hₖ(t) = αHₖ(t-1) + (1-α)Δₖ(t)."""
        alpha = self.config.alpha
        self.state.H_0 = alpha * self.state.H_0 + (1 - alpha) * self.state.Delta_0
        self.state.H_1 = alpha * self.state.H_1 + (1 - alpha) * self.state.Delta_1
        self.state.H_2 = alpha * self.state.H_2 + (1 - alpha) * self.state.Delta_2
    
    def step(self, signal: Optional[np.ndarray] = None) -> DDAgentState:
        """
        Perform one time step of DD-agent dynamics.
        
        Args:
            signal: External signal S(t), defaults to noise
            
        Returns:
            New agent state
        """
        cfg = self.config
        dt = cfg.dt
        
        # Default signal is noise
        if signal is None:
            signal = np.random.randn(cfg.dim_sensory) * 0.1
        
        # Store old state for computing derivatives
        old_Delta_0 = self.state.Delta_0.copy()
        old_Delta_1 = self.state.Delta_1.copy()
        
        # === Layer 0: Sensory ===
        # dΔ₀/dt = F⁽⁰⁾(Δ₀) + S(t)
        dDelta_0 = self.F_0(self.state.Delta_0) + signal
        self.state.Delta_0 = self.state.Delta_0 + dt * dDelta_0
        
        # === Layer 1: Cognitive ===
        # dΔ₁/dt = F⁽¹⁾(Δ₁, Δ₀) + H₁
        dDelta_1 = self.F_1(self.state.Delta_1, self.state.Delta_0) + 0.1 * self.state.H_1
        self.state.Delta_1 = self.state.Delta_1 + dt * dDelta_1
        
        # === Layer 2: Meta ===
        # Compute value gradient for adaptation
        grad_V = self.compute_value_gradient(self.state.Delta_1)
        
        # dΔ₂/dt = M⁽²⁾(Δ₂, Δ₁, H₂)
        # dF⁽¹⁾/dt = M⁽²⁾(∇V)
        dDelta_2, dF_1 = self.M_2(
            self.state.Delta_2, 
            self.state.Delta_1,
            self.state.H_2,
            grad_V
        )
        self.state.Delta_2 = self.state.Delta_2 + dt * dDelta_2
        self.state.F_1_weights = self.state.F_1_weights + dt * dF_1
        
        # === Update derived quantities ===
        
        # Memory
        self.update_memory()
        
        # Emotion: E(t) = ||dΔ/dt||
        total_dDelta = np.concatenate([dDelta_0, dDelta_1, dDelta_2])
        raw_emotion = self.compute_emotion(total_dDelta)
        self.state.emotion = (1 - cfg.emotion_smoothing) * self.state.emotion + \
                             cfg.emotion_smoothing * raw_emotion
        
        # Value
        self.state.value = self.compute_value(self.state.Delta_1)
        
        # Update time
        self.time += dt
        
        # Store history
        self.history.append(self.state.copy())
        
        return self.state
    
    def set_goal(self, goal: np.ndarray):
        """Set target state Δ*."""
        assert len(goal) == self.config.dim_cognitive
        self.state.Delta_star = goal.copy()
    
    def apply_trauma(self, intensity: float = 2.0):
        """
        Apply trauma as β-deformation of M.
        Trauma = increased sensitivity of meta-operator.
        """
        self.config.trauma_sensitivity = intensity
        print(f"Trauma applied: β = {intensity}")
    
    def heal_trauma(self, sessions: int = 100):
        """
        Simulate therapy: gradual reduction of β.
        """
        original_beta = self.config.trauma_sensitivity
        for i in range(sessions):
            # Gradual reduction
            self.config.trauma_sensitivity = original_beta * (1 - i/sessions) + 1.0 * (i/sessions)
            # Run agent
            self.step()
        print(f"Therapy complete: β reduced from {original_beta:.2f} to {self.config.trauma_sensitivity:.2f}")
    
    def run(self, n_steps: int, signals: Optional[np.ndarray] = None) -> List[DDAgentState]:
        """
        Run agent for n_steps.
        
        Args:
            n_steps: Number of time steps
            signals: Optional array of shape (n_steps, dim_sensory)
            
        Returns:
            History of states
        """
        for i in range(n_steps):
            signal = signals[i] if signals is not None else None
            self.step(signal)
        return self.history
    
    def analyze_consciousness(self) -> dict:
        """
        Analyze consciousness indicators.
        
        Criterion: Consciousness = ability to change F through M.
        """
        if len(self.history) < 10:
            return {"error": "Need more history"}
        
        # Track F_1 weight changes
        weight_changes = []
        for i in range(1, len(self.history)):
            diff = np.linalg.norm(
                self.history[i].F_1_weights - self.history[i-1].F_1_weights
            )
            weight_changes.append(diff)
        
        avg_dF = np.mean(weight_changes)
        
        # Consciousness criterion: dF/dt ≠ 0
        is_conscious = avg_dF > 1e-6
        
        # Complexity = variance of distinctions
        Delta_1_history = np.array([s.Delta_1 for s in self.history])
        complexity = np.mean(np.var(Delta_1_history, axis=0))
        
        # Emotion dynamics
        emotions = [s.emotion for s in self.history]
        emotion_mean = np.mean(emotions)
        emotion_var = np.var(emotions)
        
        return {
            "is_conscious": is_conscious,
            "avg_dF_dt": avg_dF,
            "complexity": complexity,
            "emotion_mean": emotion_mean,
            "emotion_variance": emotion_var,
            "interpretation": self._interpret_consciousness(is_conscious, avg_dF, complexity)
        }
    
    def _interpret_consciousness(self, is_conscious: bool, dF: float, complexity: float) -> str:
        """Interpret consciousness analysis."""
        if not is_conscious:
            return "AUTOMATON: F fixed, deterministic reactions"
        elif dF < 0.01:
            return "LOW CONSCIOUSNESS: Minimal adaptation"
        elif complexity < 0.1:
            return "RIGID: Adapting but low distinction variance"
        else:
            return "CONSCIOUS: Active adaptation and rich distinctions"
    
    def plot_history(self, save_path: Optional[str] = None):
        """Plot agent history."""
        if len(self.history) < 2:
            print("Not enough history to plot")
            return
        
        fig, axes = plt.subplots(2, 3, figsize=(15, 10))
        
        t = np.arange(len(self.history)) * self.config.dt
        
        # Δ₀ (mean)
        Delta_0_mean = [np.mean(s.Delta_0) for s in self.history]
        axes[0, 0].plot(t, Delta_0_mean, 'b-', linewidth=1.5)
        axes[0, 0].set_xlabel('Time')
        axes[0, 0].set_ylabel('mean(Δ₀)')
        axes[0, 0].set_title('Sensory Distinctions')
        axes[0, 0].grid(True, alpha=0.3)
        
        # Δ₁ (mean)
        Delta_1_mean = [np.mean(s.Delta_1) for s in self.history]
        axes[0, 1].plot(t, Delta_1_mean, 'g-', linewidth=1.5)
        axes[0, 1].set_xlabel('Time')
        axes[0, 1].set_ylabel('mean(Δ₁)')
        axes[0, 1].set_title('Cognitive Distinctions')
        axes[0, 1].grid(True, alpha=0.3)
        
        # Δ₂ (mean)
        Delta_2_mean = [np.mean(s.Delta_2) for s in self.history]
        axes[0, 2].plot(t, Delta_2_mean, 'r-', linewidth=1.5)
        axes[0, 2].set_xlabel('Time')
        axes[0, 2].set_ylabel('mean(Δ₂)')
        axes[0, 2].set_title('Meta Distinctions')
        axes[0, 2].grid(True, alpha=0.3)
        
        # Emotion
        emotions = [s.emotion for s in self.history]
        axes[1, 0].plot(t, emotions, 'purple', linewidth=1.5)
        axes[1, 0].set_xlabel('Time')
        axes[1, 0].set_ylabel('E(t)')
        axes[1, 0].set_title('Emotion ||dΔ/dt||')
        axes[1, 0].grid(True, alpha=0.3)
        
        # Value
        values = [s.value for s in self.history]
        axes[1, 1].plot(t, values, 'orange', linewidth=1.5)
        axes[1, 1].set_xlabel('Time')
        axes[1, 1].set_ylabel('V(Δ)')
        axes[1, 1].set_title('Value Function')
        axes[1, 1].grid(True, alpha=0.3)
        
        # F₁ weight norm (adaptation indicator)
        F_norms = [np.linalg.norm(s.F_1_weights) for s in self.history]
        axes[1, 2].plot(t, F_norms, 'brown', linewidth=1.5)
        axes[1, 2].set_xlabel('Time')
        axes[1, 2].set_ylabel('||F₁||')
        axes[1, 2].set_title('Reaction Function Norm')
        axes[1, 2].grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"Saved plot to {save_path}")
        
        plt.show()
        return fig


def demo_trauma_therapy():
    """Demonstrate trauma and therapy in DD-agent."""
    print("=" * 60)
    print("DD-Agent: Trauma and Therapy Demonstration")
    print("=" * 60)
    
    # Create agent
    agent = DDAgent()
    
    # Set a goal state
    goal = np.ones(agent.config.dim_cognitive) * 0.5
    agent.set_goal(goal)
    
    # Phase 1: Normal operation
    print("\nPhase 1: Normal operation (100 steps)")
    agent.run(100)
    analysis1 = agent.analyze_consciousness()
    print(f"  Consciousness: {analysis1['interpretation']}")
    print(f"  Emotion mean: {analysis1['emotion_mean']:.4f}")
    
    # Phase 2: Apply trauma
    print("\nPhase 2: Trauma applied (β = 5.0)")
    agent.apply_trauma(intensity=5.0)
    agent.run(100)
    analysis2 = agent.analyze_consciousness()
    print(f"  Consciousness: {analysis2['interpretation']}")
    print(f"  Emotion mean: {analysis2['emotion_mean']:.4f}")
    
    # Phase 3: Therapy
    print("\nPhase 3: Therapy (gradual β reduction)")
    agent.heal_trauma(sessions=200)
    analysis3 = agent.analyze_consciousness()
    print(f"  Consciousness: {analysis3['interpretation']}")
    print(f"  Emotion mean: {analysis3['emotion_mean']:.4f}")
    
    # Plot
    agent.plot_history(save_path='dd_agent_trauma.png')


def main():
    """Main demonstration."""
    print("=" * 60)
    print("DD-Agent v0.1 — Distinction Dynamics Model of Consciousness")
    print("=" * 60)
    
    # Create agent
    config = DDAgentConfig(
        dim_sensory=10,
        dim_cognitive=20,
        dim_meta=5,
        alpha=0.95,
        dt=0.01
    )
    agent = DDAgent(config)
    
    # Set goal
    goal = np.random.randn(config.dim_cognitive) * 0.3
    agent.set_goal(goal)
    print(f"\nGoal set: ||Δ*|| = {np.linalg.norm(goal):.4f}")
    
    # Run simulation
    print("\nRunning simulation (500 steps)...")
    agent.run(500)
    
    # Analyze consciousness
    print("\n=== Consciousness Analysis ===")
    analysis = agent.analyze_consciousness()
    for key, value in analysis.items():
        print(f"  {key}: {value}")
    
    # Plot
    print("\nGenerating plots...")
    agent.plot_history(save_path='dd_agent_history.png')
    
    # Trauma demo
    print("\n" + "=" * 60)
    demo_trauma_therapy()
    
    print("\n" + "=" * 60)
    print("DD-Agent Demonstration Complete")
    print("=" * 60)


if __name__ == "__main__":
    main()
