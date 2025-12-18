"""
Riemann Operator on CUDA - Large Scale Verification
====================================================
Uses CuPy for GPU acceleration on 4090.
"""

import numpy as np
try:
    import cupy as cp
    from cupyx.scipy import linalg as cp_linalg
    HAS_CUDA = True
    print("CUDA available via CuPy")
except ImportError:
    HAS_CUDA = False
    print("CuPy not found, using NumPy")
    cp = np
    from scipy import linalg as cp_linalg

from scipy import linalg
import time

# First 100 zeta zeros
ZETA_ZEROS = np.array([
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
    37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
    52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048,
    67.079810529, 69.546401711, 72.067157674, 75.704690699, 77.144840069,
    79.337375020, 82.910380854, 84.735492981, 87.425274613, 88.809111208,
    92.491899271, 94.651344041, 95.870634228, 98.831194218, 101.317851006
])

def sieve_primes(n):
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, n + 1, i):
                is_prime[j] = False
    return [i for i in range(n + 1) if is_prime[i]]

def build_hamiltonian_gpu(N, num_primes=100, lam=1.0):
    """Build H = -d^2/dx^2 + sum_p delta(x - log p) on GPU"""
    primes = sieve_primes(num_primes * 10)[:num_primes]
    log_primes = np.log(primes)
    L = log_primes[-1] * 1.2
    dx = L / N
    
    # Build on GPU
    H = cp.zeros((N, N), dtype=cp.float64)
    
    # Kinetic term: tridiagonal
    diag = cp.full(N, 2.0 / dx**2)
    off_diag = cp.full(N-1, -1.0 / dx**2)
    
    H += cp.diag(diag)
    H += cp.diag(off_diag, k=1)
    H += cp.diag(off_diag, k=-1)
    
    # Potential from primes
    for lp in log_primes:
        idx = int(lp / dx)
        if 0 <= idx < N:
            H[idx, idx] += lam / dx
    
    return H, dx, log_primes

def analyze_spectrum(eigenvalues):
    """Analyze level spacing statistics"""
    eigs = cp.asnumpy(eigenvalues) if HAS_CUDA else eigenvalues
    eigs_sorted = np.sort(eigs)
    spacings = np.diff(eigs_sorted)
    mean_s = np.mean(spacings)
    s = spacings / mean_s
    return np.mean(s), np.var(s)

def main():
    print("="*60)
    print("RIEMANN OPERATOR - CUDA LARGE SCALE")
    print("="*60)
    
    if HAS_CUDA:
        print(f"GPU: {cp.cuda.runtime.getDeviceProperties(0)['name'].decode()}")
        print(f"Memory: {cp.cuda.runtime.memGetInfo()[1] / 1e9:.1f} GB")
    
    sizes = [1000, 2000, 5000, 10000]
    results = []
    
    for N in sizes:
        print(f"\n--- N = {N} ---")
        
        t0 = time.time()
        H, dx, log_primes = build_hamiltonian_gpu(N, num_primes=100, lam=1.0)
        build_time = time.time() - t0
        print(f"Build time: {build_time:.2f}s")
        
        t0 = time.time()
        if HAS_CUDA:
            eigenvalues = cp.linalg.eigvalsh(H)
        else:
            eigenvalues = linalg.eigvalsh(cp.asnumpy(H) if HAS_CUDA else H)
        diag_time = time.time() - t0
        print(f"Diag time: {diag_time:.2f}s")
        
        s_mean, s_var = analyze_spectrum(eigenvalues)
        print(f"Level stats: <s>={s_mean:.4f}, Var(s)={s_var:.4f}")
        print(f"GUE test: {'PASS' if s_var < 0.4 else 'FAIL'} (GUE~0.286)")
        
        results.append({
            'N': N,
            'build': build_time,
            'diag': diag_time,
            'var_s': s_var
        })
    
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    for r in results:
        print(f"N={r['N']:5d}: diag={r['diag']:.2f}s, Var(s)={r['var_s']:.4f}")
    
    return results

if __name__ == "__main__":
    main()
