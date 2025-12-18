"""
Riemann Operator - Sparse Large Scale
=====================================
Uses scipy.sparse for N up to 50000
"""

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh
import time

def sieve_primes(n):
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, n + 1, i):
                is_prime[j] = False
    return [i for i in range(n + 1) if is_prime[i]]

def build_sparse_hamiltonian(N, num_primes=200):
    """Build sparse H = -d^2/dx^2 + V(x)"""
    primes = sieve_primes(num_primes * 10)[:num_primes]
    log_primes = np.log(primes)
    L = log_primes[-1] * 1.2
    dx = L / N
    
    # Kinetic: tridiagonal
    diag = np.full(N, 2.0 / dx**2)
    off = np.full(N-1, -1.0 / dx**2)
    
    # Add potential
    for lp in log_primes:
        idx = int(lp / dx)
        if 0 <= idx < N:
            diag[idx] += 1.0 / dx
    
    H = sparse.diags([off, diag, off], [-1, 0, 1], format='csr')
    return H

def analyze(eigs):
    """Level spacing variance"""
    eigs_sorted = np.sort(eigs)
    spacings = np.diff(eigs_sorted)
    s = spacings / np.mean(spacings)
    return np.var(s)

def main():
    print("="*50)
    print("SPARSE RIEMANN OPERATOR")
    print("="*50)
    
    sizes = [5000, 10000, 20000, 50000]
    
    for N in sizes:
        print(f"\nN = {N}")
        
        t0 = time.time()
        H = build_sparse_hamiltonian(N, num_primes=200)
        print(f"  Build: {time.time()-t0:.2f}s")
        
        t0 = time.time()
        # Get lowest 500 eigenvalues
        k = min(500, N-2)
        eigs, _ = eigsh(H, k=k, which='SM')
        print(f"  Diag ({k} eigs): {time.time()-t0:.2f}s")
        
        var_s = analyze(eigs)
        print(f"  Var(s) = {var_s:.4f}")
        print(f"  GUE test: {'PASS' if var_s < 0.4 else 'FAIL'}")
        
        # Check all real
        max_imag = np.max(np.abs(np.imag(eigs)))
        print(f"  Max|Im| = {max_imag:.2e}")

if __name__ == "__main__":
    main()
