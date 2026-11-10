#!/usr/bin/env python3
"""Tabla exacta de tau_k(N) = N - r_k(N) con el buscador exhaustivo tau_dfs (C++).
Uso: python3 tabla.py k Nmax [limite_seg_por_llamada]
tau_k(N) es tau_k(N-1) o tau_k(N-1)+1 (añadir N a un conjunto válido para N-1 da uno válido para N),
así que basta una decisión por N: ¿existe un conjunto de tamaño tau_k(N-1)?"""
import subprocess, sys, os
exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tau_dfs")
k, Nmax = int(sys.argv[1]), int(sys.argv[2])
tlim = float(sys.argv[3]) if len(sys.argv) > 3 else 120.0
tau = 0
for N in range(1, Nmax + 1):
    if N >= k:
        try:
            out = subprocess.run([exe, str(k), str(N), str(tau)], capture_output=True, text=True, timeout=tlim).stdout
        except subprocess.TimeoutExpired:
            print(f"# k={k}: límite de tiempo en N={N}; se detiene", flush=True)
            break
        if " UNSAT" in out:
            tau += 1
        elif " SAT " not in out:
            print(f"# k={k}: salida inesperada en N={N}: {out!r}", flush=True)
            break
    print(f"{k} {N} {tau} {N - tau}", flush=True)
