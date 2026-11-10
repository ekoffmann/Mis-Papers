#!/usr/bin/env python3
"""Contraste del buscador en C++ (tau_dfs) con la búsqueda exhaustiva independiente en Python
(checks.tau_exact) en todos los casos pequeños, con y sin las podas (3) y (4)."""
import subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checks
exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tau_dfs")
def dec(k, N, B, *flags):
    out = subprocess.run([exe, str(k), str(N), str(B), *flags], capture_output=True, text=True).stdout
    return " SAT " in out
n = 0; bad = 0
for k in range(2, 8):
    for N in range(k, min(k * k + 6, 46) + 1):
        t = checks.tau_exact(k, N)
        for flags in ((), ("--nosym",), ("--nowin",), ("--nosym", "--nowin")):
            for B in (t - 1, t):
                if B < 0: continue
                n += 1
                if dec(k, N, B, *flags) != (B >= t):
                    bad += 1
                    print("DISCREPANCIA", k, N, B, flags)
print(f"casos comprobados: {n}, discrepancias: {bad}")
sys.exit(1 if bad else 0)
