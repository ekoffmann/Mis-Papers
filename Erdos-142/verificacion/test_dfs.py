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

# La opción --split J j reparte el espacio de prefijos en J partes disjuntas: el número de
# soluciones de las partes debe sumar el total (se usa en la decisión k=11, N=121, B=16).
import re
def nsol(*args):
    out = subprocess.run([exe, *map(str, args)], capture_output=True, text=True).stdout
    return int(re.search(r"soluciones=(\d+)", out).group(1))
total = nsol(7, 49, 11, "--all", "--nosym")
partes = [nsol(7, 49, 11, "--all", "--nosym", "--split", 3, j) for j in range(3)]
print(f"particion: total={total}, partes={partes}, suma={sum(partes)}")
if total != sum(partes) or total != 1257:
    bad += 1

# Tercer buscador (tau_perfil, búsqueda por perfiles de filas) en N = k^2: debe dar los mismos
# valores que la búsqueda en Python (k <= 6) y que tau_dfs (k = 7, 8), y sus conjuntos deben cortar
# todas las progresiones.
for nombre in ("tau_perfil", "hs_perfil"):
    exe_p = os.path.join(os.path.dirname(os.path.abspath(__file__)), nombre)
    if not os.path.exists(exe_p):
        print(f"({nombre} no compilado; se omite su contraste)")
        continue
    for kk, t in checks.TAU_SQ.items():
        o1 = subprocess.run([exe_p, str(kk), str(t - 1)], capture_output=True, text=True).stdout if t - 1 >= kk else " UNSAT "
        o2 = subprocess.run([exe_p, str(kk), str(t)], capture_output=True, text=True).stdout
        mm = re.search(r"H=([\d,]+)", o2)
        H = list(map(int, mm.group(1).split(","))) if mm else []
        okset = len(H) == t and checks.unhit(kk, kk * kk, H) == 0
        if " UNSAT" not in o1 or " SAT " not in o2 or not okset:
            bad += 1
            print("DISCREPANCIA", nombre, kk, t)
    print(f"{nombre}: valores de tau_k(k^2) para k = 2..8 reproducidos, discrepancias acumuladas: {bad}")
sys.exit(1 if bad else 0)
