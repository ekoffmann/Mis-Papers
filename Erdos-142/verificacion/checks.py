#!/usr/bin/env python3
"""Comprobaciones numéricas independientes para la nota sobre el Problema 142 de Erdős.

Notación: r_k(N) = mayor tamaño de un subconjunto de {1..N} sin progresión aritmética (PA) de k
términos; tau_k(N) = N - r_k(N) = menor tamaño de un H ⊆ {1..N} que corta todas las k-PA de [1,N].

Todo se comprueba por fuerza bruta con código independiente del buscador en C++ (tau_dfs.cpp).
Uso:  python3 checks.py            (unos minutos)
Devuelve código 0 si todas las comprobaciones pasan.
"""
import itertools, math, os, random, re, sys

FALLOS = []
def check(nombre, cond, detalle=""):
    estado = "OK " if cond else "FALLO"
    print(f"[{estado}] {nombre} {detalle}", flush=True)
    if not cond:
        FALLOS.append(nombre)

# ---------------------------------------------------------------------------------------------
# Utilidades básicas
# ---------------------------------------------------------------------------------------------
def aps(k, N):
    """Todas las k-PA (a, d) con d >= 1 contenidas en [1,N]."""
    d = 1
    while (k - 1) * d <= N - 1:
        for a in range(1, N - (k - 1) * d + 1):
            yield a, d
        d += 1

def unhit(k, N, H):
    """Número de k-PA de [1,N] que NO cortan a H (fuerza bruta)."""
    Hs = set(H)
    return sum(1 for a, d in aps(k, N) if not any((a + j * d) in Hs for j in range(k)))

def is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))

def minfac(n):
    return next(q for q in range(2, n + 1) if n % q == 0)

def tau_exact(k, N):
    """tau_k(N) exacto por búsqueda exhaustiva simple (elementos en orden creciente)."""
    if N < k:
        return 0
    ends = [[] for _ in range(N + 1)]           # PAs por término máximo, como máscaras de bits
    for a, d in aps(k, N):
        ends[a + (k - 1) * d].append(sum(1 << (a + j * d) for j in range(k)))
    def feasible(B):
        def dfs(y, m, mask):
            # T = primer t > y tal que, sin más elementos hasta t, alguna PA con máximo t queda libre
            T = None
            for t in range(y + 1, N + 1):
                if any((ms & mask) == 0 for ms in ends[t]):
                    T = t
                    break
            if T is None:
                return True
            if m == B:
                return False
            if (N - y) // k > B - m:                 # bloques disjuntos restantes
                return False
            for x in range(T, y, -1):
                if dfs(x, m + 1, mask | (1 << x)):
                    return True
            return False
        return dfs(0, 0, 0)
    B = N // k
    while not feasible(B):
        B += 1
    return B

def count_sets(k, N, B):
    """Número de conjuntos H ⊆ [1,N] con |H| <= B que cortan todas las k-PA (enumeración exhaustiva).
    Con B = tau_k(N) cuenta los conjuntos de corte mínimos, es decir, los conjuntos extremales."""
    ends = [[] for _ in range(N + 1)]
    for a, d in aps(k, N):
        ends[a + (k - 1) * d].append(sum(1 << (a + j * d) for j in range(k)))
    total = 0
    def dfs(y, m, mask):
        nonlocal total
        T = None
        for t in range(y + 1, N + 1):
            if any((ms & mask) == 0 for ms in ends[t]):
                T = t
                break
        if T is None:
            total += 1
            return
        if m == B or (N - y) // k > B - m:
            return
        for x in range(T, y, -1):
            dfs(x, m + 1, mask | (1 << x))
    dfs(0, 0, 0)
    return total

# ---------------------------------------------------------------------------------------------
# 1. Contraste con OEIS (A003002-A003005), valores copiados de los ficheros de oeisdata
# ---------------------------------------------------------------------------------------------
OEIS = {
    3: (0, [0,1,2,2,3,4,4,4,4,5,5,6,6,7,8,8,8,8,8,8,9,9,9,9,10,10,11,11,11,11,12]),          # A003002, offset 0
    4: (1, [1,2,3,3,4,5,5,6,7,8,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,17,17,18,18,18,19,20,20,20]),  # A003003
    5: (1, [1,2,3,4,4,5,6,7,8,8,9,10,11,12,12,13,14,15,16,16,16,16,16,17,18,18,19,20,21,21,22,22,23,24,24,25]),  # A003004
    6: (1, [1,2,3,4,5,5,6,7,8,9,9,10,11,12,13,13,14,15,16,17,17,18,19,20,21,22,22,22,23,23,23,24,25,25,26,27]),  # A003005
}
def test_oeis():
    for k, (off, vals) in OEIS.items():
        lim = {3: 24, 4: 30, 5: 36, 6: 36}[k]
        ok = True
        for i, r in enumerate(vals):
            N = off + i
            if N < 1 or N > lim:
                continue
            if N - tau_exact(k, N) != r:
                ok = False
                print(f"   discrepancia k={k} N={N}: {N - tau_exact(k, N)} vs OEIS {r}")
        check(f"OEIS: r_{k}(N) coincide para N <= {lim}", ok)

# ---------------------------------------------------------------------------------------------
# 2. Fórmula exacta y optimalidad del rango (Teoremas A y B)
# ---------------------------------------------------------------------------------------------
def test_formula():
    ok1 = ok2 = True
    for k in range(2, 10):
        q = minfac(k)
        for N in range(1, q * (k - 1) + 1):
            if tau_exact(k, N) != N // k:
                ok1 = False
                print(f"   falla fórmula k={k} N={N}")
        N = q * (k - 1) + 1
        if tau_exact(k, N) != q or N // k != q - 1:
            ok2 = False
            print(f"   falla umbral k={k} N={N}: tau={tau_exact(k, N)}")
    check("Teorema A: tau_k(N) = floor(N/k) para N <= minFac(k)(k-1), 2 <= k <= 9", ok1)
    check("Teorema B: tau_k(minFac(k)(k-1)+1) = minFac(k) = floor(N/k)+1, 2 <= k <= 9", ok2)
    # Corolario A.2: r_p(ip-1) = i(p-1) con conjunto extremal único
    ok4 = all(tau_exact(p, i * p - 1) == i - 1 and count_sets(p, i * p - 1, i - 1) == 1
              for p in (3, 5, 7) for i in range(2, p))
    check("Corolario A.2: r_p(ip-1) = i(p-1) y el conjunto extremal es único, p = 3,5,7, 2 <= i <= p-1", ok4)
    # número de conjuntos extremales b(k,n): contraste con la tabla de Ahmed-Dybizbanski-Snevily (2013)
    ADS_B = {(5, 24): 40, (5, 25): 2, (5, 27): 70, (5, 28): 12, (5, 29): 2, (7, 46): 18, (7, 48): 9}
    ok5 = True
    for (k, N), b in ADS_B.items():
        c = count_sets(k, N, tau_exact(k, N))
        if c != b:
            ok5 = False
            print(f"   b({k},{N}) = {c} (tabla ADS: {b})")
    check("Número de conjuntos extremales b(k,n): coincide con la tabla de Ahmed-Dybizbanski-Snevily en 7 casos", ok5)
    # sándwich con un primo p <= k
    ok3 = True
    for k in range(4, 10):
        for p in [q for q in range(2, k + 1) if is_prime(q)]:
            for N in range(1, p * (k - 1) + 1):
                t = tau_exact(k, N)
                if not (N // k <= t <= N // p):
                    ok3 = False
    check("Sándwich: floor(N/k) <= tau_k(N) <= floor(N/p) para p primo <= k, N <= p(k-1), 4 <= k <= 9", ok3)

# ---------------------------------------------------------------------------------------------
# 3. Forma de ventanas (Lema 3.1)
# ---------------------------------------------------------------------------------------------
def test_ventanas():
    rng = random.Random(142)
    ok = True
    for _ in range(3000):
        k = rng.randint(2, 6); N = rng.randint(k, 40)
        H = set(x for x in range(1, N + 1) if rng.random() < rng.choice([0.2, 0.4, 0.6]))
        d = rng.randint(1, max(1, N // k))
        if k * d > N:
            continue
        hits = all(any((a + j * d) in H for j in range(k)) for a in range(1, N - (k - 1) * d + 1))
        wins = all(len({x % d for x in H if a <= x <= a + k * d - 1}) == d for a in range(1, N - k * d + 2))
        if hits != wins:
            ok = False
    check("Lema de ventanas: cortar las k-PA de diferencia d <=> toda ventana de longitud kd es d-completa", ok)

# ---------------------------------------------------------------------------------------------
# 4. Construcción explícita |H_p| = 2p-3 en N = p^2 (Teorema D)
# ---------------------------------------------------------------------------------------------
def H_p(p):
    return sorted({2, p + 1, 2 * p - 1} | set(range(2 * p + 3, 3 * p - 1)) | {j * p for j in range(3, p + 1)})

def test_construccion(pmax=61):
    ok = True
    for p in [q for q in range(7, pmax + 1) if is_prime(q)]:
        H = H_p(p)
        if len(H) != 2 * p - 3 or unhit(p, p * p, H) != 0:
            ok = False
            print(f"   falla H_p para p={p}")
    check(f"Teorema D: H_p corta todas las p-PA de [1,p^2] y |H_p| = 2p-3, primos 7 <= p <= {pmax}", ok)
    check("p = 5: {5,10,15,16,17,19,23} corta todas las 5-PA de [1,25]", unhit(5, 25, [5,10,15,16,17,19,23]) == 0)
    check("p = 5: la fórmula H_5 NO funciona (por eso el teorema pide p >= 7)", unhit(5, 25, H_p(5)) > 0)

# ---------------------------------------------------------------------------------------------
# 5. Cota inferior en N = k^2 (Teorema C) y lema de clases
# ---------------------------------------------------------------------------------------------
def D_min(k, s):
    """Mínimo déficit total de k+s-1 huecos si a lo sumo s+j huecos tienen déficit j."""
    left, tot, j = k + s - 1, 0, 0
    while left > 0:
        c = min(left, s + j)
        tot += c * j
        left -= c
        j += 1
    return tot

def s_min(k):
    s = 0
    while D_min(k, s) > k * (s + 1) - 1:
        s += 1
    return s

def s_closed(k):
    s = 0
    while not (k < 8 * s * s + 8 * s + 4):
        s += 1
    return s

TAU_SQ = {2: 3, 3: 4, 4: 6, 5: 7, 6: 9, 7: 11, 8: 13}      # valores exactos de tau_k(k^2) (tau_dfs)

def test_cota_inferior():
    ok = True
    for k in range(2, 7):
        t = tau_exact(k, k * k)
        if t != TAU_SQ[k]:
            ok = False
            print(f"   tau_{k}({k*k}) = {t} (esperado {TAU_SQ[k]})")
    check("tau_k(k^2) = 3, 4, 6, 7, 9 para k = 2..6 (búsqueda exhaustiva en Python)", ok)
    check("Teorema C: tau_k(k^2) >= k + s_min(k) para k = 2..8",
          all(TAU_SQ[k] >= k + s_min(k) for k in TAU_SQ),
          str({k: (TAU_SQ[k], k + s_min(k)) for k in TAU_SQ}))
    check("Forma cerrada: s_closed(k) <= s_min(k) para 2 <= k <= 20000",
          all(s_closed(k) <= s_min(k) for k in range(2, 20001)))
    check("Forma cerrada: s_min(k) > (sqrt((k-2)/2) - 1)/2 para 2 <= k <= 20000",
          all(s_min(k) > (math.sqrt((k - 2) / 2) - 1) / 2 for k in range(2, 20001)))
    print("   k -> k + s_min(k):", {k: k + s_min(k) for k in (5, 7, 11, 13, 17, 19, 23, 101, 1009, 10007)})
    print("   s_min(k)/sqrt(k):", {k: round(s_min(k) / math.sqrt(k), 3) for k in (101, 1009, 10007, 100003)})

def lema_clases(k, N, H):
    """Para 1 <= g <= k con kg <= N: #{h en H : h-g en H} + g <= |H|."""
    Hs = set(H)
    return all(sum(1 for h in Hs if h - g in Hs) + g <= len(Hs) for g in range(1, k + 1) if k * g <= N)

# ---------------------------------------------------------------------------------------------
# 6. Conjuntos guardados (mejores cotas superiores) y lema de clases sobre ellos
# ---------------------------------------------------------------------------------------------
def test_conjuntos(path):
    if not os.path.exists(path):
        print(f"   (no se encuentra {path}; se omite)")
        return
    ok = True; n = 0
    for line in open(path):
        m = re.match(r"k=(\d+) N=(\d+) .*H=([\d,]+)", line)
        if not m:
            continue
        k, N = int(m.group(1)), int(m.group(2))
        H = sorted(set(map(int, m.group(3).split(","))))
        good = unhit(k, N, H) == 0 and all(1 <= x <= N for x in H) and lema_clases(k, N, H)
        n += 1
        nota = f" (2k-3={2*k-3})" if N == k * k else ""
        print(f"   k={k} N={N} |H|={len(H)}{nota} válido={good}")
        ok = ok and good
    check(f"Los {n} conjuntos guardados cortan todas las PA (y cumplen el lema de clases)", ok and n > 0)

# ---------------------------------------------------------------------------------------------
# 7. Construcción de dígitos (clásica): sin dígito p-1 en base p
# ---------------------------------------------------------------------------------------------
def test_digitos():
    ok = True
    for p, m in [(3, 2), (3, 3), (3, 4), (5, 2), (5, 3), (7, 2), (7, 3)]:
        A = [x for x in range(p ** m) if all((x // p ** i) % p != p - 1 for i in range(m))]
        As = set(A)
        free = not any(all((a + j * d) in As for j in range(p)) for a in A for d in range(1, p ** m // (p - 1) + 1))
        if not free or len(A) != (p - 1) ** m:
            ok = False
    check("Construcción de dígitos: {x < p^m sin dígito p-1} no contiene p-PA y tiene (p-1)^m elementos", ok)

# ---------------------------------------------------------------------------------------------
# 8. Relajación lineal (opcional: requiere ortools)
# ---------------------------------------------------------------------------------------------
def test_lp():
    try:
        from ortools.linear_solver import pywraplp
    except Exception:
        print("   (ortools no disponible; se omite la comprobación de la relajación lineal)")
        return
    ok = True
    for k in (3, 5, 7, 8, 11):
        N = k * k
        s = pywraplp.Solver.CreateSolver("GLOP")
        h = [None] + [s.NumVar(0, 1, f"h{x}") for x in range(1, N + 1)]
        for a, d in aps(k, N):
            s.Add(sum(h[a + j * d] for j in range(k)) >= 1)
        s.Minimize(sum(h[1:]))
        s.Solve()
        if abs(s.Objective().Value() - k) > 1e-6:
            ok = False
    check("Relajación lineal en N = k^2: el óptimo fraccionario es exactamente k (k = 3,5,7,8,11)", ok)

if __name__ == "__main__":
    aqui = os.path.dirname(os.path.abspath(__file__))
    test_oeis()
    test_formula()
    test_ventanas()
    test_construccion()
    test_cota_inferior()
    test_conjuntos(os.path.join(aqui, "datos", "mejores_conjuntos.txt"))
    test_digitos()
    test_lp()
    print()
    if FALLOS:
        print("FALLOS:", FALLOS)
        sys.exit(1)
    print("TODAS LAS COMPROBACIONES PASAN")
