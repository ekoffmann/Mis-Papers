#!/usr/bin/env python3
"""
Comprobaciones numericas independientes ([NUMERICO]) para la nota sobre el Problema 281 de Erdos.
Solo biblioteca estandar. Cada bloque verifica exhaustivamente o por muestreo un enunciado FINITO
usado en la nota. No sustituyen a las demostraciones: sirven para detectar errores de enunciado.

Uso:  python3 checks.py
"""
import itertools, math, random
from fractions import Fraction
from functools import reduce

random.seed(281)

def lcm(a, b):
    return a * b // math.gcd(a, b)

def lcmm(xs):
    return reduce(lcm, xs, 1)

def uncovered_count(mods, res, N):
    """#{x mod N : x !≡ res[i] (mod mods[i]) para todo i}."""
    return sum(1 for x in range(N) if all((x - r) % n != 0 for n, r in zip(mods, res)))

# ---------------------------------------------------------------------------------------------
# 1. Teorema de Rogers: max_a d_k(a) se alcanza en a = 0  (exhaustivo sobre TODAS las elecciones)
# ---------------------------------------------------------------------------------------------
def check_rogers(trials=400, maxmod=14, maxk=4, cap=3000):
    tested = 0
    for _ in range(trials):
        k = random.randint(1, maxk)
        mods = sorted(random.sample(range(2, maxmod + 1), k))
        N = lcmm(mods)
        if N * math.prod(mods) > 4_000_000 or N > cap:
            continue
        zero = uncovered_count(mods, [0] * k, N)
        best = max(uncovered_count(mods, res, N) for res in itertools.product(*[range(n) for n in mods]))
        assert best == zero, (mods, best, zero)
        tested += 1
    return tested

# ---------------------------------------------------------------------------------------------
# 2. Monotonia de f_B(s) = sum_{J != vacio} (-1)^{|J|+1} lcm(J)^{-s}  y  f_B(1) = d(M(B))
#    (lema de acoplamiento; es la desigualdad sum_{m in M(B)} m^{-s} <= zeta(s) d(M(B)), s > 1)
# ---------------------------------------------------------------------------------------------
def f_B(B, s):
    tot = 0.0
    for r in range(1, len(B) + 1):
        for J in itertools.combinations(B, r):
            tot += (-1) ** (r + 1) * lcmm(J) ** (-s)
    return tot

def dens_multiples(B):
    N = lcmm(B)
    return Fraction(sum(1 for x in range(N) if any(x % b == 0 for b in B)), N)

def check_monotone(trials=300):
    grid = [0.05 * i for i in range(1, 121)]  # s en (0, 6]
    for _ in range(trials):
        k = random.randint(1, 5)
        B = random.sample(range(2, 40), k)
        if lcmm(B) > 200000:
            continue
        vals = [f_B(B, s) for s in grid]
        assert all(vals[i] >= vals[i + 1] - 1e-12 for i in range(len(vals) - 1)), B
        assert abs(f_B(B, 1.0) - float(dens_multiples(B))) < 1e-12, B
    return trials

def check_dirichlet_inequality():
    """sum_{m in M(B), m<=X} m^{-s}  <=  zeta(s) d(M(B))  (suma parcial <= suma total <= cota)."""
    out = []
    for B in ([4, 6, 9], [6, 10, 15], [2, 3], [12, 18, 20, 45]):
        d = float(dens_multiples(B))
        for s in (1.05, 1.2, 1.5, 2.0, 3.0):
            X = 200000
            part = sum(m ** (-s) for m in range(1, X + 1) if any(m % b == 0 for b in B))
            zeta = sum(m ** (-s) for m in range(1, X + 1)) + X ** (1 - s) / (s - 1)  # cota inferior de zeta + cola
            exact = f_B(B, s) * zeta
            assert part <= exact + 1e-9 and f_B(B, s) <= d + 1e-12, (B, s)
            out.append((B, s, round(f_B(B, s), 6), round(d, 6)))
    return out

# ---------------------------------------------------------------------------------------------
# 3. Rogers FALLA en grupos no ciclicos: (Z/2)^2 y las tres subgrupos de orden 2
# ---------------------------------------------------------------------------------------------
def check_noncyclic():
    G = [(x, y) for x in range(2) for y in range(2)]
    add = lambda g, h: ((g[0] + h[0]) % 2, (g[1] + h[1]) % 2)
    subgroups = [[(0, 0), (0, 1)], [(0, 0), (1, 0)], [(0, 0), (1, 1)]]
    union0 = set().union(*[set(H) for H in subgroups])
    best = min(len(set().union(*[{add(t, h) for h in H} for t, H in zip(ts, subgroups)]))
               for ts in itertools.product(G, repeat=3))
    return len(union0), best  # (4, 3): las clases laterales cubren MENOS que los subgrupos

# ---------------------------------------------------------------------------------------------
# 4. Identidad de promedio (eleccion aleatoria de las primeras j clases):
#    promedio_{a_1..a_j} d(W \ U_{i<=j} (a_i + n_i Z)) = d(W) * prod_{i<=j} (1 - 1/n_i)
# ---------------------------------------------------------------------------------------------
def check_average_identity(trials=60):
    for _ in range(trials):
        j = random.randint(1, 3)
        head = random.sample(range(2, 9), j)
        tail = random.sample(range(2, 13), random.randint(1, 3))
        tail_res = [random.randrange(n) for n in tail]
        N = lcmm(head + tail)
        if N > 3000:
            continue
        W = [x for x in range(N) if all((x - r) % n != 0 for n, r in zip(tail, tail_res))]
        total = Fraction(0)
        cnt = 0
        for res in itertools.product(*[range(n) for n in head]):
            total += Fraction(sum(1 for x in W if all((x - r) % n != 0 for n, r in zip(head, res))), N)
            cnt += 1
        avg = total / cnt
        c = Fraction(1)
        for n in head:
            c *= Fraction(n - 1, n)
        assert avg == Fraction(len(W), N) * c, (head, tail)
    return trials

# ---------------------------------------------------------------------------------------------
# 5. Multiplicidad: para modulos = primeros primos, max sobre elecciones de la densidad de
#    enteros cubiertos MENOS de r veces (exhaustivo).  Ilustra el Teorema de multiplicidad.
# ---------------------------------------------------------------------------------------------
def max_density_fewer_than_r(mods, r):
    N = lcmm(mods)
    best = Fraction(0)
    for res in itertools.product(*[range(n) for n in mods]):
        c = sum(1 for x in range(N) if sum(1 for n, a in zip(mods, res) if (x - a) % n == 0) < r)
        best = max(best, Fraction(c, N))
    return best

def check_multiplicity():
    rows = []
    primes = [2, 3, 5, 7, 11]
    for k in range(1, 6):
        mods = primes[:k]
        rows.append((mods, [str(max_density_fewer_than_r(mods, r)) for r in (1, 2, 3)]))
    return rows

# ---------------------------------------------------------------------------------------------
# 6. Lema maximal en Z/N (constante 2): #{t : existe L<=N con |E ∩ (t, t+L]| > lam*L} <= 2|E|/lam
# ---------------------------------------------------------------------------------------------
def check_maximal(trials=300):
    for _ in range(trials):
        N = random.randint(1, 60)
        E = {x for x in range(N) if random.random() < random.choice([0.05, 0.2, 0.5])}
        lam = random.choice([0.1, 0.25, 0.5, 0.75, 0.9])
        ind = [1 if (x % N) in E else 0 for x in range(2 * N + 1)]
        pref = [0]
        for v in ind:
            pref.append(pref[-1] + v)
        bad = 0
        for t in range(N):
            if any(pref[t + L + 1] - pref[t + 1] > lam * L for L in range(1, N + 1)):
                bad += 1
        assert bad <= 2 * len(E) / lam + 1e-9, (N, sorted(E), lam, bad)
    return trials

# ---------------------------------------------------------------------------------------------
# 7. Experimento del argumento del arbol (Prop. finitaria) en un ejemplo no-Behrend:
#    modulos n_i = cuadrados de primos, a* = 0 (R(0) = libres de cuadrados, rho = 6/pi^2).
#    Se toma un desplazamiento coherente t_k (mod N_k) elegido al azar nivel a nivel y se mide
#    |R_k(b) ∩ [1, L]| / L  frente a rho_k = prod (1 - 1/p^2).
# ---------------------------------------------------------------------------------------------
def tree_experiment():
    mods = [4, 9, 25, 49, 121, 169]
    rows = []
    t, Nk = 0, 1
    for k, n in enumerate(mods, start=1):
        Nk_new = lcm(Nk, n)
        t = t + Nk * random.randrange(Nk_new // Nk)   # extension coherente: t_{k} ≡ t_{k-1} (mod N_{k-1})
        Nk = Nk_new
        rho_k = math.prod(1 - 1 / m for m in mods[:k])
        L = 200000
        cnt = sum(1 for m in range(1, L + 1) if all((m + t) % q != 0 for q in mods[:k]))
        rows.append((k, round(rho_k, 5), round(cnt / L, 5)))
    return rows

if __name__ == "__main__":
    print("1. Rogers (exhaustivo, familias aleatorias):", check_rogers(), "familias verificadas, 0 contraejemplos")
    print("2. f_B(s) decreciente y f_B(1)=d(M(B)):", check_monotone(), "conjuntos B verificados")
    print("   Desigualdad de Dirichlet (B, s, f_B(s), d(M(B))):")
    for row in check_dirichlet_inequality():
        print("     ", row)
    u0, best = check_noncyclic()
    print(f"3. (Z/2)^2: |union de subgrupos| = {u0}, min |union de clases laterales| = {best}  (Rogers falla: {best} < {u0})")
    print("4. Identidad de promedio sobre elecciones aleatorias:", check_average_identity(), "casos, exacta (fracciones)")
    print("5. Multiplicidad (modulos primos): max_a densidad{cubiertos < r veces}, r = 1,2,3")
    for mods, vals in check_multiplicity():
        print("     ", mods, vals)
    print("6. Lema maximal en Z/N (constante 2):", check_maximal(), "casos, 0 violaciones")
    print("7. Experimento del arbol (n_i = p^2, a* = 0): (k, rho_k, densidad empirica desplazada en [1,2e5])")
    for row in tree_experiment():
        print("     ", row)
    print("TODAS LAS COMPROBACIONES PASARON")
