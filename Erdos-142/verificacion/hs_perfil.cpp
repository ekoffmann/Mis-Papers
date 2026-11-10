// hs_perfil.cpp — segunda implementación de la decisión por perfiles de filas (N = k^2, k <= 11).
//
// Misma pregunta que tau_perfil.cpp (¿existe un conjunto de corte de tamaño B?), mismo reparto en
// perfiles (c_0, ..., c_{k-1}) con c_v >= 1 elementos en la fila v, pero con una búsqueda distinta:
// en lugar de colocar los elementos de izquierda a derecha, ramifica sobre la progresión sin cortar
// con menos elementos disponibles (como hs_independiente.cpp), con exclusión de elementos y cota
// inferior por empaquetamiento voraz de progresiones disjuntas.  Sirve de control cruzado.
//
// Restricciones del perfil usadas (todas necesarias):
//   - cada fila v contiene exactamente c_v elementos (se propaga: fila llena => resto prohibido;
//     fila con los justos disponibles => todos incluidos);
//   - en cada ventana alineada de g filas [t, t+g-1], los elementos incluidos tienen a lo sumo
//     e = suma de (c_v - 1) colisiones módulo g (el conjunto final tiene g + e elementos y debe
//     tocar las g clases; las colisiones no decrecen al añadir elementos), y si todas las filas
//     de la ventana están completas deben aparecer las g clases.
//
// Uso: hs_perfil k B [J j]     (J j: tratar solo los perfiles con índice % J == j)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128;

static int k, N, B;
static vector<u128> ap;
static u128 rowMask[16];
static int c[16], E[17];
static long long nodes = 0;
static u128 solC = 0;

static inline int pc(u128 x) {
    return __builtin_popcountll((unsigned long long)x) + __builtin_popcountll((unsigned long long)(x >> 64));
}
static inline int lowbit(u128 x) {
    unsigned long long lo = (unsigned long long)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((unsigned long long)(x >> 64));
}

// Propaga las restricciones de fila.  Devuelve false si son incompatibles.
static bool propagateRows(u128 &C, u128 &F) {
    for (int v = 0; v < k; v++) {
        int incl = pc(C & rowMask[v]);
        if (incl > c[v]) return false;
        u128 av = rowMask[v] & ~C & ~F;
        int a = pc(av);
        if (incl + a < c[v]) return false;
        if (incl == c[v]) F |= av;                    // fila llena: el resto queda prohibido
        else if (incl + a == c[v]) C |= av;           // hacen falta todos los disponibles
    }
    return true;
}

// Colisiones módulo g en ventanas alineadas.
static bool windowsOK(u128 C, u128 F) {
    int incl[16]; bool full[16];
    for (int v = 0; v < k; v++) {
        incl[v] = pc(C & rowMask[v]);
        full[v] = (incl[v] == c[v]);
    }
    for (int g = 2; g <= k; g++) {
        for (int t = 0; t + g <= k; t++) {
            unsigned long long mask = 0; int kappa = 0, cnt = 0; bool allFull = true;
            for (int v = t; v < t + g; v++) {
                if (!full[v]) allFull = false;
                u128 r = C & rowMask[v];
                while (r) {
                    int x = lowbit(r); r &= r - 1;
                    int cc = x % g;
                    if (!((mask >> cc) & 1ULL)) { mask |= (1ULL << cc); kappa++; }
                    cnt++;
                }
            }
            int e = E[t + g] - E[t];
            if (cnt - kappa > e) return false;
            if (allFull && kappa < g) return false;
        }
    }
    return true;
}

static bool rec(u128 C, u128 F, const vector<int> &live) {
    nodes++;
    if (!propagateRows(C, F)) return false;
    if (C & F) return false;
    if (!windowsOK(C, F)) return false;
    int m = pc(C);
    if (m > B) return false;
    vector<int> un; un.reserve(live.size());
    int best = -1, bestc = 1000;
    for (int id : live) {
        if (ap[id] & C) continue;
        u128 av = ap[id] & ~F;
        if (!av) return false;
        int cnt = pc(av);
        un.push_back(id);
        if (cnt < bestc) { bestc = cnt; best = id; }
    }
    if (un.empty()) {
        // todas las progresiones cortadas: completar las filas con elementos disponibles cualesquiera
        for (int v = 0; v < k; v++) {
            int incl = pc(C & rowMask[v]);
            u128 av = rowMask[v] & ~C & ~F;
            while (incl < c[v] && av) { int x = lowbit(av); av &= av - 1; C |= ((u128)1 << x); incl++; }
            if (incl != c[v]) return false;
        }
        solC = C;
        return true;
    }
    if (m >= B) return false;
    {   // cota inferior por empaquetamiento voraz
        int needv = 0; u128 used = 0;
        for (int pass = 0; pass < 2; pass++) {
            for (int id : un) {
                u128 av = ap[id] & ~F;
                int cnt = pc(av);
                if ((pass == 0) != (cnt <= 3)) continue;
                if (av & used) continue;
                used |= av; needv++;
                if (m + needv > B) return false;
            }
        }
    }
    u128 av = ap[best] & ~F;
    while (av) {
        int e = lowbit(av);
        av &= av - 1;
        if (rec(C | ((u128)1 << e), F, un)) return true;
        F |= ((u128)1 << e);
    }
    return false;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "uso: hs_perfil k B [J j]\n"); return 2; }
    k = atoi(argv[1]); B = atoi(argv[2]);
    int J = 1, jj = 0;
    if (argc >= 5) { J = atoi(argv[3]); jj = atoi(argv[4]); }
    N = k * k;
    if (k < 2 || k > 11 || B < k) { fprintf(stderr, "parámetros fuera de rango (2 <= k <= 11, B >= k)\n"); return 2; }
    for (int d = 1; (k - 1) * d <= N - 1; d++)
        for (int a = 1; a + (k - 1) * d <= N; a++) {
            u128 msk = 0;
            for (int j = 0; j < k; j++) msk |= ((u128)1 << (a + j * d));
            ap.push_back(msk);
        }
    for (int v = 0; v < k; v++) {
        rowMask[v] = 0;
        for (int x = v * k + 1; x <= (v + 1) * k; x++) rowMask[v] |= ((u128)1 << x);
    }
    vector<int> live(ap.size()); iota(live.begin(), live.end(), 0);
    auto t0 = chrono::steady_clock::now();
    long long nprof = 0, done = 0; bool found = false;
    vector<int> comp(k, 1);
    function<void(int, int)> gen = [&](int pos, int rest) {
        if (found) return;
        if (pos == k - 1) {
            comp[pos] = 1 + rest;
            bool keep = true;
            for (int i = 0; i < k; i++) {
                if (comp[i] < comp[k - 1 - i]) break;
                if (comp[i] > comp[k - 1 - i]) { keep = false; break; }
            }
            if (!keep) return;
            long long id = nprof++;
            if (id % J != jj) return;
            for (int i = 0; i < k; i++) c[i] = comp[i];
            E[0] = 0; for (int i = 0; i < k; i++) E[i + 1] = E[i] + c[i] - 1;
            done++;
            if (rec(0, 0, live)) found = true;
            return;
        }
        for (int v = 0; v <= rest; v++) { comp[pos] = 1 + v; gen(pos + 1, rest - v); if (found) return; }
    };
    gen(0, B - k);
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (found) {
        printf("k=%d N=%d B=%d SAT perfiles=%lld nodos=%lld t=%.1fs perfil=", k, N, B, done, nodes, secs);
        for (int i = 0; i < k; i++) printf("%d", c[i]);
        printf(" H=");
        bool first = true;
        for (int x = 1; x <= N; x++) if ((solC >> x) & 1) { printf("%s%d", first ? "" : ",", x); first = false; }
        printf("\n");
    } else {
        printf("k=%d N=%d B=%d UNSAT%s perfiles=%lld (de %lld) nodos=%lld t=%.1fs\n", k, N, B,
               J > 1 ? " (parcial)" : "", done, nprof, nodes, secs);
    }
    return 0;
}
