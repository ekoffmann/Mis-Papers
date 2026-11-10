// hs_independiente.cpp — SEGUNDA implementación, independiente de tau_dfs.cpp.
// La escribió un revisor independiente (otro agente) durante la revisión adversarial de la nota,
// con un algoritmo distinto: ramificación clásica de «hitting set» sobre la progresión sin cortar
// con menos elementos disponibles, con exclusión de elementos («incluir e_i, prohibir e_1..e_{i-1}»)
// y una cota inferior por empaquetamiento voraz de progresiones disjuntas.
// Se incluye tal cual (salvo esta cabecera) como control cruzado de los resultados de exhaustivo.txt.
// Uso: hs_independiente k N B [J j]   (opcional: explorar solo las ramas con índice % J == j)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned __int128 u128;
static int k, N, B;
static vector<u128> ap;            // AP masks
static long long nodes = 0;
static vector<int> sol;
static int splitJ = 1, splitj = 0;
static long long splitCounter = 0;
static const int SPLITDEPTH = 3;   // children created at depth 2 (i.e. nodes of depth 3) are dealt round-robin
static inline int pc(u128 x) { return __builtin_popcountll((unsigned long long)x) + __builtin_popcountll((unsigned long long)(x >> 64)); }
static inline int lowbit(u128 x) {
    unsigned long long lo = (unsigned long long)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((unsigned long long)(x >> 64));
}
// returns true if a hitting set extending C (avoiding F) with total size <= B exists
static bool rec(u128 C, u128 F, int m, const vector<int> &live, int depth) {
    nodes++;
    // collect un-hit APs
    vector<int> un; un.reserve(live.size());
    int best = -1, bestc = 1000;
    for (int id : live) {
        if (ap[id] & C) continue;
        u128 av = ap[id] & ~F;
        if (!av) return false;                    // AP can no longer be hit
        int c = pc(av);
        un.push_back(id);
        if (c < bestc) { bestc = c; best = id; }
    }
    if (un.empty()) {
        sol.clear();
        for (int x = 1; x <= N; x++) if ((C >> x) & 1) sol.push_back(x);
        return true;
    }
    if (m >= B) return false;
    // greedy disjoint packing lower bound (prefer APs with few available elements)
    {
        int need = 0; u128 used = 0;
        // first pass: forced / small APs
        for (int pass = 0; pass < 2; pass++) {
            for (int id : un) {
                u128 av = ap[id] & ~F;
                int c = pc(av);
                if ((pass == 0) != (c <= 3)) continue;
                if (av & used) continue;
                used |= av; need++;
                if (m + need > B) return false;
            }
        }
    }
    u128 av = ap[best] & ~F;
    int idx = 0;
    while (av) {
        int e = lowbit(av);
        av &= av - 1;
        bool go = true;
        if (depth == SPLITDEPTH - 1 && splitJ > 1) { if ((splitCounter++ % splitJ) != splitj) go = false; }
        idx++;
        if (go && rec(C | ((u128)1 << e), F, m + 1, un, depth + 1)) return true;
        F |= ((u128)1 << e);
    }
    return false;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: hs k N B [J j]\n"); return 2; }
    k = atoi(argv[1]); N = atoi(argv[2]); B = atoi(argv[3]);
    if (argc >= 6) { splitJ = atoi(argv[4]); splitj = atoi(argv[5]); }
    if (N > 126) { fprintf(stderr, "N too large\n"); return 2; }
    for (int d = 1; (k - 1) * d <= N - 1; d++)
        for (int a = 1; a + (k - 1) * d <= N; a++) {
            u128 msk = 0;
            for (int j = 0; j < k; j++) msk |= ((u128)1 << (a + j * d));
            ap.push_back(msk);
        }
    vector<int> live(ap.size()); iota(live.begin(), live.end(), 0);
    auto t0 = chrono::steady_clock::now();
    bool ok = rec(0, 0, 0, live, 0);
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (ok) {
        printf("k=%d N=%d B=%d SAT nodes=%lld t=%.1fs H=", k, N, B, nodes, secs);
        for (size_t i = 0; i < sol.size(); i++) printf("%s%d", i ? "," : "", sol[i]);
        printf("\n");
    } else printf("k=%d N=%d B=%d UNSAT%s nodes=%lld t=%.1fs\n", k, N, B, splitJ > 1 ? " (partial)" : "", nodes, secs);
    return 0;
}
