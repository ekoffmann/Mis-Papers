// tau_perfil.cpp — decisión exacta para N = k^2 organizada por «perfiles de filas».
//
// ¿Existe H ⊆ [1,k^2] con |H| = B que corte toda progresión aritmética de k términos de [1,k^2]?
//
// Filas: R_v = [vk+1, (v+1)k], v = 0..k-1.  Cada fila es una k-PA de diferencia 1, así que un
// conjunto de corte tiene c_v >= 1 elementos en R_v.  El programa recorre todos los perfiles
// (c_0, ..., c_{k-1}) con c_v >= 1 y suma B y, para cada uno, hace una búsqueda en profundidad de
// izquierda a derecha (como tau_dfs.cpp) con el número de elementos de cada fila fijado.
//
// Poda adicional (la que da la ganancia).  Una ventana alineada de g filas [t, t+g-1] es un
// intervalo de g·k enteros; por el lema de ventanas, H debe tocar en ella las g clases mod g.
// Con el perfil fijado, la ventana contiene exactamente g + e elementos, e = suma de (c_v - 1)
// sobre sus filas, luego el número de «colisiones» (elementos menos clases distintas) es al final
// exactamente e.  Las colisiones no decrecen al añadir elementos, así que un prefijo con más de e
// colisiones en la ventana no puede completarse; y una ventana ya completa debe tener las g clases.
//
// Además se conservan las podas (1), (2) y (4) de tau_dfs.cpp (todas condiciones necesarias).
// Simetría x -> k^2+1-x: invierte el perfil, así que basta recorrer los perfiles c <=_lex inv(c).
//
// Uso: tau_perfil k B [J j]     (J j: tratar solo los perfiles con índice % J == j)
// Imprime SAT + un conjunto, o UNSAT, con el número de perfiles y de nodos.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

static int k, N, B, W, Dmax;
struct BS { u64 w[5]; };
static vector<vector<BS>> endAt;
static vector<vector<int>> lastIdx, clsLen, clsFirst;
static vector<int> sumNeed;
static BS Hm;
static int elems[400], rowOf[400];
static int m = 0;
static long long nodes = 0;
static int c[64], E[65], cntRow[64];
static int undoStack[400][64];
static vector<int> sol;

static inline bool hit(const BS &a) {
    for (int i = 0; i < W; i++) if (a.w[i] & Hm.w[i]) return true;
    return false;
}
static inline bool deadAt(int t) {
    for (const BS &ms : endAt[t]) if (!hit(ms)) return true;
    return false;
}
static inline int need(int L, int i0) { return (L - 1 - i0) / k; }

static inline void addElem(int x) {
    Hm.w[x >> 6] |= (1ULL << (x & 63));
    for (int d = 1; d <= Dmax; d++) {
        int cc = x % d;
        int idx = (x - clsFirst[d][cc]) / d;
        int old = lastIdx[d][cc];
        undoStack[m][d] = old;
        sumNeed[d] += need(clsLen[d][cc], idx) - need(clsLen[d][cc], old);
        lastIdx[d][cc] = idx;
    }
    rowOf[m] = (x - 1) / k;
    cntRow[rowOf[m]]++;
    elems[m++] = x;
}
static inline void delElem() {
    int x = elems[--m];
    cntRow[rowOf[m]]--;
    Hm.w[x >> 6] &= ~(1ULL << (x & 63));
    for (int d = 1; d <= Dmax; d++) {
        int cc = x % d;
        int idx = lastIdx[d][cc];
        int old = undoStack[m][d];
        sumNeed[d] += need(clsLen[d][cc], old) - need(clsLen[d][cc], idx);
        lastIdx[d][cc] = old;
    }
}

// y = último elemento colocado (0 si no hay).  Devuelve true si encuentra un conjunto de corte.
static bool dfs(int y) {
    nodes++;
    int b = B - m;
    for (int d = 1; d <= Dmax; d++) if (sumNeed[d] > b) return false;
    int rl = (m == 0) ? 0 : rowOf[m - 1];                 // fila en curso
    bool rowDone = (m > 0) && (cntRow[rl] == c[rl]);
    // poda (4) de tau_dfs: ventanas arbitrarias con el presupuesto restante
    for (int g = 2; g * k <= N; g++) {
        u64 mask = 0; int kappa = 0;
        for (int j = 0; j <= m; j++) {
            int a = (j == m) ? 1 : elems[m - 1 - j] + 1;
            int end = a + g * k - 1;
            if (end <= N && end > y) {
                int bound = (g - kappa) + (N - end) / k;
                if (bound > b) return false;
            }
            if (j < m) {
                int cc = elems[m - 1 - j] % g;
                if (!((mask >> cc) & 1ULL)) { mask |= (1ULL << cc); kappa++; }
            }
        }
    }
    // poda de perfil: ventanas alineadas [t, t+g-1] que contienen la fila en curso
    if (m > 0) {
        for (int g = 2; g <= k; g++) {
            u64 mask = 0; int kappa = 0, cnt = 0;
            for (int idx = m - 1; idx >= 0; idx--) {
                int cc = elems[idx] % g;
                if (!((mask >> cc) & 1ULL)) { mask |= (1ULL << cc); kappa++; }
                cnt++;
                if (idx == 0 || rowOf[idx - 1] < rowOf[idx]) {
                    int t = rowOf[idx];
                    if (t + g - 1 < rl) break;             // la ventana ya no contiene la fila en curso
                    if (t + g <= k) {
                        int e = E[t + g] - E[t];
                        if (cnt - kappa > e) return false;
                        if (rowDone && t + g - 1 == rl && kappa < g) return false;   // ventana completa
                    }
                }
            }
        }
    }
    if (m == B) {                                          // todo colocado: comprobar el final
        for (int t = y + 1; t <= N; t++) if (deadAt(t)) return false;
        sol.assign(elems, elems + m);
        return true;
    }
    int R = (m == 0) ? 0 : (rowDone ? rl + 1 : rl);        // fila del siguiente elemento
    if (R >= k) return false;
    int lo = max(y + 1, R * k + 1), hi = (R + 1) * k;
    // T = primer t > y tal que dejar y+1..t fuera de H deja una PA sin cortar
    for (int t = y + 1; t <= hi; t++) {
        if (deadAt(t)) { hi = t; break; }
    }
    if (hi < lo) return false;
    for (int x = hi; x >= lo; x--) {
        addElem(x);
        bool ok = dfs(x);
        delElem();
        if (ok) return true;
    }
    return false;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "uso: tau_perfil k B [J j]\n"); return 2; }
    k = atoi(argv[1]); B = atoi(argv[2]);
    int J = 1, jj = 0;
    if (argc >= 5) { J = atoi(argv[3]); jj = atoi(argv[4]); }
    N = k * k;
    if (k < 2 || k > 17 || B < k) { fprintf(stderr, "parámetros fuera de rango (2 <= k <= 17, B >= k)\n"); return 2; }
    W = (N >> 6) + 1;
    Dmax = (N - 1) / (k - 1);
    endAt.assign(N + 1, {});
    for (int d = 1; d <= Dmax; d++)
        for (int a = 1; a + (k - 1) * d <= N; a++) {
            BS ms; memset(&ms, 0, sizeof ms);
            for (int j = 0; j < k; j++) { int x = a + j * d; ms.w[x >> 6] |= (1ULL << (x & 63)); }
            endAt[a + (k - 1) * d].push_back(ms);
        }
    lastIdx.assign(Dmax + 1, {}); clsLen.assign(Dmax + 1, {}); clsFirst.assign(Dmax + 1, {});
    sumNeed.assign(Dmax + 1, 0);
    vector<int> sumNeed0(Dmax + 1, 0);
    for (int d = 1; d <= Dmax; d++) {
        lastIdx[d].assign(d, -1); clsLen[d].assign(d, 0); clsFirst[d].assign(d, 0);
        for (int cc = 0; cc < d; cc++) {
            int cf = (cc == 0) ? d : cc;
            clsFirst[d][cc] = cf;
            clsLen[d][cc] = (cf <= N) ? (N - cf) / d + 1 : 0;
            sumNeed0[d] += need(clsLen[d][cc], -1);
        }
    }
    auto t0 = chrono::steady_clock::now();
    long long nprof = 0, done = 0;
    bool found = false;
    // enumerar composiciones de B en k partes positivas (orden lexicográfico)
    vector<int> comp(k, 1);
    int extra = B - k;
    // generador recursivo iterativo: distribuimos 'extra' unidades
    function<void(int, int)> gen = [&](int pos, int rest) {
        if (found) return;
        if (pos == k - 1) {
            comp[pos] = 1 + rest;
            // simetría: solo perfiles c <=_lex invertido(c)
            bool keep = true;
            for (int i = 0; i < k; i++) {
                if (comp[i] < comp[k - 1 - i]) break;
                if (comp[i] > comp[k - 1 - i]) { keep = false; break; }
            }
            if (!keep) return;
            long long id = nprof++;
            if (id % J != jj) return;
            for (int i = 0; i < k; i++) { c[i] = comp[i]; cntRow[i] = 0; }
            E[0] = 0; for (int i = 0; i < k; i++) E[i + 1] = E[i] + c[i] - 1;
            memset(&Hm, 0, sizeof Hm); m = 0;
            for (int d = 1; d <= Dmax; d++) { sumNeed[d] = sumNeed0[d]; fill(lastIdx[d].begin(), lastIdx[d].end(), -1); }
            done++;
            if (dfs(0)) found = true;
            return;
        }
        for (int v = 0; v <= rest; v++) { comp[pos] = 1 + v; gen(pos + 1, rest - v); if (found) return; }
    };
    gen(0, extra);
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (found) {
        printf("k=%d N=%d B=%d SAT perfiles=%lld nodos=%lld t=%.1fs perfil=", k, N, B, done, nodes, secs);
        for (int i = 0; i < k; i++) printf("%d", c[i]);
        printf(" H=");
        for (size_t i = 0; i < sol.size(); i++) printf("%s%d", i ? "," : "", sol[i]);
        printf("\n");
    } else {
        printf("k=%d N=%d B=%d UNSAT%s perfiles=%lld (de %lld) nodos=%lld t=%.1fs\n", k, N, B,
               J > 1 ? " (parcial)" : "", done, nprof, nodes, secs);
    }
    return 0;
}
