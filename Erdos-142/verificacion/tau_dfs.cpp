// tau_dfs.cpp — decisión exacta: ¿existe H ⊆ [1,N] con |H| ≤ B que corte toda progresión
// aritmética de k términos contenida en [1,N]?
//
// Búsqueda en profundidad de izquierda a derecha sobre los elementos ordenados de H.
// Podas (todas son condiciones necesarias, así que la búsqueda es exhaustiva):
//   (1) al declarar t ∉ H, ninguna k-PA con término máximo t puede quedar sin cortar;
//   (2) para cada diferencia d y cada clase c mod d: si la clase tiene L miembros en [1,N] y el
//       último elemento de H en ella tiene índice i0 (−1 si no hay), hacen falta al menos
//       ⌊(L−1−i0)/k⌋ elementos futuros en la clase (ventanas disjuntas aún sin cortar);
//       la suma sobre las clases no puede superar el presupuesto restante;
//   (3) simetría x ↦ N+1−x: se exige h_1 − 1 ≤ N − h_max (salvo con --nosym);
//   (4) forma de ventanas: para cada g con g·k ≤ N y cada intervalo I = [a, a+g·k−1] ⊆ [1,N],
//       H ∩ I debe contener las g clases mod g (cada clase es una k-PA de diferencia g dentro
//       de I).  Si los elementos ya fijados en [a, y] ocupan κ clases, hacen falta g − κ
//       elementos futuros dentro de I y además ⌊(N − a − g·k + 1)/k⌋ después de I
//       (bloques disjuntos de k enteros consecutivos).  Se desactiva con --nowin.
//
// Uso: tau_dfs k N B [--all] [--nosym] [--split J j]
//   Imprime SAT + un H, o UNSAT, y el número de nodos.  Con --all enumera todas las soluciones.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

static int k, N, B, W, Dmax;
struct BS { u64 w[5]; };
static vector<vector<BS>> endAt;          // endAt[t]: máscaras de las k-PA con término máximo t
static vector<vector<int>> lastIdx, clsLen, clsFirst;
static vector<int> sumNeed;
static BS Hm;
static int elems[400];
static int m = 0;
static long long nodes = 0, nsol = 0;
static bool wantAll = false, useSym = true, useWin = true;
static int splitJ = 1, jobj = 0;
static long long prefixCounter = 0;
static vector<int> firstSol;

static inline bool hit(const BS &a) {
    for (int i = 0; i < W; i++) if (a.w[i] & Hm.w[i]) return true;
    return false;
}
static inline bool deadAt(int t) {
    for (const BS &ms : endAt[t]) if (!hit(ms)) return true;
    return false;
}
static inline int need(int L, int i0) { return (L - 1 - i0) / k; }

static int undoStack[400][64];

static inline void addElem(int x) {
    Hm.w[x >> 6] |= (1ULL << (x & 63));
    for (int d = 1; d <= Dmax; d++) {
        int c = x % d;
        int idx = (x - clsFirst[d][c]) / d;
        int old = lastIdx[d][c];
        undoStack[m][d] = old;
        sumNeed[d] += need(clsLen[d][c], idx) - need(clsLen[d][c], old);
        lastIdx[d][c] = idx;
    }
    elems[m++] = x;
}
static inline void delElem() {
    int x = elems[--m];
    Hm.w[x >> 6] &= ~(1ULL << (x & 63));
    for (int d = 1; d <= Dmax; d++) {
        int c = x % d;
        int idx = lastIdx[d][c];
        int old = undoStack[m][d];
        sumNeed[d] += need(clsLen[d][c], old) - need(clsLen[d][c], idx);
        lastIdx[d][c] = old;
    }
}

// devuelve true si hay que detener la búsqueda (solución encontrada y no se piden todas)
static bool dfs(int y) {
    nodes++;
    if (m == 2 && splitJ > 1) {
        if ((prefixCounter++ % splitJ) != jobj) return false;
    }
    int b = B - m;
    for (int d = 1; d <= Dmax; d++) if (sumNeed[d] > b) return false;
    if (useWin) {
        for (int g = 2; g * k <= N; g++) {
            u64 mask = 0; int kappa = 0;
            for (int j = 0; j <= m; j++) {
                // ventana que contiene exactamente los j últimos elementos fijados
                int a = (j == m) ? 1 : elems[m - 1 - j] + 1;
                int end = a + g * k - 1;
                if (end <= N && end > y) {
                    int bound = (g - kappa) + (N - end) / k;
                    if (bound > b) return false;
                }
                if (j < m) {
                    int c = elems[m - 1 - j] % g;
                    if (!((mask >> c) & 1ULL)) { mask |= (1ULL << c); kappa++; }
                }
            }
        }
    }
    // T = primer t > y tal que declarar y+1..t fuera de H deja una PA sin cortar
    int T = -1;
    for (int t = y + 1; t <= N; t++) {
        if (deadAt(t)) { T = t; break; }
    }
    if (T < 0) {            // H ya corta todo
        nsol++;
        if (firstSol.empty()) firstSol.assign(elems, elems + m);
        if (wantAll) {
            printf("SOL");
            for (int i = 0; i < m; i++) printf(" %d", elems[i]);
            printf("\n");
            // también puede haber soluciones mayores dentro del presupuesto; se siguen explorando
        } else return true;
        T = N;              // con --all: seguir añadiendo elementos (soluciones no minimales)
        if (!wantAll) return true;
    }
    if (b == 0) return false;
    int cap = N;
    if (useSym && m >= 1) cap = N + 1 - elems[0];
    int hi = min(T, cap);
    for (int x = hi; x > y; x--) {
        addElem(x);
        bool stop = dfs(x);
        delElem();
        if (stop) return true;
    }
    return false;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "uso: tau_dfs k N B [--all] [--nosym] [--split J j]\n"); return 2; }
    k = atoi(argv[1]); N = atoi(argv[2]); B = atoi(argv[3]);
    for (int i = 4; i < argc; i++) {
        string a = argv[i];
        if (a == "--all") wantAll = true;
        else if (a == "--nosym") useSym = false;
        else if (a == "--nowin") useWin = false;
        else if (a == "--split" && i + 2 < argc) { splitJ = atoi(argv[i + 1]); jobj = atoi(argv[i + 2]); i += 2; }
    }
    if (N > 319 || k < 2) { fprintf(stderr, "parámetros fuera de rango\n"); return 2; }
    W = (N >> 6) + 1;
    Dmax = (N - 1) / (k - 1);
    if (Dmax > 63) { fprintf(stderr, "Dmax demasiado grande\n"); return 2; }
    endAt.assign(N + 1, {});
    for (int d = 1; d <= Dmax; d++)
        for (int a = 1; a + (k - 1) * d <= N; a++) {
            BS ms; memset(&ms, 0, sizeof ms);
            for (int j = 0; j < k; j++) { int x = a + j * d; ms.w[x >> 6] |= (1ULL << (x & 63)); }
            endAt[a + (k - 1) * d].push_back(ms);
        }
    lastIdx.assign(Dmax + 1, {}); clsLen.assign(Dmax + 1, {}); clsFirst.assign(Dmax + 1, {});
    sumNeed.assign(Dmax + 1, 0);
    for (int d = 1; d <= Dmax; d++) {
        lastIdx[d].assign(d, -1); clsLen[d].assign(d, 0); clsFirst[d].assign(d, 0);
        for (int c = 0; c < d; c++) {
            int cf = (c == 0) ? d : c;          // primer miembro de la clase en [1,N]
            clsFirst[d][c] = cf;
            clsLen[d][c] = (cf <= N) ? (N - cf) / d + 1 : 0;
            sumNeed[d] += need(clsLen[d][c], -1);
        }
    }
    memset(&Hm, 0, sizeof Hm);
    auto t0 = chrono::steady_clock::now();
    dfs(0);
    double secs = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (wantAll) {
        printf("k=%d N=%d B=%d soluciones=%lld nodos=%lld t=%.1fs\n", k, N, B, nsol, nodes, secs);
    } else if (nsol > 0) {
        printf("k=%d N=%d B=%d SAT nodos=%lld t=%.1fs H=", k, N, B, nodes, secs);
        for (size_t i = 0; i < firstSol.size(); i++) printf("%s%d", i ? "," : "", firstSol[i]);
        printf("\n");
    } else {
        printf("k=%d N=%d B=%d UNSAT%s nodos=%lld t=%.1fs\n", k, N, B,
               splitJ > 1 ? " (parcial)" : "", nodes, secs);
    }
    return 0;
}
