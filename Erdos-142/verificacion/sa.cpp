// sa.cpp — búsqueda heurística (recocido simulado) de un conjunto H ⊆ [1,N] con |H| = B que corte
// todas las k-PA de [1,N].  Solo puede demostrar existencia (si encuentra coste 0); un fracaso no
// demuestra nada.
// Uso: sa k N B segundos semilla
#include <bits/stdc++.h>
using namespace std;

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "uso: sa k N B segundos semilla\n"); return 2; }
    int k = atoi(argv[1]), N = atoi(argv[2]), B = atoi(argv[3]);
    double secs = atof(argv[4]);
    unsigned seed = (unsigned)atoi(argv[5]);
    mt19937 rng(seed);
    vector<vector<int>> aps;                 // lista de PAs (elementos)
    vector<vector<int>> inc(N + 1);          // PAs que contienen x
    for (int d = 1; (k - 1) * d <= N - 1; d++)
        for (int a = 1; a + (k - 1) * d <= N; a++) {
            vector<int> P;
            for (int j = 0; j < k; j++) P.push_back(a + j * d);
            for (int x : P) inc[x].push_back((int)aps.size());
            aps.push_back(P);
        }
    int M = (int)aps.size();
    vector<int> cnt(M, 0);                   // nº de elementos de H en cada PA
    vector<char> in(N + 1, 0);
    vector<int> elems, outs;
    auto t0 = chrono::steady_clock::now();
    auto elapsed = [&]() { return chrono::duration<double>(chrono::steady_clock::now() - t0).count(); };
    long long iters = 0; int best = INT_MAX; int restarts = 0;
    uniform_real_distribution<double> U(0, 1);
    while (elapsed() < secs) {
        restarts++;
        // estado inicial aleatorio
        fill(in.begin(), in.end(), 0); fill(cnt.begin(), cnt.end(), 0);
        vector<int> perm(N); iota(perm.begin(), perm.end(), 1); shuffle(perm.begin(), perm.end(), rng);
        elems.assign(perm.begin(), perm.begin() + B); outs.assign(perm.begin() + B, perm.end());
        for (int x : elems) { in[x] = 1; for (int p : inc[x]) cnt[p]++; }
        int cost = 0; for (int p = 0; p < M; p++) if (cnt[p] == 0) cost++;
        double T = 2.0;
        long long steps = 400000LL * 20;
        for (long long it = 0; it < steps && cost > 0; it++) {
            iters++;
            if ((it & 4095) == 0) { T = 2.0 * pow(0.02 / 2.0, (double)it / steps); if (elapsed() > secs) break; }
            int i = rng() % B, j = rng() % (N - B);
            int x = elems[i], z = outs[j];
            // delta de coste al cambiar x (sale) por z (entra)
            int delta = 0;
            for (int p : inc[x]) if (cnt[p] == 1) delta++;          // quedarían sin cortar
            for (int p : inc[z]) if (cnt[p] == 0) delta--;          // quedarían cortadas
            // corrección: PAs que contienen a ambos y tenían cnt==1 (solo x) siguen cortadas por z
            for (int p : inc[x]) if (cnt[p] == 1) {
                const vector<int> &P = aps[p];
                if (binary_search(P.begin(), P.end(), z)) delta--;
            }
            if (delta <= 0 || U(rng) < exp(-delta / T)) {
                for (int p : inc[x]) cnt[p]--;
                for (int p : inc[z]) cnt[p]++;
                in[x] = 0; in[z] = 1; elems[i] = z; outs[j] = x; cost += delta;
            }
        }
        if (cost < best) { best = cost; fprintf(stderr, "  [restart %d] mejor coste=%d\n", restarts, best); }
        if (cost == 0) {
            sort(elems.begin(), elems.end());
            // verificación independiente
            bool ok = true;
            for (auto &P : aps) { bool h = false; for (int x : P) if (in[x]) { h = true; break; } if (!h) ok = false; }
            printf("k=%d N=%d B=%d ENCONTRADO (verificado=%d) H=", k, N, B, (int)ok);
            for (int i = 0; i < B; i++) printf("%s%d", i ? "," : "", elems[i]);
            printf("  [%.1fs, %lld iteraciones, %d reinicios]\n", elapsed(), iters, restarts);
            return 0;
        }
    }
    printf("k=%d N=%d B=%d NO ENCONTRADO: mejor coste=%d  [%.1fs, %lld iteraciones, %d reinicios]\n",
           k, N, B, best, elapsed(), iters, restarts);
    return 1;
}
