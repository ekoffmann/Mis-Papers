// check_Hp.cpp — comprueba por fuerza bruta el Teorema D de la nota: para cada primo p en [7, Pmax],
// el conjunto H_p = {2, p+1, 2p-1} ∪ [2p+3, 3p-2] ∪ {jp : 3 <= j <= p} corta todas las progresiones
// aritméticas de p términos contenidas en [1, p^2], y |H_p| = 2p-3.
// Uso: check_Hp Pmax
#include <bits/stdc++.h>
using namespace std;
int main(int argc, char **argv) {
    int Pmax = argc > 1 ? atoi(argv[1]) : 199;
    int nprimes = 0; bool allok = true;
    for (int p = 7; p <= Pmax; p++) {
        bool prime = true;
        for (int q = 2; q * q <= p; q++) if (p % q == 0) { prime = false; break; }
        if (!prime) continue;
        int N = p * p;
        vector<char> H(N + 1, 0);
        H[2] = H[p + 1] = H[2 * p - 1] = 1;
        for (int x = 2 * p + 3; x <= 3 * p - 2; x++) H[x] = 1;
        for (int j = 3; j <= p; j++) H[j * p] = 1;
        int card = 0; for (int x = 1; x <= N; x++) card += H[x];
        long long unhit = 0, total = 0;
        for (int d = 1; (long long)(p - 1) * d <= N - 1; d++)
            for (int a = 1; a + (p - 1) * d <= N; a++) {
                total++;
                bool hit = false;
                for (int j = 0; j < p; j++) if (H[a + j * d]) { hit = true; break; }
                if (!hit) unhit++;
            }
        bool ok = (unhit == 0 && card == 2 * p - 3);
        if (!ok) { allok = false; printf("FALLO p=%d: |H|=%d, progresiones sin cortar=%lld\n", p, card, unhit); }
        nprimes++;
    }
    printf("primos comprobados en [7, %d]: %d; resultado: %s\n", Pmax, nprimes, allok ? "TODOS OK" : "HAY FALLOS");
    return allok ? 0 : 1;
}
