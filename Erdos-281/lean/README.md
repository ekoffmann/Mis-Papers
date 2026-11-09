# Verificación formal (Lean 4 + Mathlib) — Problema 281 de Erdős

Protocolo: un enunciado lleva **[PROBADO]** solo si (1) el archivo compila con código de salida 0, (2) no contiene `sorry`, y (3) `#print axioms` muestra únicamente `propext`, `Classical.choice` y `Quot.sound`.

## Versiones

- Lean `4.35.0` (`leanprover/lean4:v4.35.0`, ver `lean-toolchain`).
- Mathlib `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (ver `lake-manifest.json`).

## Cómo reproducir

```bash
cd Erdos-281/lean
```

```bash
lake exe cache get
```

```bash
lake build
```

`lake build` compila todos los módulos (`Nous.lean` los importa a todos) e imprime la salida de `#print axioms` de cada teorema. Un archivo suelto se comprueba con, por ejemplo:

```bash
lake env lean Nous/Erdos281.lean
```

## Archivos y enunciados

| Archivo | Teoremas principales | Contenido |
|---|---|---|
| `Nous/Erdos281.lean` (812 líneas) | `erdos_281`, `erdos_281_converse`, `erdos_281_strong`, `erdos_281_zmod` | Problema 281 por la demostración finitaria (König dos veces, conteo doble, Markov, ventanas de un período). Autocontenido: solo `import Mathlib`. |
| `Nous/Rogers.lean` (343) | `rogers`, `rogers_uncovered` | Teorema de Rogers por inducción sobre $N$ (teorema chino + lema de la cadena). Autocontenido. |
| `Nous/Erdos281Int.lean` (301) | `erdos_281_int` | Versión para subconjuntos de $\mathbb{Z}$ con densidad bilateral y clases en `ZMod (n i)`; misma forma que el enunciado de `google-deepmind/formal-conjectures`. |
| `Nous/Behrend.lean` (78) | `density_le_homogeneous`, `uniform_of_homogeneous` | Rogers en forma de densidad; la elección homogénea controla todas. |
| `Nous/Multiplicity.lean` (378) | `tail_uniform`, `erdos_281_multiplicity`, `erdos_281_multiplicity_of_hyp`, `few_congruences_density_zero` | Las colas heredan (C); versión con multiplicidad (NOTA, Teorema 4). |
| `Nous/LowerDensity.lean` (420) | `maximal_ineq`, `erdos_281_strong_lower`, `erdos_281_lower` | Desigualdad maximal elemental; hipótesis debilitada a densidad inferior cero. |
| `Nous/Resumen.lean` (55) | `erdos_281_iff`, `uniform_iff_homogeneous` | Equivalencias (H) ⟺ (C) y (C) ⟺ (C) para $a=0$; reimprime los axiomas de los 18 teoremas. |

Enunciados principales, tal como compilan:

```lean
theorem erdos_281 (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (H : ∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d

theorem erdos_281_lower (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0)
    (H : ∀ a : ℕ → ℕ, ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((UncInf n a ∩ Set.Iio N).ncard : ℝ) < c * (N : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d

theorem erdos_281_int (n : ℕ → ℕ) (hn : StrictMono n) (hpos : ∀ i, 0 < n i)
    (H : ∀ a : (i : ℕ) → ZMod (n i), HasIntDensity {m : ℤ | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i} 0) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : (i : ℕ) → ZMod (n i),
      ∃ d : ℝ, HasIntDensity {m : ℤ | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i} d ∧ d < ε

theorem erdos_281_multiplicity (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 2 ≤ n 0)
    (C : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) :
    ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧
      HasNatDensity {m : ℕ | mult n a k m < r} d

theorem rogers (k : ℕ) (n a : ℕ → ℕ) (N : ℕ) (hN : 0 < N) (hdvd : ∀ i, i < k → n i ∣ N) :
    ((Finset.range N).filter (fun m => ∃ i, i < k ∧ n i ∣ m)).card ≤
      ((Finset.range N).filter (fun m => ∃ i, i < k ∧ m ≡ a i [MOD n i])).card
```

## Correspondencia enunciado informal ↔ enunciado Lean

| Informal | Lean |
|---|---|
| Sucesión $n_1 \lt n_2 \lt \cdots$ de enteros positivos | `n : ℕ → ℕ`, `StrictMono n`, `0 < n 0` (índices desde 0) |
| Elección de clases $a_i \pmod{n_i}$ | `a : ℕ → ℕ` (un representante natural de cada clase) o `a : (i : ℕ) → ZMod (n i)` |
| $m \equiv a_i \pmod{n_i}$ | `m ≡ a i [MOD n i]` (`Nat.ModEq`) o `(m : ZMod (n i)) = a i` |
| No cubiertos por las primeras $k$ congruencias | `Unc n a k = {m | ∀ i, i < k → ¬ m ≡ a i [MOD n i]}` |
| No cubiertos por ninguna | `UncInf n a = {m | ∀ i, ¬ m ≡ a i [MOD n i]}` |
| $S \subseteq \mathbb{N}$ tiene densidad natural $d$ | `HasNatDensity S d`: `#(S ∩ [0,N)) / N → d` |
| $S \subseteq \mathbb{Z}$ tiene densidad (bilateral) $d$ | `HasIntDensity S d`: `#(S ∩ [-N,N]) / (2N+1) → d` |
| "la densidad … es menor que $\varepsilon$" | `∃ d, d < ε ∧ HasNatDensity (Unc n a k) d` (la densidad existe y es $\lt \varepsilon$) |

Trampas revisadas: no hay resta truncada en los enunciados (las densidades son reales; los desplazamientos se codifican con sumas); `N = 0` da `0/0 = 0` en Lean pero no afecta a los límites; `n i > 0` se deduce de `StrictMono n` y `0 < n 0`; el orden de cuantificadores de la conclusión es `∀ ε, ∃ k, ∀ a` (uniformidad en la elección), como en el problema.

## Registro de verificación

Resultado de la compilación limpia de todo el proyecto (`lake build`), realizada el 9‑11‑2026: **código de salida 0**, sin `sorry`, y los 18 teoremas listados dependen únicamente de `[propext, Classical.choice, Quot.sound]`. El registro completo (versiones, sha256 de cada fuente, auditoría de palabras prohibidas y salida de `#print axioms`) está en [`registro_verificacion.txt`](registro_verificacion.txt).

Etiqueta resultante: **[PROBADO]** para los enunciados de la tabla anterior. Lo que **no** está formalizado (y por tanto queda **[PLAUSIBLE]** en `../NOTA.md`): el valor exacto $d(R(b)) = \varepsilon^\ast$ de la Proposición 4.2 (aquí solo la cota $\ge \varepsilon/2$), la Proposición 5.3 (dirección necesaria de Davenport–Erdős), el Teorema 3(b),(d) y el Teorema 7.1 (grupos abelianos). Un lema probado no es el teorema grande: la etiqueta [PROBADO] se aplica exactamente a los enunciados Lean citados, cuya correspondencia con los enunciados informales se detalla en la sección anterior.

Las advertencias que emite `lake build` son solo de estilo (longitud de línea, uso de `show`, cabecera de copyright) y no afectan a la corrección.

Nota: existe una formalización pública independiente, anterior, del argumento profinito de Somani/GPT‑5.2 Pro (<https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos281.lean>); la de esta carpeta formaliza una demostración distinta (finitaria) y enunciados adicionales, y no reutiliza código de aquella.
