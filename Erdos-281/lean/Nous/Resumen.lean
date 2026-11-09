import Nous.Erdos281
import Nous.Rogers
import Nous.Erdos281Int
import Nous.Behrend
import Nous.Multiplicity
import Nous.LowerDensity

/-!
# Problema 281 de Erdős — resumen de los teoremas verificados

Este archivo reúne los enunciados principales (demostrados en los demás módulos) en dos
equivalencias y vuelve a imprimir los axiomas de los que depende cada teorema.

* `Erdos281.erdos_281_iff` : (H) ⟺ (C).
* `Erdos281.uniform_iff_homogeneous` : (C) ⟺ (C) solo para la elección homogénea `a = 0`
  (consecuencia del teorema de Rogers).
-/

namespace Erdos281

/-- **(H) ⟺ (C).** Para una sucesión estrictamente creciente de módulos positivos:
toda elección de clases deja sin cubrir un conjunto de densidad `0` si y solo si, para todo `ε > 0`,
un número finito `k` de congruencias ya deja sin cubrir densidad `< ε`, uniformemente en la elección. -/
theorem erdos_281_iff (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    (∀ a : ℕ → ℕ, HasNatDensity (UncInf n a) 0) ↔
      (∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) :=
  ⟨erdos_281 n hn hn0, erdos_281_converse n hn hn0⟩

/-- **Rogers ⟹ basta la elección homogénea.** La conclusión uniforme (C) equivale a la misma
afirmación solo para `a = 0` (es decir, a que los módulos formen una sucesión de Behrend). -/
theorem uniform_iff_homogeneous (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    (∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n a k) d) ↔
      (∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∃ d : ℝ, d < ε ∧ HasNatDensity (Unc n (fun _ => 0) k) d) :=
  ⟨fun C ε hε => (C ε hε).imp fun _ hk => hk _, uniform_of_homogeneous n hn hn0⟩

end Erdos281

#print axioms Erdos281.erdos_281
#print axioms Erdos281.erdos_281_converse
#print axioms Erdos281.erdos_281_iff
#print axioms Erdos281.erdos_281_strong
#print axioms Erdos281.erdos_281_zmod
#print axioms Erdos281.erdos_281_int
#print axioms Rogers.rogers
#print axioms Rogers.rogers_uncovered
#print axioms Erdos281.density_le_homogeneous
#print axioms Erdos281.uniform_of_homogeneous
#print axioms Erdos281.uniform_iff_homogeneous
#print axioms Erdos281.tail_uniform
#print axioms Erdos281.erdos_281_multiplicity
#print axioms Erdos281.erdos_281_multiplicity_of_hyp
#print axioms Erdos281.few_congruences_density_zero
#print axioms Erdos281.maximal_ineq
#print axioms Erdos281.erdos_281_strong_lower
#print axioms Erdos281.erdos_281_lower
