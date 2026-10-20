import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_2_prove : Prop :=
∃ H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  (∀ M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
    M ∈ H ↔ ∃ a b : ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a]) ∧
  Nonempty (ℂˣ ≃* H)

def judson_9_4_2_disprove : Prop :=
¬ (
∃ H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  (∀ M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
    M ∈ H ↔ ∃ a b : ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a]) ∧
  Nonempty (ℂˣ ≃* H)
)

theorem judson_9_4_2_pair :
  judson_9_4_2_disprove ↔ ¬ judson_9_4_2_prove := Iff.rfl
#print axioms judson_9_4_2_pair

end JudsonGoals
