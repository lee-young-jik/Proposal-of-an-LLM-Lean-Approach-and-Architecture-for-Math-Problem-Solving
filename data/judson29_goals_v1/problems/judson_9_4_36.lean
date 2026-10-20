import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_36_prove : Prop :=
∀ B : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  ∃ f : Matrix.SpecialLinearGroup (Fin 2) ℝ ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ((f A) : Matrix (Fin 2) (Fin 2) ℝ) =
        (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
        (A : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ)

def judson_9_4_36_disprove : Prop :=
¬ (
∀ B : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  ∃ f : Matrix.SpecialLinearGroup (Fin 2) ℝ ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ((f A) : Matrix (Fin 2) (Fin 2) ℝ) =
        (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
        (A : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ)
)

theorem judson_9_4_36_pair :
  judson_9_4_36_disprove ↔ ¬ judson_9_4_36_prove := Iff.rfl
#print axioms judson_9_4_36_pair

end JudsonGoals
