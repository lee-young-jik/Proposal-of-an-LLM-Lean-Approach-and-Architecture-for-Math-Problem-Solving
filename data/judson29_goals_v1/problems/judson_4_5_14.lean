import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_14_prove : Prop :=
let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0];
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1];
  IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B)

def judson_4_5_14_disprove : Prop :=
¬ (
let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0];
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1];
  IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B)
)

theorem judson_4_5_14_pair :
  judson_4_5_14_disprove ↔ ¬ judson_4_5_14_prove := Iff.rfl
#print axioms judson_4_5_14_pair

end JudsonGoals
