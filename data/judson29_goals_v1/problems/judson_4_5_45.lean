import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_45_prove : Prop :=
∀ z : ℂˣ, ‖(z : ℂ)‖ ≠ 1 → orderOf z = 0

def judson_4_5_45_disprove : Prop :=
¬ (
∀ z : ℂˣ, ‖(z : ℂ)‖ ≠ 1 → orderOf z = 0
)

theorem judson_4_5_45_pair :
  judson_4_5_45_disprove ↔ ¬ judson_4_5_45_prove := Iff.rfl
#print axioms judson_4_5_45_pair

end JudsonGoals
