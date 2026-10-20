import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_8_prove : Prop :=
¬ Nonempty (ℚ ≃+ ℤ)

def judson_9_4_8_disprove : Prop :=
¬ (
¬ Nonempty (ℚ ≃+ ℤ)
)

theorem judson_9_4_8_pair :
  judson_9_4_8_disprove ↔ ¬ judson_9_4_8_prove := Iff.rfl
#print axioms judson_9_4_8_pair

end JudsonGoals
