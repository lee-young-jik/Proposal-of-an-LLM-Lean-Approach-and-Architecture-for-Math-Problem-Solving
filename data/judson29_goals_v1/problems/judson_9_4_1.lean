import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_1_prove : Prop :=
∀ n : ℤ, n ≠ 0 →
  Nonempty (ℤ ≃+ AddSubgroup.zmultiples n)

def judson_9_4_1_disprove : Prop :=
¬ (
∀ n : ℤ, n ≠ 0 →
  Nonempty (ℤ ≃+ AddSubgroup.zmultiples n)
)

theorem judson_9_4_1_pair :
  judson_9_4_1_disprove ↔ ¬ judson_9_4_1_prove := Iff.rfl
#print axioms judson_9_4_1_pair

end JudsonGoals
