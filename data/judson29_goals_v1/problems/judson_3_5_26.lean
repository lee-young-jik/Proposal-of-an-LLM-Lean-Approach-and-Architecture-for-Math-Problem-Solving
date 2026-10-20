import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_3_5_26_prove : Prop :=
∀ n : ℕ, 2 < n → ∃ k : (ZMod n)ˣ, k ^ 2 = 1 ∧ k ≠ 1

def judson_3_5_26_disprove : Prop :=
¬ (
∀ n : ℕ, 2 < n → ∃ k : (ZMod n)ˣ, k ^ 2 = 1 ∧ k ≠ 1
)

theorem judson_3_5_26_pair :
  judson_3_5_26_disprove ↔ ¬ judson_3_5_26_prove := Iff.rfl
#print axioms judson_3_5_26_pair

end JudsonGoals
