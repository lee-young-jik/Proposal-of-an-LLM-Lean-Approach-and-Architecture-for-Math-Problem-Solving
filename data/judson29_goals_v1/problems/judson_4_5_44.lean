import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_44_prove : Prop :=
∀ (α : Circle) (m n : ℤ),
  (α ^ m = 1 ∧ α ^ n = 1) ↔ α ^ (Int.gcd m n : ℤ) = 1

def judson_4_5_44_disprove : Prop :=
¬ (
∀ (α : Circle) (m n : ℤ),
  (α ^ m = 1 ∧ α ^ n = 1) ↔ α ^ (Int.gcd m n : ℤ) = 1
)

theorem judson_4_5_44_pair :
  judson_4_5_44_disprove ↔ ¬ judson_4_5_44_prove := Iff.rfl
#print axioms judson_4_5_44_pair

end JudsonGoals
