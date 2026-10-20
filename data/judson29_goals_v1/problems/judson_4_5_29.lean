import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_29_prove : Prop :=
∀ n : ℕ, 2 < n →
  Even (Nat.card {x : ZMod n | AddSubgroup.zmultiples x = ⊤})

def judson_4_5_29_disprove : Prop :=
¬ (
∀ n : ℕ, 2 < n →
  Even (Nat.card {x : ZMod n | AddSubgroup.zmultiples x = ⊤})
)

theorem judson_4_5_29_pair :
  judson_4_5_29_disprove ↔ ¬ judson_4_5_29_prove := Iff.rfl
#print axioms judson_4_5_29_pair

end JudsonGoals
