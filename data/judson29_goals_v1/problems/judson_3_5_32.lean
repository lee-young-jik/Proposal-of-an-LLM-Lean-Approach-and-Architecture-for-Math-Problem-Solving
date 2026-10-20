import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_3_5_32_prove : Prop :=
∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) →
  ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1

def judson_3_5_32_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) →
  ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1
)

theorem judson_3_5_32_pair :
  judson_3_5_32_disprove ↔ ¬ judson_3_5_32_prove := Iff.rfl
#print axioms judson_3_5_32_pair

end JudsonGoals
