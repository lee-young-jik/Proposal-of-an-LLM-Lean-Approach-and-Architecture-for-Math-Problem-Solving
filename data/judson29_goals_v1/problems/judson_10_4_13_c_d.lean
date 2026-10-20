import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_10_4_13_c_d_prove : Prop :=
∀ (G : Type) [Group G],
  (Subgroup.center G).Normal ∧
  (IsCyclic (G ⧸ Subgroup.center G) → ∀ a b : G, a * b = b * a)

def judson_10_4_13_c_d_disprove : Prop :=
¬ (
∀ (G : Type) [Group G],
  (Subgroup.center G).Normal ∧
  (IsCyclic (G ⧸ Subgroup.center G) → ∀ a b : G, a * b = b * a)
)

theorem judson_10_4_13_c_d_pair :
  judson_10_4_13_c_d_disprove ↔ ¬ judson_10_4_13_c_d_prove := Iff.rfl
#print axioms judson_10_4_13_c_d_pair

end JudsonGoals
