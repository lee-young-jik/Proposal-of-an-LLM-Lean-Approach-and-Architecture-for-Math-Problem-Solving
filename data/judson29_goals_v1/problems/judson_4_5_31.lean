import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_31_prove : Prop :=
∀ (G : Type) [CommGroup G], ∃ H : Subgroup G,
  ∀ g : G, g ∈ H ↔ IsOfFinOrder g

def judson_4_5_31_disprove : Prop :=
¬ (
∀ (G : Type) [CommGroup G], ∃ H : Subgroup G,
  ∀ g : G, g ∈ H ↔ IsOfFinOrder g
)

theorem judson_4_5_31_pair :
  judson_4_5_31_disprove ↔ ¬ judson_4_5_31_prove := Iff.rfl
#print axioms judson_4_5_31_pair

end JudsonGoals
