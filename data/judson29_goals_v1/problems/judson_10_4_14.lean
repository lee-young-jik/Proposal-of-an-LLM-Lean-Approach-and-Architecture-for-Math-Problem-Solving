import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_10_4_14_prove : Prop :=
∀ (G : Type) [Group G],
  (commutator G).Normal ∧
  (∀ N : Subgroup G, ∀ _ : N.Normal,
    (∀ a b : G ⧸ N, a * b = b * a) ↔ commutator G ≤ N)

def judson_10_4_14_disprove : Prop :=
¬ (
∀ (G : Type) [Group G],
  (commutator G).Normal ∧
  (∀ N : Subgroup G, ∀ _ : N.Normal,
    (∀ a b : G ⧸ N, a * b = b * a) ↔ commutator G ≤ N)
)

theorem judson_10_4_14_pair :
  judson_10_4_14_disprove ↔ ¬ judson_10_4_14_prove := Iff.rfl
#print axioms judson_10_4_14_pair

end JudsonGoals
