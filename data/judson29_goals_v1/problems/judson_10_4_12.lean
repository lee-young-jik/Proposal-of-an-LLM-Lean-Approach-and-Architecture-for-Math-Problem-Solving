import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_10_4_12_prove : Prop :=
∀ (G : Type) [Group G] (g : G),
  ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x * g = g * x) ∧
    ((Subgroup.zpowers g).Normal → H.Normal)

def judson_10_4_12_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (g : G),
  ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x * g = g * x) ∧
    ((Subgroup.zpowers g).Normal → H.Normal)
)

theorem judson_10_4_12_pair :
  judson_10_4_12_disprove ↔ ¬ judson_10_4_12_prove := Iff.rfl
#print axioms judson_10_4_12_pair

end JudsonGoals
