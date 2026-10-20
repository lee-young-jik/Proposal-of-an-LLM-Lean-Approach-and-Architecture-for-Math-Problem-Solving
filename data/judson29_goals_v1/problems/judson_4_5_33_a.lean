import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_33_a_prove : Prop :=
∀ (G : Type) [CommGroup G] (H K : Subgroup G),
  Nat.card H = 2 → Nat.card K = 2 → H ≠ K →
  ∃ L : Subgroup G, Nat.card L = 4

def judson_4_5_33_a_disprove : Prop :=
¬ (
∀ (G : Type) [CommGroup G] (H K : Subgroup G),
  Nat.card H = 2 → Nat.card K = 2 → H ≠ K →
  ∃ L : Subgroup G, Nat.card L = 4
)

theorem judson_4_5_33_a_pair :
  judson_4_5_33_a_disprove ↔ ¬ judson_4_5_33_a_prove := Iff.rfl
#print axioms judson_4_5_33_a_pair

end JudsonGoals
