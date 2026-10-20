import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_46_prove : Prop :=
∀ (G H : Type) [Group G] [Group H], Nonempty (G ≃* H) →
  ∀ n : ℕ, 0 < n → (∃ K : Subgroup G, Nat.card K = n) →
    ∃ L : Subgroup H, Nat.card L = n

def judson_9_4_46_disprove : Prop :=
¬ (
∀ (G H : Type) [Group G] [Group H], Nonempty (G ≃* H) →
  ∀ n : ℕ, 0 < n → (∃ K : Subgroup G, Nat.card K = n) →
    ∃ L : Subgroup H, Nat.card L = n
)

theorem judson_9_4_46_pair :
  judson_9_4_46_disprove ↔ ¬ judson_9_4_46_prove := Iff.rfl
#print axioms judson_9_4_46_pair

end JudsonGoals
