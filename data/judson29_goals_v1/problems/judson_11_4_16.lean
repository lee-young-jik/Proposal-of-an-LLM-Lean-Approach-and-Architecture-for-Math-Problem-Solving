import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_11_4_16_prove : Prop :=
∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
  H ⊓ K = ⊥ → ∃ L : Subgroup ((G ⧸ H) × (G ⧸ K)), Nonempty (G ≃* L)

def judson_11_4_16_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
  H ⊓ K = ⊥ → ∃ L : Subgroup ((G ⧸ H) × (G ⧸ K)), Nonempty (G ≃* L)
)

theorem judson_11_4_16_pair :
  judson_11_4_16_disprove ↔ ¬ judson_11_4_16_prove := Iff.rfl
#print axioms judson_11_4_16_pair

end JudsonGoals
