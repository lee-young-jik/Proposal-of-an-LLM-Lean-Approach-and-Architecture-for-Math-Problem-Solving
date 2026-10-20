import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_39_prove : Prop :=
∀ (G : Type) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
  d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d

def judson_4_5_39_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
  d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d
)

theorem judson_4_5_39_pair :
  judson_4_5_39_disprove ↔ ¬ judson_4_5_39_prove := Iff.rfl
#print axioms judson_4_5_39_pair

end JudsonGoals
