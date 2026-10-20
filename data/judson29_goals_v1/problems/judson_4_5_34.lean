import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_34_prove : Prop :=
∀ (G : Type) [CommGroup G] [Finite G] (p q : ℕ),
  Nat.card G = p * q → Nat.Coprime p q →
  (∃ a : G, orderOf a = p) → (∃ b : G, orderOf b = q) → IsCyclic G

def judson_4_5_34_disprove : Prop :=
¬ (
∀ (G : Type) [CommGroup G] [Finite G] (p q : ℕ),
  Nat.card G = p * q → Nat.Coprime p q →
  (∃ a : G, orderOf a = p) → (∃ b : G, orderOf b = q) → IsCyclic G
)

theorem judson_4_5_34_pair :
  judson_4_5_34_disprove ↔ ¬ judson_4_5_34_prove := Iff.rfl
#print axioms judson_4_5_34_pair

end JudsonGoals
