import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_22_prove : Prop :=
∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
  Nat.card G = 20 → Nat.card H = 4 → Nat.card K = 5 →
  (∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G)) →
  ∀ g : G, ∃! p : H × K, g = (p.1 : G) * (p.2 : G)

def judson_9_4_22_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
  Nat.card G = 20 → Nat.card H = 4 → Nat.card K = 5 →
  (∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G)) →
  ∀ g : G, ∃! p : H × K, g = (p.1 : G) * (p.2 : G)
)

theorem judson_9_4_22_pair :
  judson_9_4_22_disprove ↔ ¬ judson_9_4_22_prove := Iff.rfl
#print axioms judson_9_4_22_pair

end JudsonGoals
