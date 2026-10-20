import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_11_4_12_prove : Prop :=
∀ (G : Type) [Group G] (H : Subgroup G) (k : ℕ),
  0 < k → Nat.card H = k →
  (∀ K : Subgroup G, Nat.card K = k → K = H) → H.Normal

def judson_11_4_12_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (H : Subgroup G) (k : ℕ),
  0 < k → Nat.card H = k →
  (∀ K : Subgroup G, Nat.card K = k → K = H) → H.Normal
)

theorem judson_11_4_12_pair :
  judson_11_4_12_disprove ↔ ¬ judson_11_4_12_prove := Iff.rfl
#print axioms judson_11_4_12_pair

end JudsonGoals
