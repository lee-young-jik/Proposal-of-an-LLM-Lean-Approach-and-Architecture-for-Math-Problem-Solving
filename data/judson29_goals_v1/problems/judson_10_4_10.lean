import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_10_4_10_prove : Prop :=
(∀ (G : Type) [Group G] (H : Subgroup G), H.index = 2 → H.Normal) ∧
  (∀ n : ℕ, 3 ≤ n → ¬ IsSimpleGroup (Equiv.Perm (Fin n)))

def judson_10_4_10_disprove : Prop :=
¬ (
(∀ (G : Type) [Group G] (H : Subgroup G), H.index = 2 → H.Normal) ∧
  (∀ n : ℕ, 3 ≤ n → ¬ IsSimpleGroup (Equiv.Perm (Fin n)))
)

theorem judson_10_4_10_pair :
  judson_10_4_10_disprove ↔ ¬ judson_10_4_10_prove := Iff.rfl
#print axioms judson_10_4_10_pair

end JudsonGoals
