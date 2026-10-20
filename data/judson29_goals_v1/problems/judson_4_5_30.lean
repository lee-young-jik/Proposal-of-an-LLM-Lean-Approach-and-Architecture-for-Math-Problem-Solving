import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_30_prove : Prop :=
∀ (G : Type) [Group G] (a b : G) (m n : ℕ),
  orderOf a = m → orderOf b = n → 0 < m → 0 < n →
  Nat.Coprime m n → Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥

def judson_4_5_30_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (a b : G) (m n : ℕ),
  orderOf a = m → orderOf b = n → 0 < m → 0 < n →
  Nat.Coprime m n → Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥
)

theorem judson_4_5_30_pair :
  judson_4_5_30_disprove ↔ ¬ judson_4_5_30_prove := Iff.rfl
#print axioms judson_4_5_30_pair

end JudsonGoals
