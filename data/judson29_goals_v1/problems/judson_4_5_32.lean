import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_32_prove : Prop :=
∀ (G : Type) [Group G] [Finite G] (x : G),
  Subgroup.zpowers x = ⊤ → ∀ k : ℕ, Nat.Coprime k (Nat.card G) →
  Subgroup.zpowers (x ^ k) = ⊤

def judson_4_5_32_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G] (x : G),
  Subgroup.zpowers x = ⊤ → ∀ k : ℕ, Nat.Coprime k (Nat.card G) →
  Subgroup.zpowers (x ^ k) = ⊤
)

theorem judson_4_5_32_pair :
  judson_4_5_32_disprove ↔ ¬ judson_4_5_32_prove := Iff.rfl
#print axioms judson_4_5_32_pair

end JudsonGoals
