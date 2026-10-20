import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_3_5_38_prove : Prop :=
(∀ n : ℕ, ∃ H : AddSubgroup ℤ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) ∧
  (∀ H : AddSubgroup ℤ, ∃ n : ℕ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k)

def judson_3_5_38_disprove : Prop :=
¬ (
(∀ n : ℕ, ∃ H : AddSubgroup ℤ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) ∧
  (∀ H : AddSubgroup ℤ, ∃ n : ℕ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k)
)

theorem judson_3_5_38_pair :
  judson_3_5_38_disprove ↔ ¬ judson_3_5_38_prove := Iff.rfl
#print axioms judson_3_5_38_pair

end JudsonGoals
