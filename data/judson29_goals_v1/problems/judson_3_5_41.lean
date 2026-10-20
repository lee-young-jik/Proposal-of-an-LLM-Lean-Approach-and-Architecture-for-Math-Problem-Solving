import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_3_5_41_prove : Prop :=
∃ H : Subgroup ℝˣ, ∀ x : ℝˣ,
  x ∈ H ↔ ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    (x : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 2

def judson_3_5_41_disprove : Prop :=
¬ (
∃ H : Subgroup ℝˣ, ∀ x : ℝˣ,
  x ∈ H ↔ ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    (x : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 2
)

theorem judson_3_5_41_pair :
  judson_3_5_41_disprove ↔ ¬ judson_3_5_41_prove := Iff.rfl
#print axioms judson_3_5_41_pair

end JudsonGoals
