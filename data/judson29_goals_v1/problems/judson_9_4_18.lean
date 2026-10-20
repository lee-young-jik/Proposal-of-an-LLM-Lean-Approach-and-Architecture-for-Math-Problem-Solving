import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_9_4_18_prove : Prop :=
let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num);
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num);
  let A := Subgroup.zpowers u;
  let B := Subgroup.zpowers v;
  ∃ H : Subgroup ℚˣ,
    (∀ x : ℚˣ, x ∈ H ↔ ∃ m n : ℤ, x = u ^ m * v ^ n) ∧
    A ≤ H ∧ B ≤ H ∧
    (∀ a : A, ∀ b : B, (a : ℚˣ) * (b : ℚˣ) = (b : ℚˣ) * (a : ℚˣ)) ∧
    (∀ x : H, ∃! p : A × B, (x : ℚˣ) = (p.1 : ℚˣ) * (p.2 : ℚˣ)) ∧
    Nonempty (Multiplicative (ℤ × ℤ) ≃* H)

def judson_9_4_18_disprove : Prop :=
¬ (
let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num);
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num);
  let A := Subgroup.zpowers u;
  let B := Subgroup.zpowers v;
  ∃ H : Subgroup ℚˣ,
    (∀ x : ℚˣ, x ∈ H ↔ ∃ m n : ℤ, x = u ^ m * v ^ n) ∧
    A ≤ H ∧ B ≤ H ∧
    (∀ a : A, ∀ b : B, (a : ℚˣ) * (b : ℚˣ) = (b : ℚˣ) * (a : ℚˣ)) ∧
    (∀ x : H, ∃! p : A × B, (x : ℚˣ) = (p.1 : ℚˣ) * (p.2 : ℚˣ)) ∧
    Nonempty (Multiplicative (ℤ × ℤ) ≃* H)
)

theorem judson_9_4_18_pair :
  judson_9_4_18_disprove ↔ ¬ judson_9_4_18_prove := Iff.rfl
#print axioms judson_9_4_18_pair

end JudsonGoals
