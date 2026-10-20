import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_4_5_26_prove : Prop :=
∀ p : ℕ, Nat.Prime p →
  ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤

def judson_4_5_26_disprove : Prop :=
¬ (
∀ p : ℕ, Nat.Prime p →
  ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤
)

theorem judson_4_5_26_pair :
  judson_4_5_26_disprove ↔ ¬ judson_4_5_26_prove := Iff.rfl
#print axioms judson_4_5_26_pair

end JudsonGoals
