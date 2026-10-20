import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_11_4_15_prove : Prop :=
∀ (G₁ G₂ : Type) [Group G₁] [Group G₂]
  (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [H₁.Normal] [H₂.Normal]
  (φ : G₁ →* G₂), (∀ x ∈ H₁, φ x ∈ H₂) →
  ∃ ψ : (G₁ ⧸ H₁) →* (G₂ ⧸ H₂),
    ∀ x : G₁, ψ (QuotientGroup.mk' H₁ x) = QuotientGroup.mk' H₂ (φ x)

def judson_11_4_15_disprove : Prop :=
¬ (
∀ (G₁ G₂ : Type) [Group G₁] [Group G₂]
  (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [H₁.Normal] [H₂.Normal]
  (φ : G₁ →* G₂), (∀ x ∈ H₁, φ x ∈ H₂) →
  ∃ ψ : (G₁ ⧸ H₁) →* (G₂ ⧸ H₂),
    ∀ x : G₁, ψ (QuotientGroup.mk' H₁ x) = QuotientGroup.mk' H₂ (φ x)
)

theorem judson_11_4_15_pair :
  judson_11_4_15_disprove ↔ ¬ judson_11_4_15_prove := Iff.rfl
#print axioms judson_11_4_15_pair

end JudsonGoals
