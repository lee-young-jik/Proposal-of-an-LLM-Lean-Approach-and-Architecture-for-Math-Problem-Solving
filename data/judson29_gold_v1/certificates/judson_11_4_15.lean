import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_11_4_15_certificate :
∀ (G₁ G₂ : Type) [Group G₁] [Group G₂]
  (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [H₁.Normal] [H₂.Normal]
  (φ : G₁ →* G₂), (∀ x ∈ H₁, φ x ∈ H₂) →
  ∃ ψ : (G₁ ⧸ H₁) →* (G₂ ⧸ H₂),
    ∀ x : G₁, ψ (QuotientGroup.mk' H₁ x) = QuotientGroup.mk' H₂ (φ x) := by
  intro G₁ G₂ _ _ H₁ H₂ _ _ φ hφ
  let f : G₁ →* G₂ ⧸ H₂ := (QuotientGroup.mk' H₂).comp φ
  have hk : H₁ ≤ f.ker := by
    intro x hx
    change QuotientGroup.mk' H₂ (φ x) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hφ x hx)
  exact ⟨QuotientGroup.lift H₁ f hk, fun x => rfl⟩

#print axioms JudsonGold.judson_11_4_15_certificate
