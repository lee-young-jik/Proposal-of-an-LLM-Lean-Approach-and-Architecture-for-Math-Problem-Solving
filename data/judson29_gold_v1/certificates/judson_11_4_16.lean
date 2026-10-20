import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_11_4_16_certificate :
∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
  H ⊓ K = ⊥ → ∃ L : Subgroup ((G ⧸ H) × (G ⧸ K)), Nonempty (G ≃* L) := by
  intro G _ H K _ _ hi
  let f : G →* (G ⧸ H) × (G ⧸ K) := (QuotientGroup.mk' H).prod (QuotientGroup.mk' K)
  have hk : f.ker = H ⊓ K := by
    ext x
    simp [f, MonoidHom.mem_ker]
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (hk.trans hi)
  exact ⟨f.range, ⟨MonoidHom.ofInjective hinj⟩⟩

#print axioms JudsonGold.judson_11_4_16_certificate
