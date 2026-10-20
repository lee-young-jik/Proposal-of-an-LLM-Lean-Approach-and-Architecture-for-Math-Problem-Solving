import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_10_4_14_certificate :
∀ (G : Type) [Group G],
  (commutator G).Normal ∧
  (∀ N : Subgroup G, ∀ _ : N.Normal,
    (∀ a b : G ⧸ N, a * b = b * a) ↔ commutator G ≤ N) := by
  intro G _
  refine ⟨inferInstance, ?_⟩
  intro N hN
  letI := hN
  constructor
  · intro h
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp ⟨h⟩
  · intro h
    exact ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mpr h).comm

#print axioms JudsonGold.judson_10_4_14_certificate
