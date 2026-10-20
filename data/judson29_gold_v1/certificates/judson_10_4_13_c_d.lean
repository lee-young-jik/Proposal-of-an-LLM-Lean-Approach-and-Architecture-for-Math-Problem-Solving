import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_10_4_13_c_d_certificate :
∀ (G : Type) [Group G],
  (Subgroup.center G).Normal ∧
  (IsCyclic (G ⧸ Subgroup.center G) → ∀ a b : G, a * b = b * a) := by
  intro G _
  refine ⟨inferInstance, ?_⟩
  intro hc
  letI := hc
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G)) (by simp)

#print axioms JudsonGold.judson_10_4_13_c_d_certificate
