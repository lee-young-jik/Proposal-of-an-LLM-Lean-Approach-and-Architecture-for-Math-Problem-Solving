import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_10_4_12_certificate :
∀ (G : Type) [Group G] (g : G),
  ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x * g = g * x) ∧
    ((Subgroup.zpowers g).Normal → H.Normal) := by
  intro G _ g
  refine ⟨Subgroup.centralizer {g}, fun x => Subgroup.mem_centralizer_singleton_iff, ?_⟩
  intro hn
  letI := hn
  have he : Subgroup.centralizer (Subgroup.zpowers g : Set G) = Subgroup.centralizer {g} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← he]
  infer_instance

#print axioms JudsonGold.judson_10_4_12_certificate
