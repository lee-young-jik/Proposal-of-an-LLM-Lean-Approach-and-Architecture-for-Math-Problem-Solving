import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_31_certificate :
∀ (G : Type) [CommGroup G], ∃ H : Subgroup G,
  ∀ g : G, g ∈ H ↔ IsOfFinOrder g := by
  intro G _
  exact ⟨CommGroup.torsion G, fun _ => Iff.rfl⟩

#print axioms JudsonGold.judson_4_5_31_certificate
