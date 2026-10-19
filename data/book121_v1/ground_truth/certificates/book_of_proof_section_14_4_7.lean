import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_4_7_certificate :
∀ (α β : Type), (∃ f : α → β, Function.Injective f) →
  (∃ g : α → β, Function.Surjective g) → ∃ h : α → β, Function.Bijective h := by
  classical
  intro α β ⟨f, hf⟩ ⟨g, hg⟩
  let k : β → α := fun y => Classical.choose (hg y)
  have hk : Function.Injective k := by
    intro y z h
    have hy : g (k y) = y := Classical.choose_spec (hg y)
    have hz : g (k z) = z := Classical.choose_spec (hg z)
    rw [h] at hy
    exact hy.symm.trans hz
  exact Function.Embedding.schroeder_bernstein hf hk

#print axioms GroundTruth.book_of_proof_section_14_4_7_certificate
