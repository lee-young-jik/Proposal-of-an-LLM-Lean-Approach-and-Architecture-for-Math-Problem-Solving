import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_11_2_15_certificate :
∃ (α : Type) (R : α → α → Prop), Symmetric R ∧ Transitive R ∧ ¬Reflexive R := by
  refine ⟨Fin 1, (fun _ _ => False), ?_, ?_, ?_⟩
  · intro a b h; exact h.elim
  · intro a b c h; exact h.elim
  · intro h; exact h 0

#print axioms GroundTruth.book_of_proof_section_11_2_15_certificate
