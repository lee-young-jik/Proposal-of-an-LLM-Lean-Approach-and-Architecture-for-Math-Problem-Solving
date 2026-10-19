import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_12_6_6_certificate :
∃ (α : Type) (β : Type) (f : α → β) (Y : Set β), f '' (f ⁻¹' Y) ≠ Y := by
  refine ⟨Fin 1, Fin 2, (fun _ => 0), Set.univ, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 2) => (1 : Fin 2) ∈ S) h
  norm_num at hh

#print axioms GroundTruth.book_of_proof_section_12_6_6_certificate
