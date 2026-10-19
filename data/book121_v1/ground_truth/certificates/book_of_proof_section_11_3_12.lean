import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_11_3_12_certificate :
∃ (α : Type) (R : α → α → Prop) (S : α → α → Prop),
  Equivalence R ∧ Equivalence S ∧ ¬Equivalence fun (a b : α) => R a b ∨ S a b := by
  classical
  let R : Fin 3 → Fin 3 → Prop := fun a b => (a = 1 ↔ b = 1)
  let S : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ↔ b = 0)
  refine ⟨Fin 3, R, S, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Iff.rfl
    · intro a b hab
      exact hab.symm
    · intro a b c hab hbc
      exact hab.trans hbc
  · refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Iff.rfl
    · intro a b hab
      exact hab.symm
    · intro a b c hab hbc
      exact hab.trans hbc
  · intro h
    have h02 : R (0 : Fin 3) 2 ∨ S (0 : Fin 3) 2 := by
      left
      simp [R]
    have h21 : R (2 : Fin 3) 1 ∨ S (2 : Fin 3) 1 := by
      right
      simp [S]
    have h01 : R (0 : Fin 3) 1 ∨ S (0 : Fin 3) 1 := h.3 h02 h21
    rcases h01 with hR | hS
    · simp [R] at hR
    · simp [S] at hS

#print axioms GroundTruth.book_of_proof_section_11_3_12_certificate
