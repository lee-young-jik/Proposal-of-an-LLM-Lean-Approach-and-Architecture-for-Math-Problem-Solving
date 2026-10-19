import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_11_3_11_certificate :
∃ (α : Type) (A : Set α) (R : ↑A → ↑A → Prop),
  A.Infinite ∧ Equivalence R ∧ (Set.range fun (a : ↑A) => {b : ↑A | R a b}).Finite := by
  classical
  refine ⟨ℕ, Set.univ, (fun _ _ => True), ?_, ?_, ?_⟩
  · exact Set.infinite_univ
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      trivial
    · intro x y h
      trivial
    · intro x y z hxy hyz
      trivial
  · have heq :
        Set.range (fun a : (Set.univ : Set ℕ) =>
          {b : (Set.univ : Set ℕ) | True}) =
          ({Set.univ} : Set (Set (Set.univ : Set ℕ))) := by
      ext C
      constructor
      · rintro ⟨a, rfl⟩
        simp
      · intro hC
        have hCU : C = (Set.univ : Set (Set.univ : Set ℕ)) := by
          simpa using hC
        subst C
        refine ⟨⟨0, by simp⟩, ?_⟩
        ext b
        simp
    rw [heq]
    exact Set.finite_singleton _

#print axioms GroundTruth.book_of_proof_section_11_3_11_certificate
