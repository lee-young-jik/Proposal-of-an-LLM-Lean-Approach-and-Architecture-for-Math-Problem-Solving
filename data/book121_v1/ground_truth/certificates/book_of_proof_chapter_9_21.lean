import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_21_certificate :
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → ↑p - ↑q ≠ (97 : ℤ) := by
  intro p q hp hq h
  have hpne : p ≠ 2 := by
    intro hp2
    subst p
    have hq2 := hq.two_le
    omega
  rcases hp.odd_of_ne_two hpne with ⟨k,hk⟩
  by_cases hq2 : q = 2
  · subst q
    have hp99 : p = 99 := by omega
    rw [hp99] at hp
    norm_num at hp
  · rcases hq.odd_of_ne_two hq2 with ⟨j,hj⟩
    omega

#print axioms GroundTruth.book_of_proof_chapter_9_21_certificate
