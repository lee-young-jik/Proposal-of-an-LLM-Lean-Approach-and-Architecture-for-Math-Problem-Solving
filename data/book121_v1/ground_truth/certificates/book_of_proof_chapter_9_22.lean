import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_22_certificate :
∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p < q → Odd (2*p + q^2) := by
  intro p q hp hq hpq
  have hqne : q ≠ 2 := by
    intro hq2
    subst q
    have hp2 := hp.two_le
    omega
  rcases hq.odd_of_ne_two hqne with ⟨k,hk⟩
  refine ⟨p+2*k*k+2*k, ?_⟩
  rw [hk]
  ring

#print axioms GroundTruth.book_of_proof_chapter_9_22_certificate
