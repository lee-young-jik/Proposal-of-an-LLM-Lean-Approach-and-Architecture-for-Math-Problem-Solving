import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_29_certificate :
∀ n : ℕ, 2 < n →
  Even (Nat.card {x : ZMod n | AddSubgroup.zmultiples x = ⊤}) := by
  intro n hn
  classical
  haveI : NeZero n := ⟨by omega⟩
  have he : ∀ x : ZMod n, AddSubgroup.zmultiples x = ⊤ ↔ addOrderOf x = n := by
    intro x
    have hc : Nat.card (ZMod n) = n := by simp
    constructor
    · intro h
      simpa only [hc] using addOrderOf_eq_card_of_zmultiples_eq_top h
    · intro h
      apply (AddSubgroup.card_eq_iff_eq_top (AddSubgroup.zmultiples x)).mp
      simpa only [Nat.card_zmultiples, hc] using h
  have hc : Nat.card {x : ZMod n | AddSubgroup.zmultiples x = ⊤} = n.totient := by
    simp_rw [he]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa using (IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod n) (d := n) (by simp))
  rw [hc]
  exact Nat.totient_even hn

#print axioms JudsonGold.judson_4_5_29_certificate
