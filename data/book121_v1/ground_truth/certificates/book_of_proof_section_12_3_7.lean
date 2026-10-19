import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_12_3_7_certificate :
∀ (n : ℕ) (X : Finset ℕ), (∀ x ∈ X, 1 ≤ x ∧ x ≤ 2*n) →
  n < X.card → ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ x ∣ y := by
  classical
  intro n X hX hcard
  have hex : ∀ x : ℕ, ∃ e m : ℕ, x ≠ 0 → Odd m ∧ x = 2^e*m := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, 1, fun h => False.elim (h hx)⟩
    · obtain ⟨e,m,hm,he⟩ := Nat.exists_eq_two_pow_mul_odd hx
      exact ⟨e,m,fun _ => ⟨hm,he⟩⟩
  choose e m hm using hex
  have hbound : ∀ x ∈ X, m x / 2 < n := by
    intro x hx
    have hxpos := (hX x hx).1
    have hxm := hm x (by omega)
    have hp : 1 ≤ 2^(e x) := Nat.succ_le_iff.mpr (by positivity)
    have hmul : m x ≤ 2^(e x)*m x := by nlinarith
    have hle : m x ≤ 2*n := by have := (hX x hx).2; omega
    obtain ⟨k,hk⟩ := hxm.1
    omega
  obtain ⟨x,hx,y,hy,hne,heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := X) (t := Finset.range n) (f := fun x => m x / 2)
    (by simpa using hcard) (by intro x hx; exact Finset.mem_range.mpr (hbound x hx))
  have hxpos := (hX x hx).1
  have hypos := (hX y hy).1
  have hxm := hm x (by omega)
  have hym := hm y (by omega)
  have hmxy : m x = m y := by
    obtain ⟨a,ha⟩ := hxm.1
    obtain ⟨b,hb⟩ := hym.1
    omega
  by_cases he : e x ≤ e y
  · refine ⟨x,hx,y,hy,hne,?_⟩
    rw [hxm.2, hym.2, ← hmxy]
    exact mul_dvd_mul (pow_dvd_pow 2 he) (dvd_refl (m x))
  · refine ⟨y,hy,x,hx,hne.symm,?_⟩
    rw [hxm.2, hym.2, hmxy]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega : e y ≤ e x)) (dvd_refl (m y))

#print axioms GroundTruth.book_of_proof_section_12_3_7_certificate
