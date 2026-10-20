import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_4_5_33_a_certificate :
∀ (G : Type) [CommGroup G] (H K : Subgroup G),
  Nat.card H = 2 → Nat.card K = 2 → H ≠ K →
  ∃ L : Subgroup G, Nat.card L = 4 := by
  intro G _ H K hH hK hne
  letI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  letI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hi : H ⊓ K = ⊥ := by
    have hd : Nat.card (H ⊓ K : Subgroup G) ∣ 2 := by
      simpa [hH] using Subgroup.card_dvd_of_le (inf_le_left : H ⊓ K ≤ H)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd | hd
    · exact Subgroup.eq_bot_of_card_eq _ hd
    · have hh : H ⊓ K = H := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      have hle : H ≤ K := by rw [← hh]; exact inf_le_right
      exact (hne (Subgroup.eq_of_le_of_card_ge hle (by omega))).elim
  let f : H × K →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := by intros; simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]; ac_rfl }
  have hf : Function.Injective f := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hi)
  refine ⟨f.range, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, hH, hK]

#print axioms JudsonGold.judson_4_5_33_a_certificate
