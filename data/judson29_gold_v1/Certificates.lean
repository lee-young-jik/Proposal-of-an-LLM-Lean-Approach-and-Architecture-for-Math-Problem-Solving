import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_3_5_26_certificate :
∀ n : ℕ, 2 < n → ∃ k : (ZMod n)ˣ, k ^ 2 = 1 ∧ k ≠ 1 := by
  intro n hn
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨-1, by simp, ?_⟩
  intro h
  have hh : (-1 : ZMod n) = 1 := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) h
  have hh2 : (2 : ZMod n) = 0 := by linear_combination -hh
  have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp hh2
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

#print axioms JudsonGold.judson_3_5_26_certificate

theorem JudsonGold.judson_3_5_32_certificate :
∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) →
  ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1 := by
  intro G _ _ he
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.mp he)
  refine ⟨a, ?_, ?_⟩
  · intro h
    simp [h] at ha
  · simpa [ha] using pow_orderOf_eq_one a

#print axioms JudsonGold.judson_3_5_32_certificate

theorem JudsonGold.judson_3_5_38_certificate :
(∀ n : ℕ, ∃ H : AddSubgroup ℤ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) ∧
  (∀ H : AddSubgroup ℤ, ∃ n : ℕ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) := by
  constructor
  · intro n
    refine ⟨AddSubgroup.zmultiples (n : ℤ), ?_⟩
    intro z
    simp [Int.mem_zmultiples_iff, dvd_def]
  · intro H
    obtain ⟨n, hn⟩ := (AddSubgroup.le_zmultiples_iff (1 : ℤ) H).mp (by simp)
    refine ⟨n, ?_⟩
    intro z
    simp only [nsmul_eq_mul, mul_one] at hn
    rw [hn]
    simp [Int.mem_zmultiples_iff, dvd_def]

#print axioms JudsonGold.judson_3_5_38_certificate

theorem JudsonGold.judson_3_5_41_certificate :
∃ H : Subgroup ℝˣ, ∀ x : ℝˣ,
  x ∈ H ↔ ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    (x : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
  let s : ℝ := Real.sqrt 2
  have hs : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : ∀ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) → (a : ℝ) + (b : ℝ) * s ≠ 0 := by
    intro a b hab he
    by_cases hb : b = 0
    · have ha : a = 0 := by exact_mod_cast (by simpa [hb] using he : (a : ℝ) = 0)
      exact hab.elim (fun h => h ha) (fun h => h hb)
    · have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have hrat : s = ((-a / b : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hb').mpr
        linarith
      exact irrational_sqrt_two.ne_rat (-a / b) hrat
  let H : Subgroup ℝˣ :=
    { carrier := {x | ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧ (x : ℝ) = (a : ℝ) + (b : ℝ) * s}
      one_mem' := by refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩; simp
      mul_mem' := by
        rintro x y ⟨a,b,hab,hx⟩ ⟨c,e,hce,hy⟩
        have hv : (x * y : ℝˣ) = x * y := rfl
        have hrep : ((x*y : ℝˣ) : ℝ) = ((a*c+2*b*e : ℚ) : ℝ) + ((a*e+b*c : ℚ) : ℝ)*s := by
          simp only [Units.val_mul, hx, hy]
          push_cast
          ring_nf
          rw [hs]
          ring
        refine ⟨a*c+2*b*e, a*e+b*c, ?_, hrep⟩
        by_contra h
        push_neg at h
        have hz : ((x*y : ℝˣ) : ℝ) = 0 := by rw [hrep,h.1,h.2]; simp
        exact Units.ne_zero (x*y) hz
      inv_mem' := by
        rintro x ⟨a,b,hab,hx⟩
        let δ : ℚ := a^2 - 2*b^2
        have hδ : δ ≠ 0 := by
          intro hz
          have he : ((a : ℝ)+(b : ℝ)*s)*((a : ℝ)-(b : ℝ)*s) = (δ : ℝ) := by
            dsimp [δ]
            push_cast
            ring_nf
            rw [hs]
          have hz' : (δ : ℝ) = 0 := by exact_mod_cast hz
          have hb : a ≠ 0 ∨ -b ≠ 0 := by simpa using hab
          have hnon := mul_ne_zero (hn a b hab) (by simpa [sub_eq_add_neg] using hn a (-b) hb)
          exact hnon (he.trans hz')
        have hδ' : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
        refine ⟨a/δ, -b/δ, ?_, ?_⟩
        · rcases hab with ha | hb
          · exact Or.inl (div_ne_zero ha hδ)
          · exact Or.inr (div_ne_zero (neg_ne_zero.mpr hb) hδ)
        · rw [Units.val_inv_eq_inv_val]
          rw [hx]
          push_cast
          field_simp [hδ', hn a b hab]
          dsimp [δ]
          push_cast
          ring_nf
          rw [hs] }
  exact ⟨H, fun _ => Iff.rfl⟩

#print axioms JudsonGold.judson_3_5_41_certificate

theorem JudsonGold.judson_4_5_14_certificate :
let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0];
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1];
  IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B) := by
  dsimp only
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1]
  change IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B)
  refine ⟨?_, ?_, ?_⟩
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨4, by decide, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, pow_succ, Matrix.mul_fin_two]
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B, pow_succ, Matrix.mul_fin_two]
  · intro h
    have hp : ∀ n : ℕ, (A * B) ^ n = !![1, -(n : ℝ); 0, 1] := by
      intro n
      induction n with
      | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num
      | succ n ih =>
        rw [pow_succ, ih]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_fin_two, Nat.cast_add] <;> ring
    obtain ⟨n, hn, he⟩ := h.exists_pow_eq_one
    have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
    rw [hp] at hx
    simp at hx
    exact (Nat.ne_of_gt hn) (by exact_mod_cast hx)

#print axioms JudsonGold.judson_4_5_14_certificate

theorem JudsonGold.judson_4_5_26_certificate :
∀ p : ℕ, Nat.Prime p →
  ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤ := by
  intro p hp H
  haveI : Fact p.Prime := ⟨hp⟩
  exact eq_bot_or_eq_top H

#print axioms JudsonGold.judson_4_5_26_certificate

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

theorem JudsonGold.judson_4_5_30_certificate :
∀ (G : Type) [Group G] (a b : G) (m n : ℕ),
  orderOf a = m → orderOf b = n → 0 < m → 0 < n →
  Nat.Coprime m n → Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  intro G _ a b m n ha hb hm hn hc
  apply le_antisymm
  · intro x hx
    have hxa : orderOf x ∣ m := by
      rw [← ha]
      exact orderOf_dvd_of_mem_zpowers hx.1
    have hxb : orderOf x ∣ n := by
      rw [← hb]
      exact orderOf_dvd_of_mem_zpowers hx.2
    have hx1 : orderOf x ∣ 1 := by simpa [hc.gcd_eq_one] using Nat.dvd_gcd hxa hxb
    simpa using orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hx1)
  · exact bot_le

#print axioms JudsonGold.judson_4_5_30_certificate

theorem JudsonGold.judson_4_5_31_certificate :
∀ (G : Type) [CommGroup G], ∃ H : Subgroup G,
  ∀ g : G, g ∈ H ↔ IsOfFinOrder g := by
  intro G _
  exact ⟨CommGroup.torsion G, fun _ => Iff.rfl⟩

#print axioms JudsonGold.judson_4_5_31_certificate

theorem JudsonGold.judson_4_5_32_certificate :
∀ (G : Type) [Group G] [Finite G] (x : G),
  Subgroup.zpowers x = ⊤ → ∀ k : ℕ, Nat.Coprime k (Nat.card G) →
  Subgroup.zpowers (x ^ k) = ⊤ := by
  intro G _ _ x hx k hk
  have ho : orderOf x = Nat.card G := by
    exact orderOf_eq_card_of_forall_mem_zpowers (fun g => by rw [hx]; trivial)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := x) (by simpa [ho] using hk)
  apply le_antisymm le_top
  rw [← hx]
  apply Subgroup.zpowers_le.mpr
  have hmem : (x ^ k) ^ m ∈ Subgroup.zpowers (x ^ k) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m
  simpa only [hm] using hmem

#print axioms JudsonGold.judson_4_5_32_certificate

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

theorem JudsonGold.judson_4_5_34_certificate :
∀ (G : Type) [CommGroup G] [Finite G] (p q : ℕ),
  Nat.card G = p * q → Nat.Coprime p q →
  (∃ a : G, orderOf a = p) → (∃ b : G, orderOf b = q) → IsCyclic G := by
  intro G _ _ p q hcard hc ha hb
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  apply isCyclic_of_orderOf_eq_card (a * b)
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all a b)]
  · simpa [ha, hb] using hcard.symm
  · simpa [ha, hb] using hc

#print axioms JudsonGold.judson_4_5_34_certificate

theorem JudsonGold.judson_4_5_39_certificate :
∀ (G : Type) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
  d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d := by
  intro G _ _ _ d hd
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine ⟨Subgroup.zpowers (x ^ (orderOf x / d)), ?_⟩
  rw [Nat.card_zpowers]
  apply orderOf_pow_orderOf_div
  · rw [hx]
    exact Nat.card_pos.ne'
  · simpa [hx] using hd

#print axioms JudsonGold.judson_4_5_39_certificate

theorem JudsonGold.judson_4_5_44_certificate :
∀ (α : Circle) (m n : ℤ),
  (α ^ m = 1 ∧ α ^ n = 1) ↔ α ^ (Int.gcd m n : ℤ) = 1 := by
  intro a m n
  constructor
  · rintro ⟨hm, hn⟩
    rw [Int.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, hm, hn]
    simp
  · intro h
    constructor
    · obtain ⟨k, hk⟩ := Int.gcd_dvd_left m n
      rw [hk, zpow_mul, h]
      simp
    · obtain ⟨k, hk⟩ := Int.gcd_dvd_right m n
      rw [hk, zpow_mul, h]
      simp

#print axioms JudsonGold.judson_4_5_44_certificate

theorem JudsonGold.judson_4_5_45_certificate :
∀ z : ℂˣ, ‖(z : ℂ)‖ ≠ 1 → orderOf z = 0 := by
  intro z hz
  apply orderOf_eq_zero_iff.mpr
  intro h
  apply hz
  apply Complex.norm_eq_one_of_pow_eq_one (n := orderOf z)
  · simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg (fun w : ℂˣ => (w : ℂ)) (pow_orderOf_eq_one z)
  · exact h.orderOf_pos.ne'

#print axioms JudsonGold.judson_4_5_45_certificate

theorem JudsonGold.judson_9_4_1_certificate :
∀ n : ℤ, n ≠ 0 →
  Nonempty (ℤ ≃+ AddSubgroup.zmultiples n) := by
  intro n hn
  let f : ℤ →+ ℤ := zmultiplesHom ℤ n
  have hi : Function.Injective f := by
    intro a b h
    change a * n = b * n at h
    exact mul_right_cancel₀ hn h
  exact ⟨AddMonoidHom.ofInjective hi⟩

#print axioms JudsonGold.judson_9_4_1_certificate

theorem JudsonGold.judson_9_4_2_certificate :
∃ H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  (∀ M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
    M ∈ H ↔ ∃ a b : ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a]) ∧
  Nonempty (ℂˣ ≃* H) := by
  let ρ : ℂ →+* Matrix (Fin 2) (Fin 2) ℝ :=
    { toFun := fun z => !![z.re, z.im; -z.im, z.re]
      map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
      map_mul' := by
        intro z w
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two, Complex.mul_re, Complex.mul_im] <;> ring
      map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
      map_add' := by intro z w; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring }
  let f : ℂˣ →* (Matrix (Fin 2) (Fin 2) ℝ)ˣ := Units.map ρ.toMonoidHom
  have hf : Function.Injective f := by
    intro z w h
    have hh := congrArg (fun x : (Matrix (Fin 2) (Fin 2) ℝ)ˣ => (x : Matrix (Fin 2) (Fin 2) ℝ)) h
    apply Units.ext
    apply Complex.ext
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hh
    · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hh
  refine ⟨f.range, ?_, ⟨MonoidHom.ofInjective hf⟩⟩
  intro M
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z : ℂ).re, (z : ℂ).im, rfl⟩
  · rintro ⟨a, b, hm⟩
    let z : ℂ := ⟨a, b⟩
    have hz : z ≠ 0 := by
      intro h
      have ha : a = 0 := congrArg Complex.re h
      have hb : b = 0 := congrArg Complex.im h
      apply Units.ne_zero M
      rw [hm, ha, hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    refine ⟨Units.mk0 z hz, ?_⟩
    apply Units.ext
    change ρ z = (M : Matrix (Fin 2) (Fin 2) ℝ)
    exact hm.symm

#print axioms JudsonGold.judson_9_4_2_certificate

theorem JudsonGold.judson_9_4_8_certificate :
¬ Nonempty (ℚ ≃+ ℤ) := by
  rintro ⟨e⟩
  let q : ℚ := e.symm 1 / 2
  have hh : (2 : ℤ) * e q = 1 := by
    calc
      2 * e q = e q + e q := by ring
      _ = e (q + q) := (e.map_add q q).symm
      _ = e (e.symm 1) := by congr 1; dsimp [q]; ring
      _ = 1 := e.apply_symm_apply 1
  omega

#print axioms JudsonGold.judson_9_4_8_certificate

theorem JudsonGold.judson_9_4_18_certificate :
let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num);
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num);
  let A := Subgroup.zpowers u;
  let B := Subgroup.zpowers v;
  ∃ H : Subgroup ℚˣ,
    (∀ x : ℚˣ, x ∈ H ↔ ∃ m n : ℤ, x = u ^ m * v ^ n) ∧
    A ≤ H ∧ B ≤ H ∧
    (∀ a : A, ∀ b : B, (a : ℚˣ) * (b : ℚˣ) = (b : ℚˣ) * (a : ℚˣ)) ∧
    (∀ x : H, ∃! p : A × B, (x : ℚˣ) = (p.1 : ℚˣ) * (p.2 : ℚˣ)) ∧
    Nonempty (Multiplicative (ℤ × ℤ) ≃* H) := by
  dsimp only
  let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num)
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num)
  let A := Subgroup.zpowers u
  let B := Subgroup.zpowers v
  change ∃ H : Subgroup ℚˣ, _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), q ≠ 0 → ∀ k : ℤ,
      padicValRat p (q ^ k) = k * padicValRat p q := by
    intro p hp q hq k
    rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩
    · simp [zpow_natCast, padicValRat.pow hq]
    · simp [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow hq]
  have h22 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide)
  have h33 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  have h23 : padicValRat 2 (3 : ℚ) = 0 := by
    change padicValRat 2 ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes (by decide)]
    rfl
  have h32 : padicValRat 3 (2 : ℚ) = 0 := by
    change padicValRat 3 ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes (by decide)]
    rfl
  have hvp : ∀ (p : ℕ) [Fact p.Prime] (m n : ℤ),
      padicValRat p ((2 : ℚ)^m * (3 : ℚ)^n) = m * padicValRat p 2 + n * padicValRat p 3 := by
    intro p hp m n
    rw [padicValRat.mul (zpow_ne_zero m (by norm_num)) (zpow_ne_zero n (by norm_num)), hv, hv] <;> norm_num
  let f : Multiplicative (ℤ × ℤ) →* ℚˣ :=
    { toFun := fun p => u ^ p.toAdd.1 * v ^ p.toAdd.2
      map_one' := by simp
      map_mul' := by
        intro p q
        change u ^ (p.toAdd.1 + q.toAdd.1) * v ^ (p.toAdd.2 + q.toAdd.2) = _
        simp only [zpow_add]
        ac_rfl }
  have hf : Function.Injective f := by
    intro p q h
    have he : (2 : ℚ)^p.toAdd.1 * (3 : ℚ)^p.toAdd.2 =
        (2 : ℚ)^q.toAdd.1 * (3 : ℚ)^q.toAdd.2 := by
      have he := congrArg (fun w : ℚˣ => (w : ℚ)) h
      change ((u ^ p.toAdd.1 * v ^ p.toAdd.2 : ℚˣ) : ℚ) = ((u ^ q.toAdd.1 * v ^ q.toAdd.2 : ℚˣ) : ℚ) at he
      simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, u, v, Units.val_mk0] using he
    have h2 := congrArg (padicValRat 2) he
    have h3 := congrArg (padicValRat 3) he
    simp only [hvp, h22, h23, h32, h33, mul_one, mul_zero, zero_add, add_zero] at h2 h3
    exact Prod.ext h2 h3
  refine ⟨f.range, ?_, ?_, ?_, ?_, ?_, ⟨MonoidHom.ofInjective hf⟩⟩
  · intro x
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.toAdd.1, p.toAdd.2, hp.symm⟩
    · rintro ⟨m,n,hx⟩
      exact ⟨Multiplicative.ofAdd (m,n), hx.symm⟩
  · intro x hx
    obtain ⟨m,hm⟩ := hx
    refine ⟨Multiplicative.ofAdd (m,0), ?_⟩
    change u ^ m * v ^ (0 : ℤ) = x
    simpa only [zpow_zero, mul_one] using hm
  · intro x hx
    obtain ⟨n,hn⟩ := hx
    refine ⟨Multiplicative.ofAdd (0,n), ?_⟩
    change u ^ (0 : ℤ) * v ^ n = x
    simpa only [zpow_zero, one_mul] using hn
  · intros
    exact mul_comm _ _
  · intro x
    obtain ⟨p,hp⟩ := x.property
    let a : A := ⟨u ^ p.toAdd.1, Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _⟩
    let b : B := ⟨v ^ p.toAdd.2, Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _⟩
    refine ⟨(a,b), hp.symm, ?_⟩
    intro q hq
    obtain ⟨m,hm⟩ := q.1.property
    obtain ⟨n,hn⟩ := q.2.property
    change u ^ m = (q.1 : ℚˣ) at hm
    change v ^ n = (q.2 : ℚˣ) at hn
    have hh : f (Multiplicative.ofAdd (m,n)) = f p := by
      change u ^ m * v ^ n = f p
      rw [hm,hn,hp]
      exact hq.symm
    have hc := hf hh
    apply Prod.ext
    · apply Subtype.ext
      change (q.1 : ℚˣ) = u ^ p.toAdd.1
      rw [← hm]
      exact congrArg (fun m : ℤ => u ^ m) (congrArg (fun t : Multiplicative (ℤ × ℤ) => t.toAdd.1) hc)
    · apply Subtype.ext
      change (q.2 : ℚˣ) = v ^ p.toAdd.2
      rw [← hn]
      exact congrArg (fun n : ℤ => v ^ n) (congrArg (fun t : Multiplicative (ℤ × ℤ) => t.toAdd.2) hc)

#print axioms JudsonGold.judson_9_4_18_certificate

theorem JudsonGold.judson_9_4_22_certificate :
∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
  Nat.card G = 20 → Nat.card H = 4 → Nat.card K = 5 →
  (∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G)) →
  ∀ g : G, ∃! p : H × K, g = (p.1 : G) * (p.2 : G) := by
  intro G _ _ H K hG hH hK hcomm g
  have hc : Subgroup.IsComplement' H K := Subgroup.isComplement'_of_coprime
    (by rw [hH, hK, hG]) (by rw [hH, hK]; decide)
  simpa only [eq_comm] using hc.existsUnique g

#print axioms JudsonGold.judson_9_4_22_certificate

theorem JudsonGold.judson_9_4_36_certificate :
∀ B : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  ∃ f : Matrix.SpecialLinearGroup (Fin 2) ℝ ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ((f A) : Matrix (Fin 2) (Fin 2) ℝ) =
        (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
        (A : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro B
  let C : Matrix (Fin 2) (Fin 2) ℝ := B
  let D : Matrix (Fin 2) (Fin 2) ℝ := ↑(B⁻¹)
  have hCD : C * D = 1 := B.val_inv
  have hDC : D * C = 1 := B.inv_val
  let f : Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun A => ⟨D * (A : Matrix (Fin 2) (Fin 2) ℝ) * C, by
      change Matrix.det ((↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (↑B : Matrix (Fin 2) (Fin 2) ℝ)) = 1
      rw [Matrix.det_units_conj']
      exact A.property⟩
  let g : Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun A => ⟨C * (A : Matrix (Fin 2) (Fin 2) ℝ) * D, by
      change Matrix.det ((↑B : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ)) = 1
      rw [Matrix.det_units_conj]
      exact A.property⟩
  refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · intro A
    apply Subtype.ext
    change C * (D * (A : Matrix (Fin 2) (Fin 2) ℝ) * C) * D = _
    calc
      _ = (C * D) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (C * D) := by noncomm_ring
      _ = (A : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hCD]; simp
  · intro A
    apply Subtype.ext
    change D * (C * (A : Matrix (Fin 2) (Fin 2) ℝ) * D) * C = _
    calc
      _ = (D * C) * (A : Matrix (Fin 2) (Fin 2) ℝ) * (D * C) := by noncomm_ring
      _ = (A : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hDC]; simp
  · intro A E
    apply Subtype.ext
    change D * ((A : Matrix (Fin 2) (Fin 2) ℝ) * (E : Matrix (Fin 2) (Fin 2) ℝ)) * C = (D * (A : Matrix (Fin 2) (Fin 2) ℝ) * C) * (D * (E : Matrix (Fin 2) (Fin 2) ℝ) * C)
    calc
      _ = D * (A : Matrix (Fin 2) (Fin 2) ℝ) * (C * D) * (E : Matrix (Fin 2) (Fin 2) ℝ) * C := by rw [hCD]; simp [mul_assoc]
      _ = _ := by noncomm_ring

#print axioms JudsonGold.judson_9_4_36_certificate

theorem JudsonGold.judson_9_4_46_certificate :
∀ (G H : Type) [Group G] [Group H], Nonempty (G ≃* H) →
  ∀ n : ℕ, 0 < n → (∃ K : Subgroup G, Nat.card K = n) →
    ∃ L : Subgroup H, Nat.card L = n := by
  intro G H _ _ he n hn hk
  obtain ⟨e⟩ := he
  obtain ⟨K, hK⟩ := hk
  refine ⟨K.map e.toMonoidHom, ?_⟩
  rw [← hK]
  exact Nat.card_congr (e.subgroupMap K).toEquiv.symm

#print axioms JudsonGold.judson_9_4_46_certificate

theorem JudsonGold.judson_10_4_10_certificate :
(∀ (G : Type) [Group G] (H : Subgroup G), H.index = 2 → H.Normal) ∧
  (∀ n : ℕ, 3 ≤ n → ¬ IsSimpleGroup (Equiv.Perm (Fin n))) := by
  constructor
  · intro G _ H h
    exact H.normal_of_index_eq_two h
  · intro n hn hs
    letI := hs
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    let A := alternatingGroup (Fin n)
    have hi : A.index = 2 := alternatingGroup.index_eq_two
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A inferInstance with ha | ha
    · have hc := two_mul_nat_card_alternatingGroup (α := Fin n)
      have hf : 6 ≤ n.factorial := by simpa using Nat.factorial_le hn
      have hca : Nat.card A = 1 := by simp [ha]
      change 2 * Nat.card A = _ at hc
      rw [hca] at hc
      simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
      omega
    · simp [ha] at hi

#print axioms JudsonGold.judson_10_4_10_certificate

theorem JudsonGold.judson_10_4_12_certificate :
∀ (G : Type) [Group G] (g : G),
  ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x * g = g * x) ∧
    ((Subgroup.zpowers g).Normal → H.Normal) := by
  intro G _ g
  refine ⟨Subgroup.centralizer {g}, fun x => Subgroup.mem_centralizer_singleton_iff, ?_⟩
  intro hn
  letI := hn
  have he : Subgroup.centralizer (Subgroup.zpowers g : Set G) = Subgroup.centralizer {g} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← he]
  infer_instance

#print axioms JudsonGold.judson_10_4_12_certificate

theorem JudsonGold.judson_10_4_13_c_d_certificate :
∀ (G : Type) [Group G],
  (Subgroup.center G).Normal ∧
  (IsCyclic (G ⧸ Subgroup.center G) → ∀ a b : G, a * b = b * a) := by
  intro G _
  refine ⟨inferInstance, ?_⟩
  intro hc
  letI := hc
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G)) (by simp)

#print axioms JudsonGold.judson_10_4_13_c_d_certificate

theorem JudsonGold.judson_10_4_14_certificate :
∀ (G : Type) [Group G],
  (commutator G).Normal ∧
  (∀ N : Subgroup G, ∀ _ : N.Normal,
    (∀ a b : G ⧸ N, a * b = b * a) ↔ commutator G ≤ N) := by
  intro G _
  refine ⟨inferInstance, ?_⟩
  intro N hN
  letI := hN
  constructor
  · intro h
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp ⟨h⟩
  · intro h
    exact ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mpr h).comm

#print axioms JudsonGold.judson_10_4_14_certificate

theorem JudsonGold.judson_11_4_12_certificate :
∀ (G : Type) [Group G] (H : Subgroup G) (k : ℕ),
  0 < k → Nat.card H = k →
  (∀ K : Subgroup G, Nat.card K = k → K = H) → H.Normal := by
  intro G _ H k hk hcard huniq
  constructor
  intro x hx g
  let e := MulAut.conj g
  have hm : H.map e.toMonoidHom = H := by
    apply huniq
    rw [← hcard]
    exact Nat.card_congr (e.subgroupMap H).toEquiv.symm
  rw [← hm]
  exact ⟨x, hx, rfl⟩

#print axioms JudsonGold.judson_11_4_12_certificate

theorem JudsonGold.judson_11_4_15_certificate :
∀ (G₁ G₂ : Type) [Group G₁] [Group G₂]
  (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [H₁.Normal] [H₂.Normal]
  (φ : G₁ →* G₂), (∀ x ∈ H₁, φ x ∈ H₂) →
  ∃ ψ : (G₁ ⧸ H₁) →* (G₂ ⧸ H₂),
    ∀ x : G₁, ψ (QuotientGroup.mk' H₁ x) = QuotientGroup.mk' H₂ (φ x) := by
  intro G₁ G₂ _ _ H₁ H₂ _ _ φ hφ
  let f : G₁ →* G₂ ⧸ H₂ := (QuotientGroup.mk' H₂).comp φ
  have hk : H₁ ≤ f.ker := by
    intro x hx
    change QuotientGroup.mk' H₂ (φ x) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hφ x hx)
  exact ⟨QuotientGroup.lift H₁ f hk, fun x => rfl⟩

#print axioms JudsonGold.judson_11_4_15_certificate

theorem JudsonGold.judson_11_4_16_certificate :
∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
  H ⊓ K = ⊥ → ∃ L : Subgroup ((G ⧸ H) × (G ⧸ K)), Nonempty (G ≃* L) := by
  intro G _ H K _ _ hi
  let f : G →* (G ⧸ H) × (G ⧸ K) := (QuotientGroup.mk' H).prod (QuotientGroup.mk' K)
  have hk : f.ker = H ⊓ K := by
    ext x
    simp [f, MonoidHom.mem_ker]
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (hk.trans hi)
  exact ⟨f.range, ⟨MonoidHom.ofInjective hinj⟩⟩

#print axioms JudsonGold.judson_11_4_16_certificate
