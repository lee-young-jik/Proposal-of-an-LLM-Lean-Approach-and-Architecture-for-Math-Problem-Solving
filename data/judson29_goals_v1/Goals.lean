import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace JudsonGoals

def judson_3_5_26_prove : Prop :=
∀ n : ℕ, 2 < n → ∃ k : (ZMod n)ˣ, k ^ 2 = 1 ∧ k ≠ 1

def judson_3_5_26_disprove : Prop :=
¬ (
∀ n : ℕ, 2 < n → ∃ k : (ZMod n)ˣ, k ^ 2 = 1 ∧ k ≠ 1
)

theorem judson_3_5_26_pair :
  judson_3_5_26_disprove ↔ ¬ judson_3_5_26_prove := Iff.rfl
#print axioms judson_3_5_26_pair

def judson_3_5_32_prove : Prop :=
∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) →
  ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1

def judson_3_5_32_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G], Even (Nat.card G) →
  ∃ a : G, a ≠ 1 ∧ a ^ 2 = 1
)

theorem judson_3_5_32_pair :
  judson_3_5_32_disprove ↔ ¬ judson_3_5_32_prove := Iff.rfl
#print axioms judson_3_5_32_pair

def judson_3_5_38_prove : Prop :=
(∀ n : ℕ, ∃ H : AddSubgroup ℤ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) ∧
  (∀ H : AddSubgroup ℤ, ∃ n : ℕ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k)

def judson_3_5_38_disprove : Prop :=
¬ (
(∀ n : ℕ, ∃ H : AddSubgroup ℤ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k) ∧
  (∀ H : AddSubgroup ℤ, ∃ n : ℕ,
    ∀ z : ℤ, z ∈ H ↔ ∃ k : ℤ, z = (n : ℤ) * k)
)

theorem judson_3_5_38_pair :
  judson_3_5_38_disprove ↔ ¬ judson_3_5_38_prove := Iff.rfl
#print axioms judson_3_5_38_pair

def judson_3_5_41_prove : Prop :=
∃ H : Subgroup ℝˣ, ∀ x : ℝˣ,
  x ∈ H ↔ ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    (x : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 2

def judson_3_5_41_disprove : Prop :=
¬ (
∃ H : Subgroup ℝˣ, ∀ x : ℝˣ,
  x ∈ H ↔ ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    (x : ℝ) = (a : ℝ) + (b : ℝ) * Real.sqrt 2
)

theorem judson_3_5_41_pair :
  judson_3_5_41_disprove ↔ ¬ judson_3_5_41_prove := Iff.rfl
#print axioms judson_3_5_41_pair

def judson_4_5_14_prove : Prop :=
let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0];
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1];
  IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B)

def judson_4_5_14_disprove : Prop :=
¬ (
let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0];
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -1];
  IsOfFinOrder A ∧ IsOfFinOrder B ∧ ¬ IsOfFinOrder (A * B)
)

theorem judson_4_5_14_pair :
  judson_4_5_14_disprove ↔ ¬ judson_4_5_14_prove := Iff.rfl
#print axioms judson_4_5_14_pair

def judson_4_5_26_prove : Prop :=
∀ p : ℕ, Nat.Prime p →
  ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤

def judson_4_5_26_disprove : Prop :=
¬ (
∀ p : ℕ, Nat.Prime p →
  ∀ H : AddSubgroup (ZMod p), H = ⊥ ∨ H = ⊤
)

theorem judson_4_5_26_pair :
  judson_4_5_26_disprove ↔ ¬ judson_4_5_26_prove := Iff.rfl
#print axioms judson_4_5_26_pair

def judson_4_5_29_prove : Prop :=
∀ n : ℕ, 2 < n →
  Even (Nat.card {x : ZMod n | AddSubgroup.zmultiples x = ⊤})

def judson_4_5_29_disprove : Prop :=
¬ (
∀ n : ℕ, 2 < n →
  Even (Nat.card {x : ZMod n | AddSubgroup.zmultiples x = ⊤})
)

theorem judson_4_5_29_pair :
  judson_4_5_29_disprove ↔ ¬ judson_4_5_29_prove := Iff.rfl
#print axioms judson_4_5_29_pair

def judson_4_5_30_prove : Prop :=
∀ (G : Type) [Group G] (a b : G) (m n : ℕ),
  orderOf a = m → orderOf b = n → 0 < m → 0 < n →
  Nat.Coprime m n → Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥

def judson_4_5_30_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (a b : G) (m n : ℕ),
  orderOf a = m → orderOf b = n → 0 < m → 0 < n →
  Nat.Coprime m n → Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥
)

theorem judson_4_5_30_pair :
  judson_4_5_30_disprove ↔ ¬ judson_4_5_30_prove := Iff.rfl
#print axioms judson_4_5_30_pair

def judson_4_5_31_prove : Prop :=
∀ (G : Type) [CommGroup G], ∃ H : Subgroup G,
  ∀ g : G, g ∈ H ↔ IsOfFinOrder g

def judson_4_5_31_disprove : Prop :=
¬ (
∀ (G : Type) [CommGroup G], ∃ H : Subgroup G,
  ∀ g : G, g ∈ H ↔ IsOfFinOrder g
)

theorem judson_4_5_31_pair :
  judson_4_5_31_disprove ↔ ¬ judson_4_5_31_prove := Iff.rfl
#print axioms judson_4_5_31_pair

def judson_4_5_32_prove : Prop :=
∀ (G : Type) [Group G] [Finite G] (x : G),
  Subgroup.zpowers x = ⊤ → ∀ k : ℕ, Nat.Coprime k (Nat.card G) →
  Subgroup.zpowers (x ^ k) = ⊤

def judson_4_5_32_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G] (x : G),
  Subgroup.zpowers x = ⊤ → ∀ k : ℕ, Nat.Coprime k (Nat.card G) →
  Subgroup.zpowers (x ^ k) = ⊤
)

theorem judson_4_5_32_pair :
  judson_4_5_32_disprove ↔ ¬ judson_4_5_32_prove := Iff.rfl
#print axioms judson_4_5_32_pair

def judson_4_5_33_a_prove : Prop :=
∀ (G : Type) [CommGroup G] (H K : Subgroup G),
  Nat.card H = 2 → Nat.card K = 2 → H ≠ K →
  ∃ L : Subgroup G, Nat.card L = 4

def judson_4_5_33_a_disprove : Prop :=
¬ (
∀ (G : Type) [CommGroup G] (H K : Subgroup G),
  Nat.card H = 2 → Nat.card K = 2 → H ≠ K →
  ∃ L : Subgroup G, Nat.card L = 4
)

theorem judson_4_5_33_a_pair :
  judson_4_5_33_a_disprove ↔ ¬ judson_4_5_33_a_prove := Iff.rfl
#print axioms judson_4_5_33_a_pair

def judson_4_5_34_prove : Prop :=
∀ (G : Type) [CommGroup G] [Finite G] (p q : ℕ),
  Nat.card G = p * q → Nat.Coprime p q →
  (∃ a : G, orderOf a = p) → (∃ b : G, orderOf b = q) → IsCyclic G

def judson_4_5_34_disprove : Prop :=
¬ (
∀ (G : Type) [CommGroup G] [Finite G] (p q : ℕ),
  Nat.card G = p * q → Nat.Coprime p q →
  (∃ a : G, orderOf a = p) → (∃ b : G, orderOf b = q) → IsCyclic G
)

theorem judson_4_5_34_pair :
  judson_4_5_34_disprove ↔ ¬ judson_4_5_34_prove := Iff.rfl
#print axioms judson_4_5_34_pair

def judson_4_5_39_prove : Prop :=
∀ (G : Type) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
  d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d

def judson_4_5_39_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
  d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d
)

theorem judson_4_5_39_pair :
  judson_4_5_39_disprove ↔ ¬ judson_4_5_39_prove := Iff.rfl
#print axioms judson_4_5_39_pair

def judson_4_5_44_prove : Prop :=
∀ (α : Circle) (m n : ℤ),
  (α ^ m = 1 ∧ α ^ n = 1) ↔ α ^ (Int.gcd m n : ℤ) = 1

def judson_4_5_44_disprove : Prop :=
¬ (
∀ (α : Circle) (m n : ℤ),
  (α ^ m = 1 ∧ α ^ n = 1) ↔ α ^ (Int.gcd m n : ℤ) = 1
)

theorem judson_4_5_44_pair :
  judson_4_5_44_disprove ↔ ¬ judson_4_5_44_prove := Iff.rfl
#print axioms judson_4_5_44_pair

def judson_4_5_45_prove : Prop :=
∀ z : ℂˣ, ‖(z : ℂ)‖ ≠ 1 → orderOf z = 0

def judson_4_5_45_disprove : Prop :=
¬ (
∀ z : ℂˣ, ‖(z : ℂ)‖ ≠ 1 → orderOf z = 0
)

theorem judson_4_5_45_pair :
  judson_4_5_45_disprove ↔ ¬ judson_4_5_45_prove := Iff.rfl
#print axioms judson_4_5_45_pair

def judson_9_4_1_prove : Prop :=
∀ n : ℤ, n ≠ 0 →
  Nonempty (ℤ ≃+ AddSubgroup.zmultiples n)

def judson_9_4_1_disprove : Prop :=
¬ (
∀ n : ℤ, n ≠ 0 →
  Nonempty (ℤ ≃+ AddSubgroup.zmultiples n)
)

theorem judson_9_4_1_pair :
  judson_9_4_1_disprove ↔ ¬ judson_9_4_1_prove := Iff.rfl
#print axioms judson_9_4_1_pair

def judson_9_4_2_prove : Prop :=
∃ H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  (∀ M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
    M ∈ H ↔ ∃ a b : ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a]) ∧
  Nonempty (ℂˣ ≃* H)

def judson_9_4_2_disprove : Prop :=
¬ (
∃ H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  (∀ M : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
    M ∈ H ↔ ∃ a b : ℝ, (M : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a]) ∧
  Nonempty (ℂˣ ≃* H)
)

theorem judson_9_4_2_pair :
  judson_9_4_2_disprove ↔ ¬ judson_9_4_2_prove := Iff.rfl
#print axioms judson_9_4_2_pair

def judson_9_4_8_prove : Prop :=
¬ Nonempty (ℚ ≃+ ℤ)

def judson_9_4_8_disprove : Prop :=
¬ (
¬ Nonempty (ℚ ≃+ ℤ)
)

theorem judson_9_4_8_pair :
  judson_9_4_8_disprove ↔ ¬ judson_9_4_8_prove := Iff.rfl
#print axioms judson_9_4_8_pair

def judson_9_4_18_prove : Prop :=
let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num);
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num);
  let A := Subgroup.zpowers u;
  let B := Subgroup.zpowers v;
  ∃ H : Subgroup ℚˣ,
    (∀ x : ℚˣ, x ∈ H ↔ ∃ m n : ℤ, x = u ^ m * v ^ n) ∧
    A ≤ H ∧ B ≤ H ∧
    (∀ a : A, ∀ b : B, (a : ℚˣ) * (b : ℚˣ) = (b : ℚˣ) * (a : ℚˣ)) ∧
    (∀ x : H, ∃! p : A × B, (x : ℚˣ) = (p.1 : ℚˣ) * (p.2 : ℚˣ)) ∧
    Nonempty (Multiplicative (ℤ × ℤ) ≃* H)

def judson_9_4_18_disprove : Prop :=
¬ (
let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num);
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num);
  let A := Subgroup.zpowers u;
  let B := Subgroup.zpowers v;
  ∃ H : Subgroup ℚˣ,
    (∀ x : ℚˣ, x ∈ H ↔ ∃ m n : ℤ, x = u ^ m * v ^ n) ∧
    A ≤ H ∧ B ≤ H ∧
    (∀ a : A, ∀ b : B, (a : ℚˣ) * (b : ℚˣ) = (b : ℚˣ) * (a : ℚˣ)) ∧
    (∀ x : H, ∃! p : A × B, (x : ℚˣ) = (p.1 : ℚˣ) * (p.2 : ℚˣ)) ∧
    Nonempty (Multiplicative (ℤ × ℤ) ≃* H)
)

theorem judson_9_4_18_pair :
  judson_9_4_18_disprove ↔ ¬ judson_9_4_18_prove := Iff.rfl
#print axioms judson_9_4_18_pair

def judson_9_4_22_prove : Prop :=
∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
  Nat.card G = 20 → Nat.card H = 4 → Nat.card K = 5 →
  (∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G)) →
  ∀ g : G, ∃! p : H × K, g = (p.1 : G) * (p.2 : G)

def judson_9_4_22_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G),
  Nat.card G = 20 → Nat.card H = 4 → Nat.card K = 5 →
  (∀ h : H, ∀ k : K, (h : G) * (k : G) = (k : G) * (h : G)) →
  ∀ g : G, ∃! p : H × K, g = (p.1 : G) * (p.2 : G)
)

theorem judson_9_4_22_pair :
  judson_9_4_22_disprove ↔ ¬ judson_9_4_22_prove := Iff.rfl
#print axioms judson_9_4_22_pair

def judson_9_4_36_prove : Prop :=
∀ B : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  ∃ f : Matrix.SpecialLinearGroup (Fin 2) ℝ ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ((f A) : Matrix (Fin 2) (Fin 2) ℝ) =
        (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
        (A : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ)

def judson_9_4_36_disprove : Prop :=
¬ (
∀ B : (Matrix (Fin 2) (Fin 2) ℝ)ˣ,
  ∃ f : Matrix.SpecialLinearGroup (Fin 2) ℝ ≃* Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ((f A) : Matrix (Fin 2) (Fin 2) ℝ) =
        (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
        (A : Matrix (Fin 2) (Fin 2) ℝ) * (B : Matrix (Fin 2) (Fin 2) ℝ)
)

theorem judson_9_4_36_pair :
  judson_9_4_36_disprove ↔ ¬ judson_9_4_36_prove := Iff.rfl
#print axioms judson_9_4_36_pair

def judson_9_4_46_prove : Prop :=
∀ (G H : Type) [Group G] [Group H], Nonempty (G ≃* H) →
  ∀ n : ℕ, 0 < n → (∃ K : Subgroup G, Nat.card K = n) →
    ∃ L : Subgroup H, Nat.card L = n

def judson_9_4_46_disprove : Prop :=
¬ (
∀ (G H : Type) [Group G] [Group H], Nonempty (G ≃* H) →
  ∀ n : ℕ, 0 < n → (∃ K : Subgroup G, Nat.card K = n) →
    ∃ L : Subgroup H, Nat.card L = n
)

theorem judson_9_4_46_pair :
  judson_9_4_46_disprove ↔ ¬ judson_9_4_46_prove := Iff.rfl
#print axioms judson_9_4_46_pair

def judson_10_4_10_prove : Prop :=
(∀ (G : Type) [Group G] (H : Subgroup G), H.index = 2 → H.Normal) ∧
  (∀ n : ℕ, 3 ≤ n → ¬ IsSimpleGroup (Equiv.Perm (Fin n)))

def judson_10_4_10_disprove : Prop :=
¬ (
(∀ (G : Type) [Group G] (H : Subgroup G), H.index = 2 → H.Normal) ∧
  (∀ n : ℕ, 3 ≤ n → ¬ IsSimpleGroup (Equiv.Perm (Fin n)))
)

theorem judson_10_4_10_pair :
  judson_10_4_10_disprove ↔ ¬ judson_10_4_10_prove := Iff.rfl
#print axioms judson_10_4_10_pair

def judson_10_4_12_prove : Prop :=
∀ (G : Type) [Group G] (g : G),
  ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x * g = g * x) ∧
    ((Subgroup.zpowers g).Normal → H.Normal)

def judson_10_4_12_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (g : G),
  ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x * g = g * x) ∧
    ((Subgroup.zpowers g).Normal → H.Normal)
)

theorem judson_10_4_12_pair :
  judson_10_4_12_disprove ↔ ¬ judson_10_4_12_prove := Iff.rfl
#print axioms judson_10_4_12_pair

def judson_10_4_13_c_d_prove : Prop :=
∀ (G : Type) [Group G],
  (Subgroup.center G).Normal ∧
  (IsCyclic (G ⧸ Subgroup.center G) → ∀ a b : G, a * b = b * a)

def judson_10_4_13_c_d_disprove : Prop :=
¬ (
∀ (G : Type) [Group G],
  (Subgroup.center G).Normal ∧
  (IsCyclic (G ⧸ Subgroup.center G) → ∀ a b : G, a * b = b * a)
)

theorem judson_10_4_13_c_d_pair :
  judson_10_4_13_c_d_disprove ↔ ¬ judson_10_4_13_c_d_prove := Iff.rfl
#print axioms judson_10_4_13_c_d_pair

def judson_10_4_14_prove : Prop :=
∀ (G : Type) [Group G],
  (commutator G).Normal ∧
  (∀ N : Subgroup G, ∀ _ : N.Normal,
    (∀ a b : G ⧸ N, a * b = b * a) ↔ commutator G ≤ N)

def judson_10_4_14_disprove : Prop :=
¬ (
∀ (G : Type) [Group G],
  (commutator G).Normal ∧
  (∀ N : Subgroup G, ∀ _ : N.Normal,
    (∀ a b : G ⧸ N, a * b = b * a) ↔ commutator G ≤ N)
)

theorem judson_10_4_14_pair :
  judson_10_4_14_disprove ↔ ¬ judson_10_4_14_prove := Iff.rfl
#print axioms judson_10_4_14_pair

def judson_11_4_12_prove : Prop :=
∀ (G : Type) [Group G] (H : Subgroup G) (k : ℕ),
  0 < k → Nat.card H = k →
  (∀ K : Subgroup G, Nat.card K = k → K = H) → H.Normal

def judson_11_4_12_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (H : Subgroup G) (k : ℕ),
  0 < k → Nat.card H = k →
  (∀ K : Subgroup G, Nat.card K = k → K = H) → H.Normal
)

theorem judson_11_4_12_pair :
  judson_11_4_12_disprove ↔ ¬ judson_11_4_12_prove := Iff.rfl
#print axioms judson_11_4_12_pair

def judson_11_4_15_prove : Prop :=
∀ (G₁ G₂ : Type) [Group G₁] [Group G₂]
  (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [H₁.Normal] [H₂.Normal]
  (φ : G₁ →* G₂), (∀ x ∈ H₁, φ x ∈ H₂) →
  ∃ ψ : (G₁ ⧸ H₁) →* (G₂ ⧸ H₂),
    ∀ x : G₁, ψ (QuotientGroup.mk' H₁ x) = QuotientGroup.mk' H₂ (φ x)

def judson_11_4_15_disprove : Prop :=
¬ (
∀ (G₁ G₂ : Type) [Group G₁] [Group G₂]
  (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [H₁.Normal] [H₂.Normal]
  (φ : G₁ →* G₂), (∀ x ∈ H₁, φ x ∈ H₂) →
  ∃ ψ : (G₁ ⧸ H₁) →* (G₂ ⧸ H₂),
    ∀ x : G₁, ψ (QuotientGroup.mk' H₁ x) = QuotientGroup.mk' H₂ (φ x)
)

theorem judson_11_4_15_pair :
  judson_11_4_15_disprove ↔ ¬ judson_11_4_15_prove := Iff.rfl
#print axioms judson_11_4_15_pair

def judson_11_4_16_prove : Prop :=
∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
  H ⊓ K = ⊥ → ∃ L : Subgroup ((G ⧸ H) × (G ⧸ K)), Nonempty (G ≃* L)

def judson_11_4_16_disprove : Prop :=
¬ (
∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
  H ⊓ K = ⊥ → ∃ L : Subgroup ((G ⧸ H) × (G ⧸ K)), Nonempty (G ≃* L)
)

theorem judson_11_4_16_pair :
  judson_11_4_16_disprove ↔ ¬ judson_11_4_16_prove := Iff.rfl
#print axioms judson_11_4_16_pair

end JudsonGoals
