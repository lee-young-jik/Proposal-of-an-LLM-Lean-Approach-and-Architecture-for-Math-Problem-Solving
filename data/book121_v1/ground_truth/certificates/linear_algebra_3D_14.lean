import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_3D_14_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ R S T : V →ₗ[F] V, Function.Surjective (R.comp (S.comp T)) → Function.Injective S := by
  intro F _ V _ _ _ R S T hsurj
  have hcomp : Function.Injective (R.comp (S.comp T)) :=
    ((R.comp (S.comp T)).injective_iff_surjective_of_finrank_eq_finrank rfl).2 hsurj
  have hTinj : Function.Injective T := by
    intro x y hxy
    apply hcomp
    simp only [LinearMap.comp_apply]
    rw [hxy]
  have hTsurj : Function.Surjective T :=
    (T.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hTinj
  intro x y hxy
  obtain ⟨x', rfl⟩ := hTsurj x
  obtain ⟨y', rfl⟩ := hTsurj y
  have h' : x' = y' := by
    apply hcomp
    simp only [LinearMap.comp_apply]
    rw [hxy]
  exact congrArg T h'

#print axioms GroundTruth.linear_algebra_3D_14_certificate
