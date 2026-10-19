import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_6A_24_certificate :
∀ B : LinearMap.BilinForm ℝ (Fin 2 → ℝ),
  (∀ v w, B v w = B w v) → (∀ v, v ≠ 0 → 0 < B v v) →
  ∃ v : Fin 2 → ℝ, Real.sqrt (B v v) ≠ max |v 0| |v 1| := by
  classical
  intro B hsym hpos
  by_contra h
  push_neg at h
  let e0 : Fin 2 → ℝ := ![1, 0]
  let e1 : Fin 2 → ℝ := ![0, 1]
  let p : Fin 2 → ℝ := e0 + e1
  let m : Fin 2 → ℝ := e0 - e1
  have he0 : e0 ≠ 0 := by
    intro he
    have he' := congrFun he (0 : Fin 2)
    norm_num [e0] at he'
  have he1 : e1 ≠ 0 := by
    intro he
    have he' := congrFun he (1 : Fin 2)
    norm_num [e1] at he'
  have hp : p ≠ 0 := by
    intro he
    have he' := congrFun he (0 : Fin 2)
    norm_num [p, e0, e1] at he'
  have hm : m ≠ 0 := by
    intro he
    have he' := congrFun he (0 : Fin 2)
    norm_num [m, e0, e1] at he'
  have h00 : B e0 e0 = 1 := by
    have hs := h e0
    have hs' : Real.sqrt (B e0 e0) = 1 := by
      simpa [e0] using hs
    have hb : 0 ≤ B e0 e0 := le_of_lt (hpos e0 he0)
    nlinarith [Real.sq_sqrt hb]
  have h11 : B e1 e1 = 1 := by
    have hs := h e1
    have hs' : Real.sqrt (B e1 e1) = 1 := by
      simpa [e1] using hs
    have hb : 0 ≤ B e1 e1 := le_of_lt (hpos e1 he1)
    nlinarith [Real.sq_sqrt hb]
  have hpp : B p p = 1 := by
    have hs := h p
    have hs' : Real.sqrt (B p p) = 1 := by
      simpa [p, e0, e1] using hs
    have hb : 0 ≤ B p p := le_of_lt (hpos p hp)
    nlinarith [Real.sq_sqrt hb]
  have hmm : B m m = 1 := by
    have hs := h m
    have hs' : Real.sqrt (B m m) = 1 := by
      simpa [m, e0, e1] using hs
    have hb : 0 ≤ B m m := le_of_lt (hpos m hm)
    nlinarith [Real.sq_sqrt hb]
  simp [p, m] at hpp hmm
  nlinarith

#print axioms GroundTruth.linear_algebra_6A_24_certificate
