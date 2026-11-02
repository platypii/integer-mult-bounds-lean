module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedClassRun
public import Mathlib.Algebra.Order.Floor.Ring

/-! Reuse the structural initialization wrapper with real-valued selected time
bounds. Rounding a uniform run bound adds at most one transition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open ComputedClassBanks
variable {T Q A : ℕ} {P U : Type}

theorem initializedClassRun_exec_within_real (body : P → Pr P T Q A U)
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (src : Fin 4 → Fin T) (hoff : ∀ i k, src i ≠ bank k)
    (B : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, i ≠ .control .source → S.R (bank i) = [])
    (hwords : ∀ i, (S.R (src i)).length = B)
    (p : Pr P T Q A U) (runTime : ℝ) (runStock depth : ℕ)
    (Valid : List (List (Fin (A+4))) → Prop)
    (hrun : ∀ w : HS T Q A U, ∃ w', ∃ n : ℕ, ∃ outputs, w'.user = w.user ∧ (n : ℝ) ≤ runTime ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk w (loadedClassGeometry bank src S))+depth+runStock)
        depth p (Host.mk w (loadedClassGeometry bank src S)) n
        (Host.mk w' {loadedClassGeometry bank src S with R :=
          (Function.update (loadedClassGeometry bank src S).R (plan bank hinj).result
            (outputs.reverse.flatten++(loadedClassGeometry bank src S).R (plan bank hinj).result))})) :
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧ (n : ℝ) ≤ 32*(B : ℝ)+runTime+35 ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(2*(24*B+25)+runStock)) depth
        (initializedClassProgram bank src p) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  have hnonneg : 0 ≤ runTime := by
    obtain ⟨w,n,outputs,hu,hn,hvalid,he⟩ := hrun v
    exact (Nat.cast_nonneg n).trans hn
  have hrunNat : ∀ w : HS T Q A U, ∃ w', ∃ n : ℕ, ∃ outputs, w'.user = w.user ∧ n ≤ ⌈runTime⌉₊ ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk w (loadedClassGeometry bank src S))+depth+runStock)
        depth p (Host.mk w (loadedClassGeometry bank src S)) n
        (Host.mk w' {loadedClassGeometry bank src S with R :=
          (Function.update (loadedClassGeometry bank src S).R (plan bank hinj).result
            (outputs.reverse.flatten++(loadedClassGeometry bank src S).R (plan bank hinj).result))}) := by
    intro w
    obtain ⟨w',n,outputs,hu,hn,hvalid,he⟩ := hrun w
    exact ⟨w',n,outputs,hu,by exact_mod_cast hn.trans (Nat.le_ceil runTime),hvalid,he⟩
  obtain ⟨v',n,outputs,hu,hn,hvalid,he⟩ := initializedClassRun_exec_within body bank hinj src hoff B v S
    hblank hwords p ⌈runTime⌉₊ runStock depth Valid hrunNat
  refine ⟨v',n,outputs,hu,?_,hvalid,he⟩
  have ht := (Nat.cast_le (α := ℝ)).mpr hn
  have hc := Nat.ceil_lt_add_one hnonneg
  push_cast at ht
  linarith

end IntegerMultBounds.MathlibTM2.Cost
