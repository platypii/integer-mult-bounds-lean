import IntegerMultBounds.Machine.BinaryDescriptorStack
import IntegerMultBounds.Machine.GrowingCounterData

/-! A physical four-state width-one guard. It reads the first bit and, only
when that bit is one, its successor. Every tape and head is restored exactly;
the actual terminal state selects the base or recursive continuation. -/
namespace IntegerMultBounds.Machine.RecursiveWidthGuard
variable {t a : ℕ}

def base : Fin 4 := 2
def recurse : Fin 4 := 3

def program (width : Fin t) : Program t 4 a where
  tapes_pos := Nat.zero_lt_of_lt width.isLt
  start := 0
  transition := fun st sy =>
    if st = 0 then
      if sy width = bitSymbol true then
        some (1,fun i => (sy i,if i = width then Move.right else Move.stay))
      else some (recurse,fun i => (sy i,Move.stay))
    else if st = 1 then
      some (if sy width = blank then base else recurse,
        fun i => (sy i,if i = width then Move.left else Move.stay))
    else none

def cfg (v : Tapes t a) (st : Fin 4) : Config t 4 a := ⟨st,v.head,v.tape⟩
def advanced (width : Fin t) (v : Tapes t a) : Tapes t a :=
  ⟨fun i => v.head i + if i = width then 1 else 0,v.tape⟩

theorem step_recurse (width : Fin t) (v : Tapes t a)
    (h : v.tape width (v.head width) ≠ bitSymbol true) :
    step (program width) (cfg v 0) = some (cfg v recurse) := by
  simp only [step,program,cfg,ite_true,h,ite_false]
  congr 1
  apply congrArg₂ (Config.mk recurse)
  · funext i; simp [Move.offset]
  · funext i z; by_cases hz : z = v.head i <;> simp [hz]

theorem step_advance (width : Fin t) (v : Tapes t a)
    (h : v.tape width (v.head width) = bitSymbol true) :
    step (program width) (cfg v 0) = some (cfg (advanced width v) 1) := by
  simp only [step,program,cfg,ite_true,h]
  congr 1
  apply congrArg₂ (Config.mk 1)
  · funext i; by_cases hi : i = width <;> simp [advanced,hi,Move.offset]
  · funext i z; by_cases hz : z = v.head i <;> simp [advanced,hz]

theorem step_return (width : Fin t) (v : Tapes t a) :
    step (program width) (cfg (advanced width v) 1) =
      some (cfg v (if v.tape width (v.head width+1) = blank then base else recurse)) := by
  simp only [step,program,cfg,advanced,show (1 : Fin 4) ≠ 0 by decide,ite_false,ite_true]
  congr 1
  apply congrArg₂ (Config.mk _)
  · funext i; by_cases hi : i = width <;> simp [hi,Move.offset]
  · funext i z; by_cases hz : z = v.head i + if i = width then 1 else 0 <;> simp [hz]

theorem halt (width : Fin t) (v : Tapes t a) (st : Fin 4) (hs : st = base ∨ st = recurse) :
    step (program width) (cfg v st) = none := by
  rcases hs with rfl | rfl <;> simp [step,program,cfg,base,recurse]

def result (width : Fin t) (v : Tapes t a) : Fin 4 :=
  if v.tape width (v.head width) = bitSymbol true ∧ v.tape width (v.head width+1) = blank then base else recurse

def cost (width : Fin t) (v : Tapes t a) : ℕ :=
  if v.tape width (v.head width) = bitSymbol true then 2 else 1

/-- Exact terminal state and full-bank preservation, without a descriptor assumption. -/
theorem run_exact (width : Fin t) (v : Tapes t a) :
    run (program width) (cost width v) (v.start (program width)) = some (cfg v (result width v)) := by
  by_cases h : v.tape width (v.head width) = bitSymbol true
  · simp only [cost,h,ite_true]
    change run (program width) (1+1) (cfg v 0) = _
    rw [run_add,run_one,step_advance width v h]
    simp only [Option.bind_some,run_one,step_return,result,h,true_and]
  · simp only [cost,h,ite_false]
    rw [run_one]
    change step (program width) (cfg v 0) = _
    simpa only [result,h,false_and,ite_false] using step_recurse width v h

theorem cost_le (width : Fin t) (v : Tapes t a) : cost width v ≤ 2 := by
  unfold cost; split_ifs <;> omega

theorem result_halt (width : Fin t) (v : Tapes t a) :
    step (program width) (cfg v (result width v)) = none := by
  apply halt
  unfold result; split_ifs <;> simp

private theorem descriptor_test (bs : List Bool) :
    (BinaryDescriptorStack.descriptor (a := a) bs 1 = bitSymbol true ∧
      BinaryDescriptorStack.descriptor (a := a) bs 2 = blank) ↔ bs = [true] := by
  cases bs with
  | nil => simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty,blank,bitSymbol,Fin.ext_iff]
  | cons b bs =>
    cases bs with
    | nil => cases b <;> simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty,blank,bitSymbol,Fin.ext_iff]
    | cons c cs =>
      cases b <;> cases c <;> simp [BinaryDescriptorStack.descriptor,putWord,blank,bitSymbol,Fin.ext_iff]

theorem canonical_one_iff (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    Counter.value bs = 1 ↔ bs = [true] := by
  constructor
  · intro hv
    have hl := GrowingCounterData.canonical_width bs hc
    rw [hv] at hl
    rw [show Nat.log2 1 = 0 by decide] at hl
    cases bs with
    | nil => simp [Counter.value] at hv
    | cons b bs =>
      have he : bs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
      subst bs
      cases b <;> simp_all [Counter.value]
  · rintro rfl; rfl

theorem result_base_iff (width : Fin t) (v : Tapes t a) (bs : List Bool)
    (hh : v.head width = 1) (ht : v.tape width = BinaryDescriptorStack.descriptor bs)
    (hc : GrowingCounterData.Canonical bs) : result width v = base ↔ Counter.value bs = 1 := by
  rw [canonical_one_iff bs hc]
  simp only [result,hh,ht,show (1 : ℤ)+1 = 2 by rfl,descriptor_test]
  split_ifs <;> simp_all [base,recurse]

/-- The actual terminating configuration, suitable for finite-state dispatch. -/
theorem canonical_exact (width : Fin t) (v : Tapes t a) (bs : List Bool)
    (hh : v.head width = 1) (ht : v.tape width = BinaryDescriptorStack.descriptor bs)
    (hc : GrowingCounterData.Canonical bs) :
    ∃ k ≤ 2, run (program width) k (v.start (program width)) =
      some (cfg v (if Counter.value bs = 1 then base else recurse)) ∧
      step (program width) (cfg v (if Counter.value bs = 1 then base else recurse)) = none := by
  have he : result width v = if Counter.value bs = 1 then base else recurse := by
    have hi := result_base_iff width v bs hh ht hc
    unfold result at hi ⊢
    split_ifs <;> simp_all [base,recurse]
  exact ⟨cost width v,cost_le width v,he ▸ run_exact width v,he ▸ result_halt width v⟩

theorem guard_hoare (width : Fin t) (v : Tapes t a) :
    HoareTime (program width) (fun w => w = v) (fun w => w = v) 2 := by
  intro w hw
  subst w
  exact ⟨cost width v,cfg v (result width v),cost_le width v,run_exact width v,result_halt width v,rfl⟩

end IntegerMultBounds.Machine.RecursiveWidthGuard
