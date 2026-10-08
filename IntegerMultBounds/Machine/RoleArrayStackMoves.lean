import IntegerMultBounds.Machine.StackPush
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physically initialize/reset the reusable stack-transfer clock and move
payload heads by the runtime binary count. All payload symbols are spectators. -/
namespace IntegerMultBounds.Machine.RoleArrayStackMoves
variable {a : ℕ}
noncomputable section

def ready (v : Tapes 2 a) (bs : List Bool) : Tapes 4 a := StackPush.controls v bs

def idle (v : Tapes 2 a) (bs : List Bool) : Tapes 4 a :=
  CountedLoopReuseAlphabet.bank v (fun _ => blank) (CountedLoopReuseAlphabet.binary bs) 0 1

theorem binary_descriptor (bs : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) bs = BinaryDescriptorStack.descriptor bs := by
  rw [← CountedLoopReuseAlphabet.encoding_binary,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  rfl

def initializeProgram (a : ℕ) := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 0)
  (FiniteReturnStackAt.placement (2 : Fin 4))

theorem initialize_hoare (v : Tapes 2 a) (bs : List Bool) :
    HoareTime (initializeProgram a) (fun w => w = idle v bs) (fun w => w = ready v bs) 6 := by
  have hh := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 0)
    (FiniteReturnStackAt.placement (2 : Fin 4)) (idle v bs) (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [idle,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,Tapes.append,RecursiveChildQuotientsConstant.bits,
      GrowingCounterData.advance,BinaryDescriptorStack.descriptor,putWord,
      ] <;> rfl

def cleanupProgram (a : ℕ) := BinaryDescriptorCleanupList.oneProgram (a := a) (2 : Fin 4)

theorem cleanup_hoare (v : Tapes 2 a) (bs : List Bool) :
    HoareTime (cleanupProgram a) (fun w => w = ready v bs) (fun w => w = idle v bs) 4 := by
  have hh := BinaryDescriptorCleanupList.one_hoare (a := a) (2 : Fin 4) (ready v bs) [] rfl rfl
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [ready,StackPush.controls,CountedLoopReuseAlphabet.bank,
      CountedLoopReuseAlphabet.controls,Tapes.append] <;> rfl

def shifted (v : Tapes 2 a) (moves : Fin 2 → Move) (n : ℕ) : Tapes 2 a :=
  ⟨fun i => v.head i+n*(moves i).offset,v.tape⟩

def moveCell (moves : Fin 2 → Move) : Program 2 2 a :=
  DescriptorStackControl.once (by decide) (fun sy i => (sy i,moves i))

theorem move_cell_hoare (v : Tapes 2 a) (moves : Fin 2 → Move) :
    HoareTime (moveCell moves) (fun w => w = v) (fun w => w = shifted v moves 1) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ v).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  apply congrArg₂ Tapes.mk
  · funext i; simp
  · funext i z; by_cases hz : z = v.head i <;> simp [hz]

def moveProgram (moves : Fin 2 → Move) := CountedLoopReuseAlphabet.program (moveCell (a := a) moves)

theorem move_hoare (v : Tapes 2 a) (moves : Fin 2 → Move) (bs : List Bool) (n : ℕ)
    (hc : Counter.value bs = n) :
    HoareTime (moveProgram moves) (fun w => w = ready v bs) (fun w => w = ready (shifted v moves n) bs)
      (7*n+7*bs.length+16) := by
  have h := CountedLoopReuseAlphabet.loop_hoare (moveCell moves) bs n (fun i => shifted v moves i) (fun _ => 1) hc
    (by
      intro i _
      have he : shifted (shifted v moves i) moves 1 = shifted v moves (i+1) := by
        apply congrArg₂ Tapes.mk
        · funext j; simp only [shifted,Nat.cast_one,Nat.cast_add]; ring
        · rfl
      simpa only [he] using move_cell_hoare (shifted v moves i) moves)
  have hz : shifted v moves 0 = v := by cases v; simp [shifted]
  rw [hz] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]; omega)

def stepProgram (moves : Fin 2 → Move) := extend (moveCell (a := a) moves) 2

theorem step_hoare (v : Tapes 2 a) (moves : Fin 2 → Move) (bs : List Bool) :
    HoareTime (stepProgram moves) (fun w => w = ready v bs) (fun w => w = ready (shifted v moves 1) bs) 1 :=
  hoare_extend_eq (move_cell_hoare v moves) _

def swap : Fin 4 ≃ Fin 4 where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def swapped (v : Tapes 2 a) : Tapes 2 a := StackPop.bank (v.tape 1) (v.tape 0) (v.head 1) (v.head 0)

theorem ready_swap (v : Tapes 2 a) (bs : List Bool) : (ready v bs).reindex swap = ready (swapped v) bs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem swapped_swapped (v : Tapes 2 a) : swapped (swapped v) = v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def popProgram (a : ℕ) := reindex (StackPop.program (a := a)) swap

theorem pop_hoare (v : Tapes 2 a) (bs : List Bool) (n : ℕ) (hc : Counter.value bs = n) :
    HoareTime (popProgram a) (fun w => w = ready v bs)
      (fun w => w = ready (swapped (StackPop.transfer (swapped v) n)) bs) (7*n+7*bs.length+16) := by
  have h := hoare_reindex_eq (StackPop.pop_hoare (swapped v) bs n hc) swap
  change HoareTime _ (fun w => w = (ready (swapped v) bs).reindex swap)
    (fun w => w = (ready (StackPop.transfer (swapped v) n) bs).reindex swap) _ at h
  simpa only [ready_swap,swapped_swapped,popProgram] using h

end
end IntegerMultBounds.Machine.RoleArrayStackMoves
