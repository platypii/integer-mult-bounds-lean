import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCopy
import IntegerMultBounds.Machine.Negate

/-! Copy one runtime-width row into blank scratch, execute verified two's
complement from its start state, emit the result, and erase scratch. The
negation state is physically restarted for every row. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetRow
open CountedCopyReuse (empty binary)
open TwosComplement (negWord)
noncomputable section

def word (xs : List Bool) := putWord (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
def bank (source dest scratch : ℤ → Fin 4) (p q r : ℤ) (ws : List Bool) : Tapes 5 0 :=
  ⟨![p,q,r,1,1],![source,dest,scratch,empty,binary ws]⟩
def copyPlace : Fin (4+1) ≃ Fin 5 where
  toFun := ![0,2,3,4,1]
  invFun := ![0,4,1,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def emitPlace : Fin (2+3) ≃ Fin 5 where
  toFun := ![2,1,0,3,4]
  invFun := ![2,1,0,3,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def copyProgram := Placement.placed CountedCopyReuse.program copyPlace
def rewindProgram := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (2 : Fin 5))
def negateProgram := Placement.placed (Negate.program 0) (FiniteReturnStackAt.placement (2 : Fin 5))
def emitProgram := Placement.placed BinaryAddressOffsetRepeatCopy.program emitPlace
def clearProgram := WordBankCleanup.clearProgram (2 : Fin 5) (by decide) 0
def program := seq (seq (seq (seq (seq copyProgram rewindProgram) negateProgram) rewindProgram) emitProgram) clearProgram

theorem copy_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) (hw : Counter.value ws=xs.length) :
    HoareTime copyProgram (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (fun _ => blank) p q 0 ws)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (word xs) (p+xs.length) q xs.length ws)
      (5*xs.length+7*ws.length+16) := by
  have h := CountedCopyReuse.copy_hoare f (fun _ => blank) p 0 (xs.map bitSymbol) ws (by simpa using hw)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active copyPlace (bank (putWord f p (xs.map bitSymbol)) g (fun _ => blank) p q 0 ws)=
      CountedCopyReuse.bank (putWord f p (xs.map bitSymbol)) (fun _ => blank) empty (binary ws) p 0 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h copyPlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rewind_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) :
    HoareTime rewindProgram (fun z => z=bank f g (word xs) p q xs.length ws)
      (fun z => z=bank f g (word xs) p q 0 ws) (xs.length+2) := by
  have h := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (2 : Fin 5)) (bank f g (word xs) p q xs.length ws)=
      (ReturnOrigin.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (word xs) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem negate_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) :
    HoareTime negateProgram (fun z => z=bank f g (word xs) p q 0 ws)
      (fun z => z=bank f g (word (negWord xs)) p q xs.length ws) xs.length := by
  have h := Negate.neg_hoare (fun _ => (blank : Fin 4)) 0 xs rfl
  simp only [zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (2 : Fin 5)) (bank f g (word xs) p q 0 ws)=
      (Negate.cfg (word xs) 0 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (word (negWord xs)) xs.length)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem emit_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) :
    HoareTime emitProgram (fun z => z=bank f g (word xs) p q 0 ws)
      (fun z => z=bank f (putWord g q (xs.map bitSymbol)) (word xs) p (q+xs.length) 0 ws)
      (2*xs.length+3) := by
  have h := BinaryAddressOffsetRepeatCopy.copies xs g q
  have ha : Placement.active emitPlace (bank f g (word xs) p q 0 ws)=BinaryAddressOffsetRepeatCopy.bank xs g q := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h emitPlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clear_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) :
    HoareTime clearProgram (fun z => z=bank f g (word xs) p q 0 ws)
      (fun z => z=bank f g (fun _ => blank) p q 0 ws) (2*xs.length+3) := by
  have h := WordBankCleanup.clear_hoare (bank f g (word xs) p q 0 ws) (2 : Fin 5) (by decide)
    (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs) rfl
  have he : WordBankCleanup.write (bank f g (word xs) p q 0 ws) 2 (fun _ => blank)=bank f g (fun _ => blank) p q 0 ws := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,List.length_map,clearProgram] using h

theorem runs (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws : List Bool) (hw : Counter.value ws=xs.length) :
    HoareTime program (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (fun _ => blank) p q 0 ws)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) (putWord g q ((negWord xs).map bitSymbol))
        (fun _ => blank) (p+xs.length) (q+xs.length) 0 ws) (12*xs.length+7*ws.length+31) := by
  have h0 := (copy_hoare xs f g p q ws hw).seq (rewind_hoare xs _ g (p+xs.length) q ws)
  have h1 := h0.seq (negate_hoare xs _ g (p+xs.length) q ws)
  have hr := rewind_hoare (negWord xs) (putWord f p (xs.map bitSymbol)) g (p+xs.length) q ws
  have he := emit_hoare (negWord xs) (putWord f p (xs.map bitSymbol)) g (p+xs.length) q ws
  have hc := clear_hoare (negWord xs) (putWord f p (xs.map bitSymbol)) (putWord g q ((negWord xs).map bitSymbol))
    (p+xs.length) (q+xs.length) ws
  simp only [TwosComplement.negWord_length] at hr he hc
  exact (((h1.seq hr).seq he).seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryParityXorOffsetRow
