import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCopy

/-! Load one runtime-width packed block into scratch, emit it L times using
an actual countdown, then erase scratch. The original source advances one
block and all three descriptor/work heads are restored. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBlock
open CountedCopyReuse (empty binary)
open BinaryAddressOffsetRepeatData
noncomputable section

def bank (f g scratch : ℤ → Fin 4) (p q r : ℤ) (ws ls : List Bool) : Tapes 7 0 :=
  ⟨![p,q,r,1,1,1,1],![f,g,scratch,empty,binary ws,empty,binary ls]⟩

def copyPlace : Fin (4+3) ≃ Fin 7 where
  toFun := ![0,2,3,4,1,5,6]
  invFun := ![0,4,1,2,3,5,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def repeatPlace : Fin (4+3) ≃ Fin 7 where
  toFun := ![2,1,5,6,0,3,4]
  invFun := ![4,1,0,5,6,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def copyProgram := Placement.placed CountedCopyReuse.program copyPlace
def rewindProgram := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (2 : Fin 7))
def repeatProgram := Placement.placed (CountedLoopReuse.program BinaryAddressOffsetRepeatCopy.program) repeatPlace
def cleanup := WordBankCleanup.clearProgram (2 : Fin 7) (by decide) 0
def program := seq (seq (seq copyProgram rewindProgram) repeatProgram) cleanup

def scratch (xs : List Bool) := putWord (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)

theorem copy_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool)
    (hw : Counter.value ws=xs.length) :
    HoareTime copyProgram
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (fun _ => blank) p q 0 ws ls)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (scratch xs) (p+xs.length) q xs.length ws ls)
      (5*xs.length+7*ws.length+16) := by
  let v := bank (putWord f p (xs.map bitSymbol)) g (fun _ => blank) p q 0 ws ls
  have hh := CountedCopyReuse.copy_hoare f (fun _ => blank) p 0 (xs.map bitSymbol) ws (by simpa using hw)
  simp only [List.length_map,zero_add] at hh
  have ha : Placement.active copyPlace v=CountedCopyReuse.bank (putWord f p (xs.map bitSymbol))
      (fun _ => blank) empty (binary ws) p 0 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at hh copyPlace v ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rewind_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool) :
    HoareTime rewindProgram (fun z => z=bank f g (scratch xs) p q xs.length ws ls)
      (fun z => z=bank f g (scratch xs) p q 0 ws ls) (xs.length+2) := by
  have hh := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at hh
  have ha : Placement.active (FiniteReturnStackAt.placement (2 : Fin 7))
      (bank f g (scratch xs) p q xs.length ws ls)=(ReturnOrigin.cfg (scratch xs) xs.length 0).tapes := by
    rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at hh (FiniteReturnStackAt.placement (2 : Fin 7)) _ ha).consequence
    (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (scratch xs) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem repeat_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool) (L : ℕ)
    (hL : Counter.value ls=L) :
    HoareTime repeatProgram (fun z => z=bank f g (scratch xs) p q 0 ws ls)
      (fun z => z=bank f (putWord g q ((copies xs L).map bitSymbol)) (scratch xs)
        p (q+(L*xs.length : ℕ)) 0 ws ls) (L*(2*xs.length+9)+7*ls.length+16) := by
  have hh := CountedLoopReuse.loop_hoare BinaryAddressOffsetRepeatCopy.program ls L
    (BinaryAddressOffsetRepeatCopy.state xs g q) (fun _ => 2*xs.length+3) hL
    (fun i _ => BinaryAddressOffsetRepeatCopy.step xs g q i)
  have ha : Placement.active repeatPlace (bank f g (scratch xs) p q 0 ws ls)=
      CountedLoopReuse.bank (BinaryAddressOffsetRepeatCopy.state xs g q 0) empty (binary ls) 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change q=q+(0*xs.length : ℕ); simp)
  apply (Placement.hoare_at hh repeatPlace (bank f g (scratch xs) p q 0 ws ls) ha).consequence
    (fun _ h => h) _ (by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]; nlinarith)
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clear_hoare (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool) :
    HoareTime cleanup (fun z => z=bank f g (scratch xs) p q 0 ws ls)
      (fun z => z=bank f g (fun _ => blank) p q 0 ws ls) (2*xs.length+3) := by
  have hh := WordBankCleanup.clear_hoare (bank f g (scratch xs) p q 0 ws ls) (2 : Fin 7) (by decide)
    (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs) rfl
  have he : WordBankCleanup.write (bank f g (scratch xs) p q 0 ws ls) 2 (fun _ => blank)=
      bank f g (fun _ => blank) p q 0 ws ls := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,List.length_map,cleanup] using hh

theorem runs (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (ws ls : List Bool) (L : ℕ)
    (hw : Counter.value ws=xs.length) (hL : Counter.value ls=L) :
    HoareTime program
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) g (fun _ => blank) p q 0 ws ls)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) (putWord g q ((copies xs L).map bitSymbol))
        (fun _ => blank) (p+xs.length) (q+(L*xs.length : ℕ)) 0 ws ls)
      (L*(2*xs.length+9)+8*xs.length+7*ws.length+7*ls.length+40) := by
  have h0 := copy_hoare xs f g p q ws ls hw
  have h1 := h0.seq (rewind_hoare xs (putWord f p (xs.map bitSymbol)) g (p+xs.length) q ws ls)
  have h2 := h1.seq (repeat_hoare xs (putWord f p (xs.map bitSymbol)) g (p+xs.length) q ws ls L hL)
  have h3 := h2.seq (clear_hoare xs (putWord f p (xs.map bitSymbol))
    (putWord g q ((copies xs L).map bitSymbol)) (p+xs.length) (q+(L*xs.length : ℕ)) ws ls)
  exact h3.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBlock
