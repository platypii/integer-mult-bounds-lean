import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatBlock
import IntegerMultBounds.Machine.ColumnTransducer

/-! One physical modular subtraction row. Both packed operands are copied
through the runtime width clock into blank-backed scratch. The transducer
starts at borrow zero and halts at the scratch boundary, so no borrow can
cross a row boundary. Both scratch tapes are physically erased on return. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetRow
open CountedCopyReuse (empty binary)
noncomputable section

def word (xs : List Bool) := putWord (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
def diff (xs ys : List Bool) := ColumnTransducer.digits ColumnTransducer.subRule 0 (xs.zip ys)
def bank (f g out left right : ℤ → Fin 4) (p q r x y : ℤ) (ws : List Bool) : Tapes 7 0 :=
  ⟨![p,q,r,x,y,1,1],![f,g,out,left,right,empty,binary ws]⟩

def leftPlace : Fin (4+3) ≃ Fin 7 where
  toFun := ![0,3,5,6,1,2,4]
  invFun := ![0,4,5,1,6,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def rightPlace : Fin (4+3) ≃ Fin 7 where
  toFun := ![1,4,5,6,0,2,3]
  invFun := ![4,0,5,6,1,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def subPlace : Fin (3+4) ≃ Fin 7 where
  toFun := ![3,4,2,0,1,5,6]
  invFun := ![3,4,2,0,1,5,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def copyLeft := Placement.placed CountedCopyReuse.program leftPlace
def copyRight := Placement.placed CountedCopyReuse.program rightPlace
def rewindLeft := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (3 : Fin 7))
def rewindRight := Placement.placed (ReturnOrigin.program (a := 0)) (FiniteReturnStackAt.placement (4 : Fin 7))
def subtract := Placement.placed (ColumnTransducer.program ColumnTransducer.subRule 0) subPlace
def eraseLeft := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (3 : Fin 7))
def eraseRight := Placement.placed (EraseBack.program (a := 0)) (FiniteReturnStackAt.placement (4 : Fin 7))
def program := seq (seq (seq (seq (seq (seq copyLeft copyRight) rewindLeft) rewindRight) subtract) eraseLeft) eraseRight

theorem copy_left (xs : List Bool) (f g out right : ℤ → Fin 4) (p q r y : ℤ) (ws : List Bool)
    (hw : Counter.value ws=xs.length) :
    HoareTime copyLeft (fun z => z=bank (putWord f p (xs.map bitSymbol)) g out (fun _ => blank) right p q r 0 y ws)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) g out (word xs) right (p+xs.length) q r xs.length y ws)
      (5*xs.length+7*ws.length+16) := by
  have h := CountedCopyReuse.copy_hoare f (fun _ => blank) p 0 (xs.map bitSymbol) ws (by simpa using hw)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active leftPlace (bank (putWord f p (xs.map bitSymbol)) g out (fun _ => blank) right p q r 0 y ws)=
      CountedCopyReuse.bank (putWord f p (xs.map bitSymbol)) (fun _ => blank) empty (binary ws) p 0 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h leftPlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem copy_right (ys : List Bool) (f g out left : ℤ → Fin 4) (p q r x : ℤ) (ws : List Bool)
    (hw : Counter.value ws=ys.length) :
    HoareTime copyRight (fun z => z=bank f (putWord g q (ys.map bitSymbol)) out left (fun _ => blank) p q r x 0 ws)
      (fun z => z=bank f (putWord g q (ys.map bitSymbol)) out left (word ys) p (q+ys.length) r x ys.length ws)
      (5*ys.length+7*ws.length+16) := by
  have h := CountedCopyReuse.copy_hoare g (fun _ => blank) q 0 (ys.map bitSymbol) ws (by simpa using hw)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active rightPlace (bank f (putWord g q (ys.map bitSymbol)) out left (fun _ => blank) p q r x 0 ws)=
      CountedCopyReuse.bank (putWord g q (ys.map bitSymbol)) (fun _ => blank) empty (binary ws) q 0 1 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h rightPlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rewind_left (xs : List Bool) (f g out right : ℤ → Fin 4) (p q r y : ℤ) (ws : List Bool) :
    HoareTime rewindLeft (fun z => z=bank f g out (word xs) right p q r xs.length y ws)
      (fun z => z=bank f g out (word xs) right p q r 0 y ws) (xs.length+2) := by
  have h := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs) rfl
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (3 : Fin 7)) (bank f g out (word xs) right p q r xs.length y ws)=
      (ReturnOrigin.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (word xs) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rewind_right (ys : List Bool) (f g out left : ℤ → Fin 4) (p q r x : ℤ) (ws : List Bool) :
    HoareTime rewindRight (fun z => z=bank f g out left (word ys) p q r x ys.length ws)
      (fun z => z=bank f g out left (word ys) p q r x 0 ws) (ys.length+2) := by
  have h := ReturnOrigin.return_hoare_at (fun _ => (blank : Fin 4)) 0 (ys.map bitSymbol) (ReturnOrigin.bits_nonblank ys) rfl
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (4 : Fin 7)) (bank f g out left (word ys) p q r x ys.length ws)=
      (ReturnOrigin.cfg (word ys) ys.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (word ys) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem subtract_hoare (xs ys : List Bool) (hlen : xs.length=ys.length)
    (f g out : ℤ → Fin 4) (p q r : ℤ) (ws : List Bool) :
    HoareTime subtract (fun z => z=bank f g out (word xs) (word ys) p q r 0 0 ws)
      (fun z => z=bank f g (putWord out r ((diff xs ys).map bitSymbol)) (word xs) (word ys)
        p q (r+xs.length) xs.length ys.length ws) xs.length := by
  have h := ColumnTransducer.transduce_hoare ColumnTransducer.subRule xs ys hlen
    (fun _ => (blank : Fin 4)) (fun _ => blank) out 0 0 r rfl rfl
  simp only [zero_add] at h
  have ha : Placement.active subPlace (bank f g out (word xs) (word ys) p q r 0 0 ws)=
      (ColumnTransducer.cfg (s := 1) (word xs) (word ys) out 0 0 r 0).tapes := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h subPlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem erase_left (xs : List Bool) (f g out right : ℤ → Fin 4) (p q r y : ℤ) (ws : List Bool) :
    HoareTime eraseLeft (fun z => z=bank f g out (word xs) right p q r xs.length y ws)
      (fun z => z=bank f g out (fun _ => blank) right p q r 0 y ws) (xs.length+2) := by
  have h := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl (by intros; rfl)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (3 : Fin 7)) (bank f g out (word xs) right p q r xs.length y ws)=
      (EraseBack.cfg (word xs) xs.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem erase_right (ys : List Bool) (f g out left : ℤ → Fin 4) (p q r x : ℤ) (ws : List Bool) :
    HoareTime eraseRight (fun z => z=bank f g out left (word ys) p q r x ys.length ws)
      (fun z => z=bank f g out left (fun _ => blank) p q r x 0 ws) (ys.length+2) := by
  have h := EraseBack.erase_hoare (fun _ => (blank : Fin 4)) 0 (ys.map bitSymbol)
    (ReturnOrigin.bits_nonblank ys) rfl (by intros; rfl)
  simp only [List.length_map,zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement (4 : Fin 7)) (bank f g out left (word ys) p q r x ys.length ws)=
      (EraseBack.cfg (word ys) ys.length 0).tapes := by rw [FiniteReturnStackAt.active_bank]; rfl
  apply (Placement.hoare_at h _ _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank (fun _ => blank) 0)=_
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (xs ys : List Bool) (hlen : xs.length=ys.length)
    (f g out : ℤ → Fin 4) (p q r : ℤ) (ws : List Bool) (hw : Counter.value ws=xs.length) :
    HoareTime program
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol)) out
        (fun _ => blank) (fun _ => blank) p q r 0 0 ws)
      (fun z => z=bank (putWord f p (xs.map bitSymbol)) (putWord g q (ys.map bitSymbol))
        (putWord out r ((diff xs ys).map bitSymbol)) (fun _ => blank) (fun _ => blank)
        (p+xs.length) (q+xs.length) (r+xs.length) 0 0 ws)
      (15*xs.length+14*ws.length+46) := by
  have h0 := (copy_left xs f (putWord g q (ys.map bitSymbol)) out (fun _ => blank) p q r 0 ws hw).seq
    (copy_right ys (putWord f p (xs.map bitSymbol)) g out (word xs) (p+xs.length) q r xs.length ws (hw.trans hlen))
  have h1 := h0.seq (rewind_left xs _ _ out (word ys) (p+xs.length) (q+ys.length) r ys.length ws)
  have h2 := h1.seq (rewind_right ys _ _ out (word xs) (p+xs.length) (q+ys.length) r 0 ws)
  have h3 := h2.seq (subtract_hoare xs ys hlen _ _ out (p+xs.length) (q+ys.length) r ws)
  have h4 := h3.seq (erase_left xs _ _ _ (word ys) (p+xs.length) (q+ys.length) (r+xs.length) ys.length ws)
  have h5 := h4.seq (erase_right ys _ _ _ (fun _ => blank) (p+xs.length) (q+ys.length) (r+xs.length) 0 ws)
  apply h5.consequence (fun _ h => h) _ (by omega)
  intro z hz
  simpa only [←hlen] using hz

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetRow
