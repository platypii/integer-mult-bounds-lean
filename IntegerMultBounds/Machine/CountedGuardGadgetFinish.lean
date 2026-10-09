import IntegerMultBounds.Machine.CountedGuardGadgetRecord
import IntegerMultBounds.Machine.AnyFlag
import IntegerMultBounds.Machine.WordMoves

/-! Physical guard-word finalization: source and flag rewinds, AnyFlag scan,
and complete flag erasure. A fixed fifteen-tape machine retains every spectator. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetFinish
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def rewindAt (i : Fin 15) := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement i)
def eraseAt (i : Fin 15) := Placement.placed (EraseBack.program (a := a)) (FiniteReturnStackAt.placement i)

theorem rewinds (v : Tapes 15 a) (i : Fin 15) (xs : List Bool)
    (ht : v.tape i=word xs) (hp : v.head i=xs.length) :
    HoareTime (rewindAt (a := a) i) (fun w => w=v)
      (fun w => w=setTape v i (word xs) 0) (xs.length+2) := by
  have h0 := ReturnOrigin.return_hoare (xs.map (bitSymbol (a := a))) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  rfl

theorem erases (v : Tapes 15 a) (i : Fin 15) (xs : List Bool)
    (ht : v.tape i=word xs) (hp : v.head i=xs.length) :
    HoareTime (eraseAt (a := a) i) (fun w => w=v)
      (fun w => w=setTape v i (fun _ => blank) 0) (xs.length+2) := by
  have h0 := EraseBack.erase_hoare (a := a) (fun _ => blank) 0 (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) rfl (fun _ _ => rfl)
  simp only [List.length_map,zero_add] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  rfl

def anyPlace : Fin (2+13) ≃ Fin 15 where
  toFun := ![5,14,0,1,2,3,4,6,7,8,9,10,11,12,13]
  invFun := ![2,3,4,5,6,0,7,8,9,10,11,12,13,14,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def key (fl : List Bool) : ℤ → Fin (a+4) := Function.update (fun _ => blank) 0 (bitSymbol (fl.any id))
def anyProgram := Placement.placed (AnyFlag.program (a := a)) anyPlace

theorem anyRuns (v : Tapes 15 a) (fl : List Bool)
    (ht : v.tape 5=word fl) (hp : v.head 5=0)
    (hk : v.tape 14=fun _ => blank) (hpk : v.head 14=0) :
    HoareTime (anyProgram (a := a)) (fun w => w=v)
      (fun w => w=setTape (setTape v 5 (word fl) fl.length) 14 (key fl) 1) (fl.length+1) := by
  have h0 := AnyFlag.any_hoare (a := a) (fun _ => blank) (fun _ => blank) 0 0 fl rfl
  simp only [zero_add] at h0
  have h := Placement.hoare_at h0 anyPlace v (by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> first | exact hp | exact hpk
    · funext i; fin_cases i <;> first | exact ht | exact hk)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program := seq (seq (seq (seq (rewindAt (a := a) 0) (rewindAt 1)) (rewindAt 5)) anyProgram) (eraseAt 5)
def output (v : Tapes 15 a) (V W fl : List Bool) : Tapes 15 a :=
  setTape (setTape (setTape (setTape v 0 (word V) 0) 1 (word W) 0) 5 (fun _ => blank) 0) 14 (key fl) 1

theorem runs (v : Tapes 15 a) (V W fl : List Bool)
    (hVt : v.tape 0=word V) (hVp : v.head 0=V.length)
    (hWt : v.tape 1=word W) (hWp : v.head 1=W.length)
    (hFt : v.tape 5=word fl) (hFp : v.head 5=fl.length)
    (hKt : v.tape 14=fun _ => blank) (hKp : v.head 14=0) :
    HoareTime (program (a := a)) (fun w => w=v) (fun w => w=output v V W fl)
      (V.length+W.length+3*fl.length+13) := by
  let A := setTape v 0 (word V) 0
  let B := setTape A 1 (word W) 0
  let C := setTape B 5 (word fl) 0
  let D := setTape (setTape C 5 (word fl) fl.length) 14 (key fl) 1
  have h1 := rewinds v 0 V hVt hVp
  have h2 := rewinds A 1 W (by simpa [A,setTape] using hWt) (by simpa [A,setTape] using hWp)
  have h3 := rewinds B 5 fl (by simpa [B,A,setTape] using hFt) (by simpa [B,A,setTape] using hFp)
  have h4 := anyRuns C fl (by simp [C,setTape]) (by simp [C,setTape])
    (by simpa [C,B,A,setTape] using hKt) (by simpa [C,B,A,setTape] using hKp)
  have h5 := erases D 5 fl (by simp [D,setTape]) (by simp [D,setTape])
  have he : setTape D 5 (fun _ => blank) 0=output v V W fl := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h5
  exact ((((h1.seq h2).seq h3).seq h4).seq h5).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedGuardGadgetFinish
