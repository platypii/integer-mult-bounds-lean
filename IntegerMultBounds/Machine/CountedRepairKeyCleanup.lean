import IntegerMultBounds.Machine.CountedRepairKeyWrite

/-! Physical erasure of all nine generated words after conditional key writing. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyCleanup
noncomputable section
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def clearAt (i : Fin 30) := Placement.placed (WordBankCleanup.eraseProgram 1) (FiniteReturnStackAt.placement i)

theorem clears (v : Tapes 30 1) (i : Fin 30) (xs : List Bool)
    (ht : v.tape i=word xs) (hp : v.head i=0) :
    HoareTime (clearAt i) (fun w => w=v)
      (fun w => w=setTape v i (fun _ => blank) 0) (2*xs.length+3) := by
  have h0 := WordBankCleanup.erase_hoare (a := 1) 0 (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  rfl

def output (v : Tapes 30 1) :=
  setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (setTape (v) 0 (fun _ => blank) 0) 1 (fun _ => blank) 0) 3 (fun _ => blank) 0) 4 (fun _ => blank) 0) 5 (fun _ => blank) 0) 6 (fun _ => blank) 0) 8 (fun _ => blank) 0) 29 (fun _ => blank) 0) 28 (fun _ => blank) 0

def program := seq (seq (seq (seq (seq (seq (seq (seq (clearAt 0) (clearAt 1)) (clearAt 3)) (clearAt 4)) (clearAt 5)) (clearAt 6)) (clearAt 8)) (clearAt 29)) (clearAt 28)

theorem runs (v : Tapes 30 1) (x0 x1 x3 x4 x5 x6 x8 x29 x28 : List Bool)
    (h0t : v.tape 0=word x0) (h0p : v.head 0=0)
    (h1t : v.tape 1=word x1) (h1p : v.head 1=0)
    (h3t : v.tape 3=word x3) (h3p : v.head 3=0)
    (h4t : v.tape 4=word x4) (h4p : v.head 4=0)
    (h5t : v.tape 5=word x5) (h5p : v.head 5=0)
    (h6t : v.tape 6=word x6) (h6p : v.head 6=0)
    (h8t : v.tape 8=word x8) (h8p : v.head 8=0)
    (h29t : v.tape 29=word x29) (h29p : v.head 29=0)
    (h28t : v.tape 28=word x28) (h28p : v.head 28=0)
    : HoareTime program (fun w => w=v) (fun w => w=output v)
      (2*(x0.length+x1.length+x3.length+x4.length+x5.length+x6.length+x8.length+x29.length+x28.length)+35) := by
  let A1 := setTape v 0 (fun _ => blank) 0
  have h1 := clears v 0 x0 h0t h0p
  let A2 := setTape A1 1 (fun _ => blank) 0
  have h2 := clears A1 1 x1 (by simpa [A1,setTape] using h1t) (by simpa [A1,setTape] using h1p)
  let A3 := setTape A2 3 (fun _ => blank) 0
  have h3 := clears A2 3 x3 (by simpa [A2,A1,setTape] using h3t) (by simpa [A2,A1,setTape] using h3p)
  let A4 := setTape A3 4 (fun _ => blank) 0
  have h4 := clears A3 4 x4 (by simpa [A3,A2,A1,setTape] using h4t) (by simpa [A3,A2,A1,setTape] using h4p)
  let A5 := setTape A4 5 (fun _ => blank) 0
  have h5 := clears A4 5 x5 (by simpa [A4,A3,A2,A1,setTape] using h5t) (by simpa [A4,A3,A2,A1,setTape] using h5p)
  let A6 := setTape A5 6 (fun _ => blank) 0
  have h6 := clears A5 6 x6 (by simpa [A5,A4,A3,A2,A1,setTape] using h6t) (by simpa [A5,A4,A3,A2,A1,setTape] using h6p)
  let A7 := setTape A6 8 (fun _ => blank) 0
  have h7 := clears A6 8 x8 (by simpa [A6,A5,A4,A3,A2,A1,setTape] using h8t) (by simpa [A6,A5,A4,A3,A2,A1,setTape] using h8p)
  let A8 := setTape A7 29 (fun _ => blank) 0
  have h8 := clears A7 29 x29 (by simpa [A7,A6,A5,A4,A3,A2,A1,setTape] using h29t) (by simpa [A7,A6,A5,A4,A3,A2,A1,setTape] using h29p)
  let A9 := setTape A8 28 (fun _ => blank) 0
  have h9 := clears A8 28 x28 (by simpa [A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h28t) (by simpa [A8,A7,A6,A5,A4,A3,A2,A1,setTape] using h28p)
  exact ((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRepairKeyCleanup
