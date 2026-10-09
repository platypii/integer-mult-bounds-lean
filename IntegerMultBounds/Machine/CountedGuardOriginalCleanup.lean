import IntegerMultBounds.Machine.CountedGuardGadget
import IntegerMultBounds.Machine.WordBankCleanup

/-! Actual scan-and-erase cleanup of the three synthesized guard constants.
The fixed fifteen-tape program retains the result and every source/header. -/
namespace IntegerMultBounds.Machine.CountedGuardOriginalCleanup
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

def clearAt (i : Fin 15) := Placement.placed (WordBankCleanup.eraseProgram a) (FiniteReturnStackAt.placement i)

theorem clears (v : Tapes 15 a) (i : Fin 15) (xs : List Bool)
    (ht : v.tape i=word xs) (hp : v.head i=0) :
    HoareTime (clearAt (a := a) i) (fun w => w=v)
      (fun w => w=setTape v i (fun _ => blank) 0) (2*xs.length+3) := by
  have h0 := WordBankCleanup.erase_hoare (a := a) 0 (xs.map bitSymbol) (ReturnOrigin.bits_nonblank xs)
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  rfl

def output (v : Tapes 15 a) : Tapes 15 a :=
  setTape (setTape (setTape v 2 (fun _ => blank) 0) 3 (fun _ => blank) 0) 4 (fun _ => blank) 0

def program := seq (seq (clearAt (a := a) 2) (clearAt 3)) (clearAt 4)

theorem runs (v : Tapes 15 a) (C1 C2 C3 : List Bool)
    (h1t : v.tape 2=word C1) (h1p : v.head 2=0)
    (h2t : v.tape 3=word C2) (h2p : v.head 3=0)
    (h3t : v.tape 4=word C3) (h3p : v.head 4=0) :
    HoareTime (program (a := a)) (fun w => w=v) (fun w => w=output v)
      (2*C1.length+2*C2.length+2*C3.length+11) := by
  let A := setTape v 2 (fun _ => blank) 0
  let B := setTape A 3 (fun _ => blank) 0
  have h1 := clears v 2 C1 h1t h1p
  have h2 := clears A 3 C2 (by simpa [A,setTape] using h2t) (by simpa [A,setTape] using h2p)
  have h3 := clears B 4 C3 (by simpa [B,A,setTape] using h3t) (by simpa [B,A,setTape] using h3p)
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedGuardOriginalCleanup
