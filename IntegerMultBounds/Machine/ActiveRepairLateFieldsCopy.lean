import IntegerMultBounds.Machine.WordBankCleanup
import IntegerMultBounds.Machine.CountedRepairKeyCleanup

/-! Paid copying of an extracted unmarked binary word to blank workspace,
with both heads restored and every complementary tape retained. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFieldsCopy
noncomputable section
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)

private theorem blank_word (a : ℕ) (p : ℤ) (n : ℕ) :
    putWord (fun _ => (blank : Fin (a+4))) p (List.replicate n blank) = (fun _ => blank) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,putWord]
    rw [ih (p+1)]
    rw [show Function.update (fun _ => (blank : Fin (a+4))) p blank = (fun _ => blank) by
      funext z; simp]


def program (src dst : Fin t) (hne : src ≠ dst) (ht : 2≤t) :=
  WordBankCleanup.replaceProgram src dst hne ht 1

theorem runs (v : Tapes t 1) (src dst : Fin t) (hne : src ≠ dst) (ht : 2≤t)
    (xs : List Bool) (hs : v.tape src=word xs) (hd : v.tape dst=fun _ => blank)
    (ps : v.head src=0) (pd : v.head dst=0) :
    HoareTime (program src dst hne ht) (fun z => z=v)
      (fun z => z=WordBankCleanup.write v dst (word xs)) (3*xs.length+6) := by
  have h := WordBankCleanup.replace_hoare v src dst hne ht (fun _ => blank) (fun _ => blank)
    (xs.map bitSymbol) (List.replicate xs.length blank) (by simp)
    (by simpa only [ps,word] using hs) (by rw [pd,blank_word]; exact hd)
    (ReturnOrigin.bits_nonblank xs) rfl rfl rfl
  simpa only [program,ps,pd,List.length_map,word] using h

end
end IntegerMultBounds.Machine.ActiveRepairLateFieldsCopy
