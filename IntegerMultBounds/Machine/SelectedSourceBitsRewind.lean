import IntegerMultBounds.Machine.SelectedSourceBitsScan
import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! Return from an interior source position across its actual nonblank prefix;
there is no blank assumption at rho or at any selected subsegment boundary. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsRewind
noncomputable section
open SelectedSourceBitsCore (payload)
open SelectedSourceBitsScan (word)
open SelectedSourceBitsBank (marked)
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def atProgram (i : Fin t) := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement i)

theorem rewinds_at (caller : Tapes t a) (i : Fin t) (xs : List Bool) (p : ℕ)
    (hp : p≤xs.length) (ht : caller.tape i=word xs) (hh : caller.head i=p) :
    HoareTime (atProgram i) (fun v => v=caller)
      (fun v => v=setTape caller i (word xs) 0) (p+2) := by
  have h := ReturnOrigin.return_hoare_prefix (a := a) (fun _ => blank) 0
    ((xs.take p).map bitSymbol) ((xs.drop p).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  rw [← List.map_append,List.take_append_drop,List.length_map,List.length_take,min_eq_left hp] at h
  simp only [zero_add] at h
  have ha : Placement.active (FiniteReturnStackAt.placement i) caller =
      (ReturnOrigin.cfg (word xs) p 0).tapes := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
    rfl
  have hh := Placement.hoare_at h (FiniteReturnStackAt.placement i) caller ha
  refine hh.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

def program := seq (atProgram (a := a) (0 : Fin 8)) (atProgram (a := a) (1 : Fin 8))

theorem rewinds (xs ys : List Bool) (hs : Fin 3 → List Bool) (p : ℕ) (hp : p≤xs.length) :
    HoareTime (program (a := a))
      (fun v => v=marked (payload (word xs) (word ys) p ys.length) hs)
      (fun v => v=marked (payload (word xs) (word ys) 0 0) hs) (p+ys.length+5) := by
  have h0 := rewinds_at (marked (payload (word (a := a) xs) (word ys) p ys.length) hs) 0 xs p hp rfl rfl
  have he0 : setTape (marked (payload (word (a := a) xs) (word ys) p ys.length) hs) 0 (word xs) 0 =
      marked (payload (word xs) (word ys) 0 ys.length) hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he0] at h0
  have h1 := rewinds_at (marked (payload (word (a := a) xs) (word ys) 0 ys.length) hs) 1 ys ys.length le_rfl rfl rfl
  have he1 : setTape (marked (payload (word (a := a) xs) (word ys) 0 ys.length) hs) 1 (word ys) 0 =
      marked (payload (word xs) (word ys) 0 0) hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he1] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.SelectedSourceBitsRewind
