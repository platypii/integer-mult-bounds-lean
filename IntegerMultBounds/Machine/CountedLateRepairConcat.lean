import IntegerMultBounds.Machine.CountedRepairKeyAppend

/-! Literal concatenation of the two recovered dirty words by actual scans.
Both sources and the result are returned to their original zero heads. -/
namespace IntegerMultBounds.Machine.CountedLateRepairConcat
noncomputable section
open CountedRepairKeyAppendMoves
open CountedGuardGadgetRecord (word)
open CountedRepairKeyAppend (set_bank1 set_bank2 set_bank3)

def input (V W : List Bool) := bank (fun _ => blank) (fun _ => blank) (word V) (word W) 0 0 0 0
def output (V W : List Bool) := bank (fun _ => blank) (word (V++W)) (word V) (word W) 0 0 0 0
def program := seq (seq (seq (seq copyV copyW) (backAt 1)) (backAt 2)) (backAt 3)

theorem runs (V W : List Bool) :
    HoareTime program (fun v => v=input V W) (fun v => v=output V W)
      (3*(V.length+W.length)+10) := by
  have h1 := copyV_runs (fun _ => blank) (fun _ => blank) (word W) 0 0 0 V
  simp only [zero_add] at h1
  have h2 := copyW_runs (fun _ => blank) (word V) (word V) 0 V.length V.length W
  have hk : putWord (word (a := 1) V) V.length (W.map bitSymbol)=word (V++W) := by
    have h := putWord_append_forward (a := 1) (fun _ => blank) 0 (V.map bitSymbol) (W.map bitSymbol)
    simpa only [word,List.length_map,List.map_append,zero_add] using h
  rw [hk] at h2
  let K := word (a := 1) (V++W)
  let A := bank (fun _ => blank) K (word V) (word W) 0 (V.length+W.length) V.length W.length
  have h3 := back_runs A 1 (V++W) rfl (by
    change (V.length : ℤ)+W.length=((V++W).length : ℤ)
    simp only [List.length_append]; push_cast; rfl)
  have h4 := back_runs (bank (fun _ => blank) K (word V) (word W) 0 0 V.length W.length) 2 V rfl rfl
  have h5 := back_runs (bank (fun _ => blank) K (word V) (word W) 0 0 0 W.length) 3 W rfl rfl
  simp only [A,set_bank1] at h3
  simp only [set_bank2] at h4
  simp only [set_bank3] at h5
  have hall := (((h1.seq h2).seq h3).seq h4).seq h5
  refine hall.consequence (fun _ h => h) (fun _ h => h) ?_
  simp only [List.length_append]
  omega

end
end IntegerMultBounds.Machine.CountedLateRepairConcat
