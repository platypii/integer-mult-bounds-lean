module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord

/-! The correction between the two address fields consists of forward shears. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix M8.Exchange
open IntegerMultBounds.Swap.Shear (State)
variable {d : ℕ} {R : Type*} [CommRing R]

def crossEntryShear (K : Matrix (Fin d) (Fin d) R) (i j : Fin d) : RowOp (d+d) R :=
  .shear (j.castAdd d) (i.natAdd d) (by change j.val < d+i.val; omega) (K i j)

def crossRowWord (K : Matrix (Fin d) (Fin d) R) (i : Fin d) :=
  (List.finRange d).map (crossEntryShear K i)

def crossWord (K : Matrix (Fin d) (Fin d) R) := (List.finRange d).flatMap (crossRowWord K)

private theorem crossRow_apply (K : Matrix (Fin d) (Fin d) R) (i : Fin d) (js : List (Fin d))
    (x y : Fin d → R) :
    (js.map (crossEntryShear K i)).foldl (fun z op => op.apply z) (Fin.append x y) =
      Fin.append x (Function.update y i (y i+(js.map fun j => K i j*x j).sum)) := by
  induction js generalizing y with
  | nil => simp
  | cons j js ih =>
    let y' := Function.update y i (y i+K i j*x j)
    have step : (crossEntryShear K i j).apply (Fin.append x y) = Fin.append x y' := by
      funext t
      refine Fin.addCases (fun a => ?_) (fun b => ?_) t
      · have ne : a.castAdd d ≠ i.natAdd d := fun eq => by
          have := congrArg Fin.val eq
          change a.val = d+i.val at this
          omega
        simp only [crossEntryShear,RowOp.apply,Function.update_of_ne ne,Fin.append_left]
      · by_cases eq : b = i
        · subst b; simp only [crossEntryShear,RowOp.apply,y',Function.update_self,Fin.append_left,Fin.append_right]
        · have ne : b.natAdd d ≠ i.natAdd d := fun h => eq (Fin.ext (by have := congrArg Fin.val h; change d+b.val = d+i.val at this; omega))
          simp only [crossEntryShear,RowOp.apply,y',Function.update_of_ne ne,Fin.append_right,Function.update_of_ne eq]
    simp only [List.map_cons,List.foldl_cons,step,ih,List.sum_cons]
    simp [y',add_assoc]

private theorem crossRows_apply (K : Matrix (Fin d) (Fin d) R) (rows : List (Fin d)) (hd : rows.Nodup)
    (x y : Fin d → R) :
    (rows.flatMap (crossRowWord K)).foldl (fun z op => op.apply z) (Fin.append x y) =
      Fin.append x (fun i => if i ∈ rows then y i+(K.mulVec x) i else y i) := by
  induction rows generalizing y with
  | nil => simp
  | cons i rows ih =>
    rw [List.flatMap_cons,List.foldl_append]
    simp only [crossRowWord,crossRow_apply]
    rw [ih hd.tail]
    congr 1
    funext j
    by_cases eq : j = i
    · subst j
      simp [hd.notMem,List.finRange,List.map_ofFn,List.sum_ofFn,Function.comp_def,mulVec,dotProduct]
    · simp [eq]

theorem crossWord_apply (K : Matrix (Fin d) (Fin d) R) (s : State (Fin d) R) :
    (crossWord K).foldl (fun z op => op.apply z) (Fin.append s.1 s.2) =
      Fin.append (cross K s).1 (cross K s).2 := by
  change _ = Fin.append s.1 (fun i => s.2 i + (K.mulVec s.1) i)
  simpa [crossWord] using crossRows_apply K (List.finRange d) (List.nodup_finRange d) s.1 s.2

omit [CommRing R] in
theorem crossWord_children (K : Matrix (Fin d) (Fin d) R) :
    ((crossWord K).map RowOp.children).sum = 0 := by
  apply List.sum_eq_zero_iff.mpr
  intro n hn
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hn
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hop
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  rfl

omit [CommRing R] in
theorem crossWord_length (K : Matrix (Fin d) (Fin d) R) : (crossWord K).length = d*d := by
  simp [crossWord,crossRowWord,List.length_flatMap]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
