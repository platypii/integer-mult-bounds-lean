module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackEliminateRow
public import IntegerMultBounds.MathlibTM2.Cover.FallbackItineraryEntries

/-! One complete elimination column on a packed matrix, using a shared pivot reciprocal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d : ℕ} {P U : Type}

def pivotCopyPorts : Fin 7 ↪ Fin 19 := ⟨![3,2,15,16,4,5,6],by decide⟩

def updateMatrix (k pivot : Fin d) (r : Fin 19 ↪ Fin T) : Pr P T Q A U :=
  emitBlocks (fun i => if i = k then copyMatrixRow pivot (pivotCopyPorts.trans r)
    else eliminateRow k (Equiv.swap k pivot i) pivot r) (List.ofFn (id : Fin d → Fin d))

theorem updateMatrix_exec (body : P → Pr P T Q A U) (r : Fin 19 ↪ Fin T) (p w : ℕ)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (k pivot : Fin d) (H : ℕ)
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (inverse : S.R (r 17) = binSyms H (pivotReciprocal p (m pivot k) w).val)
    (free : ∀ i : Fin 19, (i < 15 ∧ i ≠ 2) ∨ i = 18 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ d*((d+1)*entryTime d H)+1 ∧ Exec body (updateMatrix k pivot r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 16) (matrixWords A H (clearColumn p w k pivot m) ++ S.R (r 16))}) := by
  let emit := fun i : Fin d => if i = k then copyMatrixRow (P := P) (Q := Q) (A := A) (U := U) pivot (pivotCopyPorts.trans r)
    else eliminateRow k (Equiv.swap k pivot i) pivot r
  let words := fun i => (List.ofFn fun j => binSyms (A := A) H (clearColumn p w k pivot m i j).val).flatten
  have step (i : Fin d) (u : HS T Q A U) (suffix : List (Fin (A+4))) : ∃ z n, z.user = u.user ∧
      n ≤ (d+1)*entryTime d H ∧ Exec body (emit i) (mk u {S with R := Function.update S.R (r 16) suffix}) n
        (mk z {S with R := Function.update S.R (r 16) (words i ++ suffix)}) := by
    let D : Stacks T A := {S with R := Function.update S.R (r 16) suffix}
    have keep (i : Fin 19) (h : i ≠ 16) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
    have fresh (j : Fin 19) (h : (j < 15 ∧ j ≠ 2) ∨ j = 18) := (keep j (by omega)).trans (free j h)
    by_cases hi : i = k
    · subst i
      have ports : ∀ j : Fin 7, j = 0 ∨ 4 ≤ j → pivotCopyPorts j < 15 ∧ pivotCopyPorts j ≠ 2 := by decide
      obtain ⟨z,n,hz,hn,run⟩ := copyMatrixRow_exec body (pivotCopyPorts.trans r) m pivot H u D tail
        ((keep 15 (by decide)).trans matrix) (by change (D.R (r 2)).length = H; simp [keep 2 (by decide),modulus,length_binSyms])
        (fun j h => fresh _ (Or.inl (ports j h)))
      have le : 8*(d*d*H)+14*H+22 ≤ entryTime d H := by unfold entryTime; omega
      refine ⟨z,n,hz,?_,?_⟩
      · have := Nat.mul_le_mul_left d le
        rw [Nat.succ_mul]; unfold entryTime at *; omega
      · change Exec _ _ _ _ (mk z {D with R := Function.update D.R (r 16) (_ ++ D.R (r 16))}) at run
        simpa [emit,words,clearColumn,D,Function.update_idem] using run
    · let row := Equiv.swap k pivot i
      obtain ⟨z,n,hz,hn,run⟩ := eliminateRow_exec body r m k row pivot _ H hm u D tail
        ((keep 15 (by decide)).trans matrix) ((keep 2 (by decide)).trans modulus) ((keep 17 (by decide)).trans inverse) fresh
      refine ⟨z,n,hz,?_,?_⟩
      · have hb := matrixOffset_le H row k
        rw [Nat.succ_mul]
        unfold entryTime at *
        omega
      · simpa [emit,hi,words,clearColumn,row,D,Function.update_idem] using run
  simpa [updateMatrix,emit,words,matrixWords,List.flatMap_def,List.map_ofFn] using
    emitBlocks_exec body (r 16) emit words _ v S step (List.ofFn (id : Fin d → Fin d))

end IntegerMultBounds.MathlibTM2.Cover.Fallback
