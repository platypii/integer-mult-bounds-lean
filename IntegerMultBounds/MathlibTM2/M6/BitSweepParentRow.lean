module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixRead
public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Widen archived parent coefficients into the sweep evaluator's parent row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node Cover.Fallback Cover.LabelTraversal
variable {T Q A : ℕ} {P U : Type}

def writeSweepParentRow (d : ℕ) (r : Fin 7 ↪ Fin T) (width out : Fin T) : Pr P T Q A U :=
  sequence (fun i : Fin d => .seq (readMatrixWord i.val r)
    (.seq (bwiden (r 3) width (r 0) (r 4) (r 5)) (moveRightOrdered (r 3) (r 4) out))) (List.finRange d)

theorem writeSweepParentRow_writes {d M : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (r : Fin 7 ↪ Fin T) (width out : Fin T) (external : width ≠ out)
    (widthOff : ∀ i, width ≠ r i) (outOff : ∀ i, r i ≠ out)
    (parent : Fin d → ZMod M) (H : ℕ) (fits : M.size ≤ H) (tail : List (Fin (A+4))) :
    let ok := fun (R : Regs T A) =>
      R (r 2) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ tail ∧
      (R (r 1)).length = M.size ∧ (R width).length = H ∧
      ∀ j : Fin 7, j = 0 ∨ 3 ≤ j → R (r j) = []
    Writes body ok out (writeSweepParentRow d r width out)
      (List.ofFn fun i => binSyms H (parent i).val).flatten (d*(8*(d*M.size)+14*M.size+16*H+44)+1) := by
  intro ok
  have stable (R) (xs) (h : ok R) : ok (Function.update R out xs) := by
    simpa only [ok,Function.update_of_ne (outOff _),Function.update_of_ne external] using h
  have entry (i : Fin d) : Writes body ok out (.seq (readMatrixWord i.val r)
      (.seq (bwiden (r 3) width (r 0) (r 4) (r 5)) (moveRightOrdered (r 3) (r 4) out)))
      (binSyms H (parent i).val) (8*(d*M.size)+14*M.size+16*H+44) := by
    intro v S ⟨archive,hsize,bits,free⟩
    let m : Matrix (Fin 1) (Fin d) (ZMod M) := fun _ => parent
    obtain ⟨u,hu,read⟩ := readMatrixWord_exec body r m 0 i M.size v S tail
      (by simpa [matrixWords,List.ofFn_succ,m] using archive) hsize (fun j hj => free j (by omega))
    have empty := free 3 (by decide)
    simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add,m,empty,List.append_nil] at read
    let B := {S with R := Function.update S.R (r 3) (binSyms M.size (parent i).val)}
    obtain ⟨y,hy,widen⟩ := bwiden_exec (body := body) (a := r 3) (wR := width) (cnt := r 0) (t₁ := r 4) (t₂ := r 5)
      (by simp [List.nodup_cons,widthOff,Ne.symm (widthOff 3)]) fits ((parent i).val_lt.trans (Nat.lt_size_self M)) u B
      (Function.update_self ..) (by simpa [B,widthOff] using bits) (by simpa [B] using free 0 (by decide))
      (by simpa [B] using free 4 (by decide)) (by simpa [B] using free 5 (by decide))
    let F := {B with R := Function.update B.R (r 3) (binSyms H (parent i).val)}
    obtain ⟨z,hz,move⟩ := moveRightOrdered_exec (body := body) (r 3) (r 4) out (by simp) (outOff 3) (outOff 4)
      y F (by simpa [F,B] using free 4 (by decide))
    refine ⟨z,8*(i.val*M.size)+14*M.size+22+(12*H+18+(4*(F.R (r 3)).length+4)),hz.trans (hy.trans hu),?_,Exec.seq read (Exec.seq widen ?_)⟩
    · simp only [F,Function.update_self,length_binSyms]
      have := Nat.mul_le_mul_right M.size i.isLt.le
      omega
    · simpa only [F,B,Function.update_self,Function.update_idem,Function.update_of_ne (outOff 3).symm,
        ← empty,Function.update_eq_self] using move
  simpa [writeSweepParentRow,List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def] using
    sequence_writes stable entry (List.finRange d)

/-- The archived weights occupy the entire third row. The trailing rows
can therefore be prepared first and left in place while writing the prefix. -/
theorem sweepMatrixWords_parts {M : ℕ} [NeZero M] (A H : ℕ)
    (mat : Matrix (Fin 64) (Fin 64) (ZMod M)) (parent : Fin 64 → ZMod M)
    (top : ℕ) (firstRows : ∀ i : Fin 2, ∀ j, (mat (i.castLE (by decide)) j).val = top)
    (weights : ∀ j, mat 2 j = parent j) :
    matrixWords A H mat =
      (List.replicate 128 (binSyms H top)).flatten ++
      (List.ofFn fun j => binSyms H (parent j).val).flatten ++
      matrixWords A H (mat.submatrix (Fin.natAdd 3 : Fin 61 → Fin 64) id) := by
  let row := fun i : Fin 64 => (List.ofFn fun j => binSyms (A := A) H (mat i j).val).flatten
  change (List.ofFn row).flatten = _
  rw [List.ofFn_add (n := 3) (m := 61),List.flatten_append]
  apply congrArg (· ++ _)
  have topRow (i : Fin 2) : row (i.castLE (by decide)) = (List.replicate 64 (binSyms H top)).flatten := by
    simp [row,firstRows]
  have h₀ : row 0 = _ := topRow 0
  have h₁ : row 1 = _ := topRow 1
  have h₂ : row 2 = _ := congrArg (fun v : Fin 64 → ZMod M => (List.ofFn fun j => binSyms (A := A) H (v j).val).flatten)
    (funext weights)
  change row 0 ++ (row 1 ++ (row 2 ++ [])) = _
  rw [h₀,h₁,h₂,List.append_nil,← List.append_assoc,← List.flatten_append,← List.replicate_add]

end IntegerMultBounds.MathlibTM2.M6.BitNode
