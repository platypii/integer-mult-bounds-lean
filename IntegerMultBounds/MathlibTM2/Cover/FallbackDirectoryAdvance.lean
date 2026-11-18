module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalConjugation
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRewind

/-! Collect a computed matrix and advance past the complete directory record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

def advanceDirectory {A : ℕ} (m : ℕ) (r : Fin 6 ↪ Fin T) : Pr P T Q A U :=
  .seq (usub (r 0) (r 2) (r 3)) (dropWords (r 1) (r 2) (r 3) (m*m))

theorem advanceDirectory_exec (body : P → Pr P T Q prime U) (r : Fin 6 ↪ Fin T) (m w j : ℕ)
    (ancestor tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime)
    (dir : S.R (r 2) = ancestor ++ (LabelDirectory.digits m w j).map RadixDigits.digitSymbol ++ tail)
    (prefixWidth : (S.R (r 0)).length = ancestor.length) (width : (S.R (r 1)).length = w)
    (blank : S.R (r 3) = []) :
    ∃ z, z.user = v.user ∧ Exec body (advanceDirectory m r) (mk v S)
      (4*ancestor.length+4+(m*m*(4*w+4)+1)) (mk z {S with R := Function.update S.R (r 2) tail}) := by
  obtain ⟨u,hu,skip⟩ := usub_exec body (a := r 0) (b := r 2) (t := r 3) (by simp) (by simp) (by simp) v S blank
  rw [prefixWidth,dir,List.append_assoc,List.drop_left] at skip
  let digits := (LabelDirectory.digits m w j).map RadixDigits.digitSymbol
  let B := {S with R := Function.update S.R (r 2) (digits ++ tail)}
  obtain ⟨z,hz,rest⟩ := dropWords_exec body (width := r 1) (src := r 2) (tmp := r 3) (by simp) (by simp)
    (by simp) (m*m) w u B (by simpa [B] using width) (by simpa [B] using blank)
  have len : digits.length = m*m*w := by simp [digits,LabelDirectory.digits,Nat.mul_comm]
  simp only [B,Function.update_self,← len,List.drop_left,Function.update_idem] at rest
  exact ⟨z,hz.trans hu,Exec.seq skip rest⟩

theorem collectDirectory_exec (body : P → Pr P T Q prime U) (r : Fin 6 ↪ Fin T) (m w j : ℕ)
    (ok : Regs T prime → Prop) (emit : Pr P T Q prime U) (word ancestor tail : List (Fin (prime+4)))
    (cost : ℕ) (writer : Writes body ok (r 4) emit word cost)
    (v : HS T Q prime U) (S : Stacks T prime) (ready : ok S.R) (empty : S.R (r 4) = [])
    (dir : S.R (r 2) = ancestor ++ (LabelDirectory.digits m w j).map RadixDigits.digitSymbol ++ tail)
    (prefixWidth : (S.R (r 0)).length = ancestor.length) (width : (S.R (r 1)).length = w)
    (blank : S.R (r 3) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ cost+2*word.length+2+(4*ancestor.length+4+(m*m*(4*w+4)+1)) ∧
      Exec body (.seq emit (.seq (moveR (r 4) (r 5) id) (advanceDirectory m r))) (mk v S) n
        (mk z {S with R := Function.update (Function.update S.R (r 5) (word.reverse ++ S.R (r 5))) (r 2) tail}) := by
  obtain ⟨u,n,hu,hn,write⟩ := writer v S ready
  rw [empty,List.append_nil] at write
  let B := {S with R := Function.update S.R (r 4) word}
  obtain ⟨y,hy,move⟩ := moveR_exec body (r 4) (r 5) (by simp) id u B
  let F := {S with R := Function.update S.R (r 5) (word.reverse ++ S.R (r 5))}
  have moved : movedR B.R (r 4) (r 5) id (B.R (r 4)) = F.R := by
    simp [F,B,movedR,← empty]
  rw [moved] at move
  obtain ⟨z,hz,advance⟩ := advanceDirectory_exec body r m w j ancestor tail y F
    (by simpa [F] using dir) (by simpa [F] using prefixWidth) (by simpa [F] using width) (by simpa [F] using blank)
  exact ⟨z,_,hz.trans (hy.trans hu),by simp [B]; omega,Exec.seq write (Exec.seq move advance)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
