module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries

/-! Initialize the padding matrix from the queue's two binary constants. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T Q A M : ℕ} [NeZero M] {P U : Type}

/-- Copy a fixed-width constant for each entry. Only the matrix dimension is
compiled into the program; the binary words themselves are read from tape. -/
def identitySeed (d : ℕ) (zero one out tmp saved : Fin T) : Pr P T Q A U :=
  sequence (fun i : Fin d => sequence (fun j : Fin d =>
    bcopy (if i = j then one else zero) out tmp saved) (List.finRange d)) (List.finRange d)

theorem identitySeed_writes (body : P → Pr P T Q A U) (d H : ℕ) (zero one out tmp saved : Fin T)
    (zeroPorts : [zero,out,tmp,saved].Nodup) (onePorts : [one,out,tmp,saved].Nodup) :
    Writes body (fun R => R zero = binSyms H 0 ∧ R one = binSyms H (1 : ZMod M).val ∧
      R tmp = [] ∧ R saved = []) out (identitySeed d zero one out tmp saved)
      (matrixWords A H (1 : Matrix (Fin d) (Fin d) (ZMod M))) (d*(d*(6*H+6)+1)+1) := by
  apply matrixWords_writes
  · intro R xs ok
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at zeroPorts onePorts
    simpa [Function.update_of_ne,zeroPorts.1.1,onePorts.1.1,
      Ne.symm zeroPorts.2.1.1,Ne.symm zeroPorts.2.1.2.1] using ok
  · intro i j v S ⟨z,o,ht,hs⟩
    by_cases h : i = j
    · obtain ⟨v',hv,run⟩ := bcopy_exec body onePorts v S ht hs
      rw [o,length_binSyms] at run
      exact ⟨v',_,hv,le_rfl,by simpa [h,Matrix.one_apply,o] using run⟩
    · obtain ⟨v',hv,run⟩ := bcopy_exec body zeroPorts v S ht hs
      rw [z,length_binSyms] at run
      exact ⟨v',_,hv,le_rfl,by simpa [h,Matrix.one_apply,z] using run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
