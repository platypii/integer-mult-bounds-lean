module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries

/-! Initialize the padding matrix from the queue's two binary constants. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T Q A M : ℕ} [NeZero M] {P U : Type}

/-- Copy a fixed-width zero or one for each matrix entry. The program fixes the
entry pattern and reads both binary words from tape. -/
def binaryMatrixSeed {d : ℕ} (entry : Fin d → Fin d → Bool) (zero one out tmp saved : Fin T) : Pr P T Q A U :=
  sequence (fun i : Fin d => sequence (fun j : Fin d =>
    bcopy (if entry i j then one else zero) out tmp saved) (List.finRange d)) (List.finRange d)

theorem binaryMatrixSeed_writes (body : P → Pr P T Q A U) {d : ℕ} (entry : Fin d → Fin d → Bool) (H : ℕ) (zero one out tmp saved : Fin T)
    (zeroPorts : [zero,out,tmp,saved].Nodup) (onePorts : [one,out,tmp,saved].Nodup) :
    Writes body (fun R => R zero = binSyms H 0 ∧ R one = binSyms H (1 : ZMod M).val ∧
      R tmp = [] ∧ R saved = []) out (binaryMatrixSeed entry zero one out tmp saved)
      (matrixWords A H (fun i j => if entry i j then (1 : ZMod M) else 0)) (d*(d*(6*H+6)+1)+1) := by
  apply matrixWords_writes
  · intro R xs ok
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at zeroPorts onePorts
    simpa [Function.update_of_ne,zeroPorts.1.1,onePorts.1.1,
      Ne.symm zeroPorts.2.1.1,Ne.symm zeroPorts.2.1.2.1] using ok
  · intro i j v S ⟨z,o,ht,hs⟩
    by_cases h : entry i j = true
    · obtain ⟨v',hv,run⟩ := bcopy_exec body onePorts v S ht hs
      rw [o,length_binSyms] at run
      exact ⟨v',_,hv,le_rfl,by simpa [h,o] using run⟩
    · obtain ⟨v',hv,run⟩ := bcopy_exec body zeroPorts v S ht hs
      rw [z,length_binSyms] at run
      exact ⟨v',_,hv,le_rfl,by simpa [h,z] using run⟩

def identitySeed (d : ℕ) (zero one out tmp saved : Fin T) : Pr P T Q A U :=
  binaryMatrixSeed (fun i j : Fin d => decide (i = j)) zero one out tmp saved

theorem identitySeed_writes (body : P → Pr P T Q A U) (d H : ℕ) (zero one out tmp saved : Fin T)
    (zeroPorts : [zero,out,tmp,saved].Nodup) (onePorts : [one,out,tmp,saved].Nodup) :
    Writes body (fun R => R zero = binSyms H 0 ∧ R one = binSyms H (1 : ZMod M).val ∧
      R tmp = [] ∧ R saved = []) out (identitySeed d zero one out tmp saved)
      (matrixWords A H (1 : Matrix (Fin d) (Fin d) (ZMod M))) (d*(d*(6*H+6)+1)+1) := by
  have matrixEq : (fun i j : Fin d => if i = j then (1 : ZMod M) else 0) = (1 : Matrix (Fin d) (Fin d) (ZMod M)) := by
    ext i j; simp [Matrix.one_apply]
  simpa only [identitySeed,decide_eq_true_eq,matrixEq] using
    binaryMatrixSeed_writes (M := M) body (fun i j : Fin d => decide (i = j)) H zero one out tmp saved zeroPorts onePorts

/-- Generate the zero word at the width of the supplied one, then reclaim its tape. -/
def writeBinaryMatrix {d : ℕ} (entry : Fin d → Fin d → Bool) (r : Fin 5 ↪ Fin T) : Pr P T Q A U :=
  (bzero (r 1) (r 0) (r 3)).seq ((binaryMatrixSeed entry (r 0) (r 1) (r 2) (r 3) (r 4)).seq (bclear (r 0)))

theorem writeBinaryMatrix_writes (body : P → Pr P T Q A U) {d : ℕ} (entry : Fin d → Fin d → Bool)
    (H : ℕ) (r : Fin 5 ↪ Fin T) :
    Writes body (fun R => R (r 1) = binSyms H (1 : ZMod M).val ∧ R (r 0) = [] ∧ R (r 3) = [] ∧ R (r 4) = [])
      (r 2) (writeBinaryMatrix entry r) (matrixWords A H (fun i j => if entry i j then (1 : ZMod M) else 0))
      (4*H+4 + (d*(d*(6*H+6)+1)+1 + (2*H+2))) := by
  intro u S ⟨one,zero,tmp,saved⟩
  obtain ⟨y,yu,init⟩ := bzero_exec body (List.Nodup.map r.injective (by decide : ([1,0,3] : List (Fin 5)).Nodup)) u S tmp
  rw [one,length_binSyms,zero,List.append_nil] at init
  let B := {S with R := Function.update S.R (r 0) (binSyms H 0)}
  have keep (i : Fin 5) (hi : i ≠ 0) : B.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) ..
  obtain ⟨z,n,zy,time,write⟩ := binaryMatrixSeed_writes (M := M) body entry H (r 0) (r 1) (r 2) (r 3) (r 4)
    (List.Nodup.map r.injective (by decide : ([0,2,3,4] : List (Fin 5)).Nodup))
    (List.Nodup.map r.injective (by decide : ([1,2,3,4] : List (Fin 5)).Nodup)) y B
    ⟨Function.update_self ..,(keep 1 (by decide)).trans one,(keep 3 (by decide)).trans tmp,(keep 4 (by decide)).trans saved⟩
  let word := matrixWords A H (fun i j => if entry i j then (1 : ZMod M) else 0)
  let D := {B with R := Function.update B.R (r 2) (word ++ B.R (r 2))}
  have zeros : D.R (r 0) = binSyms H 0 := (Function.update_of_ne (r.injective.ne (by decide : (0 : Fin 5) ≠ 2)) ..).trans (Function.update_self ..)
  obtain ⟨v,vz,_,clear⟩ := bclear_exec body (r 0) z D
  rw [zeros,length_binSyms] at clear
  refine ⟨v,_,vz.trans (zy.trans yu),Nat.add_le_add_left (Nat.add_le_add_right time _) _,(Exec.seq init (Exec.seq write clear)).cast rfl ?_⟩
  congr 2
  funext i
  by_cases a : i = r 0
  · subst i; simp [D,B,zero]
  · by_cases b : i = r 2
    · subst i; simp [D,B,word]
    · simp [D,B,Function.update_of_ne a,Function.update_of_ne b]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
