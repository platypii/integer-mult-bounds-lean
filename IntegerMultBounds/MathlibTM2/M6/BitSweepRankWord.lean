module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRadixWord
public import IntegerMultBounds.MathlibTM2.Host.IndexCode
public import IntegerMultBounds.Machine.PrefixAddressData
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Encode a record rank directly from the modular coordinate words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node RadixDigits

private theorem value_fields {q w d : ℕ} (fields : Fin d → List (Fin q))
    (width : ∀ i, (fields i).length = w) :
    value (List.ofFn fields).flatten =
      ∑ i : Fin d, value (fields i)*(q^w)^i.val := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    rw [List.ofFn_succ,List.flatten_cons,PrefixAddressData.value_append,width,Fin.sum_univ_succ]
    rw [ih (fun i => fields i.succ) (fun i => width i.succ),Finset.mul_sum]
    simp [pow_succ, mul_assoc, mul_comm]

/-- The physical field words are listed least significant first, while
the flat coordinate layout numbers its axes most significant first. -/
theorem sweepRankWord_exec {q w d T Q : ℕ} [NeZero (q^w)] {P U : Type}
    (body : P → Pr P T Q q U) (r : Fin 6 ↪ Fin T) (x : Fin d → ZMod (q^w))
    (fields : Fin d → List (Fin q)) (width : ∀ i, (fields i).length = w)
    (digits : ∀ i, value (fields i) = (x i.rev).val)
    (H : ℕ) (pos : 0 < H) (v : HS T Q q U) (S : Stacks T q)
    (input : S.R (r 0) = (List.ofFn fields).flatten.map digitSymbol)
    (clock : (S.R (r 4)).length = H) (zero : S.R (r 2) = binSyms H 0)
    (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (r i) = []) :
    ∃ z steps, z.user = v.user ∧ steps ≤ d*w*(7*H+q+15)+4 ∧
      Exec body (Cover.Fallback.radixWord r) (mk v S) steps
        (mk z {S with R := Function.update S.R (r 2) (binSyms H (FlatCoordinateLayout.rank x).val)}) := by
  have rank : value (List.ofFn fields).flatten = (FlatCoordinateLayout.rank x).val := by
    simp only [value_fields fields width,digits,FlatCoordinateLayout.rank,finFunctionFinEquiv_apply,
      FlatCoordinateLayout.finEquiv_symm_val]
  have len : (List.ofFn fields).flatten.length = d*w := by
    simp [List.length_flatten,List.map_ofFn,Function.comp_def,width,List.ofFn_const]
  simpa only [rank,len] using Cover.Fallback.radixWord_exec body r (List.ofFn fields).flatten H pos v S input clock zero free

def emitSweepRank {q T Q : ℕ} {P U : Type} (r : Fin 6 ↪ Fin T) (dst : Fin T) : Pr P T Q q U :=
  .seq (Cover.Fallback.radixWord r) (.seq (.act (.push (.rt dst) (fun _ => separator) .done))
    (.seq (bcopy (r 2) dst (r 1) (r 3)) (resetField (r 2) (r 1))))

/-- Prepend one binary source rank and its delimiter to the selector-frame
stream. The coordinate input and zero accumulator are ready for reuse. -/
theorem emitSweepRank_exec {q w d T Q : ℕ} [NeZero (q^w)] {P U : Type}
    (body : P → Pr P T Q q U) (r : Fin 6 ↪ Fin T) (dst : Fin T) (apart : ∀ i, dst ≠ r i)
    (x : Fin d → ZMod (q^w)) (fields : Fin d → List (Fin q)) (width : ∀ i, (fields i).length = w)
    (digits : ∀ i, value (fields i) = (x i.rev).val)
    (H : ℕ) (pos : 0 < H) (v : HS T Q q U) (S : Stacks T q)
    (input : S.R (r 0) = (List.ofFn fields).flatten.map digitSymbol)
    (clock : (S.R (r 4)).length = H) (zero : S.R (r 2) = binSyms H 0)
    (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (r i) = []) :
    ∃ z steps, z.user = v.user ∧ steps ≤ d*w*(7*H+q+15)+10*H+15 ∧
      Exec body (emitSweepRank r dst) (mk v S) steps (mk z {S with
        R := Function.update S.R dst
          (binSyms H (FlatCoordinateLayout.rank x).val ++ separator :: S.R dst)}) := by
  let word := binSyms (A := q) H (FlatCoordinateLayout.rank x).val
  let B := {S with R := Function.update S.R (r 2) word}
  let C := {B with R := Function.update B.R dst (separator :: B.R dst)}
  obtain ⟨u,t,user,bill,rank⟩ := sweepRankWord_exec body r x fields width digits H pos v S input clock zero free
  have push : Exec body (.act (.push (.rt dst) (fun _ => separator) .done)) (mk u B) 1 (mk u C) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,update_rt,C]
  have sep (i) : r i ≠ dst := (apart i).symm
  obtain ⟨y,hy,copy⟩ := bcopy_exec body (a := r 2) (c := dst) (t₁ := r 1) (t₂ := r 3)
    (by simp [List.nodup_cons,apart,sep,r.injective.eq_iff]) u C
    (by simp [C,B,sep,free 1 (by decide)]) (by simp [C,B,sep,free 3 (by decide)])
  let F := {C with R := Function.update C.R dst (word ++ separator :: S.R dst)}
  have acc : C.R (r 2) = word := by simp [C,B,sep]
  rw [acc] at copy
  have copied : Exec body (bcopy (r 2) dst (r 1) (r 3)) (mk u C) (6*H+6) (mk y F) := by
    simpa [F,C,B,apart,word,length_binSyms] using copy
  obtain ⟨z,hz,reset⟩ := resetField_exec (body := body) (r 2) (r 1) (by simp) y F
    (by simp [F,C,B,sep,free 1 (by decide)])
  have len : (F.R (r 2)).length = H := by simp [F,C,B,sep,word,length_binSyms]
  rw [len,← binSyms_zero_eq,← zero] at reset
  refine ⟨z,_,hz.trans (hy.trans user),?_,(Exec.seq rank (Exec.seq push (Exec.seq copied reset))).cast rfl ?_⟩
  · omega
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h : i = dst <;> by_cases k : i = r 2 <;> simp_all [F,C,B,word]

end IntegerMultBounds.MathlibTM2.M6.BitNode
