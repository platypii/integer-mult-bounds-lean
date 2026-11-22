module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOutputCrop
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderReturnTranspose
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Load the compact crop result as an exact stack word, preserving the source tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem markedPayload {V : ℕ} (x : Fin V → ZMod 2) (L R : List (Fin (prime+4)))
    (ready : WordAtZero x L R) :
    ∀ z, readAt blank (separator::L) R (z-1) =
      RadixZeroFill.encodedBinary (List.ofFn (fun i => decide (x i = 1))) z := by
  intro z
  rw [encodedBinary_eq,← readAt_single,List.map_ofFn]
  have same (p : ℤ) : readAt blank L R p =
      readAt blank [] (List.ofFn fun i => SparseRoleCircuit.encode (x i)) p := by
    rw [ready,putWord_blank_zero,readAt_nil_left]
  rcases int_cases (z-1) with ⟨k,h⟩ | ⟨k,h⟩
  · rw [h,readAt_nonneg,readAt_nonneg]
    exact same k
  · rw [h,readAt_neg,readAt_neg]
    cases k with
    | zero => rfl
    | succ k => simpa only [readAt_neg,List.getElem?_cons_succ] using same (-((k+1 : ℕ) : ℤ))

def loadCompactWord {T Q A : ℕ} {P U : Type} (src tmp dst : Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.lt src) (fun _ => separator) .done))
    ((copyDescriptor src tmp dst).seq (.act (.pop (.lt src) (fun u _ => u) .done)))

theorem loadCompactWord_exec {T Q V : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (src tmp dst : Fin T) (apart : [src,tmp,dst].Nodup) (x : Fin V → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime) (ready : WordAtZero x (S.L src) (S.R src))
    (left : S.L tmp = []) (right : S.R tmp = []) :
    ∃ v, v.user = u.user ∧ Exec body (loadCompactWord src tmp dst) (mk u S) (8*V+10)
      (mk v {S with R := Function.update S.R dst ((List.ofFn fun i => SparseRoleCircuit.encode (x i))++S.R dst)}) := by
  let D := {S with L := Function.update S.L src (separator::S.L src)}
  have ne : tmp ≠ src := by intro eq; subst tmp; simp at apart
  have mark : Exec body (.act (.push (.lt src) (fun _ => separator) .done)) (mk u S) 1 (mk u D) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,D,get_lt,update_lt]
  obtain ⟨v,same,run⟩ := copyDescriptor_exec body apart (List.ofFn fun i => decide (x i = 1)) u D
    (by simpa [D] using markedPayload x _ _ ready) (by simp [D,Function.update_of_ne ne,left]) right
  refine ⟨v,same,(Exec.seq mark (Exec.seq run (Exec.act _ _))).cast ?_ ?_⟩
  · simp; omega
  · simp only [Action.run,mk_var,mk_stk,get_lt,update_lt,List.map_ofFn]
    simp [D,Function.update_idem,Function.comp_def,SparseRoleCircuit.encode]

end IntegerMultBounds.MathlibTM2.M6.BitNode
