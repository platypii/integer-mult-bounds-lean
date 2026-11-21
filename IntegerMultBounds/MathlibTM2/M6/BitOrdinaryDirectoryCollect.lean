module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIncoming

/-! Collect classified row payloads in directory order for the shared transpose. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Shared50ModularControl (prime)

theorem collectDirectoryRows_exec {ι P U : Type} {T Q N : ℕ} (body : P → Pr P T Q prime U)
    (p : Fin 6 ↪ Fin T) (record : Pr P T Q prime U) (cost : ι → ℕ)
    (valid : ι → (Fin N → ZMod 2) → Prop) (ready : List ι → Stacks T prime → Prop)
    (labels : List ι) (u : HS T Q prime U) (S : Stacks T prime) :
    let collect := Mult.ShortConv.transfer (p 1) (p 2) (p 3) (p 4)
    let inspect : Pr P T Q prime U := .act (peekR (p 0))
    let scan := inspect.seq (.loop (·.flag) ((record.seq collect).seq inspect))
    let next := fun (D : Stacks T prime) (word : Fin N → ZMod 2) =>
      {D with R := Function.update (Function.update D.R (p 2) ((D.R (p 2)).drop N)) (p 3) ((payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ D.R (p 3))}
    (∀ rs A, ready rs A → (A.R (p 0)).head?.isSome = rs.head?.isSome) →
    (∀ j rs (v : HS T Q prime U) A, ready (j::rs) A →
      ∃ y D n word, y.user = v.user ∧ n ≤ cost j ∧ Exec body record (mk v A) n (mk y D) ∧
        valid j word ∧ RecordPayload (p 2) (fun _ => blank) 0 word D ∧
        (D.R (p 1)).length = N ∧ D.R (p 4) = [] ∧ D.R (p 3) = A.R (p 3) ∧
        ready rs (next D word)) →
    ready labels S → S.R (p 3) = [] →
    (∀ A, ready [] A → A.R (p 5) = [] ∧ A.L (p 5) = []) →
    ∃ z F n rows, z.user = u.user ∧
      n ≤ (labels.map (fun j => cost j+(4*N+4))).sum + 2*labels.length + 2 + (2*(labels.length*N)+2) ∧
      Exec body (scan.seq (moveR (p 3) (p 5) id)) (mk u S) n (mk z F) ∧
      List.Forall₂ (fun j tape => ∃ word, valid j word ∧ tape = payloadWord (SparseRoleCircuit.encode ∘ word))
        labels rows ∧ F.R (p 5) = rows.flatten ∧ F.L (p 5) = [] ∧ F.R (p 3) = [] ∧
      ∃ D, ready [] D ∧ ∀ k, k ≠ p 3 → k ≠ p 5 → F.L k = D.L k ∧ F.R k = D.R k := by
  intro collect inspect scan next queued step start empty dest
  let inv := fun rs (acc : List (Fin (prime+4))) (A : Stacks T prime) => ready rs A ∧ A.R (p 3) = acc.reverse
  let effect := fun j tape => ∃ word, valid j word ∧ tape = payloadWord (SparseRoleCircuit.encode ∘ word)
  obtain ⟨y,D,n,rows,user,time,run,ordered,done⟩ := ownerDirectory_exec body (p 0) (record.seq collect)
    (fun j => cost j+(4*N+4)) effect inv (fun rs _ A h => queued rs A h.1) (by
      intro j rs acc v A h
      obtain ⟨b,B,t,word,hb,ht,recordRun,ok,read,width,tmp,stack,rest⟩ := step j rs v A h.1
      obtain ⟨z,hz,move,_⟩ := collectPayload_exec body
        ((by decide : ([1,2,3,4] : List (Fin 6)).Nodup).map p.injective)
        (SparseRoleCircuit.encode ∘ word) b B width tmp (by
          intro i
          simpa only [M8.AtomBank.arrTape,sub_zero,List.map_ofFn] using (read i).symm)
      exact ⟨z,next B word,_,_,hz.trans hb,Nat.add_le_add_right ht _,Exec.seq recordRun move,
        ⟨word,ok,rfl⟩,rest,by simp [next,stack,h.2,List.reverse_append]⟩)
    labels [] u S ⟨start,empty⟩
  have stack : D.R (p 3) = rows.flatten.reverse := by simpa using done.2
  obtain ⟨z,hz,restore⟩ := restoreOwnerRecords_exec body (p.injective.ne (by decide : (3 : Fin 6) ≠ 5))
    y D rows.flatten stack
  have len : rows.flatten.length = labels.length*N := by
    clear run time done stack start restore
    induction ordered with
    | nil => simp
    | cons h _ ih =>
      obtain ⟨word,_,rfl⟩ := h
      simp only [List.flatten_cons,List.length_append,List.length_cons,Nat.succ_mul,ih]
      simp [payloadWord,Nat.add_comm]
  refine ⟨z,_,_,rows,hz.trans user,?_,Exec.seq run restore,ordered,?_,(dest D done.1).2,?_,
    D,done.1,?_⟩
  · rw [← len]
    exact Nat.add_le_add_right time _
  · simp [(dest D done.1).1]
  · simp [p.injective.eq_iff]
  · intro k h₃ h₅
    simp [Function.update_of_ne,h₃,h₅]

end IntegerMultBounds.MathlibTM2.M6.BitNode
