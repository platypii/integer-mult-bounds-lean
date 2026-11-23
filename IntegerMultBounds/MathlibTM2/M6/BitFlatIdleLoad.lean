module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleMerge
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead

/-! Materialize an inherited payload on the private bank used for cyclic splitting. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Shared50ModularControl (prime)

theorem loadIdleSplit_exec {T Q V m B : ℕ} [NeZero B] {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin B ↪ Fin T) (src tmp : Fin T) (apart : [src,tmp,bank 0].Nodup)
    (span : m*142080 = V) (word : Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (payload : RecordPayload src (fun _ => blank) 0 word S)
    (scratch : S.L tmp = [] ∧ S.R tmp = [])
    (free : ∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) :
    ∃ v F, Exec body (loadCompactWord src tmp (bank 0)) (mk u S) (8*V+10) (mk v F) ∧
      v.user = u.user ∧ F.R (bank 0) = List.ofFn (fun a : Fin (m*142080) => SparseRoleCircuit.encode (word (a.cast span))) ∧
      (∀ j, F.L (bank j) = []) ∧ (∀ j, j ≠ 0 → F.R (bank j) = []) ∧
      ∀ t, t ≠ bank 0 → F.L t = S.L t ∧ F.R t = S.R t := by
  subst V
  obtain ⟨v,user,run⟩ := loadCompactWord_exec body src tmp (bank 0) apart word u S
    (fun z => by simpa only [sub_zero,encodedOwnerCell] using payload z) scratch.1 scratch.2
  refine ⟨v,_,run,user,?_,fun j => (free j).1,?_,?_⟩
  · simp only [Function.update_self,(free 0).2,List.append_nil,Fin.cast_eq_self]
  · intro j ne
    simpa only [Function.update_of_ne (bank.injective.ne ne)] using (free j).2
  · intro t ne
    exact ⟨rfl,Function.update_of_ne ne ..⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
