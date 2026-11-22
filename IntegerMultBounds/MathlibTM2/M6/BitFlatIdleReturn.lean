module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLoad

/-! Return the merged prefix to its owner without traversing padding on either tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host Node Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)

theorem returnIdlePayload_exec {P U : Type} {T Q V : ℕ} (body : P → Pr P T Q prime U)
    {count src dst saved tmp : Fin T} (apart : [count,src,dst,saved,tmp].Nodup)
    (old changed : Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (before : RecordPayload dst (fun _ => blank) 0 old S)
    (merged : RecordPayload src (fun _ => blank) 0 changed S)
    (len : (S.R count).length = V) (hs : S.R saved = []) (ht : S.R tmp = []) :
    ∃ z F, Exec body ((usub count dst tmp).seq (movePrefix count src dst saved tmp))
      (mk u S) (10*V+10) (mk z F) ∧ z.user = u.user ∧
      RecordPayload dst (fun _ => blank) 0 changed F ∧ F.R src = (S.R src).drop V ∧
      (∀ t, F.L t = S.L t) ∧ ∀ t, t ≠ dst → t ≠ src → F.R t = S.R t := by
  have regs := apart
  regs_ne regs
  obtain ⟨v,user,drop⟩ := usub_exec body ‹count ≠ dst› ‹count ≠ tmp› ‹dst ≠ tmp› u S ht
  rw [len] at drop
  let D := {S with R := Function.update S.R dst ((S.R dst).drop V)}
  have empty (j : ℤ) : readAt blank (D.L dst) (D.R dst) j = blank := by
    simp only [D,Function.update_self]
    rcases int_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · have h := before ((V+k : ℕ) : ℤ)
      rw [encodedOwnerCell,sub_zero,readAt_nonneg,putWord_outside _ _ _ _ (.inr (by simp))] at h
      rw [readAt_nonneg,List.getElem?_drop]
      exact h
    · have h := before (-(k+1 : ℕ))
      rw [encodedOwnerCell,sub_zero,readAt_neg,putWord_outside _ _ _ _ (.inl (by omega))] at h
      rwa [readAt_neg]
  obtain ⟨z,F,same,load,frame,rep⟩ := loadPayload_exec body apart (SparseRoleCircuit.encode ∘ changed)
    ((S.R src).drop V) v D (by simpa [D,Function.update_of_ne ‹src ≠ dst›] using payload_prefix_of_read changed _ _ _ _ merged)
    (by simpa [D,Function.update_of_ne ‹count ≠ dst›] using len) empty
    (by simpa [D,Function.update_of_ne ‹dst ≠ saved›.symm] using hs)
    (by simpa [D,Function.update_of_ne ‹dst ≠ tmp›.symm] using ht)
  refine ⟨z,F,(Exec.seq drop load).cast (by omega) rfl,same.trans user,?_,?_,?_,?_⟩
  · intro j
    simpa only [sub_zero,M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using (rep j).symm
  · simp [frame,Function.update_of_ne ‹src ≠ dst›]
  · intro t; rw [frame]
  · intro t hd hsrc
    simp [frame,D,Function.update_of_ne hd,Function.update_of_ne hsrc]

end IntegerMultBounds.MathlibTM2.M6.BitNode
