module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLoad
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup

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

/-- The merged word supplies its own length counter. After writeback the
counter and both scratch tapes have their entry stacks. -/
theorem returnIdlePayloadFromBlank_exec {P U : Type} {T Q V : ℕ} (body : P → Pr P T Q prime U)
    {count src dst saved tmp : Fin T} (apart : [count,src,dst,saved,tmp].Nodup)
    (old changed : Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (before : RecordPayload dst (fun _ => blank) 0 old S)
    (merged : RecordPayload src (fun _ => blank) 0 changed S)
    (hc : S.R count = []) (hs : S.R saved = []) (hlt : S.L tmp = []) (ht : S.R tmp = []) :
    ∃ z F, Exec body ((loadCompactWord src tmp count).seq
      (((usub count dst tmp).seq (movePrefix count src dst saved tmp)).seq (bclear count)))
      (mk u S) (20*V+22) (mk z F) ∧ z.user = u.user ∧
      RecordPayload dst (fun _ => blank) 0 changed F ∧ F.R src = (S.R src).drop V ∧
      (∀ t, F.L t = S.L t) ∧ ∀ t, t ≠ dst → t ≠ src → F.R t = S.R t := by
  have regs := apart
  regs_ne regs
  let bits := List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (changed i)
  let D := {S with R := Function.update S.R count bits}
  obtain ⟨v,user,copy⟩ := loadCompactWord_exec body src tmp count (by simp [‹src ≠ tmp›,‹count ≠ src›.symm,‹count ≠ tmp›.symm]) changed u S
    (fun j => by simpa only [sub_zero,encodedOwnerCell] using merged j) hlt ht
  simp only [hc,List.append_nil] at copy
  have read {t : Fin T} {word : Fin V → ZMod 2} (ne : t ≠ count)
      (h : RecordPayload t (fun _ => blank) 0 word S) : RecordPayload t (fun _ => blank) 0 word D := by
    simpa only [D,RecordPayload,Function.update_of_ne ne] using h
  obtain ⟨y,G,write,same,out,drain,left,keep⟩ := returnIdlePayload_exec body apart old changed v D
    (read ‹count ≠ dst›.symm before) (read ‹count ≠ src›.symm merged) (by simp [D,bits])
    (by simpa [D,Function.update_of_ne ‹count ≠ saved›.symm] using hs)
    (by simpa [D,Function.update_of_ne ‹count ≠ tmp›.symm] using ht)
  have counter := keep count ‹count ≠ dst› ‹count ≠ src›
  obtain ⟨z,done,_,clear⟩ := bclear_exec body count y G
  simp only [counter,D,Function.update_self,bits,List.length_ofFn] at clear
  refine ⟨z,_,(Exec.seq copy (Exec.seq write clear)).cast (by omega) rfl,done.trans (same.trans user),?_,?_,left,?_⟩
  · simpa only [RecordPayload,Function.update_of_ne ‹count ≠ dst›.symm] using out
  · simpa only [D,Function.update_of_ne ‹count ≠ src›.symm] using drain
  · intro t hd hsrc
    by_cases eq : t = count
    · subst t; simpa only [Function.update_self] using hc.symm
    · simpa only [D,Function.update_of_ne eq] using keep t hd hsrc

/-- Return the result and release the private bank. The cleanup bill is
bounded by the symbols on the bank at merge exit, independently of call time. -/
theorem returnIdleBank_exec {P U : Type} {T Q V : ℕ} (body : P → Pr P T Q prime U)
    {count src dst saved tmp : Fin T} (apart : [count,src,dst,saved,tmp].Nodup)
    (bank : List (Fin T)) (distinct : bank.Nodup) (inside : src ∈ bank) (outside : dst ∉ bank)
    (old changed : Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime)
    (before : RecordPayload dst (fun _ => blank) 0 old S)
    (merged : RecordPayload src (fun _ => blank) 0 changed S)
    (hc : S.R count = []) (hs : S.R saved = []) (hlt : S.L tmp = []) (ht : S.R tmp = []) :
    let write := (loadCompactWord src tmp count).seq
      (((usub count dst tmp).seq (movePrefix count src dst saved tmp)).seq (bclear count))
    ∃ z F n, Exec body (write.seq (clearWorkTapes bank)) (mk u S) n (mk z F) ∧
      n ≤ 20*V+23+(bank.map fun j => 4*(S.L j).length+2*(S.R j).length+4).sum ∧
      z.user = u.user ∧ RecordPayload dst (fun _ => blank) 0 changed F ∧
      (∀ j ∈ bank, F.L j = [] ∧ F.R j = []) ∧
      ∀ j, j ≠ dst → j ∉ bank → F.L j = S.L j ∧ F.R j = S.R j := by
  intro write
  obtain ⟨v,D,run,user,payload,drain,left,keep⟩ := returnIdlePayloadFromBlank_exec body apart old changed u S
    before merged hc hs hlt ht
  obtain ⟨z,same,clear⟩ := clearWorkTapes_exec body bank distinct v D
  have sum {js : List (Fin T)} (away : dst ∉ js) :
      (js.map fun j => 4*(D.L j).length+2*(D.R j).length+4).sum ≤
      (js.map fun j => 4*(S.L j).length+2*(S.R j).length+4).sum := by
    induction js with
    | nil => exact le_rfl
    | cons j js ih =>
      simp only [List.mem_cons,not_or] at away
      simp only [List.map_cons,List.sum_cons]
      apply Nat.add_le_add _ (ih away.2)
      rw [left]
      by_cases eq : j = src
      · subst j; rw [drain,List.length_drop]; omega
      · rw [keep j (fun h => away.1 h.symm) eq]
  refine ⟨z,_,_,Exec.seq run clear,by have := sum outside; omega,same.trans user,?_,?_,?_⟩
  · simpa only [RecordPayload,ite_eq_right outside] using payload
  · intro j hj
    simp only [ite_eq_left hj,and_self]
  · intro j ne away
    exact ⟨(ite_eq_right away).trans (left j),(ite_eq_right away).trans
      (keep j ne (fun eq => away (eq ▸ inside)))⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
