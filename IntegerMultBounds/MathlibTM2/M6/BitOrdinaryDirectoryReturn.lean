module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryCall

/-! Restore bypassed rows after a single directory-wide recursive transpose. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Shared50ModularControl (prime)

/-- Consume one row from each queue and append the selected row to the reversed output. -/
noncomputable def selectDirectoryRow {P U : Type} {T Q : ℕ} (count src skip dst tmp : Fin T) : Pr P T Q prime U :=
  (Node.usub count skip tmp).seq (Mult.ShortConv.transfer count src dst tmp)

private theorem selectDirectoryRow_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (count src skip dst tmp : Fin T) (distinct : [count,src,skip,dst,tmp].Nodup)
    (u : HS T Q prime U) (S : Stacks T prime) (xs ys tail rest : List (Fin (prime+4)))
    (input : S.R src = xs ++ tail) (discard : S.R skip = ys ++ rest)
    (width : (S.R count).length = xs.length) (same : ys.length = xs.length) (free : S.R tmp = []) :
    ∃ z, z.user = u.user ∧ Exec body (selectDirectoryRow count src skip dst tmp) (mk u S) (8*xs.length+8)
      (mk z {S with R := Function.update (Function.update (Function.update S.R skip rest) src tail) dst (xs.reverse ++ S.R dst)}) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at distinct
  obtain ⟨⟨cs,ck,cd,ct⟩,⟨sk,sd,st⟩,⟨kd,kt⟩,dt⟩ := distinct
  obtain ⟨v,user,drop⟩ := Node.usub_exec body ck ct kt u S free
  rw [discard,width,← same,List.drop_left] at drop
  let D := {S with R := Function.update S.R skip rest}
  have run := Mult.ShortConv.transfer_exec (body := body) (count := count) (src := src) (dst := dst) (tmp := tmp)
    (by simp [cs,cd,ct,sd,st,dt]) v D xs tail (by simpa [D,Function.update_of_ne sk] using input)
    (by simpa [D,Function.update_of_ne ck] using width) (by simpa [D,Function.update_of_ne (Ne.symm kt)] using free)
  obtain ⟨z,hz,move⟩ := run
  refine ⟨z,hz.trans user,?_⟩
  simpa only [selectDirectoryRow,D,Function.update_of_ne (Ne.symm kd),same,show 4*xs.length+4+(4*xs.length+4) = 8*xs.length+8 by omega]
    using Exec.seq drop move

/-- Registers 0 and 1 hold the returned child and the saved bypass stream.
Registers 5 and 6 hold the live and exceptional bits in directory order. -/
noncomputable def directoryReturn {T Q : ℕ} {P U : Type} (p : Fin 7 ↪ Fin T) : Pr P T Q prime U :=
  let keepChild := selectDirectoryRow (p 3) (p 0) (p 1) (p 2) (p 4)
  let keepSaved := selectDirectoryRow (p 3) (p 1) (p 0) (p 2) (p 4)
  let row := ownerDispatch (p 5) (p 6) keepChild keepSaved keepSaved
  let peek : Pr P T Q prime U := .act (peekR (p 5))
  (peek.seq (.loop (·.flag) (row.seq peek))).seq (moveR (p 2) (p 0) id)

/-- Both queues advance once per row. Only live ordinary rows take their
child output. Exceptional and padding rows retain their saved contents. -/
theorem directoryReturn_exec {ι P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (p : Fin 7 ↪ Fin T) (live bad : ι → Bool)
    (child saved : ι → List (Fin (prime+4))) (N : ℕ)
    (childWidth : ∀ j, (child j).length = N) (savedWidth : ∀ j, (saved j).length = N)
    (labels : List ι) (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime)
    (children : S.R (p 0) = labels.flatMap child ++ tail) (backup : S.R (p 1) = labels.flatMap saved)
    (empty : S.R (p 2) = []) (width : (S.R (p 3)).length = N) (tmp : S.R (p 4) = [])
    (liveBits : S.R (p 5) = labels.map (fun j => bitSymbol (live j)))
    (badBits : S.R (p 6) = labels.map (fun j => bitSymbol (bad j))) :
    let result := fun j => if live j && !bad j then child j else saved j
    ∃ z F t, z.user = u.user ∧ t ≤ labels.length*(10*N+14)+4 ∧
      Exec body (directoryReturn p) (mk u S) t (mk z F) ∧ F.R (p 0) = labels.flatMap result ++ tail ∧
      F.R (p 1) = [] ∧ F.R (p 2) = [] ∧ F.R (p 5) = [] ∧ F.R (p 6) = [] ∧ F.L = S.L ∧
      ∀ k, k ∉ [p 0,p 1,p 2,p 5,p 6] → F.R k = S.R k := by
  intro result
  let keepChild : Pr P T Q prime U := selectDirectoryRow (p 3) (p 0) (p 1) (p 2) (p 4)
  let keepSaved : Pr P T Q prime U := selectDirectoryRow (p 3) (p 1) (p 0) (p 2) (p 4)
  let row := ownerDispatch (p 5) (p 6) keepChild keepSaved keepSaved
  let ready := fun (rs : List ι) (acc : List (Fin (prime+4))) (A : Stacks T prime) =>
    A.R (p 0) = rs.flatMap child ++ tail ∧ A.R (p 1) = rs.flatMap saved ∧ A.R (p 2) = acc.reverse ∧
    A.R (p 5) = rs.map (fun j => bitSymbol (live j)) ∧ A.R (p 6) = rs.map (fun j => bitSymbol (bad j)) ∧
    A.L = S.L ∧ ∀ k, k ∉ [p 0,p 1,p 2,p 5,p 6] → A.R k = S.R k
  have step (j rs acc v A) (h : ready (j::rs) acc A) :
      ∃ z F n bits, z.user = v.user ∧ n ≤ 8*N+12 ∧ Exec body row (mk v A) n (mk z F) ∧
        bits = result j ∧ ready rs (acc ++ bits) F := by
    obtain ⟨input,copy,stack,ls,bs,left,frame⟩ := h
    simp only [List.flatMap_cons,List.append_assoc] at input copy
    let B := {A with R := Function.update A.R (p 5) (rs.map fun i => bitSymbol (live i))}
    let E := {B with R := Function.update B.R (p 6) (rs.map fun i => bitSymbol (bad i))}
    have cell (k : Fin 7) (a : k ≠ 5) (b : k ≠ 6) : E.R (p k) = A.R (p k) := by
      simp [E,B,Function.update_of_ne,p.injective.ne a,p.injective.ne b]
    have count := (congrArg List.length ((cell 3 (by decide) (by decide)).trans
      (frame _ (by simp [p.injective.eq_iff])))).trans width
    have free := (cell 4 (by decide) (by decide)).trans ((frame _ (by simp [p.injective.eq_iff])).trans tmp)
    have dispatch := @ownerDispatch_exec P U T Q body (p 5) (p 6) (p.injective.ne (by decide)) keepChild keepSaved keepSaved
      (live j) (bad j) v A _ _ ls bs
    have childRun := selectDirectoryRow_exec body (p 3) (p 0) (p 1) (p 2) (p 4)
      ((by decide : ([3,0,1,2,4] : List (Fin 7)).Nodup).map p.injective) {v with flag := bad j} E
      (child j) (saved j) _ _ ((cell 0 (by decide) (by decide)).trans input) ((cell 1 (by decide) (by decide)).trans copy)
      (count.trans (childWidth j).symm) ((savedWidth j).trans (childWidth j).symm) free
    have savedRun := selectDirectoryRow_exec body (p 3) (p 1) (p 0) (p 2) (p 4)
      ((by decide : ([3,1,0,2,4] : List (Fin 7)).Nodup).map p.injective) {v with flag := bad j} E
      (saved j) (child j) _ _ ((cell 1 (by decide) (by decide)).trans copy) ((cell 0 (by decide) (by decide)).trans input)
      (count.trans (savedWidth j).symm) ((childWidth j).trans (savedWidth j).symm) free
    cases hl : live j <;> cases hb : bad j
    all_goals
      first | (obtain ⟨z,user,exec⟩ := childRun; have run := dispatch (by simpa only [hl,hb,ite_true,Bool.false_eq_true,ite_false] using exec))
            | (obtain ⟨z,user,exec⟩ := savedRun; have run := dispatch (by simpa only [hl,hb,ite_true,Bool.false_eq_true,ite_false] using exec))
      refine ⟨z,_,_,result j,user,?_,run,rfl,?_,?_,?_,?_,?_,left,?_⟩
      · simp [hl,childWidth,savedWidth]
      all_goals first | (intro k off; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off;
                          simpa [E,B,Function.update_of_ne,off.1,off.2.1,off.2.2.1,off.2.2.2.1,off.2.2.2.2] using
                            frame k (by simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using off))
                      | simp [E,B,result,hl,hb,p.injective.eq_iff,stack,List.reverse_append,List.flatMap_def]
  obtain ⟨y,D,n,words,user,time,loop,ordered,done⟩ := ownerDirectory_exec body (p 5) row (fun _ => 8*N+12)
    (fun j bits => bits = result j) ready (fun rs acc A h => by rw [h.2.2.2.1]; cases rs <;> rfl) step labels [] u S
    ⟨children,backup,empty,liveBits,badBits,rfl,fun _ _ => rfl⟩
  have eqn : words = labels.map result := by
    clear children backup liveBits badBits time done
    induction ordered with
    | nil => rfl
    | cons h _ ih => simp [h,ih]
  obtain ⟨source,back,stack,ls,bs,left,frame⟩ := done
  obtain ⟨z,zu,finish⟩ := restoreOwnerRecords_exec body (p.injective.ne (by decide : (2 : Fin 7) ≠ 0)) y D words.flatten stack
  have len : words.flatten.length = labels.length*N := by
    rw [eqn,List.length_flatten,List.map_map]
    have each (i) : (result i).length = N := by dsimp only [result]; split <;> simp [childWidth,savedWidth]
    simp [Function.comp_def,each]
  refine ⟨z,_,_,zu.trans user,?_,Exec.seq loop finish,?_,?_,?_,?_,?_,left,?_⟩
  · simp only [List.map_const',List.sum_replicate,smul_eq_mul] at time
    rw [len]
    nlinarith
  all_goals first | (intro k off; have h := frame k off; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off;
                     simpa [Function.update_of_ne,off.1,off.2.2.1] using h)
                  | simp [p.injective.eq_iff,source,back,ls,bs,eqn,List.flatMap_def]

private theorem packedRows {R N V : ℕ} (size : R*N = V) (word : Fin V → ZMod 2) :
    payloadWord (SparseRoleCircuit.encode ∘ word) = (List.finRange R).flatMap fun (j : Fin R) =>
      payloadWord (SparseRoleCircuit.encode ∘ ownerRow (R := R) (N := N) size word j) := by
  subst V
  rw [ownerPayload_records (R := R) (N := N) word]
  apply List.flatMap_congr
  intro j _
  apply congrArg payloadWord
  funext k
  simp [Function.comp_apply,ownerRow,j.isLt]

/-- Execute the shared recursive call and reassemble the classified output.
The backup contains the bypass values in directory order. They may already
include the result of the exceptional projector. -/
theorem classifiedDirectoryCall_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (f : P) (p : Fin 7 ↪ Fin T) (parent : RecursiveInterchangeLayout.Descriptor) (r g w : ℕ) :
    let W := parent.between*parent.afterD
    let packed := ordinaryChildDescriptor r g w W
    let batch := ordinaryDirectoryChild parent r g w
    let R := LabelMask.records parent
    let V := RecursiveInterchangeLayout.volume prime batch
    let N := RecursiveInterchangeLayout.volume prime packed
    let size := ordinaryDirectoryChild_volume parent r g w
    let labels := List.finRange R
    ∀ (ready : ℕ → (Fin ((prime^(w+1))^((r+g)+(r+g))*W) → ZMod 2) → Prop)
      (rows : List (List (Fin (prime+4)))) (live bad : Fin R → Bool) (saved : Fin R → Fin N → ZMod 2)
      (u : HS T Q prime U) (S : Stacks T prime) (budget : ℕ),
    List.Forall₂ (fun j tape => ∃ word, ready j word ∧
      tape = payloadWord (SparseRoleCircuit.encode ∘ word ∘ ordinaryRecursivePosition r g w W)) (List.range R) rows →
    (∀ z, readAt blank (S.L (p 0)) (S.R (p 0)) z = readAt blank [] rows.flatten z) →
    S.R (p 1) = labels.flatMap (fun j => payloadWord (SparseRoleCircuit.encode ∘ saved j)) →
    S.R (p 2) = [] → (S.R (p 3)).length = N → S.R (p 4) = [] →
    S.R (p 5) = labels.map (fun j => bitSymbol (live j)) → S.R (p 6) = labels.map (fun j => bitSymbol (bad j)) →
    (∀ word : Fin V → ZMod 2, RecordPayload (p 0) (fun _ => blank) 0 word S →
      ∃ y F t, y.user = u.user ∧ t ≤ budget ∧ Exec body (body f) (mk u S) t (mk y F) ∧
        RecordPayload (p 0) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) F ∧
        (∀ k, k ≠ p 0 → F.L k = S.L k ∧ F.R k = S.R k)) →
    ∃ z F t, ∃ (out : Fin V → ZMod 2) (tail : List (Fin (prime+4))),
      z.user = u.user ∧ t ≤ budget+R*(10*N+14)+6 ∧
      Exec body ((.call f : Pr P T Q prime U).seq (directoryReturn p)) (mk u S) t (mk z F) ∧
      RecordPayload (p 0) (fun _ => blank) 0 out F ∧ F.R (p 0) = payloadWord (SparseRoleCircuit.encode ∘ out) ++ tail ∧
      (∀ j, if live j && !bad j then ∃ word, ready j word ∧
          ownerRow size out j = ordinaryChildOutput (r := r) (g := g) (w := w) word ∘ ordinaryRecursivePosition r g w W
        else ownerRow size out j = saved j) ∧
      F.R (p 1) = [] ∧ F.R (p 2) = [] ∧ F.R (p 5) = [] ∧ F.R (p 6) = [] ∧
      ∀ k, k ∉ [p 0,p 1,p 2,p 5,p 6] → F.L k = S.L k ∧ F.R k = S.R k := by
  intro W packed batch R V N size labels ready rows live bad saved u S budget prepared input backup empty width tmp ls bs child
  obtain ⟨y,D,n,word,user,paid,call,reads,kept,act⟩ :=
    ordinaryDirectoryCall_exec body f (p 0) parent r g w ready rows u S budget prepared input child
  let row : Fin R → Fin N → ZMod 2 := fun j => ownerRow (R := R) (N := N) size word j
  let returned := fun j => payloadWord (SparseRoleCircuit.encode ∘ row j)
  let bypass := fun j => payloadWord (SparseRoleCircuit.encode ∘ saved j)
  let tail := (D.R (p 0)).drop V
  have stream := payload_prefix_of_read word (fun _ => blank) 0 _ _ reads
  rw [packedRows size word] at stream
  have keep (j : Fin 7) (off : j ≠ 0) := (kept (p j) (p.injective.ne off)).2
  obtain ⟨z,F,t,zy,time,merge,output,back,acc,liveEnd,badEnd,left,frame⟩ :=
    directoryReturn_exec body p live bad returned bypass N (by intro j; simp [returned,payloadWord])
      (by intro j; simp [bypass,payloadWord]) labels tail y D stream ((keep 1 (by decide)).trans backup)
      ((keep 2 (by decide)).trans empty) ((congrArg List.length (keep 3 (by decide))).trans width)
      ((keep 4 (by decide)).trans tmp) ((keep 5 (by decide)).trans ls) ((keep 6 (by decide)).trans bs)
  let out := fun j => if live j && !bad j then row j else saved j
  let joined (k : Fin V) := let pair := finProdFinEquiv.symm (k.cast size.symm); out pair.1 pair.2
  have atRow (j : Fin R) : ownerRow size joined j = out j := by
    funext k
    rw [ownerRow,dite_eq_left (show j.val < LabelMask.records parent from j.isLt)]
    change out (finProdFinEquiv.symm (finProdFinEquiv (j,k))).1 (finProdFinEquiv.symm (finProdFinEquiv (j,k))).2 = _
    rw [Equiv.symm_apply_apply]
  have result : F.R (p 0) = payloadWord (SparseRoleCircuit.encode ∘ joined) ++ tail := by
    rw [packedRows size joined]
    convert output using 2
    apply List.flatMap_congr
    intro j _
    rw [atRow]
    dsimp only [out,returned,bypass]
    split <;> rfl
  have payload := ownerWord_reads word joined tail (payload_prefix_of_read word _ _ _ _ reads)
    (by simpa only [RecordPayload,sub_zero] using reads) (congrFun left (p 0)) result
  refine ⟨z,F,_,joined,tail,zy.trans user,?_,Exec.seq call merge,by simpa only [RecordPayload,sub_zero] using payload,
    result,?_,back,acc,liveEnd,badEnd,?_⟩
  · simp only [labels,List.length_finRange] at time
    omega
  · intro j
    rw [atRow]
    split
    · next h =>
      obtain ⟨original,ok,result⟩ := act j
      exact ⟨original,ok,by rw [show out j = row j from ite_eq_left h]; exact funext result⟩
    · next h => exact ite_eq_right h
  · intro k off
    have outside : k ≠ p 0 := fun eq => off (by simp [eq])
    exact ⟨(congrFun left k).trans (kept k outside).1,(frame k off).trans (kept k outside).2⟩

/-- Save the prepared stream before the recursive call. Thus bypassed rows
survive even when the transpose changes every symbol of their child output. -/
theorem preparedDirectoryCall_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (f : P) (p : Fin 7 ↪ Fin T) (parent : RecursiveInterchangeLayout.Descriptor) (r g w : ℕ) :
    let W := parent.between*parent.afterD
    let packed := ordinaryChildDescriptor r g w W
    let batch := ordinaryDirectoryChild parent r g w
    let R := LabelMask.records parent
    let V := RecursiveInterchangeLayout.volume prime batch
    let N := RecursiveInterchangeLayout.volume prime packed
    let size := ordinaryDirectoryChild_volume parent r g w
    let labels := List.finRange R
    ∀ (ready : ℕ → (Fin ((prime^(w+1))^((r+g)+(r+g))*W) → ZMod 2) → Prop)
      (rows : List (List (Fin (prime+4)))) (live bad : Fin R → Bool)
      (u : HS T Q prime U) (S : Stacks T prime) (budget : ℕ),
    List.Forall₂ (fun j tape => ∃ word, ready j word ∧
      tape = payloadWord (SparseRoleCircuit.encode ∘ word ∘ ordinaryRecursivePosition r g w W)) (List.range R) rows →
    S.L (p 0) = [] → S.R (p 0) = rows.flatten → S.R (p 1) = [] →
    S.R (p 2) = [] → (S.R (p 3)).length = N → S.R (p 4) = [] →
    S.R (p 5) = labels.map (fun j => bitSymbol (live j)) → S.R (p 6) = labels.map (fun j => bitSymbol (bad j)) →
    let D := {S with R := Function.update S.R (p 1) rows.flatten}
    (∀ v : HS T Q prime U, v.user = u.user → ∀ word : Fin V → ZMod 2, RecordPayload (p 0) (fun _ => blank) 0 word D →
      ∃ y F t, y.user = v.user ∧ t ≤ budget ∧ Exec body (body f) (mk v D) t (mk y F) ∧
        RecordPayload (p 0) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) F ∧
        (∀ k, k ≠ p 0 → F.L k = D.L k ∧ F.R k = D.R k)) →
    ∃ z F t, ∃ out : Fin V → ZMod 2, z.user = u.user ∧ t ≤ budget+R*(16*N+14)+12 ∧
      Exec body ((bcopy (p 0) (p 1) (p 2) (p 4)).seq ((.call f : Pr P T Q prime U).seq (directoryReturn p)))
        (mk u S) t (mk z F) ∧ RecordPayload (p 0) (fun _ => blank) 0 out F ∧
      (∀ j : Fin R, ∃ word, ready j word ∧ ownerRow size out j =
        (if live j && !bad j then ordinaryChildOutput (r := r) (g := g) (w := w) word else word) ∘
          ordinaryRecursivePosition r g w W) ∧
      F.R (p 1) = [] ∧ F.R (p 2) = [] ∧ F.R (p 5) = [] ∧ F.R (p 6) = [] ∧
      ∀ k, k ∉ [p 0,p 1,p 2,p 5,p 6] → F.L k = S.L k ∧ F.R k = S.R k := by
  intro W packed batch R V N size labels ready rows live bad u S budget prepared left queue free empty width tmp ls bs D child
  obtain ⟨v,user,copy⟩ := bcopy_exec body ((by decide : ([0,1,2,4] : List (Fin 7)).Nodup).map p.injective)
    u S empty tmp
  rw [queue,free,List.append_nil] at copy
  let action := fun j (row : Fin N → ZMod 2) => ∃ word, ready j word ∧ row = word ∘ ordinaryRecursivePosition r g w W
  obtain ⟨original,ok,encoded⟩ := ownerRows_pack size (action := action) (rows := rows) (by
    apply prepared.imp
    rintro j tape ⟨word,ready,eqn⟩
    exact ⟨_,⟨word,ready,rfl⟩,eqn⟩)
  let saved := fun j : Fin R => ownerRow size original j
  have backup : D.R (p 1) = labels.flatMap (fun (j : Fin R) => payloadWord (SparseRoleCircuit.encode ∘ saved j)) := by
    rw [show D.R (p 1) = rows.flatten from Function.update_self ..,encoded,packedRows size original]
  have keep (j : Fin 7) (off : j ≠ 1) : D.R (p j) = S.R (p j) := Function.update_of_ne (p.injective.ne off) ..
  obtain ⟨z,F,t,out,tail,zy,time,call,payload,_,rowsOut,back,acc,liveEnd,badEnd,frame⟩ :=
    classifiedDirectoryCall_exec body f p parent r g w ready rows live bad saved v D budget prepared
      (by intro k; change readAt blank (S.L (p 0)) (D.R (p 0)) k = _; rw [left,keep 0 (by decide),queue])
      backup ((keep 2 (by decide)).trans empty) ((congrArg List.length (keep 3 (by decide))).trans width)
      ((keep 4 (by decide)).trans tmp) ((keep 5 (by decide)).trans ls) ((keep 6 (by decide)).trans bs) (child v user)
  refine ⟨z,F,_,out,zy.trans user,?_,Exec.seq copy call,payload,?_,back,acc,liveEnd,badEnd,?_⟩
  · have bytes : rows.flatten.length = R*N := by simpa only [encoded,payloadWord,List.length_map,List.length_ofFn] using size.symm
    rw [bytes]
    nlinarith
  · intro j
    have h := rowsOut j
    split at h
    · next active =>
      obtain ⟨word,valid,eqn⟩ := h
      exact ⟨word,valid,by rwa [ite_eq_left active]⟩
    · next inactive =>
      obtain ⟨word,valid,eqn⟩ := ok j
      exact ⟨word,valid,by rw [ite_eq_right inactive]; exact h.trans eqn⟩
  · intro k off
    have outside : k ≠ p 1 := fun eq => off (by simp [eq])
    exact ⟨(frame k off).1,(frame k off).2.trans (Function.update_of_ne outside ..)⟩

/-- Feed physical scan results to the shared call. A bypass row may contain
a repaired exceptional value or an unchanged padding value. Its witness is
reindexed logically, so neither bypass branch needs a tape permutation. -/
theorem scannedDirectoryCall_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (f : P) (p : Fin 7 ↪ Fin T) (parent : RecursiveInterchangeLayout.Descriptor) (r g w : ℕ) :
    let W := parent.between*parent.afterD
    let packed := ordinaryChildDescriptor r g w W
    let batch := ordinaryDirectoryChild parent r g w
    let R := LabelMask.records parent
    let V := RecursiveInterchangeLayout.volume prime batch
    let N := RecursiveInterchangeLayout.volume prime packed
    let raw := (prime^(w+1))^((r+g)+(r+g))*W
    let size := ordinaryDirectoryChild_volume parent r g w
    let pos := ordinaryRecursivePosition r g w W
    ∀ (incoming : ℕ → (Fin raw → ZMod 2) → Prop) (bypass : ℕ → (Fin N → ZMod 2) → Prop)
      (rows : List (List (Fin (prime+4)))) (live bad : ℕ → Bool)
      (u : HS T Q prime U) (S : Stacks T prime) (budget : ℕ),
    let active := fun j => live j && !bad j
    List.Forall₂ (fun j tape => ∃ physical : Fin N → ZMod 2,
      (if active j then ∃ word, incoming j word ∧ physical = word ∘ pos else bypass j physical) ∧
      tape = payloadWord (SparseRoleCircuit.encode ∘ physical)) (List.range R) rows →
    S.L (p 0) = [] → S.R (p 0) = rows.flatten → S.R (p 1) = [] →
    S.R (p 2) = [] → (S.R (p 3)).length = N → S.R (p 4) = [] →
    S.R (p 5) = (List.finRange R).map (fun j : Fin R => bitSymbol (live j)) →
    S.R (p 6) = (List.finRange R).map (fun j : Fin R => bitSymbol (bad j)) →
    let D := {S with R := Function.update S.R (p 1) rows.flatten}
    (∀ v : HS T Q prime U, v.user = u.user → ∀ word : Fin V → ZMod 2, RecordPayload (p 0) (fun _ => blank) 0 word D →
      ∃ y F t, y.user = v.user ∧ t ≤ budget ∧ Exec body (body f) (mk v D) t (mk y F) ∧
        RecordPayload (p 0) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) F ∧
        (∀ k, k ≠ p 0 → F.L k = D.L k ∧ F.R k = D.R k)) →
    ∃ z F t, ∃ out : Fin V → ZMod 2, z.user = u.user ∧ t ≤ budget+R*(16*N+14)+12 ∧
      Exec body ((bcopy (p 0) (p 1) (p 2) (p 4)).seq ((.call f : Pr P T Q prime U).seq (directoryReturn p)))
        (mk u S) t (mk z F) ∧ RecordPayload (p 0) (fun _ => blank) 0 out F ∧
      (∀ j : Fin R, if active j then ∃ word, incoming j word ∧
        ownerRow size out j = ordinaryChildOutput (r := r) (g := g) (w := w) word ∘ pos
        else bypass j (ownerRow size out j)) ∧
      F.R (p 1) = [] ∧ F.R (p 2) = [] ∧ F.R (p 5) = [] ∧ F.R (p 6) = [] ∧
      ∀ k, k ∉ [p 0,p 1,p 2,p 5,p 6] → F.L k = S.L k ∧ F.R k = S.R k := by
  intro W packed batch R V N raw size pos incoming bypass rows live bad u S budget active scanned left queue
    free empty width tmp ls bs D child
  let ready := fun j (word : Fin raw → ZMod 2) => if active j then incoming j word else bypass j (word ∘ pos)
  obtain ⟨z,F,t,out,user,time,run,payload,returned,frame⟩ := preparedDirectoryCall_exec body f p parent r g w
    ready rows (fun j => live j) (fun j => bad j) u S budget (by
      apply scanned.imp
      rintro j tape ⟨physical,ok,rfl⟩
      cases h : active j with
      | true =>
        obtain ⟨word,hw,rfl⟩ := (show ∃ word, incoming j word ∧ physical = word ∘ pos from by simpa [h] using ok)
        exact ⟨word,by simpa [ready,h] using hw,rfl⟩
      | false =>
        let e := ordinaryChildLayoutEquiv r g w W
        have back : (physical ∘ e.symm) ∘ pos = physical := by
          funext i
          exact congrArg physical (e.symm_apply_apply i)
        exact ⟨physical ∘ e.symm,by simpa [ready,h,back] using ok,by change payloadWord _ = payloadWord (SparseRoleCircuit.encode ∘ ((physical ∘ e.symm) ∘ pos)); rw [back]⟩)
    left queue free empty width tmp ls bs child
  refine ⟨z,F,t,out,user,time,run,payload,?_,frame⟩
  intro j
  obtain ⟨word,ok,eqn⟩ := returned j
  change ownerRow size out j = (if active j then _ else word) ∘ pos at eqn
  cases h : active j <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at eqn ⊢
  · rw [eqn]
    simpa [ready,h] using ok
  · exact ⟨word,by simpa [ready,h] using ok,eqn⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
