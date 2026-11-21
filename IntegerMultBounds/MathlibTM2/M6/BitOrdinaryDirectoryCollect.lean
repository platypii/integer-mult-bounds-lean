module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIncoming

/-! Collect classified row payloads in directory order for the shared transpose. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Shared50ModularControl (prime)

/-- The incoming scan consumes the two copies. The original masks retain
directory order for the return pass. Both copies share the temporary tapes. -/
theorem copyDirectoryMasks_exec {ι P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (p : Fin 6 ↪ Fin T) (labels : List ι) (live bad : ι → Bool)
    (v : HS T Q prime U) (S : Stacks T prime)
    (ls : S.R (p 0) = labels.map (fun j => bitSymbol (live j)))
    (bs : S.R (p 1) = labels.map (fun j => bitSymbol (bad j)))
    (free : ∀ k : Fin 6, 2 ≤ k → S.R (p k) = []) :
    let D := {S with R := Function.update (Function.update S.R (p 2) (S.R (p 0))) (p 3) (S.R (p 1))}
    ∃ z, z.user = v.user ∧ Exec body
      ((bcopy (p 0) (p 2) (p 4) (p 5)).seq (bcopy (p 1) (p 3) (p 4) (p 5)))
      (mk v S) (12*labels.length+12) (mk z D) := by
  intro D
  obtain ⟨u,user,first⟩ := bcopy_exec body ((by decide : ([0,2,4,5] : List (Fin 6)).Nodup).map p.injective)
    v S (free 4 (by decide)) (free 5 (by decide))
  rw [free 2 (by decide),List.append_nil] at first
  let B := {S with R := Function.update S.R (p 2) (S.R (p 0))}
  have kept (j : Fin 6) (h : j ≠ 2) : B.R (p j) = S.R (p j) := Function.update_of_ne (p.injective.ne h) ..
  obtain ⟨z,hz,last⟩ := bcopy_exec body ((by decide : ([1,3,4,5] : List (Fin 6)).Nodup).map p.injective)
    u B ((kept 4 (by decide)).trans (free 4 (by decide))) ((kept 5 (by decide)).trans (free 5 (by decide)))
  rw [kept 1 (by decide),kept 3 (by decide),free 3 (by decide),List.append_nil] at last
  refine ⟨z,hz.trans user,Exec.cast (Exec.seq first last) ?_ rfl⟩
  simp only [ls,bs,List.length_map]
  omega

/-- Save the two selectors outside the scanner placement, then resume on
the original projected stacks with the control state left by copying. -/
theorem saveMasksAndScan_exec {ι P G U : Type} {T K Q : ℕ}
    (body : P → Pr P T Q prime U) (e : Fin T ↪ Fin K) (label : P → G) (host : G → Pr G K Q prime U)
    (calls : ∀ f, host (label f) = embProg e label (body f)) (scan : Pr P T Q prime U)
    (p : Fin 6 ↪ Fin K) (outside : ∀ i, e i ≠ p 2 ∧ e i ≠ p 3)
    (labels : List ι) (live bad : ι → Bool) (u : HS K Q prime U) (S : Stacks K prime)
    (ls : S.R (p 0) = labels.map (fun j => bitSymbol (live j)))
    (bs : S.R (p 1) = labels.map (fun j => bitSymbol (bad j)))
    (free : ∀ k : Fin 6, 2 ≤ k → S.R (p k) = [])
    (result : ℕ → Stacks T prime → Prop)
    (resume : ∀ a : HS T Q prime U, ∃ z F t, z.user = a.user ∧
      Exec body scan (mk a (embStk e S)) t (mk z F) ∧ result t F) :
    let copy := (bcopy (p 0) (p 2) (p 4) (p 5)).seq (bcopy (p 1) (p 3) (p 4) (p 5))
    ∃ z F t, z.user = u.user ∧ Exec host (copy.seq (embProg e label scan))
      (mk u S) (12*labels.length+12+t) (mk z F) ∧ result t (embStk e F) ∧
      F.R (p 2) = labels.map (fun j => bitSymbol (live j)) ∧
      F.R (p 3) = labels.map (fun j => bitSymbol (bad j)) ∧
      ∀ i, (∀ k, e k ≠ i) → i ≠ p 2 → i ≠ p 3 → F.R i = S.R i := by
  intro copy
  obtain ⟨a,user,save⟩ := copyDirectoryMasks_exec host p labels live bad u S ls bs free
  let D := {S with R := Function.update (Function.update S.R (p 2) (S.R (p 0))) (p 3) (S.R (p 1))}
  have project : embStk e D = embStk e S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    exact (Function.update_of_ne (outside i).2 ..).trans (Function.update_of_ne (outside i).1 ..)
  obtain ⟨b,B,t,hb,run,ok⟩ := resume (embDn e a)
  obtain ⟨z,F,placed,_,hz,eqn,kept⟩ := exec_emb e.injective calls run a rfl D project
  refine ⟨z,F,t,hz.trans (hb.trans user),Exec.seq save placed,eqn ▸ ok,?_,?_,?_⟩
  · exact ((kept _ (fun i => (outside i).1)).2.trans (Function.update_of_ne (p.injective.ne
      (by decide : (2 : Fin 6) ≠ 3)) ..)).trans ((Function.update_self ..).trans ls)
  · exact ((kept _ (fun i => (outside i).2)).2.trans (Function.update_self ..)).trans bs
  · intro i off h2 h3
    exact ((kept i off).2).trans ((Function.update_of_ne h3 ..).trans (Function.update_of_ne h2 ..))

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

/-- Collect one packed word per label, dispatching with the two working
masks. Each branch sees both selectors advanced past its own label. -/
theorem collectClassifiedRows_exec {ι P U : Type} {T Q N : ℕ} (body : P → Pr P T Q prime U)
    (p : Fin 7 ↪ Fin T) (good exceptional padding : Pr P T Q prime U) (cost : ι → ℕ)
    (live bad : ι → Bool) (valid : ι → (Fin N → ZMod 2) → Prop)
    (ready : List ι → Stacks T prime → Prop) (labels : List ι) (u : HS T Q prime U) (S : Stacks T prime) :
    let bits := fun (f : ι → Bool) (rs : List ι) => rs.map (fun j => bitSymbol (a := prime) (f j))
    let dispatch := ownerDispatch (p 0) (p 6) good exceptional padding
    let collect := Mult.ShortConv.transfer (p 1) (p 2) (p 3) (p 4)
    let inspect : Pr P T Q prime U := .act (peekR (p 0))
    let scan := inspect.seq (.loop (·.flag) ((dispatch.seq collect).seq inspect))
    let next := fun (D : Stacks T prime) (word : Fin N → ZMod 2) =>
      {D with R := Function.update (Function.update D.R (p 2) ((D.R (p 2)).drop N)) (p 3) ((payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ D.R (p 3))}
    (∀ j rs (v : HS T Q prime U) A, ready (j::rs) A →
      let B := {A with R := Function.update (Function.update A.R (p 0) (bits live rs)) (p 6) (bits bad rs)}
      ∃ y D n word, y.user = v.user ∧ n ≤ cost j ∧
        Exec body (if live j then (if bad j then exceptional else good) else padding)
          (mk {v with flag := bad j} B) n (mk y D) ∧ valid j word ∧
        RecordPayload (p 2) (fun _ => blank) 0 word D ∧ (D.R (p 1)).length = N ∧ D.R (p 4) = [] ∧
        D.R (p 3) = A.R (p 3) ∧ D.R (p 0) = bits live rs ∧ D.R (p 6) = bits bad rs ∧ ready rs (next D word)) →
    ready labels S → S.R (p 3) = [] → S.R (p 0) = bits live labels → S.R (p 6) = bits bad labels →
    (∀ A, ready [] A → A.R (p 5) = [] ∧ A.L (p 5) = []) →
    ∃ z F n rows, z.user = u.user ∧
      n ≤ (labels.map (fun j => (cost j+4)+(4*N+4))).sum + 2*labels.length + 2 + (2*(labels.length*N)+2) ∧
      Exec body (scan.seq (moveR (p 3) (p 5) id)) (mk u S) n (mk z F) ∧
      List.Forall₂ (fun j tape => ∃ word, valid j word ∧ tape = payloadWord (SparseRoleCircuit.encode ∘ word))
        labels rows ∧ F.R (p 5) = rows.flatten ∧ F.L (p 5) = [] ∧ F.R (p 0) = [] ∧ F.R (p 6) = [] ∧
      ∃ D, ready [] D ∧ ∀ k, k ≠ p 3 → k ≠ p 5 → F.L k = D.L k ∧ F.R k = D.R k := by
  intro bits dispatch collect inspect scan next step start empty ls bs dest
  let inv := fun rs (A : Stacks T prime) => ready rs A ∧ A.R (p 0) = bits live rs ∧ A.R (p 6) = bits bad rs
  obtain ⟨z,F,n,rows,user,time,run,ordered,queue,left,_,D,done,frame⟩ := collectDirectoryRows_exec body
    ((Fin.castLEEmb (by decide : 6 ≤ 7)).trans p) dispatch (fun j => cost j+4) valid inv labels u S
    (fun rs A h => by change (A.R (p 0)).head?.isSome = _; rw [h.2.1]; cases rs <;> rfl) (by
      intro j rs v A h
      obtain ⟨y,D,n,word,user,time,branch,ok,payload,width,tmp,stack,ls,bs,done⟩ := step j rs v A h.1
      have run := ownerDispatch_exec body (p 0) (p 6) (p.injective.ne (by decide)) good exceptional padding
        (live j) (bad j) v A (bits live rs) (bits bad rs) h.2.1 h.2.2 branch
      refine ⟨y,D,_,word,user,?_,run,ok,payload,width,tmp,stack,done,?_,?_⟩
      · split <;> omega
      · change (next D word).R (p 0) = _
        simpa [next,Function.update_of_ne,p.injective.eq_iff] using ls
      · change (next D word).R (p 6) = _
        simpa [next,Function.update_of_ne,p.injective.eq_iff] using bs)
    ⟨start,ls,bs⟩ empty (fun A h => dest A h.1)
  exact ⟨z,F,n,rows,user,time,run,ordered,queue,left,
    (frame _ (p.injective.ne (by decide : (0 : Fin 7) ≠ 3)) (p.injective.ne (by decide))).2.trans done.2.1,
    (frame _ (p.injective.ne (by decide : (6 : Fin 7) ≠ 3)) (p.injective.ne (by decide))).2.trans done.2.2,
    D,done.1,frame⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
