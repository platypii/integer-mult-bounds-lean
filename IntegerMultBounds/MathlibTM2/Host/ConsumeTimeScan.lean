module

public import IntegerMultBounds.MathlibTM2.Host.ConsumeScan
public import IntegerMultBounds.MathlibTM2.Node.ScanPTimeInvariant

/-! A fixed counted queue consumer retains the sum of actual per-job time
allowances and a single shared workspace reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U C : Type} {body : P → Pr P T Q A U}

private theorem sum_indexTime (cs : List C) (time : C → ℕ) :
    (∑ j ∈ Finset.range cs.length, ((cs[j]?).map time).getD 0) = (cs.map time).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons,Finset.sum_range_succ',List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.map_some,Option.getD_some,List.map_cons,List.sum_cons]
    rw [ih]
    omega

theorem consumeTimeScan_exec (p : Pr P T Q A U) (count saved origins source result : Fin T)
    (hreg : [count,saved,origins,source,result].Nodup)
    (origin payload : C → List (Fin (A+4))) (cs : List C) (originTail tail : List (Fin (A+4)))
    (time : C → ℕ) (reserve depth : ℕ) (Cert : C → List (Fin (A+4)) → Prop) (J : Stacks T A → Prop)
    (hJcounter : ∀ F R, (∀ k, k ≠ count → k ≠ saved → R k = F.R k) → J F → J {F with R := R})
    (hJstep : ∀ F otail rest xs, J F → J {F with R := (Function.update
      (Function.update (Function.update F.R origins otail) source rest) result (xs++F.R result))})
    (hrun : ∀ c ∈ cs, ∀ (v : HS T Q A U) (F : Stacks T A) otail rest,
      J F → F.R origins = origin c++otail → F.R source = payload c++rest →
      ∃ v' n xs, v'.user = v.user ∧ n ≤ time c ∧ xs.length ≤ (payload c).length ∧ Cert c xs ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+reserve) depth
          p (mk v F) n (mk v' {F with R := (Function.update
            (Function.update (Function.update F.R origins otail) source rest) result (xs++F.R result))}))
    (v : HS T Q A U) (S : Stacks T A) (hJ : J S)
    (horigins : S.R origins = cs.flatMap origin++originTail)
    (hsource : S.R source = cs.flatMap payload++tail)
    (hcount : (S.R count).length = cs.length) (hsaved : S.R saved = []) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (cs.map time).sum+5*cs.length+4 ∧ List.Forall₂ Cert cs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve) depth
        (scanP count saved p) (mk v S) n (mk v' {S with R := (Function.update
          (Function.update (Function.update S.R origins originTail) source tail) result
          (outputs.reverse.flatten++S.R result))}) := by
  have hr := hreg
  regs_ne hr
  let cost := fun j : ℕ => ((cs[j]?).map time).getD 0
  let I : ℕ → Stacks T A → Prop := fun j F =>
    ∃ (done todo : List C) (outputs : List (List (Fin (A+4)))),
      cs = done++todo ∧ done.length = j ∧ List.Forall₂ Cert done outputs ∧
      F.R origins = todo.flatMap origin++originTail ∧ F.R source = todo.flatMap payload++tail ∧
      F.R result = outputs.reverse.flatten++S.R result ∧ J F ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, k ≠ count → k ≠ saved → k ≠ origins → k ≠ source → k ≠ result → F.R k = S.R k
  have hframe : ∀ j F R, (∀ k, k ≠ count → k ≠ saved → R k = F.R k) → I j F → I j {F with R := R} := by
    intro j F R hR hI
    obtain ⟨done,todo,outputs,hsplit,hlen,hcert,ho,hp,hresult,hJF,hin,hout,hleft,hrest⟩ := hI
    refine ⟨done,todo,outputs,hsplit,hlen,hcert,?_,?_,?_,hJcounter F R hR hJF,hin,hout,hleft,?_⟩
    · exact (hR origins (Ne.symm ‹count ≠ origins›) (Ne.symm ‹saved ≠ origins›)).trans ho
    · exact (hR source (Ne.symm ‹count ≠ source›) (Ne.symm ‹saved ≠ source›)).trans hp
    · exact (hR result (Ne.symm ‹count ≠ result›) (Ne.symm ‹saved ≠ result›)).trans hresult
    · intro k hkc hks hko hkp hkr
      exact (hR k hkc hks).trans (hrest k hkc hks hko hkp hkr)
  have hstep : IterWithinTimeSpec body p count saved I cost cs.length (mnSize (mk v S)) reserve depth := by
    intro j hj w F hI hbound
    obtain ⟨done,todo,outputs,hsplit,hdone,hcerts,ho,hp,hresult,hJF,hin,hout,hleft,hrest⟩ := hI
    cases todo with
    | nil =>
      have hlen := congrArg List.length hsplit
      simp only [List.length_append,List.length_nil,Nat.add_zero] at hlen
      omega
    | cons c todo =>
      have hc : c ∈ cs := by rw [hsplit]; exact List.mem_append_right _ (by simp)
      obtain ⟨w',n,xs,hu,hn,hvolume,hcert,he⟩ := hrun c hc w F
        (todo.flatMap origin++originTail) (todo.flatMap payload++tail) hJF
        (by simpa only [List.flatMap_cons,List.append_assoc] using ho)
        (by simpa only [List.flatMap_cons,List.append_assoc] using hp)
      have hcost : time c = cost j := by
        dsimp only [cost]
        rw [hsplit,←hdone,List.getElem?_append_right (Nat.le_refl _)]
        simp
      let R := Function.update
        (Function.update (Function.update F.R origins (todo.flatMap origin++originTail)) source
          (todo.flatMap payload++tail)) result (xs++F.R result)
      have hboundary := mn_consume_pair_appendR_size_nonincreasing w w' F origins source result
        (by simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_false_eq_true,not_or,ne_eq,and_true])
        (origin c) (todo.flatMap origin++originTail) (payload c) (todo.flatMap payload++tail) xs
        (by simpa only [List.flatMap_cons,List.append_assoc] using ho)
        (by simpa only [List.flatMap_cons,List.append_assoc] using hp) hvolume
      refine ⟨w',R,n,hu,hn.trans_eq hcost,he.mono (by intro d z hz; omega),?_,?_,?_,hboundary.trans hbound⟩
      · simp [R,‹count ≠ origins›,‹count ≠ source›,‹count ≠ result›]
      · simp [R,‹saved ≠ origins›,‹saved ≠ source›,‹saved ≠ result›]
      · refine ⟨done++[c],todo,outputs++[xs],?_,?_,List.rel_append hcerts (.cons hcert .nil),?_,?_,?_,
          hJstep F _ _ xs hJF,hin,hout,hleft,?_⟩
        · simpa only [List.append_assoc,List.singleton_append] using hsplit
        · simp [hdone]
        · simp [R,‹origins ≠ source›,‹origins ≠ result›]
        · simp [R,‹source ≠ result›]
        · simp [R,hresult,List.reverse_append,List.append_assoc]
        · intro k hkc hks hko hkp hkr
          simpa [R,hko,hkp,hkr] using hrest k hkc hks hko hkp hkr
  have hI : I 0 S := ⟨[],cs,[],by simp,rfl,.nil,horigins,hsource,by simp,hJ,rfl,rfl,rfl,
    by intros; rfl⟩
  obtain ⟨w,R,n,hu,hn,hRc,hRs,hIf,hbound,he⟩ := scanP_exec_within_time_invariant ‹count ≠ saved›
    hframe hstep v S hI hcount hsaved le_rfl
  obtain ⟨done,todo,outputs,hsplit,hdone,hcert,ho,hp,hresult,hJF,hin,hout,hleft,hrest⟩ := hIf
  have htodo : todo = [] := by
    have hlen := congrArg List.length hsplit
    rw [List.length_append,hdone] at hlen
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst todo
  simp only [List.append_nil] at hsplit
  subst done
  have hend : {S with R := R} = {S with R := (Function.update
      (Function.update (Function.update S.R origins originTail) source tail) result
      (outputs.reverse.flatten++S.R result))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = count
    · subst k; simp [hRc,‹count ≠ origins›,‹count ≠ source›,‹count ≠ result›]
    · by_cases hs : k = saved
      · subst k; simp [hRs,hsaved,‹saved ≠ origins›,‹saved ≠ source›,‹saved ≠ result›]
      · by_cases hor : k = origins
        · subst k; simpa [‹origins ≠ source›,‹origins ≠ result›] using ho
        · by_cases hsrc : k = source
          · subst k; simpa [‹source ≠ result›] using hp
          · by_cases hr : k = result
            · subst k; simpa using hresult
            · simpa [hc,hs,hor,hsrc,hr] using hrest k hc hs hor hsrc hr
  rw [hend] at he
  have htime : n ≤ (cs.map time).sum+5*cs.length+4 := by
    simpa only [cost,sum_indexTime] using hn
  exact ⟨w,n,outputs,hu,htime,hcert,he⟩

end IntegerMultBounds.MathlibTM2.Host
