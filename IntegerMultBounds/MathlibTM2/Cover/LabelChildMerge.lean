module

public import IntegerMultBounds.MathlibTM2.Cover.LabelChildStreams

/-! Restore physical record order after the good and bad children return. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelChildMerge
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def step (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .cond (fun v => symBit (v.sym.getD blank))
    (transfer (r 2) (r 0) (r 5) (r 4)) (transfer (r 2) (r 1) (r 5) (r 4))

def program (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .seq (eachSym (r 3) (r 6) (step r)) (.seq (moveR (r 6) (r 3) id) (moveR (r 5) (r 7) id))

theorem merge_exec (r : Fin 8 ↪ Fin T) (ids : List ℕ) (keep : ℕ → Bool)
    (word : ℕ → List (Fin (A+4))) (w : ℕ) (hw : ∀ j ∈ ids, (word j).length = w)
    (a b : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A)
    (ha : S.R (r 0) = (ids.filter keep).flatMap word ++ a)
    (hb : S.R (r 1) = (ids.filter (fun k => !(keep k))).flatMap word ++ b)
    (hm : S.R (r 3) = (ids.map keep).map bitSymbol) (hlen : (S.R (r 2)).length = w)
    (hf : ∀ i ∈ ([4,5,6] : List (Fin 8)), S.R (r i) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ ids.length*(6*w+10)+6 ∧
      Exec body (program r) (mk u S) n (mk z {S with R := Function.update (Function.update (Function.update S.R (r 0) a) (r 1) b) (r 7) (ids.flatMap word ++ S.R (r 7))}) := by
  let rem (f : ℕ → Bool) (j : ℕ) := ((ids.drop j).filter f).flatMap word
  let R j := Function.update (Function.update (Function.update S.R (r 0) (rem keep j ++ a))
    (r 1) (rem (fun k => !(keep k)) j ++ b)) (r 5) ((ids.take j).flatMap word).reverse
  have spec : SymSpec body (step r) (r 3) (r 6) (S.R (r 3)) R (4*w+5) := by
    intro j hj v M hsym hM
    have lt : j < ids.length := by simpa [hm] using hj
    have slot (i : Fin 8) (h3 : i ≠ 3) (h6 : i ≠ 6) : M.R (r i) = R j (r i) :=
      hM _ (by simpa) (by simpa)
    have bit : symBit (v.sym.getD blank) = keep ids[j] := by simp [hsym,hm]
    have len : (M.R (r 2)).length = (word ids[j]).length := by
      simp [slot 2 (by decide) (by decide),R,hlen,hw _ (List.getElem_mem lt)]
    have tmp : M.R (r 4) = [] := by simp [slot 4 (by decide) (by decide),R,hf 4 (by decide)]
    have drop := List.drop_eq_getElem_cons lt
    have take := List.take_succ_eq_append_getElem lt
    have more (f : ℕ → Bool) : rem f j = (if f ids[j] then word ids[j] else []) ++ rem f (j+1) := by
      unfold rem
      rw [drop]
      cases test : f ids[j] <;> simp only [List.filter_cons,test,Bool.false_eq_true,ite_false,ite_true,List.flatMap_cons,List.nil_append]
    have accum : ((ids.take (j+1)).flatMap word).reverse =
        (word ids[j]).reverse ++ ((ids.take j).flatMap word).reverse := by
      rw [take,List.flatMap_append,List.flatMap_singleton,List.reverse_append]
    cases flag : keep ids[j] with
    | false =>
      obtain ⟨v',hu,he⟩ := transfer_exec (body := body) (count := r 2) (src := r 1) (dst := r 5)
        (tmp := r 4) (by simp) v M (word ids[j]) (rem (fun k => !(keep k)) (j+1) ++ b)
        (by rw [slot 1 (by decide) (by decide)]; simp [R]; rw [more (fun k => !(keep k))]; simp [flag,List.append_assoc]) len tmp
      refine ⟨v',_,_,hu,?_,Exec.cond_false (bit.trans flag) he,by simp,by simp,?_⟩
      · rw [hw _ (List.getElem_mem lt)]
      intro k h3 h6
      by_cases acc : k = r 5
      · subst k; rw [Function.update_self,slot 5 (by decide) (by decide)]; simp [R,accum]
      by_cases src : k = r 1
      · subst k; simp [R]
      by_cases untouched : k = r 0
      · subst k; simp only [Function.update_of_ne (by simp : r 0 ≠ r 5),Function.update_of_ne (by simp : r 0 ≠ r 1)]; rw [slot 0 (by decide) (by decide)]; simp [R]; rw [more keep]; simp [flag]
      simpa [R,acc,src,untouched] using hM k h3 h6
    | true =>
      obtain ⟨v',hu,he⟩ := transfer_exec (body := body) (count := r 2) (src := r 0) (dst := r 5)
        (tmp := r 4) (by simp) v M (word ids[j]) (rem keep (j+1) ++ a)
        (by rw [slot 0 (by decide) (by decide)]; simp [R]; rw [more keep]; simp [flag,List.append_assoc]) len tmp
      refine ⟨v',_,_,hu,?_,Exec.cond_true (bit.trans flag) he,by simp,by simp,?_⟩
      · rw [hw _ (List.getElem_mem lt)]
      intro k h3 h6
      by_cases acc : k = r 5
      · subst k; rw [Function.update_self,slot 5 (by decide) (by decide)]; simp [R,accum]
      by_cases src : k = r 0
      · subst k; simp [R]
      by_cases untouched : k = r 1
      · subst k; simp only [Function.update_of_ne (by simp : r 1 ≠ r 5),Function.update_of_ne (by simp : r 1 ≠ r 0)]; rw [slot 1 (by decide) (by decide)]; simp [R]; rw [more (fun k => !(keep k))]; simp [flag]
      simpa [R,acc,src,untouched] using hM k h3 h6
  obtain ⟨v,F,n,hu,hn,he,h3,h6,hF⟩ := eachSym_exec body (by simp) u S spec (by
    intro k _ _
    by_cases h5 : k = r 5
    · subst k; simp [R,hf 5 (by decide)]
    by_cases h0 : k = r 0
    · subst k; simpa [R,rem] using ha
    by_cases h1 : k = r 1
    · subst k; simpa [R,rem] using hb
    simp [R,h5,h0,h1])
  rw [hf 6 (by decide),List.append_nil] at h6
  let M : Stacks T A := {S with R := F}
  let H : Stacks T A := {M with R := movedR F (r 6) (r 3) id (F (r 6))}
  obtain ⟨v',hu',he'⟩ := moveR_exec body (r 6) (r 3) (by simp) id v M
  obtain ⟨z,hz,run⟩ := moveR_exec body (r 5) (r 7) (by simp) id v' H
  have acc : H.R (r 5) = (ids.flatMap word).reverse := by
    simp [H,movedR,hF _ (by simp : r 5 ≠ r 3) (by simp : r 5 ≠ r 6),R,hm]
  have total : (ids.flatMap word).length = ids.length*w := by
    rw [List.flatMap_def,List.length_flatten,List.map_map]
    simp only [Function.comp_def]
    rw [List.map_congr_left (g := fun _ => w) hw]; simp
  refine ⟨z,_,hz.trans (hu'.trans hu),?_,(Exec.seq he (Exec.seq he' run)).cast rfl ?_⟩
  · simp only [M,h6,List.length_reverse,acc,total,hm,List.length_map] at hn ⊢
    nlinarith
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases out : k = r 7
    · subst k; simp only [movedR,Function.update_self,acc,List.map_id_fun]; simp [H,movedR,hF _ (by simp : r 7 ≠ r 3) (by simp : r 7 ≠ r 6),R]
    by_cases hk5 : k = r 5
    · subst k; simp [movedR,hf 5 (by decide)]
    by_cases hk3 : k = r 3
    · subst k; simp [movedR,H,h3,h6]
    by_cases hk6 : k = r 6
    · subst k; simp [movedR,H,hf 6 (by decide)]
    simp [movedR,H,out,hk5,hk3,hk6,hF k hk3 hk6,R,rem,hm]

/-- Reassemble different child transformations, requiring a width bound only on the records
actually assigned to each child. -/
theorem children_exec (r : Fin 8 ↪ Fin T) (ids : List ℕ) (keep : ℕ → Bool)
    (good bad : ℕ → List (Fin (A+4))) (w : ℕ)
    (hg : ∀ j ∈ ids.filter keep, (good j).length = w)
    (hb : ∀ j ∈ ids.filter (fun k => !(keep k)), (bad j).length = w)
    (a b : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A)
    (srcG : S.R (r 0) = (ids.filter keep).flatMap good ++ a)
    (srcB : S.R (r 1) = (ids.filter (fun k => !(keep k))).flatMap bad ++ b)
    (hm : S.R (r 3) = (ids.map keep).map bitSymbol) (hlen : (S.R (r 2)).length = w)
    (hf : ∀ i ∈ ([4,5,6] : List (Fin 8)), S.R (r i) = []) :
    let result := ids.flatMap fun j => if keep j then good j else bad j
    ∃ z n, z.user = u.user ∧ n ≤ ids.length*(6*w+10)+6 ∧
      Exec body (program r) (mk u S) n (mk z {S with R := Function.update (Function.update (Function.update S.R (r 0) a) (r 1) b) (r 7) (result ++ S.R (r 7))}) := by
  apply merge_exec r ids keep (fun j => if keep j then good j else bad j) w _ a b u S _ _ hm hlen hf
  · intro j hj
    cases h : keep j <;> simp [h,hb,hg,hj]
  · rw [srcG,List.flatMap_def,List.flatMap_def]
    congr 2
    apply List.map_congr_left
    intro j hj
    simp [(List.mem_filter.mp hj).2]
  · rw [srcB,List.flatMap_def,List.flatMap_def]
    congr 2
    apply List.map_congr_left
    intro j hj
    have h := (List.mem_filter.mp hj).2
    cases e : keep j <;> simp_all


end
end IntegerMultBounds.MathlibTM2.Cover.LabelChildMerge
