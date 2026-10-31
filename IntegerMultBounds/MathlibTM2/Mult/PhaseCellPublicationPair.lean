module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationStock

/-! Two actual length-class sweeps compose through their computed ambient
lines. The next class's source payload is borrowed by the first sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L M : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem publicationPair_exec
    (clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
      wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock₁,padRows₁,control₁,window₁,clock₂,padRows₂,control₂,window₂,
      wordWidth,retireCount,savedControl,gap,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (windows₁ : PublicationWindows s L) (windows₂ : PublicationWindows s M)
    (w missing₁ missing₂ : ℕ) (hw1 : 1 ≤ w)
    (replicas₁ replicas₂ : List (PublicationReplica A))
    (hvalid₁ : ∀ r ∈ replicas₁, r.Valid windows₁ w missing₁)
    (hvalid₂ : ∀ r ∈ replicas₂, r.Valid windows₂ w missing₂)
    (hambient : replicas₂.flatMap PublicationReplica.ambient =
      replicas₁.flatMap (PublicationReplica.output windows₁ w))
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicas₁.flatMap (PublicationReplica.input w)++
      (replicas₂.flatMap (PublicationReplica.input w)++sourceTail))
    (hdst : S.R dst = replicas₁.flatMap PublicationReplica.ambient++outputTail)
    (hclock₁ : (S.R clock₁).length = replicas₁.length)
    (hclock₂ : (S.R clock₂).length = replicas₂.length)
    (hpad₁ : (S.R padRows₁).length = missing₁*L)
    (hpad₂ : (S.R padRows₂).length = missing₂*M)
    (hwidth : (S.R wordWidth).length = w) (hline : (S.R lineRows).length = s)
    (hc₁ : S.R control₁ = gatherControls A (windows₁.gaps w))
    (hc₂ : S.R control₂ = gatherControls A (windows₂.gaps w))
    (hw₁ : (S.R window₁).length = L*w) (hw₂ : (S.R window₂).length = M*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved,outAcc], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ replicaPublicationCost replicas₁.length s missing₁ L w+
        replicaPublicationCost replicas₂.length s missing₂ M w ∧
      Exec body (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id)))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas₂.flatMap (PublicationReplica.output windows₂ w)++outputTail ∧
      F.R clock₁ = [] ∧ F.R clock₂ = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock₁ → i ≠ clock₂ → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  have hshared : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = [] := by
    intro i hi
    apply hclean i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨v₁,F₁,n₁,hu₁,hn₁,he₁,hs₁,hd₁,ha₁,hclock₁',hi₁,ho₁,hl₁,hframe₁⟩ := replicaPublicationBatch_exec
    clock₁ padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved
    (by regs_nodup) windows₁ w missing₁ hw1 replicas₁ hvalid₁
    (replicas₂.flatMap (PublicationReplica.input w)++sourceTail) outputTail v S hsrc hdst hclock₁
    hpad₁ hwidth hline hc₁ hw₁ hshared (hclean _ (by simp))
  have hcontrols : ∀ i ∈ [clock₂,padRows₂,wordWidth,retireCount,control₂,savedControl,gap,window₂,acc,trash,tmp,lineRows,outAcc,saved],
      F₁.R i = S.R i := by
    intro i hi
    apply hframe₁
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)
  obtain ⟨v₂,F₂,n₂,hu₂,hn₂,he₂,hs₂,hd₂,ha₂,hclock₂',hi₂,ho₂,hl₂,hframe₂⟩ := replicaPublicationBatch_exec
    clock₂ padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved
    (by regs_nodup) windows₂ w missing₂ hw1 replicas₂ hvalid₂ sourceTail outputTail v₁ F₁ hs₁
    (by rw [hambient]; exact hd₁)
    (by rw [hcontrols _ (by simp)]; exact hclock₂)
    (by rw [hcontrols _ (by simp)]; exact hpad₂)
    (by rw [hcontrols _ (by simp)]; exact hwidth)
    (by rw [hcontrols _ (by simp)]; exact hline)
    (by rw [hcontrols _ (by simp)]; exact hc₂)
    (by rw [hcontrols _ (by simp)]; exact hw₂)
    (by
      intro i hi
      have hm : i ∈ [clock₂,padRows₂,wordWidth,retireCount,control₂,savedControl,gap,window₂,acc,trash,tmp,lineRows,outAcc,saved] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rw [hcontrols i hm]
      exact hshared i hi) ha₁
  refine ⟨v₂,F₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    hs₂,hd₂,?_,hclock₂',hi₂.trans hi₁,ho₂.trans ho₁,hl₂.trans hl₁,?_⟩
  · rw [hframe₂ clock₁ ‹clock₁ ≠ src› ‹clock₁ ≠ dst› ‹clock₁ ≠ clock₂›]
    exact hclock₁'
  · intro i his hid hic₁ hic₂
    exact (hframe₂ i his hid hic₂).trans (hframe₁ i his hid hic₁)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
