module

public import IntegerMultBounds.MathlibTM2.Host.RestoringRowScan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRowGatherStep

/-! Reuse one local gather control page across all packed RHS rows. Only local
source movement repeats; the caller generates and retires the controls once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retainedRowGather (replicas saved count source archive dst control savedControl advance window src acc current
    savedSource buf tmp initialControl initialSource rowCount wordR : Fin T) : Pr P T Q A U :=
  restoringRowScan replicas saved source archive
    (retainedRowGatherStep count source archive dst control savedControl advance window src acc current
      savedSource buf tmp initialControl initialSource rowCount wordR)

theorem retainedRowGather_exec
    {replicas saved count source archive dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR : Fin T}
    (hreg : [replicas,saved,source,archive,dst,count,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    (volume L w : ℕ) (origins : List ℕ) (rows : List (List (Fin (A+4))))
    (hlength : ∀ E ∈ rows, E.length = volume)
    (hne : origins ≠ []) (hordered : origins.Pairwise (· ≤ ·))
    (hfit : ∀ p ∈ origins, p+L*w ≤ volume)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = match origins with | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps))
    (hs : S.R source = rows.flatten++borrowed) (harchive : S.R archive = [])
    (hreplicas : (S.R replicas).length = rows.length) (hsaved : S.R saved = [])
    (hcount : (S.R count).length = volume) (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hsrc : S.R src = [])
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ rows.length*(retainedRowGatherStepCost volume origins.length L w+5)+4+2*(rows.length*volume)+2 ∧
      Exec body (retainedRowGather replicas saved count source archive dst control savedControl advance window src acc current
        savedSource buf tmp initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          (rows.reverse.flatMap (fun E => origins.flatMap (fun p => (E.drop p).take (L*w)))++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have hsplit : ([replicas,saved,source,archive,dst]++
      [count,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
        initialControl,initialSource,rowCount,wordR]).Nodup := hreg
  obtain ⟨hmain,_,hsep⟩ := List.nodup_append.mp hsplit
  let payload := fun E : List (Fin (A+4)) => origins.flatMap (fun p => (E.drop p).take (L*w))
  obtain ⟨v',n,huser,hcost,he⟩ := restoringRowScan_exec (body := body) replicas saved source archive dst hmain
    (retainedRowGatherStep count source archive dst control savedControl advance window src acc current
      savedSource buf tmp initialControl initialSource rowCount wordR)
    (retainedRowGatherStepCost volume origins.length L w) rows id payload borrowed v S
    (by simpa using hs) harchive hreplicas hsaved (by
      intro E hE v₀ F tail hframe hsource
      have hwork (k : Fin T) (hk : k ∈ [count,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
          initialControl,initialSource,rowCount,wordR]) : F.R k = S.R k :=
        hframe k (fun hm => hsep k hm k hk rfl)
      have hlen := hlength E hE
      obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retainedRowGatherStep_exec (body := body)
        (show [count,source,archive,dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
          initialControl,initialSource,rowCount,wordR].Nodup by regs_nodup)
        L w origins E tail hne hordered (by simpa only [hlen] using hfit) v₀ F
        (by rw [hwork control (by simp)]; exact hc) hsource
        (by simpa only [hwork count (by simp),hlen] using hcount)
        (by simpa only [hwork rowCount (by simp)] using hrow)
        (by simpa only [hwork wordR (by simp)] using hw)
        (by simpa only [hwork src (by simp)] using hsrc) (by
          intro k hk
          have hkWork : k ∈ [count,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
              initialControl,initialSource,rowCount,wordR] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
          rw [hwork k hkWork]
          exact hclean k hk)
      exact ⟨v₁,n₁,hu₁,by simpa only [hlen] using hn₁,he₁⟩)
  refine ⟨v',n,huser,?_,he⟩
  have hflat : (rows.flatMap id).length = rows.length*volume := by
    rw [List.length_flatMap]
    have hm : rows.map (fun E => (id E).length) = rows.map (fun _ => volume) := by
      apply List.map_congr_left
      exact hlength
    rw [hm]
    simp
  simpa only [hflat] using hcost

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
