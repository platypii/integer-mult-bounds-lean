module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! A single fixed counted loop publishes every replica and exposes the borrowed
suffixes. Its structural invariant keeps the computed lines in a reverse archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaPublicationStepCost (s missing L w : ℕ) :=
  (retireCountedLineCost (missing*L) w+35*s*w+6)+transferCountedLineCost s w

theorem replicaPublicationLoop_exec
    (clock padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock,padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (replicas : List (PublicationReplica A))
    (hvalid : ∀ r ∈ replicas, r.Valid windows w missing)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicas.flatMap (PublicationReplica.input w)++sourceTail)
    (hdst : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail)
    (hclock : (S.R clock).length = replicas.length)
    (hpadRows : (S.R padRows).length = missing*L) (hwidth : (S.R wordWidth).length = w)
    (hlineRows : (S.R lineRows).length = s)
    (hc : S.R control = gatherControls A (windows.gaps w)) (hw : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicas.length*(replicaPublicationStepCost s missing L w+3)+2 ∧
      Exec body (countedLoop clock (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = outputTail ∧
      F.R outAcc = (replicas.flatMap (PublicationReplica.output windows w)).reverse++S.R outAcc ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ outAcc → i ≠ clock → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  have hstepReg := hreg.tail
  let input := PublicationReplica.input (A := A) w
  let output := PublicationReplica.output (A := A) windows w
  let Inv := fun j (R : Stacks T A) => ∃ done todo : List (PublicationReplica A),
    replicas = done++todo ∧ done.length = j ∧ R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ i, i ≠ src → i ≠ dst → i ≠ outAcc → i ≠ clock → R.R i = S.R i) ∧
    R.R src = todo.flatMap input++sourceTail ∧ R.R dst = todo.flatMap PublicationReplica.ambient++outputTail ∧
    R.R outAcc = (done.flatMap output).reverse++S.R outAcc
  obtain ⟨v',F,n,hu,hn,he,hclock',hI⟩ := countedLoop_exec (body := body) clock
    (replicaPublicationStep padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved)
    replicas.length (replicaPublicationStepCost s missing L w) Inv (by
      intro j R xs hI
      obtain ⟨done,todo,hrep,hlen,hi,ho,hl,hframe,hsrc,hdst,hacc⟩ := hI
      refine ⟨done,todo,hrep,hlen,hi,ho,hl,?_,?_,?_,?_⟩
      · intro i his hid hia hic; simpa only [Function.update_of_ne hic] using hframe i his hid hia hic
      · simpa only [Function.update_of_ne ‹clock ≠ src›.symm] using hsrc
      · simpa only [Function.update_of_ne ‹clock ≠ dst›.symm] using hdst
      · simpa only [Function.update_of_ne ‹clock ≠ outAcc›.symm] using hacc)
    (by
      intro j hj vi R hI
      obtain ⟨done,todo,hrep,hlen,hi,ho,hl,hframe,hsrc,hdst,hacc⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hrep; subst replicas; omega
      | cons r todo =>
        have hrmem : r ∈ replicas := by rw [hrep]; simp
        have hcontrols : ∀ i ∈ [padRows,wordWidth,retireCount,control,savedControl,gap,window,acc,trash,tmp,lineRows,saved], R.R i = S.R i := by
          intro i hi
          apply hframe
          all_goals
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨vf,m,hu,hm,hex⟩ := replicaPublicationStep_exec (body := body)
          padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp lineRows outAcc saved hstepReg
          windows w missing hw1 r (hvalid r hrmem)
          (todo.flatMap input++sourceTail) (todo.flatMap PublicationReplica.ambient++outputTail) vi R
          (by simpa only [List.flatMap_cons,List.append_assoc] using hsrc)
          (by simpa only [List.flatMap_cons,List.append_assoc] using hdst)
          (by rw [hcontrols _ (by simp)]; exact hpadRows)
          (by rw [hcontrols _ (by simp)]; exact hwidth)
          (by rw [hcontrols _ (by simp)]; exact hlineRows)
          (by rw [hcontrols _ (by simp)]; exact hc)
          (by rw [hcontrols _ (by simp)]; exact hw)
          (by
            intro i hi
            have hm : i ∈ [padRows,wordWidth,retireCount,control,savedControl,gap,window,acc,trash,tmp,lineRows,saved] := by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
            rw [hcontrols i hm]
            exact hclean i hi)
        let R' : Stacks T A := {R with R := (Function.update (Function.update (Function.update R.R src
          (todo.flatMap input++sourceTail)) dst (todo.flatMap PublicationReplica.ambient++outputTail))
          outAcc ((output r).reverse++R.R outAcc))}
        refine ⟨vf,R',m,hu,hm,hex,?_,done++[r],todo,?_,?_,hi,ho,hl,?_,?_,?_,?_⟩
        · simp [R',‹clock ≠ src›,‹clock ≠ dst›,‹clock ≠ outAcc›]
        · simpa only [List.append_assoc,List.singleton_append] using hrep
        · simp only [List.length_append,List.length_singleton,hlen]
        · intro i his hid hia hic
          simpa only [R',Function.update_of_ne his,Function.update_of_ne hid,Function.update_of_ne hia] using hframe i his hid hia hic
        · simp [R',‹src ≠ dst›,‹src ≠ outAcc›]
        · simp [R',‹dst ≠ outAcc›]
        · simp only [R',Function.update_self,hacc,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
            List.append_nil,List.reverse_append,List.append_assoc])
    v S hclock ⟨[],replicas,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,hdst,by simp⟩
  obtain ⟨done,todo,hrep,hlen,hi,ho,hl,hframe,hsrc',hdst',hacc⟩ := hI
  have ht : todo = [] := by
    have h := congrArg List.length hrep
    simp only [List.length_append] at h
    cases todo with
    | nil => rfl
    | cons r todo => simp only [List.length_cons] at h; omega
  subst todo
  simp only [List.append_nil] at hrep
  subst done
  exact ⟨v',F,n,hu,hn,he,by simpa using hsrc',by simpa using hdst',hacc,hclock',hi,ho,hl,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
