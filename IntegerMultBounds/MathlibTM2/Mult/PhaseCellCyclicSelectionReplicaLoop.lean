module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSelectionReplicaStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! A single fixed loop reuses the nearest-row controller for all replicas.
Its invariant archives restored target windows and selected rows in reverse. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {T Q A s t : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem cyclicSelectionReplicaLoop_exec
    (clock volume queue archive outAcc dst control savedControl advance window src
      acc current savedSource buf tmp initialControl initialSource rowCount wordR : Fin T)
    (hreg : [clock,volume,queue,archive,outAcc,dst,control,savedControl,advance,window,src,
      acc,current,savedSource,buf,tmp,initialControl,initialSource,rowCount,wordR].Nodup)
    (w a n origin span : ℕ) (Fs : List (ZMod t → GaussianInt)) (hn : 0 < n)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = Fs.length) (hvolume : (S.R volume).length = span*w)
    (hc : S.R control = localRowControls A s t a n origin w)
    (hqueue : S.R queue = (Fs.flatMap fun F => cstream A w (cyclicInterval origin span F))++tail)
    (hrow : (S.R rowCount).length = 1) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [dst,src,savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    let input := fun F => cstream A w (cyclicInterval origin span F)
    let output := fun F => cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
    ∃ v' B m, v'.user = v.user ∧ m ≤ Fs.length*(cyclicSelectionReplicaStepCost n span w+3)+2 ∧
      Exec body (countedLoop clock (cyclicSelectionReplicaStep volume queue archive outAcc dst control
        savedControl advance window src acc current savedSource buf tmp initialControl initialSource rowCount wordR))
        (Host.mk v S) m (Host.mk v' B) ∧
      B.R queue = tail ∧ B.R archive = (Fs.flatMap input).reverse++S.R archive ∧
      B.R outAcc = (Fs.flatMap output).reverse++S.R outAcc ∧ B.R clock = [] ∧
      B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
      ∀ k, k ≠ queue → k ≠ archive → k ≠ outAcc → k ≠ clock → B.R k = S.R k := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let input := fun F : ZMod t → GaussianInt => cstream A w (cyclicInterval origin span F)
  let output := fun F : ZMod t → GaussianInt => cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))
  let Inv := fun j (R : Stacks T A) => ∃ done todo : List (ZMod t → GaussianInt),
    Fs = done++todo ∧ done.length = j ∧ R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ k, k ≠ queue → k ≠ archive → k ≠ outAcc → k ≠ clock → R.R k = S.R k) ∧
    R.R queue = todo.flatMap input++tail ∧
    R.R archive = (done.flatMap input).reverse++S.R archive ∧
    R.R outAcc = (done.flatMap output).reverse++S.R outAcc
  obtain ⟨v',B,m,hu,hm,he,hclock',hI⟩ := countedLoop_exec (body := body) clock
    (cyclicSelectionReplicaStep volume queue archive outAcc dst control savedControl advance window src
      acc current savedSource buf tmp initialControl initialSource rowCount wordR)
    Fs.length (cyclicSelectionReplicaStepCost n span w) Inv
    (by
      intro j R xs hI
      obtain ⟨done,todo,hFs,hlen,hi,ho,hl,hframe,hq,ha,hout⟩ := hI
      refine ⟨done,todo,hFs,hlen,hi,ho,hl,?_,?_,?_,?_⟩
      · intro k hkq hka hko hkc
        simpa only [Function.update_of_ne hkc] using hframe k hkq hka hko hkc
      · simpa only [Function.update_of_ne ‹clock ≠ queue›.symm] using hq
      · simpa only [Function.update_of_ne ‹clock ≠ archive›.symm] using ha
      · simpa only [Function.update_of_ne ‹clock ≠ outAcc›.symm] using hout)
    (by
      intro j hj vi R hI
      obtain ⟨done,todo,hFs,hlen,hi,ho,hl,hframe,hq,ha,hout⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hFs; subst Fs; omega
      | cons F todo =>
        have hcontrols : ∀ k ∈ [volume,control,rowCount,wordR,dst,src,savedControl,advance,window,
            acc,current,savedSource,buf,tmp,initialControl,initialSource], R.R k = S.R k := by
          intro k hk
          apply hframe
          all_goals
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨vf,mf,huf,hmf,hef⟩ := cyclicSelectionReplicaStep_exec (body := body)
          volume queue archive outAcc dst control savedControl advance window src acc current savedSource buf tmp
          initialControl initialSource rowCount wordR hreg.tail w a n origin span F hn hwindow
          (todo.flatMap input++tail) vi R
          (by rw [hcontrols _ (by simp)]; exact hvolume)
          (by rw [hcontrols _ (by simp)]; exact hc)
          (by simpa only [List.flatMap_cons,List.append_assoc] using hq)
          (by rw [hcontrols _ (by simp)]; exact hrow)
          (by rw [hcontrols _ (by simp)]; exact hw)
          (by
            intro k hk
            have hk' : k ∈ [volume,control,rowCount,wordR,dst,src,savedControl,advance,window,
                acc,current,savedSource,buf,tmp,initialControl,initialSource] :=
              List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)))
            rw [hcontrols k hk']
            exact hclean k hk)
        let R' : Stacks T A := {R with R := (Function.update (Function.update (Function.update R.R queue
          (todo.flatMap input++tail)) archive ((input F).reverse++R.R archive)) outAcc ((output F).reverse++R.R outAcc))}
        refine ⟨vf,R',mf,huf,hmf,hef,?_,done++[F],todo,?_,?_,hi,ho,hl,?_,?_,?_,?_⟩
        · simp [R',‹clock ≠ queue›,‹clock ≠ archive›,‹clock ≠ outAcc›]
        · simpa only [List.append_assoc,List.singleton_append] using hFs
        · simp only [List.length_append,List.length_singleton,hlen]
        · intro k hkq hka hko hkc
          simpa only [R',Function.update_of_ne hkq,Function.update_of_ne hka,Function.update_of_ne hko]
            using hframe k hkq hka hko hkc
        · simp [R',‹queue ≠ outAcc›,‹queue ≠ archive›]
        · simp only [R',Function.update_of_ne ‹archive ≠ outAcc›,Function.update_self,ha,
            List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append,List.append_assoc]
        · simp only [R',Function.update_self,hout,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
            List.append_nil,List.reverse_append,List.append_assoc])
    v S hclock ⟨[],Fs,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hqueue,by simp,by simp⟩
  obtain ⟨done,todo,hFs,hlen,hi,ho,hl,hframe,hq,ha,hout⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hFs
    simp only [List.length_append] at hh
    cases todo with
    | nil => rfl
    | cons F todo => simp only [List.length_cons] at hh; omega
  subst todo
  simp only [List.append_nil] at hFs
  subst done
  exact ⟨v',B,m,hu,hm,he,by simpa using hq,ha,hout,hclock',hi,ho,hl,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
