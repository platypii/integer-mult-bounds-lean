module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCorePublicationExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationAccuracy

/-! Execute the generated full-width and remainder classes from padded row
archives. The returned replica lines carry global accuracy and simultaneous
stock bounds for the same execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s B : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem preparedGeneratedCorePublication_exec
    (remainder quotient coreWidth product clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
      wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [remainder,quotient,coreWidth,product,clock₁,padRows₁,control₁,window₁,clock₂,padRows₂,control₂,window₂,
      wordWidth,retireCount,savedControl,gap,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (width q w missing₁ missing₂ : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w)
    (rows : Fin B → ℕ → List GaussianInt)
    (hrows : ∀ j k, k ∈ coreIndices s width → (rows j k).length = coreLength s width k)
    (padded₁ padded₂ : Fin B → List (List GaussianInt))
    (hpadded₁ : ∀ j row, row ∈ padded₁ j → row.length = width)
    (hpadded₂ : ∀ j row, row ∈ padded₂ j → row.length = s%width)
    (hcount₁ : ∀ j, missing₁+(corePublicationIndices s width width).length = (padded₁ j).length)
    (hcount₂ : ∀ j, missing₂+(corePublicationIndices s width (s%width)).length = (padded₂ j).length)
    (hdrop₁ : ∀ j, (padded₁ j).flatten.drop (missing₁*width) = ((corePublicationIndices s width width).map (rows j)).flatten)
    (hdrop₂ : ∀ j, (padded₂ j).flatten.drop (missing₂*(s%width)) = ((corePublicationIndices s width (s%width)).map (rows j)).flatten)
    (ambient : Fin B → List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = s*w)
    (target : Fin B → ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ j k, k ∈ coreIndices s width → PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream A w (rows j k))) (target j) error)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (List.ofFn fun j => cstream A w (padded₁ j).flatten).flatten++
      ((List.ofFn fun j => cstream A w (padded₂ j).flatten).flatten++sourceTail))
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock₁ : (S.R clock₁).length = B) (hclock₂ : (S.R clock₂).length = B)
    (hpad₁ : (S.R padRows₁).length = missing₁*width)
    (hpad₂ : (S.R padRows₂).length = missing₂*(s%width))
    (hwidth : (S.R wordWidth).length = w) (hline : (S.R lineRows).length = s)
    (hrem : (S.R remainder).length = s%width) (hquot : (S.R quotient).length = s/width)
    (hcore : (S.R coreWidth).length = width) (hproduct : S.R product = [])
    (hc₁ : S.R control₁ = []) (hc₂ : S.R control₂ = [])
    (hw₁ : (S.R window₁).length = width*w) (hw₂ : (S.R window₂).length = (s%width)*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved,outAcc], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+
        replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7) ∧
      Exec body (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂])))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = (List.ofFn fun j => generatedCoreOutput (s := s) width w hw (rows j) (ambient j)).flatten++outputTail ∧
      F.R clock₁ = [] ∧ F.R clock₂ = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock₁ → i ≠ clock₂ → F.R i = S.R i) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+2*(preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7)))
        0 (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂]))) (mk v S) n (mk v' F) ∧
      ∀ j : Fin B, ∀ i, ‖pairedCellRead q w ((F.R dst).drop (j.val*(s*w))) i-target j i‖ ≤ error := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := preparePublicationControls_exec (body := body)
    remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp (by regs_nodup)
    s width w hw v S hrem hquot hcore hwidth hproduct (hclean _ (by simp)) (hclean _ (by simp))
  let g₁ := gatherControls A ((corePublicationWindows s width width hw).gaps w)
  let g₂ := gatherControls A ((corePublicationWindows s width (s%width) hw).gaps w)
  let M : Stacks T A := {S with R := Function.update (Function.update S.R control₁ g₁) control₂ g₂}
  have he₀' : Exec body (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
      (mk v S) n₀ (mk v₀ M) := by simpa only [hc₁,hc₂,List.append_nil] using he₀
  have hstable (i : Fin T) (hi₁ : i ≠ control₁) (hi₂ : i ≠ control₂) : M.R i = S.R i := by simp [M,hi₁,hi₂]
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hs,hd,hclock₁',hclock₂',hi,ho,hl,hframe,_,haccuracy⟩ := generatedCorePublication_exec
    clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
    wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved (by regs_nodup)
    width q w missing₁ missing₂ hw hw1 rows hrows padded₁ padded₂ hpadded₁ hpadded₂ hcount₁ hcount₂ hdrop₁ hdrop₂
    ambient hambient target error hgood sourceTail outputTail v₀ M
    (by rw [hstable _ ‹control₁ ≠ src›.symm ‹control₂ ≠ src›.symm]; exact hsrc)
    (by rw [hstable _ ‹control₁ ≠ dst›.symm ‹control₂ ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock₁ ≠ control₁› ‹clock₁ ≠ control₂›]; exact hclock₁)
    (by rw [hstable _ ‹control₁ ≠ clock₂›.symm ‹clock₂ ≠ control₂›]; exact hclock₂)
    (by rw [hstable _ ‹padRows₁ ≠ control₁› ‹padRows₁ ≠ control₂›]; exact hpad₁)
    (by rw [hstable _ ‹control₁ ≠ padRows₂›.symm ‹padRows₂ ≠ control₂›]; exact hpad₂)
    (by rw [hstable _ ‹control₁ ≠ wordWidth›.symm ‹control₂ ≠ wordWidth›.symm]; exact hwidth)
    (by rw [hstable _ ‹control₁ ≠ lineRows›.symm ‹control₂ ≠ lineRows›.symm]; exact hline)
    (by simp [M,g₁,‹control₁ ≠ control₂›]) (by simp [M,g₂])
    (by rw [hstable _ ‹control₁ ≠ window₁›.symm ‹window₁ ≠ control₂›]; exact hw₁)
    (by rw [hstable _ ‹control₁ ≠ window₂›.symm ‹control₂ ≠ window₂›.symm]; exact hw₂)
    (by
      intro i hi
      have hoff : i ≠ control₁ ∧ i ≠ control₂ := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)
      rw [hstable i hoff.1 hoff.2]
      exact hclean i hi)
  have hg₁ : F.R control₁ = g₁ := by
    rw [hframe control₁ ‹control₁ ≠ src› ‹control₁ ≠ dst› ‹clock₁ ≠ control₁›.symm ‹control₁ ≠ clock₂›]
    simp [M,‹control₁ ≠ control₂›]
  have hg₂ : F.R control₂ = g₂ := by
    rw [hframe control₂ ‹control₂ ≠ src› ‹control₂ ≠ dst› ‹clock₁ ≠ control₂›.symm ‹clock₂ ≠ control₂›.symm]
    simp [M]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := releasePublicationControls_exec (body := body)
    control₁ control₂ ‹control₁ ≠ control₂› s width w hw hw1 v₁ F hg₁ hg₂
  let G : Stacks T A := {F with R := fun i => if i ∈ [control₁,control₂] then [] else F.R i}
  have hkeep (i : Fin T) (hi₁ : i ≠ control₁) (hi₂ : i ≠ control₂) : G.R i = F.R i := by simp [G,hi₁,hi₂]
  have htime : n₀+(n₁+n₂) ≤ preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7) := by
    have hh := Nat.add_le_add hn₁ hn₂
    have ht := Nat.add_le_add hn₀ hh
    omega
  have hex := Exec.seq he₀' (Exec.seq he₁ he₂)
  have hpush : mnNativePushBound 2 (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂]))) :=
    ⟨preparePublicationControls_pushBound _ _ _ _ _ _ _ _ _,
      ⟨⟨replicaPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
        replicaPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩,
        by simp [clearWords,uclear,scanR,drainR,popDo,whileR,peekR,mnNativePushBound,mnActPush]⟩⟩
  have hstock := mn_native_exec_within hex 2 hpush 0 (mnSize (mk v S)+2*(preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7))) (by omega)
  refine ⟨v₂,G,n₀+(n₁+n₂),hu₂.trans hu₁ |>.trans hu₀,htime,hex,?_,?_,?_,?_,hi,ho,hl,?_,hstock,?_⟩
  · rw [hkeep _ ‹control₁ ≠ src›.symm ‹control₂ ≠ src›.symm]; exact hs
  · rw [hkeep _ ‹control₁ ≠ dst›.symm ‹control₂ ≠ dst›.symm]; exact hd
  · rw [hkeep _ ‹clock₁ ≠ control₁› ‹clock₁ ≠ control₂›]; exact hclock₁'
  · rw [hkeep _ ‹control₁ ≠ clock₂›.symm ‹clock₂ ≠ control₂›]; exact hclock₂'
  · intro i his hid hic₁ hic₂
    by_cases hi₁ : i = control₁
    · subst i; simp [G,hc₁]
    · by_cases hi₂ : i = control₂
      · subst i; simp [G,hc₂]
      · rw [hkeep i hi₁ hi₂,hframe i his hid hic₁ hic₂,hstable i hi₁ hi₂]
  · intro j i
    rw [hkeep _ ‹control₁ ≠ dst›.symm ‹control₂ ≠ dst›.symm]
    exact haccuracy j i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
