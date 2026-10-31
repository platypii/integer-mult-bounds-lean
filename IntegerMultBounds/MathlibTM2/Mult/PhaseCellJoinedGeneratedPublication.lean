module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedGeneratedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinOwnedArchives
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

theorem joinedGeneratedCorePublication_exec
    (next joinSaved remainder quotient coreWidth product clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
      wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [next,joinSaved,remainder,quotient,coreWidth,product,clock₁,padRows₁,control₁,window₁,clock₂,padRows₂,control₂,window₂,
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
    (outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (List.ofFn fun j => cstream A w (padded₁ j).flatten).flatten)
    (hnext : S.R next = (List.ofFn fun j => cstream A w (padded₂ j).flatten).flatten)
    (hjoinSaved : S.R joinSaved = [])
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
      n ≤ 4*((List.ofFn fun j => cstream A w (padded₁ j).flatten).flatten.length+
        (List.ofFn fun j => cstream A w (padded₂ j).flatten).flatten.length)+6+
        (preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+
        replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7)) ∧
      Exec body (.seq (joinOwnedArchives src next joinSaved) (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂]))))
        (mk v S) n (mk v' F) ∧
      F.R src = [] ∧ F.R next = [] ∧ F.R dst = (List.ofFn fun j => generatedCoreOutput (s := s) width w hw (rows j) (ambient j)).flatten++outputTail ∧
      F.R clock₁ = [] ∧ F.R clock₂ = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ next → i ≠ dst → i ≠ clock₁ → i ≠ clock₂ → F.R i = S.R i) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+2*((4*((List.ofFn fun j => cstream A w (padded₁ j).flatten).flatten.length+(List.ofFn fun j => cstream A w (padded₂ j).flatten).flatten.length)+6)+(preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7))))
        0 (.seq (joinOwnedArchives src next joinSaved) (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂])))) (mk v S) n (mk v' F) ∧
      ∀ j : Fin B, ∀ i, ‖pairedCellRead q w ((F.R dst).drop (j.val*(s*w))) i-target j i‖ ≤ error := by
  have hr := hreg
  regs_ne hr
  let X := (List.ofFn fun j => cstream A w (padded₁ j).flatten).flatten
  let Y := (List.ofFn fun j => cstream A w (padded₂ j).flatten).flatten
  obtain ⟨v₀,hu₀,he₀⟩ := joinOwnedArchives_exec (body := body) src next joinSaved (by regs_nodup) X Y v S hsrc hnext hjoinSaved
  let M : Stacks T A := {S with R := Function.update (Function.update S.R src (X++Y)) next []}
  have hstable (i : Fin T) (his : i ≠ src) (hin : i ≠ next) : M.R i = S.R i := by simp [M,his,hin]
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hs,hd,hc₁',hc₂',hi,ho,hl,hframe,hstock,haccuracy⟩ := preparedGeneratedCorePublication_exec
    remainder quotient coreWidth product clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
    wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved (by regs_nodup)
    width q w missing₁ missing₂ hw hw1 rows hrows padded₁ padded₂ hpadded₁ hpadded₂ hcount₁ hcount₂ hdrop₁ hdrop₂
    ambient hambient target error hgood [] outputTail v₀ M
    (by simp [M,X,Y,‹next ≠ src›.symm])
    (by rw [hstable _ ‹src ≠ dst›.symm ‹next ≠ dst›.symm]; exact hdst)
    (by rw [hstable _ ‹clock₁ ≠ src› ‹next ≠ clock₁›.symm]; exact hclock₁)
    (by rw [hstable _ ‹clock₂ ≠ src› ‹next ≠ clock₂›.symm]; exact hclock₂)
    (by rw [hstable _ ‹padRows₁ ≠ src› ‹next ≠ padRows₁›.symm]; exact hpad₁)
    (by rw [hstable _ ‹padRows₂ ≠ src› ‹next ≠ padRows₂›.symm]; exact hpad₂)
    (by rw [hstable _ ‹wordWidth ≠ src› ‹next ≠ wordWidth›.symm]; exact hwidth)
    (by rw [hstable _ ‹src ≠ lineRows›.symm ‹next ≠ lineRows›.symm]; exact hline)
    (by rw [hstable _ ‹remainder ≠ src› ‹next ≠ remainder›.symm]; exact hrem)
    (by rw [hstable _ ‹quotient ≠ src› ‹next ≠ quotient›.symm]; exact hquot)
    (by rw [hstable _ ‹coreWidth ≠ src› ‹next ≠ coreWidth›.symm]; exact hcore)
    (by rw [hstable _ ‹product ≠ src› ‹next ≠ product›.symm]; exact hproduct)
    (by rw [hstable _ ‹control₁ ≠ src› ‹next ≠ control₁›.symm]; exact hc₁)
    (by rw [hstable _ ‹control₂ ≠ src› ‹next ≠ control₂›.symm]; exact hc₂)
    (by rw [hstable _ ‹window₁ ≠ src› ‹next ≠ window₁›.symm]; exact hw₁)
    (by rw [hstable _ ‹window₂ ≠ src› ‹next ≠ window₂›.symm]; exact hw₂)
    (by
      intro i hi
      have hoff : i ≠ src ∧ i ≠ next := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals constructor <;> first | assumption | (apply Ne.symm; assumption)
      rw [hstable i hoff.1 hoff.2]
      exact hclean i hi)
  have hjoin := mn_native_exec_within he₀ 1 (joinOwnedArchives_pushBound src next joinSaved) 0
    (mnSize (mk v S)+(4*(X.length+Y.length)+6)) (by omega)
  have hsize := hjoin.final
  have htrace : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+2*((4*((List.ofFn fun j => cstream A w (padded₁ j).flatten).flatten.length+(List.ofFn fun j => cstream A w (padded₂ j).flatten).flatten.length)+6)+(preparePublicationControlsCost s width w+(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w)+(4*s*w+7))))
      0 (.seq (joinOwnedArchives src next joinSaved) (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂])))) (mk v S) ((4*(X.length+Y.length)+6)+n₁) (mk v₁ F) := by
    refine .seq (hjoin.mono ?_) (hstock.mono ?_)
    · intro d z hz
      dsimp only [X,Y] at hz
      nlinarith only [hz]
    · intro d z hz
      dsimp only [X,Y] at hsize
      nlinarith only [hz,hsize]
  refine ⟨v₁,F,(4*(X.length+Y.length)+6)+n₁,hu₁.trans hu₀,Nat.add_le_add_left hn₁ _,Exec.seq he₀ he₁,
    hs,?_,hd,hc₁',hc₂',hi,ho,hl,?_,htrace,haccuracy⟩
  · rw [hframe next ‹next ≠ src› ‹next ≠ dst› ‹next ≠ clock₁› ‹next ≠ clock₂›]
    simp [M]
  · intro i his hin hid hic₁ hic₂
    exact (hframe i his hid hic₁ hic₂).trans (hstable i his hin)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
