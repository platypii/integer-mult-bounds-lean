module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationPair
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

theorem generatedCorePublication_exec
    (clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
      wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [clock₁,padRows₁,control₁,window₁,clock₂,padRows₂,control₂,window₂,
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
    (hc₁ : S.R control₁ = gatherControls A ((corePublicationWindows s width width hw).gaps w))
    (hc₂ : S.R control₂ = gatherControls A ((corePublicationWindows s width (s%width) hw).gaps w))
    (hw₁ : (S.R window₁).length = width*w) (hw₂ : (S.R window₂).length = (s%width)*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved,outAcc], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ replicaPublicationCost B s missing₁ width w+
        replicaPublicationCost B s missing₂ (s%width) w ∧
      Exec body (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id)))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = (List.ofFn fun j => generatedCoreOutput (s := s) width w hw (rows j) (ambient j)).flatten++outputTail ∧
      F.R clock₁ = [] ∧ F.R clock₂ = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock₁ → i ≠ clock₂ → F.R i = S.R i) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+
        2*(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w))
        0 (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (mk v S) n (mk v' F) ∧
      ∀ j : Fin B, ∀ i, ‖pairedCellRead q w ((F.R dst).drop (j.val*(s*w))) i-target j i‖ ≤ error := by
  let r₁ := fun j => generatedCoreReplica s width width (rows j) (padded₁ j) (ambient j)
  let r₂ := fun j => generatedCoreReplica s width (s%width) (rows j) (padded₂ j)
    (coreClassOutput (s := s) width width w hw (rows j) (ambient j))
  have hv₁ : ∀ r ∈ List.ofFn r₁, r.Valid (corePublicationWindows s width width hw) w missing₁ := by
    intro r hr
    obtain ⟨j,he⟩ := List.mem_ofFn.mp hr
    subst r
    exact generatedCoreReplica_valid width width w missing₁ hw (rows j) (hrows j)
      (padded₁ j) (hpadded₁ j) (hcount₁ j) (hdrop₁ j) (ambient j) (hambient j)
  have hclassLength (j : Fin B) : (coreClassOutput (s := s) width width w hw (rows j) (ambient j)).length = s*w := by
    apply coreClassOutput_length width width w hw (rows j) _ (ambient j) (hambient j)
    intro k hk
    have hk' := (mem_corePublicationIndices s width width k).mp hk
    exact (hrows j k hk'.1).trans hk'.2
  have hv₂ : ∀ r ∈ List.ofFn r₂, r.Valid (corePublicationWindows s width (s%width) hw) w missing₂ := by
    intro r hr
    obtain ⟨j,he⟩ := List.mem_ofFn.mp hr
    subst r
    exact generatedCoreReplica_valid width (s%width) w missing₂ hw (rows j) (hrows j)
      (padded₂ j) (hpadded₂ j) (hcount₂ j) (hdrop₂ j) _ (hclassLength j)
  obtain ⟨v',F,n,hu,hn,he,hs,hd,hc₁',hc₂',hi,ho,hl,hframe⟩ := publicationPair_exec
    clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
    wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved hreg
    (corePublicationWindows s width width hw) (corePublicationWindows s width (s%width) hw)
    w missing₁ missing₂ hw1 (List.ofFn r₁) (List.ofFn r₂) hv₁ hv₂
    (by simp only [List.flatMap,List.map_ofFn,Function.comp_def,r₁,r₂,generatedCoreReplica,
          PublicationReplica.output,PublicationReplica.words,coreClassOutput])
    sourceTail outputTail v S
    (by simpa only [List.flatMap,List.map_ofFn,Function.comp_def,r₁,r₂,generatedCoreReplica,PublicationReplica.input] using hsrc)
    (by simpa only [List.flatMap,List.map_ofFn,Function.comp_def,r₁,generatedCoreReplica] using hdst)
    (by simpa using hclock₁) (by simpa using hclock₂) hpad₁ hpad₂ hwidth hline hc₁ hc₂ hw₁ hw₂ hclean
  have hd' : F.R dst = (List.ofFn fun j => generatedCoreOutput (s := s) width w hw (rows j) (ambient j)).flatten++outputTail := by
    simpa only [List.flatMap,List.map_ofFn,Function.comp_def,r₁,r₂,generatedCoreReplica,
      PublicationReplica.output,PublicationReplica.words,coreClassOutput,generatedCoreOutput] using hd
  have hn' : n ≤ replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w := by
    simpa only [List.length_ofFn] using hn
  have hpush : mnNativePushBound 2 (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := A) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) :=
    ⟨replicaPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      replicaPublication_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  have hstock := mn_native_exec_within he 2 hpush 0
    (mnSize (mk v S)+2*(replicaPublicationCost B s missing₁ width w+replicaPublicationCost B s missing₂ (s%width) w))
    (by omega)
  refine ⟨v',F,n,hu,hn',he,hs,hd',hc₁',hc₂',hi,ho,hl,hframe,hstock,?_⟩
  let lines := List.ofFn fun j => generatedCoreOutput (s := s) width w hw (rows j) (ambient j)
  have hlength : ∀ line ∈ lines, line.length = s*w := by
    intro line hr
    obtain ⟨j,he⟩ := List.mem_ofFn.mp hr
    subst line
    exact generatedCoreOutput_length width w hw (rows j) (hrows j) (ambient j) (hambient j)
  intro j i
  have hword := fixedLines_word (s*w) w lines hlength outputTail j.val (i.val*w)
    (by simpa [lines] using j.isLt) (by
      have hh := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.val_lt)
      simpa only [Nat.succ_mul] using hh)
  rw [hd']
  change ‖value q (decodeWord ((((lines.flatten++outputTail).drop (j.val*(s*w))).drop (i.val*w)).take w))-target j i‖ ≤ error
  rw [hword]
  simpa only [lines,List.getElem_ofFn,pairedCellRead] using
    generatedCoreOutput_error width q w hw (rows j) (hrows j) (ambient j) (hambient j) (target j) error (hgood j) i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
