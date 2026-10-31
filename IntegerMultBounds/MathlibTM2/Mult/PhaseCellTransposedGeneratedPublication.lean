module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinedGeneratedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreTilePadding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinOwnedArchives
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationAccuracy

/-! Execute both class transposes and publish their actual padded outputs.
The nonempty clipped-core branch carries global accuracy, restoration and the
combined movement bill on the same returned tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₁ t₂ T Q K s c₁ c₂ d : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem transposedGeneratedCorePublication_exec
    (next joinSaved remainder quotient coreWidth product clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
      wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved : Fin T)
    (hreg : [next,joinSaved,remainder,quotient,coreWidth,product,clock₁,padRows₁,control₁,window₁,clock₂,padRows₂,control₂,window₂,
      wordWidth,retireCount,savedControl,gap,src,dst,acc,trash,tmp,lineRows,outAcc,saved].Nodup)
    (width q w missing₁ missing₂ : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w)
    (hr : 0 < s%width) (hA : 4 ≤ prime+K)
    (plan₁ : ArchiveTilePlan t₁ T Q c₁ d (width*w))
    (plan₂ : ArchiveTilePlan t₂ T Q c₂ d ((s%width)*w))
    (hsep : plan₁.src ∉ plan₂.support) (hsrcPlan : plan₁.src = src) (hnextPlan : plan₂.src = next)
    (hN₁ : (corePublicationIndices s width width).length ≤ (2^d)^c₁)
    (hN₂ : (corePublicationIndices s width (s%width)).length ≤ (2^d)^c₂)
    (hmissing₁ : missing₁ = (2^d)^c₁-(corePublicationIndices s width width).length)
    (hmissing₂ : missing₂ = (2^d)^c₂-(corePublicationIndices s width (s%width)).length)
    (rows : Fin (2^d) → ℕ → List GaussianInt)
    (hrows : ∀ j k, k ∈ coreIndices s width → (rows j k).length = coreLength s width k)
    (ambient : Fin (2^d) → List (Fin ((prime+K)+4))) (hambient : ∀ j, (ambient j).length = s*w)
    (target : Fin (2^d) → ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ j k, k ∈ coreIndices s width → PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream (prime+K) w (rows j k))) (target j) error)
    (outputTail : List (Fin ((prime+K)+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hready₁ : plan₁.Ready w (fun (i : Fin (corePublicationIndices s width width).length) j => rows j (corePublicationIndices s width width)[i]) S)
    (hready₂ : plan₂.Ready w (fun (i : Fin (corePublicationIndices s width (s%width)).length) j => rows j (corePublicationIndices s width (s%width))[i]) S)
    (hjoinSaved : S.R joinSaved = [])
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock₁ : (S.R clock₁).length = (2^d)) (hclock₂ : (S.R clock₂).length = (2^d))
    (hpad₁ : (S.R padRows₁).length = missing₁*width)
    (hpad₂ : (S.R padRows₂).length = missing₂*(s%width))
    (hwidth : (S.R wordWidth).length = w) (hline : (S.R lineRows).length = s)
    (hrem : (S.R remainder).length = s%width) (hquot : (S.R quotient).length = s/width)
    (hcore : (S.R coreWidth).length = width) (hproduct : S.R product = [])
    (hc₁ : S.R control₁ = []) (hc₂ : S.R control₂ = [])
    (hw₁ : (S.R window₁).length = width*w) (hw₂ : (S.R window₂).length = (s%width)*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp,saved,outAcc], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ plan₁.cost S+plan₂.cost S+
        (4*((2^d)*((2^d)^c₁*width*w)+(2^d)*((2^d)^c₂*(s%width)*w))+6+
        (preparePublicationControlsCost s width w+(replicaPublicationCost (2^d) s missing₁ width w+
        replicaPublicationCost (2^d) s missing₂ (s%width) w)+(4*s*w+7))) ∧
      Exec body (.seq (.seq plan₁.program plan₂.program) (.seq (joinOwnedArchives src next joinSaved) (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
        (.seq (.seq
        (.seq (countedLoop clock₁ (replicaPublicationStep (P := P) (Q := Q) (A := prime+K) (U := U) padRows₁ wordWidth retireCount control₁ savedControl gap window₁ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))
        (.seq (countedLoop clock₂ (replicaPublicationStep padRows₂ wordWidth retireCount control₂ savedControl gap window₂ src dst acc trash tmp lineRows outAcc saved)) (moveR outAcc dst id))) (clearWords [control₁,control₂])))))
        (mk v S) n (mk v' F) ∧
      F.R src = [] ∧ F.R next = [] ∧ F.R dst = (List.ofFn fun j => generatedCoreOutput (s := s) width w hw (rows j) (ambient j)).flatten++outputTail ∧
      F.R clock₁ = [] ∧ F.R clock₂ = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ next → i ≠ dst → i ≠ clock₁ → i ≠ clock₂ → F.R i = S.R i) ∧
      ∀ j : Fin (2^d), ∀ i, ‖pairedCellRead q w ((F.R dst).drop (j.val*(s*w))) i-target j i‖ ≤ error := by
  have hregs := hreg
  regs_ne hregs
  have hlen (L : ℕ) (i : Fin (corePublicationIndices s width L).length) (j : Fin (2^d)) :
      (rows j (corePublicationIndices s width L)[i]).length = L := by
    have hk := (mem_corePublicationIndices s width L _).mp (List.getElem_mem i.isLt)
    exact (hrows j _ hk.1).trans hk.2
  obtain ⟨padded₁,padded₂,hp₁,hp₂,hreal₁,hreal₂,v₀,n₀,hu₀,hn₀,he₀⟩ := ArchiveTilePlan.pair_exec
    plan₁ plan₂ hsep body hA (Nat.mul_pos hw hw1) (Nat.mul_pos hr hw1) width (s%width) w rfl rfl
    hN₁ hN₂ _ _ (hlen width) (hlen (s%width)) v S hready₁ hready₂
  let P₁ := fun j => List.ofFn (fun i => padded₁ i j)
  let P₂ := fun j => List.ofFn (fun i => padded₂ i j)
  have hpadSpec₁ (j : Fin (2^d)) := generatedCoreTilePadding_spec hN₁ rows padded₁ hp₁ hreal₁ j
  have hpadSpec₂ (j : Fin (2^d)) := generatedCoreTilePadding_spec hN₂ rows padded₂ hp₂ hreal₂ j
  let X := (List.ofFn fun j => cstream (prime+K) w (P₁ j).flatten).flatten
  let Y := (List.ofFn fun j => cstream (prime+K) w (P₂ j).flatten).flatten
  let M : Stacks T (prime+K) := {S with L := fun _ => [], R := Function.update (Function.update S.R src X) next Y}
  have he₀' : Exec body (.seq plan₁.program plan₂.program) (mk v S) n₀ (mk v₀ M) := by
    simpa only [hsrcPlan,hnextPlan] using he₀
  have hstable (i : Fin T) (his : i ≠ src) (hin : i ≠ next) : M.R i = S.R i := by simp [M,his,hin]
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hs,hnxt,hd,hc₁',hc₂',hi,ho,hl,hframe,hstock,haccuracy⟩ := joinedGeneratedCorePublication_exec
    next joinSaved remainder quotient coreWidth product clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
    wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved hreg
    width q w missing₁ missing₂ hw hw1 rows hrows P₁ P₂
    (fun j => (hpadSpec₁ j).1) (fun j => (hpadSpec₂ j).1)
    (by intro j; simpa only [hmissing₁] using (hpadSpec₁ j).2.1)
    (by intro j; simpa only [hmissing₂] using (hpadSpec₂ j).2.1)
    (by intro j; simpa only [hmissing₁] using (hpadSpec₁ j).2.2)
    (by intro j; simpa only [hmissing₂] using (hpadSpec₂ j).2.2)
    ambient hambient target error hgood outputTail v₀ M
    (by simp [M,X,‹next ≠ src›.symm]) (by simp [M,Y])
    (by rw [hstable _ ‹joinSaved ≠ src› ‹next ≠ joinSaved›.symm]; exact hjoinSaved)
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
      rw [hstable i hoff.1 hoff.2]; exact hclean i hi)
  have hx : X.length = (2^d)*((2^d)^c₁*width*w) := paddedArchiveStream_length w padded₁ hp₁
  have hy : Y.length = (2^d)*((2^d)^c₂*(s%width)*w) := paddedArchiveStream_length w padded₂ hp₂
  change n₁ ≤ 4*(X.length+Y.length)+6+_ at hn₁
  rw [hx,hy] at hn₁
  refine ⟨v₁,F,n₀+n₁,hu₁.trans hu₀,Nat.add_le_add hn₀ hn₁,Exec.seq he₀' he₁,
    hs,hnxt,hd,hc₁',hc₂',hi,ho,?_,?_,haccuracy⟩
  · exact hl.trans (by funext i; exact (hready₁.hL i).symm)
  · intro i his hin hid hic₁ hic₂
    exact (hframe i his hin hid hic₁ hic₂).trans (hstable i his hin)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
