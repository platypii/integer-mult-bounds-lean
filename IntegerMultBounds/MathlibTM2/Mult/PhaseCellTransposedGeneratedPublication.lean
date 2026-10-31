module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinedGeneratedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTilePair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreTilePadding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinOwnedArchives
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationAccuracy

/-! Execute both class transposes and publish their actual padded outputs.
Empty classes are skipped at runtime. Global accuracy, restoration and the
combined movement bill concern the same returned tape.
The previous nonempty-only supplier is available in commit e05d4aea. -/
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
    (hA : 4 ≤ prime+K)
    (plan₁ : ArchiveTilePlan t₁ T Q c₁ d (width*w))
    (plan₂ : ArchiveTilePlan t₂ T Q c₂ d ((s%width)*w))
    (hsep : plan₁.src ∉ plan₂.support) (hsrcPlan : plan₁.src = src) (hnextPlan : plan₂.src = next)
    (hN₁ : (corePublicationIndices s width width).length ≤ (2^d)^c₁)
    (hN₂ : (corePublicationIndices s width (s%width)).length ≤ (2^d)^c₂)
    (hmissing₁ : missing₁ = (ArchiveTilePlan.capacity (corePublicationIndices s width width).length ((2^d)^c₁))-(corePublicationIndices s width width).length)
    (hmissing₂ : missing₂ = (ArchiveTilePlan.capacity (corePublicationIndices s width (s%width)).length ((2^d)^c₂))-(corePublicationIndices s width (s%width)).length)
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
      n ≤ plan₁.conditionalCost (corePublicationIndices s width width).length S+plan₂.conditionalCost (corePublicationIndices s width (s%width)).length S+
        (4*((2^d)*((ArchiveTilePlan.capacity (corePublicationIndices s width width).length ((2^d)^c₁))*width*w)+(2^d)*((ArchiveTilePlan.capacity (corePublicationIndices s width (s%width)).length ((2^d)^c₂))*(s%width)*w))+6+
        (preparePublicationControlsCost s width w+(replicaPublicationCost (2^d) s missing₁ width w+
        replicaPublicationCost (2^d) s missing₂ (s%width) w)+(4*s*w+7))) ∧
      Exec body (.seq (.seq (plan₁.conditionalProgram quotient) (plan₂.conditionalProgram remainder)) (.seq (joinOwnedArchives src next joinSaved) (.seq (preparePublicationControls remainder quotient coreWidth wordWidth product control₁ control₂ saved tmp)
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
  have hflag {α : Type} (xs : List α) (n : ℕ) (hlen : xs.length = n) : xs.head?.isSome = decide (0 < n) := by
    subst n
    cases xs <;> simp
  have hfull : (corePublicationIndices s width width).length = s/width := by
    rw [corePublication_full_indices s width hw,List.length_range]
  have hremCount : 0 < (corePublicationIndices s width (s%width)).length ↔ 0 < s%width := by
    rw [corePublication_remainder_indices s width hw]
    by_cases hr : 0 < s%width <;> simp [hr]
  obtain ⟨result₁,result₂,hcap₁,hcap₂,v₀,n₀,hu₀,hn₀,he₀⟩ := ArchiveTilePlan.conditional_pair_exec
    plan₁ plan₂ quotient remainder hsep (by rw [hsrcPlan]; exact ‹remainder ≠ src›)
    body hA (fun _ => Nat.mul_pos hw hw1) (fun hn => Nat.mul_pos (hremCount.mp hn) hw1)
    width (s%width) w rfl rfl hN₁ hN₂ _ _ (hlen width) (hlen (s%width)) v S hready₁ hready₂
    (by rw [hfull]; exact hflag _ _ hquot)
    (by simpa only [hremCount] using hflag _ _ hrem)
  let padded₁ := result₁.padded
  let padded₂ := result₂.padded
  have hp₁ := result₁.rowLength
  have hp₂ := result₂.rowLength
  have hreal₁ := result₁.realRows
  have hreal₂ := result₂.realRows
  have hmissing₁' : missing₁ = result₁.capacity-(corePublicationIndices s width width).length := by
    rw [hcap₁]; exact hmissing₁
  have hmissing₂' : missing₂ = result₂.capacity-(corePublicationIndices s width (s%width)).length := by
    rw [hcap₂]; exact hmissing₂
  let P₁ := fun j => List.ofFn (fun i => padded₁ i j)
  let P₂ := fun j => List.ofFn (fun i => padded₂ i j)
  have hpadSpec₁ (j : Fin (2^d)) := generatedCoreTilePadding_spec result₁.capacity_ge rows padded₁ hp₁ hreal₁ j
  have hpadSpec₂ (j : Fin (2^d)) := generatedCoreTilePadding_spec result₂.capacity_ge rows padded₂ hp₂ hreal₂ j
  let X := (List.ofFn fun j => cstream (prime+K) w (P₁ j).flatten).flatten
  let Y := (List.ofFn fun j => cstream (prime+K) w (P₂ j).flatten).flatten
  let M : Stacks T (prime+K) := {S with L := fun _ => [], R := Function.update (Function.update S.R src X) next Y}
  have he₀' : Exec body (.seq (plan₁.conditionalProgram quotient) (plan₂.conditionalProgram remainder)) (mk v S) n₀ (mk v₀ M) := by
    simpa only [hsrcPlan,hnextPlan] using he₀
  have hstable (i : Fin T) (his : i ≠ src) (hin : i ≠ next) : M.R i = S.R i := by simp [M,his,hin]
  obtain ⟨v₁,F,n₁,hu₁,hn₁,he₁,hs,hnxt,hd,hc₁',hc₂',hi,ho,hl,hframe,hstock,haccuracy⟩ := joinedGeneratedCorePublication_exec
    next joinSaved remainder quotient coreWidth product clock₁ padRows₁ control₁ window₁ clock₂ padRows₂ control₂ window₂
    wordWidth retireCount savedControl gap src dst acc trash tmp lineRows outAcc saved hreg
    width q w missing₁ missing₂ hw hw1 rows hrows P₁ P₂
    (fun j => (hpadSpec₁ j).1) (fun j => (hpadSpec₂ j).1)
    (by intro j; simpa only [hmissing₁'] using (hpadSpec₁ j).2.1)
    (by intro j; simpa only [hmissing₂'] using (hpadSpec₂ j).2.1)
    (by intro j; simpa only [hmissing₁'] using (hpadSpec₁ j).2.2)
    (by intro j; simpa only [hmissing₂'] using (hpadSpec₂ j).2.2)
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
  have hx : X.length = (2^d)*((ArchiveTilePlan.capacity (corePublicationIndices s width width).length ((2^d)^c₁))*width*w) := by
    have hh : X.length = (2^d)*(result₁.capacity*width*w) := paddedArchiveStream_length w padded₁ hp₁
    rw [hcap₁] at hh
    exact hh
  have hy : Y.length = (2^d)*((ArchiveTilePlan.capacity (corePublicationIndices s width (s%width)).length ((2^d)^c₂))*(s%width)*w) := by
    have hh : Y.length = (2^d)*(result₂.capacity*(s%width)*w) := paddedArchiveStream_length w padded₂ hp₂
    rw [hcap₂] at hh
    exact hh
  change n₁ ≤ 4*(X.length+Y.length)+6+_ at hn₁
  rw [hx,hy] at hn₁
  refine ⟨v₁,F,n₀+n₁,hu₁.trans hu₀,Nat.add_le_add hn₀ hn₁,Exec.seq he₀' he₁,
    hs,hnxt,hd,hc₁',hc₂',hi,ho,?_,?_,haccuracy⟩
  · exact hl.trans (by funext i; exact (hready₁.hL i).symm)
  · intro i his hin hid hic₁ hic₂
    exact (hframe i his hin hid hic₁ hic₂).trans (hstable i his hin)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
