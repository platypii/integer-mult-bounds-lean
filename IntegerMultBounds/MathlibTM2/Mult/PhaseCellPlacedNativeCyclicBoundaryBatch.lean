module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryBatch

/-! All solved boundary rows are projected beside the retained cached passes.
The two global writes leave both cached banks and RHS queues untouched. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 840 Q A U}

def placedNativeCyclicBoundaryBatch : Pr P 840 Q A U :=
  embProg recoveryBank Empty.elim (nativeCyclicBoundaryBatch (P := Empty))

def placedNativeCyclicBoundaryBatchState (S : Stacks 840 A)
    (tail output : List (Fin (A+4))) : Stacks 840 A :=
  {S with R := (Function.update (Function.update S.R (recoveryBank 132)
    (output++S.R (recoveryBank 132))) (recoveryBank 224) tail)}

theorem placedNativeCyclicBoundaryBatchState_pass_frame (S : Stacks 840 A)
    (tail output : List (Fin (A+4))) (k : Fin 834)
    (hk : CyclicReplicaPlacement.left.Owns k ∨ CyclicReplicaPlacement.right.Owns k) :
    (placedNativeCyclicBoundaryBatchState S tail output).L (extendCaller k) = S.L (extendCaller k) ∧
    (placedNativeCyclicBoundaryBatchState S tail output).R (extendCaller k) = S.R (extendCaller k) := by
  have hoff (i : Fin 240) : extendCaller k ≠ recoveryBank i := by
    rcases hk with hk | hk
    · exact (CyclicRecoveryPlacement.bank_left_disjoint i k hk).symm
    · exact (CyclicRecoveryPlacement.bank_right_disjoint i k hk).symm
  refine ⟨rfl,?_⟩
  simp only [placedNativeCyclicBoundaryBatchState,Function.update_of_ne (hoff 224),
    Function.update_of_ne (hoff 132)]

theorem placedNativeCyclicBoundaryBatch_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (q w W : ℕ) (rows : List (List GaussianInt))
    (hlens : ∀ row ∈ rows, row.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 840 Q A U) (S : Stacks 840 A) (tail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk recoveryBank S)))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) (embStk recoveryBank S))) q w W
      (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i : Fin 224, S.L (recoveryBank (sharedPageBoundaryUnfoldReg i)) = [])
    (hsource : S.R (recoveryBank 224) = rows.flatMap (cstream A w)++tail)
    (hmaskR : S.R (recoveryBank 238) = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R (recoveryBank 239) = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (hfresh : ∀ i ∈ ([(231 : Fin 240),232,233,234,235,236,237]), S.R (recoveryBank i) = [])
    (hcount : (S.R (recoveryBank 229)).length = rows.length)
    (h227 : S.R (recoveryBank 227) = []) (h228 : S.R (recoveryBank 228) = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let fields := fun solution =>
      cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
        cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    let F := placedNativeCyclicBoundaryBatchState S tail (rows.reverse.flatMap fields)
    ∃ vf m, vf.user = v.user ∧ m ≤ nativeCyclicBoundaryBatchCost rows.length B.card n w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        nativeCyclicBoundaryBatchWorkspace rows.length B.card n w) 0
        placedNativeCyclicBoundaryBatch (mk v S) m (mk vf F) ∧
      NativeBoundaryUnfoldWorkspace B.card (embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk recoveryBank F)) ∧
      BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
        (embStk recoveryBank F))) q w W B.card := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let fields := fun solution =>
    cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  let output := rows.reverse.flatMap fields
  let T := nativeCyclicBoundaryRowState (embStk recoveryBank S) tail output []
  obtain ⟨vi,m,hui,hm,hei,hwT,hrT⟩ := nativeCyclicBoundaryBatch_exec
    (body := fun z : Empty => nomatch z) hst hA band a n ha hn q w W rows hlens
    (embDn recoveryBank v) (embStk recoveryBank S) tail hwork hready hleft hsource hmaskR hmaskL
    hfresh hcount h227 h228
  obtain ⟨vf,_,hu,he⟩ := exec_emb_ovr_within_stock (body' := body) (ι := Empty.elim)
    recoveryBank CyclicRecoveryPlacement.bank_injective (fun z => nomatch z) hei v rfl S rfl
  have hfinal : embOvr recoveryBank T.get S = placedNativeCyclicBoundaryBatchState S tail output := by
    dsimp only [T,nativeCyclicBoundaryRowState,nativeCyclicBoundaryRecoveryState]
    simp only [List.nil_append]
    rw [embOvr_updateR_updateR CyclicRecoveryPlacement.bank_injective]
    rfl
  have hview : embStk recoveryBank (placedNativeCyclicBoundaryBatchState S tail output) = T :=
    (congrArg (embStk recoveryBank) hfinal).symm.trans
      (embStk_ovr CyclicRecoveryPlacement.bank_injective T S)
  refine ⟨vf,m,hu.trans hui,hm,he.cast rfl (congrArg (mk vf) hfinal),?_,?_⟩
  · rw [hview]; exact hwT
  · rw [hview]; exact hrT

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
