module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryRecovery

/-! The native recovery stage sits beside both cached pass banks, with just six
new scratch tapes. Its single output write preserves both cached footprints. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicRecoveryPlacement
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 840 Q A U}

def placedNativeCyclicBoundaryRecovery : Pr P 840 Q A U :=
  embProg recoveryBank Empty.elim (nativeCyclicBoundaryRecovery (P := Empty))

def placedNativeCyclicBoundaryRecoveryState (S : Stacks 840 A)
    (left right : List (Fin (A+4))) : Stacks 840 A :=
  {S with R := Function.update S.R (recoveryBank 132) (left++(right++S.R (recoveryBank 132)))}

theorem placedNativeCyclicBoundaryRecoveryState_pass_frame (S : Stacks 840 A)
    (left right : List (Fin (A+4))) (k : Fin 834)
    (hk : CyclicReplicaPlacement.left.Owns k ∨ CyclicReplicaPlacement.right.Owns k) :
    (placedNativeCyclicBoundaryRecoveryState S left right).L (extendCaller k) = S.L (extendCaller k) ∧
    (placedNativeCyclicBoundaryRecoveryState S left right).R (extendCaller k) = S.R (extendCaller k) := by
  refine ⟨rfl,?_⟩
  have hoff : extendCaller k ≠ recoveryBank 132 := by
    rcases hk with hk | hk
    · exact (bank_left_disjoint 132 k hk).symm
    · exact (bank_right_disjoint 132 k hk).symm
  exact Function.update_of_ne hoff _ _

theorem placedNativeCyclicBoundaryRecovery_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (solution : List GaussianInt) (w : ℕ)
    (hlen : solution.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 840 Q A U) (S : Stacks 840 A) (tail : List (Fin (A+4)))
    (hleft : ∀ i, S.L (recoveryBank i) = [])
    (hmul : ∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg (embStk recoveryBank S)).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R (recoveryBank 116)).length = (cyclicPrincipalBoundary s t band a n).card)
    (hrows : (S.R (recoveryBank 192)).length = (cyclicPrincipalBoundary s t band a n).card)
    (hw : (S.R (recoveryBank 160)).length = w)
    (hsource : S.R (recoveryBank 224) = cstream A w solution++tail)
    (hmaskR : S.R (recoveryBank 238) = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R (recoveryBank 239) = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (h217 : S.R (recoveryBank 217) = []) (h231 : S.R (recoveryBank 231) = [])
    (h232 : S.R (recoveryBank 232) = []) (h233 : S.R (recoveryBank 233) = [])
    (hclean : ∀ i ∈ ([234,235,184,223,237,208,211,236,201,215] : List (Fin 240)), S.R (recoveryBank i) = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let G := boundarySolutionField B solution
    let F := placedNativeCyclicBoundaryRecoveryState S
      (cstream A w (packedInterval a (min n (s-a)) G))
      (cstream A w (packedInterval 0 (n-min n (s-a)) G))
    ∃ vf m, vf.user = v.user ∧
      m ≤ residualBatchRecoveryInputCost B.card w+(n*(6*w+10)+12) ∧
      Exec body placedNativeCyclicBoundaryRecovery (mk v S) m (mk vf F) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let G := boundarySolutionField B solution
  obtain ⟨vi,m,hui,hm,hei⟩ := nativeCyclicBoundaryRecovery_exec
    (body := fun z : Empty => nomatch z) hst hA band a n ha hn solution w hlen
    (embDn recoveryBank v) (embStk recoveryBank S) tail hleft hmul hcount hrows hw hsource hmaskR hmaskL
    h217 h231 h232 h233 hclean
  obtain ⟨vf,_,hu,he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    CyclicRecoveryPlacement.bank_injective (fun z => nomatch z) hei v rfl S rfl
  have hfinal : embOvr recoveryBank (nativeCyclicBoundaryRecoveryState (embStk recoveryBank S)
      (cstream A w (packedInterval a (min n (s-a)) G))
      (cstream A w (packedInterval 0 (n-min n (s-a)) G))).get S =
      placedNativeCyclicBoundaryRecoveryState S
        (cstream A w (packedInterval a (min n (s-a)) G))
        (cstream A w (packedInterval 0 (n-min n (s-a)) G)) := by
    rw [nativeCyclicBoundaryRecoveryState,embOvr_updR CyclicRecoveryPlacement.bank_injective,embOvr_stk]
    rfl
  exact ⟨vf,m,hu.trans hui,hm,he.cast rfl (congrArg (mk vf) hfinal)⟩

theorem placedNativeCyclicBoundaryRecovery_exec_ready {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (q w W : ℕ) (solution : List GaussianInt)
    (hlen : solution.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 840 Q A U) (S : Stacks 840 A) (tail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk (Fin.castLE (by decide : 234 ≤ 240)) (embStk recoveryBank S)))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) (embStk recoveryBank S))) q w W
      (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i, S.L (recoveryBank i) = [])
    (hsource : S.R (recoveryBank 224) = cstream A w solution++tail)
    (hmaskR : S.R (recoveryBank 238) = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R (recoveryBank 239) = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (hfresh : ∀ i ∈ ([(231 : Fin 240),232,233,234,235,236,237]), S.R (recoveryBank i) = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let G := boundarySolutionField B solution
    let F := placedNativeCyclicBoundaryRecoveryState S
      (cstream A w (packedInterval a (min n (s-a)) G))
      (cstream A w (packedInterval 0 (n-min n (s-a)) G))
    ∃ vf m, vf.user = v.user ∧
      m ≤ residualBatchRecoveryInputCost B.card w+(n*(6*w+10)+12) ∧
      Exec body placedNativeCyclicBoundaryRecovery (mk v S) m (mk vf F) := by
  obtain ⟨hcount,hrows,hw,h217,hclean,hmul⟩ := nativeBoundaryUnfold_controls (embStk recoveryBank S) hwork hready
  apply placedNativeCyclicBoundaryRecovery_exec (body := body) hst hA band a n ha hn solution w hlen
    v S tail hleft hmul hcount hrows hw hsource hmaskR hmaskL h217
    (hfresh 231 (by simp)) (hfresh 232 (by simp)) (hfresh 233 (by simp))
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfresh 234 (by simp)
  · exact hfresh 235 (by simp)
  · exact hclean 184 (by simp)
  · exact hclean 223 (by simp)
  · exact hfresh 237 (by simp)
  · exact hclean 208 (by simp)
  · exact hclean 211 (by simp)
  · exact hfresh 236 (by simp)
  · exact hclean 201 (by simp)
  · exact hclean 215 (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
