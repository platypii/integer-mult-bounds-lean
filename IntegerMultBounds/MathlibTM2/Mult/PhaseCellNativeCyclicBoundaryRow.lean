module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! One structural recovery-row transition: project one solved row, retire its
owned prefix and retain the shared factors/workspace for the next replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def nativeCyclicBoundaryRow : Pr P 240 Q A U :=
  .seq nativeCyclicBoundaryRecovery (retireCountedLine 192 160 224 231 232 233)

def nativeCyclicBoundaryRowCost (N n w : ℕ) : ℕ :=
  (residualBatchRecoveryInputCost N w+(n*(6*w+10)+12))+retireCountedLineCost N w

def nativeCyclicBoundaryRowState (S : Stacks 240 A) (tail left right : List (Fin (A+4))) : Stacks 240 A :=
  let F := nativeCyclicBoundaryRecoveryState S left right
  {F with R := Function.update F.R 224 tail}

theorem nativeCyclicBoundaryRowState_factor (S : Stacks 240 A)
    (tail left right : List (Fin (A+4))) :
    boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
      (nativeCyclicBoundaryRowState S tail left right)) =
    boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) S) := by
  refine Eq.trans ?_ (nativeCyclicBoundaryRecoveryState_factor S left right)
  funext r
  apply Function.update_of_ne
  intro he
  have hv := congrArg (fun k : Fin 240 => k.val) he
  have hr := (boundaryFactorReg r).isLt
  change (boundaryFactorReg r).val = 224 at hv
  omega

theorem nativeCyclicBoundaryRowState_workspace {N : ℕ} (S : Stacks 240 A)
    (tail left right : List (Fin (A+4)))
    (h : NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240)) S)) :
    NativeBoundaryUnfoldWorkspace N (embStk (Fin.castLE (by decide : 234 ≤ 240))
      (nativeCyclicBoundaryRowState S tail left right)) := by
  apply h.of_frame
  intro k hk
  have h132 : k.val ≠ 132 := by
    rcases hk with hk | rfl | rfl | rfl <;> omega
  have h224 : k.val ≠ 224 := by
    rcases hk with hk | rfl | rfl | rfl <;> omega
  simp [embStk,Fin.castLE,nativeCyclicBoundaryRowState,nativeCyclicBoundaryRecoveryState,
    Fin.ext_iff,h132,h224]

theorem nativeCyclicBoundaryRow_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (q w W : ℕ) (solution : List GaussianInt)
    (hlen : solution.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk (Fin.castLE (by decide : 234 ≤ 240)) S))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) S)) q w W
      (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i, S.L i = [])
    (hsource : S.R 224 = cstream A w solution++tail)
    (hmaskR : S.R 238 = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R 239 = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (hfresh : ∀ i ∈ ([(231 : Fin 240),232,233,234,235,236,237]), S.R i = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let G := boundarySolutionField B solution
    let F := nativeCyclicBoundaryRowState S tail
      (cstream A w (packedInterval a (min n (s-a)) G))
      (cstream A w (packedInterval 0 (n-min n (s-a)) G))
    ∃ vf m, vf.user = v.user ∧ m ≤ nativeCyclicBoundaryRowCost B.card n w ∧
      Exec body nativeCyclicBoundaryRow (mk v S) m (mk vf F) ∧
      NativeBoundaryUnfoldWorkspace B.card (embStk (Fin.castLE (by decide : 234 ≤ 240)) F) ∧
      BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) F)) q w W B.card := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let G := boundarySolutionField B solution
  let left := cstream A w (packedInterval a (min n (s-a)) G)
  let right := cstream A w (packedInterval 0 (n-min n (s-a)) G)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := nativeCyclicBoundaryRecovery_exec_ready (body := body)
    hst hA band a n ha hn q w W solution hlen v S tail hwork hready hleft hsource hmaskR hmaskL hfresh
  let J := nativeCyclicBoundaryRecoveryState S left right
  obtain ⟨_,hrows,hw,_,_,_⟩ := nativeBoundaryUnfold_controls S hwork hready
  obtain ⟨vf,m₂,hu₂,hm₂,he₂⟩ := retireCountedLine_exec (body := body)
    192 160 224 231 232 233 (by decide) B.card w (cstream A w solution) tail
    (by simp only [length_cstream,hlen,B]) v₁ J
    (by simpa [J,nativeCyclicBoundaryRecoveryState] using hrows)
    (by simpa [J,nativeCyclicBoundaryRecoveryState] using hw)
    (by simpa [J,nativeCyclicBoundaryRecoveryState] using hsource)
    (by simpa [J,nativeCyclicBoundaryRecoveryState] using hfresh 231 (by simp))
    (by simpa [J,nativeCyclicBoundaryRecoveryState] using hfresh 232 (by simp))
    (by simpa [J,nativeCyclicBoundaryRecoveryState] using hfresh 233 (by simp))
  refine ⟨vf,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,
    nativeCyclicBoundaryRowState_workspace S tail left right hwork,?_⟩
  rw [nativeCyclicBoundaryRowState_factor]
  exact hready

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
