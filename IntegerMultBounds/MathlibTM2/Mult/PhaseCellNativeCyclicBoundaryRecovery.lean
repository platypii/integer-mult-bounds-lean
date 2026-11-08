module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryPieces
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBatchRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeBoundaryUnfoldControls

/-! Borrow one native solved-row prefix, inverse fold it once and publish both
packed recovery windows. The original batch stream and factor bank restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def nativeCyclicBoundaryRecovery : Pr P 240 Q A U :=
  .seq residualBatchRecoveryInput nativeCyclicBoundaryPieces

def nativeCyclicBoundaryRecoveryState (S : Stacks 240 A)
    (left right : List (Fin (A+4))) : Stacks 240 A :=
  {S with R := Function.update S.R 132 (left++(right++S.R 132))}

theorem nativeCyclicBoundaryRecoveryState_factor (S : Stacks 240 A)
    (left right : List (Fin (A+4))) :
    boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240))
      (nativeCyclicBoundaryRecoveryState S left right)) =
    boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) S) := by
  funext r
  have h132 : (Fin.castLE (by decide : 224 ≤ 240) (boundaryFactorReg r)) ≠ 132 := by
    intro he
    have hv := congrArg (fun k : Fin 240 => k.val) he
    apply boundaryFactorReg_off r 132 (by decide)
    apply Fin.ext
    simpa [boundaryFactorLegacyReg] using hv
  exact Function.update_of_ne h132 _ _

theorem nativeCyclicBoundaryRecovery_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (solution : List GaussianInt) (w : ℕ)
    (hlen : solution.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (hleft : ∀ i : Fin 224, S.L (sharedPageBoundaryUnfoldReg i) = [])
    (hmul : ∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = (cyclicPrincipalBoundary s t band a n).card)
    (hrows : (S.R 192).length = (cyclicPrincipalBoundary s t band a n).card)
    (hw : (S.R 160).length = w)
    (hsource : S.R 224 = cstream A w solution++tail)
    (hmaskR : S.R 238 = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R 239 = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (h217 : S.R 217 = []) (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = [])
    (hclean : ∀ i ∈ ([234,235,184,223,237,208,211,236,201,215] : List (Fin 240)), S.R i = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let G := boundarySolutionField B solution
    let F := nativeCyclicBoundaryRecoveryState S
      (cstream A w (packedInterval a (min n (s-a)) G))
      (cstream A w (packedInterval 0 (n-min n (s-a)) G))
    ∃ vf m, vf.user = v.user ∧
      m ≤ residualBatchRecoveryInputCost B.card w+(n*(6*w+10)+12) ∧
      Exec body nativeCyclicBoundaryRecovery (mk v S) m (mk vf F) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let G := boundarySolutionField B solution
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := residualBatchRecoveryInput_exec (body := body) hA w B solution hlen
    v S tail hleft hmul hcount hrows hw hsource h217 h231 h232 h233 hclean
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 237 (cstream A w ((bOrder s B).map G))}
  obtain ⟨vf,m₂,hu₂,hm₂,he₂⟩ := nativeCyclicBoundaryPieces_exec (body := body)
    hst hA band a n ha hn solution w [] v₁ S₁
    (by simp [S₁,B,G]) (by simpa [S₁] using hmaskR)
    (by simpa [S₁] using hmaskL) (by simpa [S₁] using hw)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simpa [S₁] using hclean _ (by simp))
  have h237 : S.R 237 = [] := hclean 237 (by simp)
  have hfinal : {S₁ with R := (Function.update (Function.update S₁.R 237 []) 132
        (cstream A w (packedInterval a (min n (s-a)) G)++
          (cstream A w (packedInterval 0 (n-min n (s-a)) G)++S₁.R 132)))} =
      nativeCyclicBoundaryRecoveryState S
        (cstream A w (packedInterval a (min n (s-a)) G))
        (cstream A w (packedInterval 0 (n-min n (s-a)) G)) := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk237 : k = 237 <;> by_cases hk132 : k = 132 <;>
      simp [S₁,nativeCyclicBoundaryRecoveryState,hk237,hk132,h237]
  exact ⟨vf,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ (he₂.cast rfl (congrArg (mk vf) hfinal))⟩

/-- The solver endpoint supplies all numerical inverse-fold controls. Only
ordinary private/new scratch and the source prefix remain caller obligations. -/
theorem nativeCyclicBoundaryRecovery_exec_ready {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (q w W : ℕ) (solution : List GaussianInt)
    (hlen : solution.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk (Fin.castLE (by decide : 234 ≤ 240)) S))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) S)) q w W
      (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i : Fin 224, S.L (sharedPageBoundaryUnfoldReg i) = [])
    (hsource : S.R 224 = cstream A w solution++tail)
    (hmaskR : S.R 238 = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R 239 = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (hfresh : ∀ i ∈ ([(231 : Fin 240),232,233,234,235,236,237]), S.R i = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let G := boundarySolutionField B solution
    let F := nativeCyclicBoundaryRecoveryState S
      (cstream A w (packedInterval a (min n (s-a)) G))
      (cstream A w (packedInterval 0 (n-min n (s-a)) G))
    ∃ vf m, vf.user = v.user ∧
      m ≤ residualBatchRecoveryInputCost B.card w+(n*(6*w+10)+12) ∧
      Exec body nativeCyclicBoundaryRecovery (mk v S) m (mk vf F) := by
  obtain ⟨hcount,hrows,hw,h217,hclean,hmul⟩ := nativeBoundaryUnfold_controls S hwork hready
  apply nativeCyclicBoundaryRecovery_exec (body := body) hst hA band a n ha hn solution w hlen
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

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
