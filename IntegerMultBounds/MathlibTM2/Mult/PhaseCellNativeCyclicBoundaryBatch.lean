module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeCyclicBoundaryLoop

/-! Copy the retained replica master once and traverse the complete solved-row
archive. All private controls restore; factors and masks are shared by the batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def nativeCyclicBoundaryBatch : Pr P 240 Q A U :=
  .seq (ucopy 229 228 227) (countedLoop 228 nativeCyclicBoundaryRow)

def nativeCyclicBoundaryBatchCost (replicas N n w : ℕ) : ℕ :=
  (4*replicas+4)+(replicas*(nativeCyclicBoundaryRowCost N n w+3)+2)

def nativeCyclicBoundaryBatchWorkspace (replicas N n w : ℕ) : ℕ :=
  2*(4*replicas+4)+(replicas*(n*w)+4*nativeCyclicBoundaryRowCost N n w)

/-- Packed archive volume depends only on the window and replica count. -/
theorem nativeCyclicBoundaryBatch_fields_length {s : ℕ} [NeZero s]
    (A w t band a n : ℕ) (ha : a < s) (hn : n ≤ s) (rows : List (List GaussianInt)) :
    let B := cyclicPrincipalBoundary s t band a n
    let fields := fun solution =>
      cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
        cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    (rows.reverse.flatMap fields).length = rows.length*(n*w) := by
  dsimp only
  let fields := fun solution =>
    cstream A w (packedInterval a (min n (s-a))
      (boundarySolutionField (cyclicPrincipalBoundary s t band a n) solution))++
    cstream A w (packedInterval 0 (n-min n (s-a))
      (boundarySolutionField (cyclicPrincipalBoundary s t band a n) solution))
  have hfitL : a+min n (s-a) ≤ s := by omega
  have hfitR : 0+(n-min n (s-a)) ≤ s := by omega
  have hfield (solution : List GaussianInt) : (fields solution).length = n*w := by
    simp only [fields,List.length_append,length_cstream,packedInterval_length _ hfitL,
      packedInterval_length _ hfitR]
    have hs := Nat.sub_add_cancel (Nat.min_le_left n (s-a))
    nlinarith only [congrArg (fun k => k*w) hs]
  change (rows.reverse.flatMap fields).length = _
  rw [List.length_flatMap]
  simp only [hfield,List.map_const',List.sum_replicate,smul_eq_mul,List.length_reverse]

theorem nativeCyclicBoundaryBatch_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (q w W : ℕ) (rows : List (List GaussianInt))
    (hlens : ∀ row ∈ rows, row.length = (cyclicPrincipalBoundary s t band a n).card)
    (v : HS 240 Q A U) (S : Stacks 240 A) (tail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk (Fin.castLE (by decide : 234 ≤ 240)) S))
    (hready : BoundarySolveReady (boundaryFactorState
      (embStk (Fin.castLE (by decide : 224 ≤ 240)) S)) q w W
      (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i : Fin 224, S.L (sharedPageBoundaryUnfoldReg i) = [])
    (hsource : S.R 224 = rows.flatMap (cstream A w)++tail)
    (hmaskR : S.R 238 = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hmaskL : S.R 239 = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)))
    (hfresh : ∀ i ∈ ([(231 : Fin 240),232,233,234,235,236,237]), S.R i = [])
    (hcount : (S.R 229).length = rows.length) (h227 : S.R 227 = []) (h228 : S.R 228 = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let fields := fun solution =>
      cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
        cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    let F := nativeCyclicBoundaryRowState S tail (rows.reverse.flatMap fields) []
    ∃ vf m, vf.user = v.user ∧ m ≤ nativeCyclicBoundaryBatchCost rows.length B.card n w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        nativeCyclicBoundaryBatchWorkspace rows.length B.card n w) 0
        nativeCyclicBoundaryBatch (mk v S) m (mk vf F) ∧
      NativeBoundaryUnfoldWorkspace B.card (embStk (Fin.castLE (by decide : 234 ≤ 240)) F) ∧
      BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) F)) q w W B.card := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let fields := fun solution =>
    cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 229) (b := 228) (t := 227)
    (by decide) (by decide) (by decide) v S h227
  let J : Stacks 240 A := {S with R := Function.update S.R 228 (List.replicate rows.length tick)}
  have he₁' : Exec body (ucopy 229 228 227) (mk v S) (4*rows.length+4) (mk v₁ J) := by
    simpa only [J,hcount,h228,List.append_nil] using he₁
  have hwJ : NativeBoundaryUnfoldWorkspace B.card (embStk (Fin.castLE (by decide : 234 ≤ 240)) J) := by
    have hcast : (228 : Fin 240) = Fin.castLE (by decide : 234 ≤ 240) (228 : Fin 234) := rfl
    change NativeBoundaryUnfoldWorkspace B.card (embStk (Fin.castLE (by decide : 234 ≤ 240))
      {S with R := Function.update S.R 228 (List.replicate rows.length tick)})
    rw [hcast,embStk_updateR (Fin.castLE_injective _)]
    exact hwork.updateR 228 _ (by decide) (by decide) (by decide) (by decide)
  have hrJ : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 240)) J))
      q w W B.card := by
    have hcore : embStk (Fin.castLE (by decide : 224 ≤ 240)) J =
        embStk (Fin.castLE (by decide : 224 ≤ 240)) S := by
      apply embStk_updateR_off
      intro i he
      have hv := congrArg (fun k : Fin 240 => k.val) he
      change i.val = 228 at hv
      have := i.isLt; omega
    rw [hcore]; exact hready
  obtain ⟨vf,m₂,hu₂,hm₂,he₂⟩ := nativeCyclicBoundaryLoop_exec (body := body)
    hst hA band a n ha hn q w W rows hlens v₁ J tail hwJ hrJ hleft
    (by simpa [J] using hsource) (by simpa [J] using hmaskR) (by simpa [J] using hmaskL)
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simpa [J] using hfresh _ (by simp)) (by simp [J])
  have hfinal : nativeCyclicBoundaryLoopState J tail (rows.reverse.flatMap fields++J.R 132) [] =
      nativeCyclicBoundaryRowState S tail (rows.reverse.flatMap fields) [] := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk132 : k = 132 <;> by_cases hk224 : k = 224 <;> by_cases hk228 : k = 228 <;>
      simp [J,nativeCyclicBoundaryLoopState,nativeCyclicBoundaryRowState,
        nativeCyclicBoundaryRecoveryState,hk132,hk224,hk228,h228]
  have hp : mnNativePushBound 2 (ucopy (P := P) (Q := Q) (A := A) (U := U) (229 : Fin 240) 228 227) := by
    simp [ucopy,umulSym,scanP,pushN,scanR,drainR,popDo,keepIn,popPush,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]
  have heCopy := mn_native_exec_within he₁' 2 hp 0 _ (le_refl _)
  have hsize := heCopy.final
  have hwithin : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      nativeCyclicBoundaryBatchWorkspace rows.length B.card n w) 0
      nativeCyclicBoundaryBatch (mk v S) ((4*rows.length+4)+m₂)
      (mk vf (nativeCyclicBoundaryRowState S tail (rows.reverse.flatMap fields) [])) := by
    refine .seq (heCopy.mono ?_) ((he₂.cast rfl (congrArg (mk vf) hfinal)).mono ?_)
    all_goals
      intro d z hz
      dsimp only [nativeCyclicBoundaryBatchWorkspace,B] at *
      omega
  refine ⟨vf,_,hu₂.trans hu₁,Nat.add_le_add_left hm₂ (4*rows.length+4),
    hwithin,
    nativeCyclicBoundaryRowState_workspace S tail (rows.reverse.flatMap fields) [] hwork,?_⟩
  rw [nativeCyclicBoundaryRowState_factor]
  exact hready

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
