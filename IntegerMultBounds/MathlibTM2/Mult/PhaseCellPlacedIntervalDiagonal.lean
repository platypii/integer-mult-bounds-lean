module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedIntervalDiagonalExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalContext
public import IntegerMultBounds.MathlibTM2.Host.OrderedMoveStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Transfer the produced interval packet in order to the already allocated
recovery bank and execute the existing complete diagonal stage there. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
noncomputable section
variable {s t Q A : ℕ} [NeZero s] [NeZero t] {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalTransferState (S : Stacks tapes A) : Stacks tapes A :=
  {S with R := (Function.update (Function.update S.R (aux 5) [])
    (selector LocalRecoveryLayout.diagonalQueue) (S.R (aux 5)++S.R (selector LocalRecoveryLayout.diagonalQueue)))}

def placedDiagonal (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq (moveRightOrdered (aux 5) caller.tmp (selector LocalRecoveryLayout.diagonalQueue))
    (embProg selector Empty.elim (LocalRecoveryLayout.completeDiagonalBatch (P := Empty) hQ))

theorem diagonalContext_of_recovery_frame {s t u p w B a radius rows N : ℕ}
    {S F : Stacks tapes A}
    (h : LocalRecoveryLayout.DiagonalContext s t u p w B a radius rows N (embStk selector S))
    (hleft : F.L = S.L)
    (hframe : ∀ i, F.R (selector (LocalRecoveryLayout.recovery i)) =
      S.R (selector (LocalRecoveryLayout.recovery i))) :
    LocalRecoveryLayout.DiagonalContext s t u p w B a radius rows N (embStk selector F) :=
  h.frame (funext (fun j => congrFun hleft (selector j))) hframe

private theorem embedTwoUpdates {M N A : ℕ} (e : Fin M → Fin N) (he : Function.Injective e)
    (S : Stacks N A) (i j : Fin M) (xs ys : List (Fin (A+4))) :
    embOvr e ({embStk e S with R := Function.update (Function.update (embStk e S).R i xs) j ys} :
      Stacks M A).get S =
      {S with R := Function.update (Function.update S.R (e i) xs) (e j) ys} := by
  have h1 := embOvr_updR he (embStk e S) S i xs
  rw [embOvr_stk] at h1
  have h2 := embOvr_updR he
    ({embStk e S with R := Function.update (embStk e S).R i xs} : Stacks M A) S j ys
  rw [h1] at h2
  exact h2

private theorem readEmbeddedR {M N A : ℕ} (e : Fin M → Fin N) (he : Function.Injective e)
    (D : Stacks M A) (S : Stacks N A) (r : Fin M) :
    (embOvr e D.get S).R (e r) = D.R r := embExt_apply he D.R S.R r

private theorem transfer_read (S : Stacks tapes A) (r : Fin LocalRecoveryLayout.tapes)
    (hr : r ≠ LocalRecoveryLayout.diagonalQueue) :
    (embStk selector (diagonalTransferState S)).R r = (embStk selector S).R r := by
  simp only [embStk_R,diagonalTransferState,
    Function.update_of_ne (selector_injective.ne hr),Function.update_of_ne (selector_ne_aux r 5)]

theorem placedDiagonal_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (u alpha B p w a radius n : ℕ) (hs : 0 < s) (hst : s ≤ t) (hfit : a+radius+n ≤ s)
    (hp : 13 ≤ p) (halpha : 2 ≤ alpha) (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p)
    (hw : p+2 ≤ w) (hroom : 4*w+2 < 2^B)
    (targets : List (ZMod s → ℂ)) (error : ℝ) (word : List (Fin (A+4)))
    (hpacketOut : PackedIntervalOutput p w (a+radius) n targets error word)
    (hwordWidth : p+3 ≤ w) (herror : error ≤ 1/2)
    (hmag : ∀ z ∈ targets, ∀ i ∈ haloVertices s (a+radius) (a+radius+n), ‖z i‖ ≤ (3/2 : ℝ))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      LocalRecoveryLayout.diagonalMul LocalRecoveryLayout.diagonalMul_injective LocalRecoveryLayout.diagonal_tapes hQ
      (rsbCr LocalRecoveryLayout.diagonalRole .src .df .dst)) ≤ C)
    (v : HS tapes Q A U) (S : Stacks tapes A) (tail : List (Fin (A+4)))
    (context : LocalRecoveryLayout.DiagonalContext s t u p w B a radius n targets.length (embStk selector S))
    (hqueue : S.R (selector LocalRecoveryLayout.diagonalQueue) = tail)
    (hsource : S.R (aux 5) = word) (htmp : S.R caller.tmp = []) :
    let M := diagonalTransferState S
    ∃ (vf : HS tapes Q A U) (Ds : List (ZMod s → GaussianInt)) (F : Stacks tapes A) (steps : ℕ),
      Ds.length = targets.length ∧ vf.user = v.user ∧
      steps ≤ 4*word.length+4+
        LocalRecoveryLayout.completeDiagonalBatchCost (embStk selector M) B p w u t a radius n targets.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        (16*LocalRecoveryLayout.diagonalPreparationCost (embStk selector M) B p w u t a radius n+
          (2*bulkSelectionCountsCost targets.length n w+(2*(6*(n*w)+6)+realWeightWorkspace C w n))))
        0 (placedDiagonal hQ) (mk v S) steps (mk vf F) ∧
      F.R (aux 5) = [] ∧ F.R (selector LocalRecoveryLayout.diagonalQueue) = tail ∧
      F.R (selector (LocalRecoveryLayout.diagonalRole .dst)) =
        Ds.reverse.flatMap (fun D => cstream A w (packedInterval (a+radius) n (diagonalProduct s t alpha p D))) ∧
      F = {M with R := (Function.update (Function.update M.R (selector LocalRecoveryLayout.diagonalQueue) tail)
        (selector (LocalRecoveryLayout.diagonalRole .dst))
          (Ds.reverse.flatMap (fun D => cstream A w (packedInterval (a+radius) n (diagonalProduct s t alpha p D)))))} ∧
      PackedIntervalOutput p w (a+radius) n
        (targets.reverse.map (fun z i => (dPrime s t (alpha : ℝ) i : ℂ)*z i))
        (6/(2 : ℝ)^p+error)
        (Ds.reverse.flatMap (fun D => cstream A w (packedInterval (a+radius) n (diagonalProduct s t alpha p D)))) := by
  dsimp only
  obtain ⟨hS,hT,hu,hprec,hprecision,hpacket,hB,ha,hradius,hn,hN,hfresh⟩ := context
  obtain ⟨vi,hui,hmove⟩ := moveRightOrdered_exec (body := body) (aux 5) caller.tmp
    (selector LocalRecoveryLayout.diagonalQueue)
    (by simp [caller,aux,port_injective.eq_iff]) (selector_ne_aux _ _).symm
    (selector_ne_aux _ _).symm v S htmp
  let M := diagonalTransferState S
  have hm : Exec body (moveRightOrdered (aux 5) caller.tmp (selector LocalRecoveryLayout.diagonalQueue))
      (mk v S) (4*word.length+4) (mk vi M) := by simpa only [M,diagonalTransferState,hsource] using hmove
  have hread := transfer_read S
  have hfreshM : LocalRecoveryLayout.DiagonalFresh (embStk selector M) := by
    refine ⟨hfresh.left,?_⟩
    intro j
    rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]
    exact hfresh.work j
  obtain ⟨Ds,vf,m,hlen,hu',htime,hwithin,haccuracy⟩ :=
    LocalRecoveryLayout.completeDiagonalBatch_packet_exec (P := Empty) (body := fun z => nomatch z)
      hQ hA u alpha B p w a radius n hs hst hfit hp halpha hsquare hbudget hw hroom
      targets error word hpacketOut hwordWidth herror hmag C hpush (embDn selector vi) (embStk selector M) tail
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hS)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hT)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hu)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hprec)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hprecision)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hpacket)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.diagonalWidthSource,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hB)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.diagonalHaloStart,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact ha)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.diagonalCropOffset,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hradius)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.diagonalCropRows,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hn)
      (by rw [hread _ (by simp [LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff])]; exact hN)
      (by simp only [embStk_R,M,diagonalTransferState,Function.update_self,hsource,hqueue]) hfreshM
  let packet := Ds.reverse.flatMap (fun D => cstream A w
    (packedInterval (a+radius) n (diagonalProduct s t alpha p D)))
  let D := ({embStk selector M with R := (Function.update
    (Function.update (embStk selector M).R LocalRecoveryLayout.diagonalQueue tail)
    (LocalRecoveryLayout.diagonalRole .dst) (packet++(embStk selector M).R (LocalRecoveryLayout.diagonalRole .dst)))} :
    Stacks LocalRecoveryLayout.tapes A)
  have hdst : (embStk selector M).R (LocalRecoveryLayout.diagonalRole .dst) = [] :=
    (transfer_read S _ (LocalRecoveryLayout.diagonalRole_ne_queue .dst)).trans (hfresh.role .dst)
  have he := (hwithin 0).toExec
  obtain ⟨vg,hvg,hug,hex⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) selector_injective
    (fun z => nomatch z) he vi rfl M rfl
  let F := embOvr selector D.get M
  have hreadF (r : Fin LocalRecoveryLayout.tapes) : F.R (selector r) = D.R r :=
    readEmbeddedR selector selector_injective D M r
  have hLift := exec_emb_within_stock_of_exec selector_injective (ι := Empty.elim) (body' := body)
    (fun z => nomatch z) (hwithin 0) vi rfl M rfl hex
  have hmoveWithin := moveRightOrdered_within _ _ _ hm 0 (mnSize (mk v S)+0+0) (by omega)
  have hwhole := mn_seq_within_add hmoveWithin hLift
  simp only [embDn_user] at hu'
  refine ⟨vg,Ds,F,4*word.length+4+m,hlen,hug.trans (hu'.trans hui),
    Nat.add_le_add_left htime _,?_,?_,?_,?_,?_,haccuracy⟩
  · simpa only [placedDiagonal,Nat.zero_add] using hwhole
  · have hoff := (embOvr_off D.get M (fun r => selector_ne_aux r 5)).2
    change F.R (aux 5) = M.R (aux 5) at hoff
    rw [hoff]
    simp only [M,diagonalTransferState,Function.update_of_ne (selector_ne_aux _ _).symm,
      Function.update_self]
  · rw [hreadF]
    simp only [D,Function.update_of_ne (LocalRecoveryLayout.diagonalRole_ne_queue .dst).symm,
      Function.update_self]
  · rw [hreadF]
    simp only [D,Function.update_self,hdst,List.append_nil,packet]
  · change embOvr selector D.get M = _
    dsimp only [D]
    rw [embedTwoUpdates selector selector_injective]
    simp only [hdst,List.append_nil,packet]
    rfl

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
