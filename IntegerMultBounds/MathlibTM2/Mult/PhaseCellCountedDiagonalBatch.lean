module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalBatchCounts
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Generate private loop rulers and execute the shared-page diagonal batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s t Q A : ℕ} [NeZero s] [NeZero t] {P U : Type} {body : P → Pr P tapes Q A U}
noncomputable section

def localDiagonalBatch (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  countedLoop diagonalClock (diagonalPacketWorker (rg := diagonalRole) diagonalBytes diagonalQueue
    diagonalSaved diagonalTmp .src .df .dst diagonalMul_injective diagonal_tapes hQ)

def countedDiagonalBatch (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq diagonalBatchCounts (localDiagonalBatch hQ)

def localDiagonalBatchCost (N n w : ℕ) : ℕ :=
  N*((6*(n*w)+6)+(n*(rmulCost w+6*w+2)+8)+(2*(n*w)+2)+3)+2

def diagonalBatchCounterState (S : Stacks tapes A) (N n w : ℕ) : Stacks tapes A :=
  {S with R := (Function.update (Function.update S.R diagonalClock (List.replicate N tick))
    diagonalBytes (List.replicate (n*w) tick))}

def diagonalBatchOutputState (S : Stacks tapes A) (tail output : List (Fin (A+4))) : Stacks tapes A :=
  {S with R := (Function.update (Function.update (Function.update S.R diagonalClock []) diagonalQueue tail)
    (diagonalRole .dst) (output++S.R (diagonalRole .dst)))}

theorem countedDiagonalBatch_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (alpha p w c n : ℕ) (hw : p+2 ≤ w) (hp : 13 ≤ p) (halpha : 1 ≤ alpha) (hbudget : alpha^2 ≤ p)
    (Ds : List (ZMod s → GaussianInt)) (hfit : c+n ≤ s)
    (hD : ∀ D ∈ Ds, ∀ z ∈ packedInterval c n D, Fits w z)
    (rho : RsbR → List (Fin (A+4))) (hready : RsbReady rho w p)
    (hpage : rho .df = cstream A w (packedInterval c n (diagonalField s t alpha p)))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      diagonalMul diagonalMul_injective diagonal_tapes hQ (rsbCr diagonalRole .src .df .dst)) ≤ C)
    (v : HS tapes Q A U) (S : Stacks tapes A) (tail : List (Fin (A+4)))
    (hN : (S.R (recovery (.control .replicas))).length = Ds.length)
    (hn : (S.R (recovery (.control .cropRows))).length = n)
    (hwide : (S.R (recovery (.control .packet))).length = w)
    (hblank : ∀ k ∈ [diagonalClock,diagonalBytes,diagonalSaved,diagonalTmp], S.R k = [])
    (hqueue : S.R diagonalQueue = Ds.flatMap (fun D => cstream A w (packedInterval c n D))++tail)
    (hinput : S.R (diagonalRole .src) = []) (hclean : RsbClean diagonalMul S)
    (hholds : RsbHolds diagonalRole S rho) :
    ∃ v' F steps, v'.user = v.user ∧
      steps ≤ bulkSelectionCountsCost Ds.length n w+localDiagonalBatchCost Ds.length n w ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        (2*bulkSelectionCountsCost Ds.length n w+(2*(6*(n*w)+6)+realWeightWorkspace C w n)))
        depth (countedDiagonalBatch hQ) (mk v S) steps (mk v' F)) ∧
      F.R diagonalClock = [] ∧ F.R diagonalQueue = tail ∧
      F.R (diagonalRole .dst) = Ds.reverse.flatMap (fun D =>
        cstream A w (packedInterval c n (diagonalProduct s t alpha p D)))++S.R (diagonalRole .dst) ∧
      F.R (diagonalRole .df) = S.R (diagonalRole .df) ∧ F.R (diagonalRole .src) = [] ∧
      F = diagonalBatchOutputState (diagonalBatchCounterState S Ds.length n w) tail
        (Ds.reverse.flatMap (fun D => cstream A w (packedInterval c n (diagonalProduct s t alpha p D)))) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁,ht₁⟩ := diagonalBatchCounts_exec (body := body) Ds.length n w v S hN hn hwide hblank
  let M : Stacks tapes A := {S with R := (Function.update (Function.update S.R diagonalClock
    (List.replicate Ds.length tick)) diagonalBytes (List.replicate (n*w) tick))}
  have hclockBytes : diagonalClock ≠ diagonalBytes := by
    simp [diagonalClock,diagonalBytes,recovery_injective.eq_iff]
  have hframe (k : Fin tapes) (hc : k ≠ diagonalClock) (hb : k ≠ diagonalBytes) : M.R k = S.R k := by
    exact (Function.update_of_ne hb _ _).trans (Function.update_of_ne hc _ _)
  have hroles (r : RsbR) : M.R (diagonalRole r) = S.R (diagonalRole r) :=
    hframe _ (diagonalRole_ne_work r 300 (by decide)) (diagonalRole_ne_work r 301 (by decide))
  have hcleanM : RsbClean diagonalMul M := ⟨hclean.1,fun j =>
    (hframe _ (diagonalMul_ne_work j 300 (by decide)) (diagonalMul_ne_work j 301 (by decide))).trans (hclean.2 j)⟩
  have hqueueM : M.R diagonalQueue = S.R diagonalQueue :=
    hframe _ (diagonalWork_ne_queue 300).symm (diagonalWork_ne_queue 301).symm
  have hsavedM : M.R diagonalSaved = [] := by
    have hc : diagonalSaved ≠ diagonalClock := by simp [diagonalSaved,diagonalClock,recovery_injective.eq_iff]
    have hb : diagonalSaved ≠ diagonalBytes := by simp [diagonalSaved,diagonalBytes,recovery_injective.eq_iff]
    exact (hframe _ hc hb).trans (hblank _ (by simp))
  have htmpM : M.R diagonalTmp = [] := by
    have hc : diagonalTmp ≠ diagonalClock := by simp [diagonalTmp,diagonalClock,recovery_injective.eq_iff]
    have hb : diagonalTmp ≠ diagonalBytes := by simp [diagonalTmp,diagonalBytes,recovery_injective.eq_iff]
    exact (hframe _ hc hb).trans (hblank _ (by simp))
  obtain ⟨v₂,F,m₂,hv₂,hm₂,ht₂,hclock,hq,hout,hpageF,hsrc,hfinal⟩ := diagonalBatch_exec
    (body := body) diagonalRole_injective diagonalRole_ne_mul diagonalMul_injective diagonal_tapes hQ hA
    diagonalClock diagonalBytes diagonalQueue diagonalSaved diagonalTmp .src .df .dst diagonal_free diagonal_batch_regs
    diagonalRole_ne_queue (fun r => diagonalRole_ne_work r 300 (by decide))
    (fun j => (diagonalMul_ne_queue j).symm) (fun j => (diagonalMul_ne_work j 300 (by decide)).symm)
    rho hready hw hp halpha hbudget Ds hfit hD hpage C hpush v₁ M tail (hqueueM.trans hqueue)
    (by simp [M,Function.update_of_ne hclockBytes]) (by simp [M])
    ((hroles .src).trans hinput) hsavedM htmpM hcleanM (fun r => (hroles r).trans (hholds r))
  refine ⟨v₂,F,m₁+m₂,hv₂.trans hv₁,?_,fun depth => ?_,hclock,hq,?_,?_,hsrc,hfinal⟩
  · change m₂ ≤ localDiagonalBatchCost Ds.length n w at hm₂
    omega
  · exact mn_seq_within_add (ht₁ depth) (ht₂ depth)
  · exact hout.trans (congrArg (fun xs => Ds.reverse.flatMap (fun D =>
      cstream A w (packedInterval c n (diagonalProduct s t alpha p D)))++xs) (hroles .dst))
  · exact hpageF.trans (hroles .df)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
