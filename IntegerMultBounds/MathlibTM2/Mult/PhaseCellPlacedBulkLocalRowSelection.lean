module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRecoveryLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringCyclicSelection

/-! Concrete batch wiring for the controller-reusing selector. Its output is
the generated recovery handoff source, and recovery readiness is preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
noncomputable section
variable {Q A s t : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

/-- Batch ports are clock, volume, retained queue, input archive, output
accumulator and the ordinary target-window span ruler. -/
theorem bulk_regs :
    [batch 0,batch 1,batch 2,batch 3,batch 4,geometry 108,geometry 91,geometry 92,geometry 93,
      geometry 95,geometry 110,geometry 96,geometry 97,geometry 98,geometry 99,geometry 100,
      geometry 101,geometry 102,geometry 103,geometry 94].Nodup := by
  simp [batch,geometry,port_injective.eq_iff]

def bulkSelection : Pr P tapes Q A U :=
  restoringCyclicSelection (batch 0) (batch 1) (batch 2) (batch 3) (batch 4)
    (geometry 108) (geometry 91) (geometry 92) (geometry 93) (geometry 95) (geometry 110)
    (geometry 96) (geometry 97) (geometry 98) (geometry 99) (geometry 100)
    (geometry 101) (geometry 102) (geometry 103) (geometry 94)

theorem bulkSelection_exec_base (w a n origin span : ℕ) (Fs : List (ZMod t → GaussianInt)) (hn : 0 < n)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (tail : List (Fin (A+4))) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hclock : (S.R (batch 0)).length = Fs.length) (hvolume : (S.R (batch 1)).length = span*w)
    (hc : S.R (geometry 91) = localRowControls A s t a n origin w)
    (hqueue : S.R (batch 2) = (Fs.flatMap fun F => cstream A w (cyclicInterval origin span F))++tail)
    (hrow : (S.R (geometry 103)).length = 1) (hw : (S.R (geometry 94)).length = w)
    (harchive : S.R (batch 3) = []) (hacc : S.R (batch 4) = [])
    (hclean : ∀ k ∈ [(108 : Fin 117),110,92,93,95,96,97,98,99,100,101,102], S.R (geometry k) = []) :
    let output := selectedWindowPayload (s := s) A w a n origin span Fs
    let B := {S with R := Function.update (Function.update S.R (batch 0) []) source output}
    ∃ v' m, v'.user = v.user ∧ m ≤ restoringCyclicSelectionCost Fs.length n span w ∧
      Exec body bulkSelection (Host.mk v S) m (Host.mk v' B) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*restoringCyclicSelectionCost Fs.length n span w) depth bulkSelection (Host.mk v S) m (Host.mk v' B) := by
  dsimp only
  obtain ⟨v',m,hu,hm,he,ht⟩ := restoringCyclicSelection_exec (body := body)
    (batch 0) (batch 1) (batch 2) (batch 3) (batch 4) (geometry 108) (geometry 91) (geometry 92)
    (geometry 93) (geometry 95) (geometry 110) (geometry 96) (geometry 97) (geometry 98)
    (geometry 99) (geometry 100) (geometry 101) (geometry 102) (geometry 103) (geometry 94)
    bulk_regs w a n origin span Fs hn hwindow tail v S hclock hvolume hc hqueue hrow hw
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact harchive
      · exact hacc
      all_goals exact hclean _ (by simp))
  exact ⟨v',m,hu,hm,he,ht⟩

theorem bulkSelection_exec (w a n origin span : ℕ) (Fs : List (ZMod t → GaussianInt)) (hn : 0 < n)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (tail : List (Fin (A+4))) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hclock : (S.R (batch 0)).length = Fs.length) (hvolume : (S.R (batch 1)).length = span*w)
    (hc : S.R (geometry 91) = localRowControls A s t a n origin w)
    (hqueue : S.R (batch 2) = (Fs.flatMap fun F => cstream A w (cyclicInterval origin span F))++tail)
    (hrow : (S.R (geometry 103)).length = 1) (hw : (S.R (geometry 94)).length = w)
    (harchive : S.R (batch 3) = []) (hacc : S.R (batch 4) = [])
    (hclean : ∀ k ∈ [(108 : Fin 117),110,92,93,95,96,97,98,99,100,101,102], S.R (geometry k) = [])
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {N offset rows : ℕ}
    {wl : List (Fin (A+4))} (hready : plan.CroppedReady crop d r N offset rows wl S) :
    let output := selectedWindowPayload (s := s) A w a n origin span Fs
    let B := {S with R := Function.update (Function.update S.R (batch 0) []) source output}
    ∃ v' m, v'.user = v.user ∧ m ≤ restoringCyclicSelectionCost Fs.length n span w ∧
      Exec body bulkSelection (Host.mk v S) m (Host.mk v' B) ∧
      plan.CroppedReady crop d r N offset rows wl B ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*restoringCyclicSelectionCost Fs.length n span w) depth bulkSelection (Host.mk v S) m (Host.mk v' B) := by
  dsimp only
  obtain ⟨v',m,hu,hm,he,ht⟩ := bulkSelection_exec_base (body := body)
    w a n origin span Fs hn hwindow tail v S hclock hvolume hc hqueue hrow hw harchive hacc hclean
  refine ⟨v',m,hu,hm,he,?_,ht⟩
  apply hready.of_frame
  · intro k hk
    have hsource : k ≠ source := (geometry_off_support 108 k hk).symm
    have hclock : k ≠ batch 0 := by
      obtain ⟨i,rfl⟩ := cropSupport_range k hk
      exact (batch_ne_recovery 0 i).symm
    simp only [Function.update_of_ne hsource,Function.update_of_ne hclock]
  · intro i; rfl

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
