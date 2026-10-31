module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedWindowPublication

/-! Static wiring and ordinary control readiness for prepared publication.
The source and destination are explicit shared ports; readiness is preserved
under arbitrary updates of those two ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

structure PreparedPublicationPlan (T : ℕ) (src dst : Fin T) where
  count : Fin T
  savedControl : Fin T
  advances : Fin T
  savedAdvances : Fin T
  counter : Fin T
  window : Fin T
  zero : Fin T
  acc : Fin T
  control : Fin T
  trash : Fin T
  tmp : Fin T
  padRows : Fin T
  wordWidth : Fin T
  retireCount : Fin T
  gap : Fin T
  hreg : [count,savedControl,advances,savedAdvances,counter,window,zero,acc,control,trash,tmp,
    padRows,wordWidth,retireCount,gap,src,dst].Nodup

namespace PreparedPublicationPlan
variable {T Q A s L : ℕ} {src dst : Fin T}

def support (plan : PreparedPublicationPlan T src dst) : List (Fin T) :=
  [plan.count,plan.savedControl,plan.advances,plan.savedAdvances,plan.counter,plan.window,plan.zero,plan.acc,
    plan.control,plan.trash,plan.tmp,plan.padRows,plan.wordWidth,plan.retireCount,plan.gap]

theorem support_off (plan : PreparedPublicationPlan T src dst) {i : Fin T} (hi : i ∈ plan.support) :
    i ≠ src ∧ i ≠ dst := by
  have hr := plan.hreg
  change (plan.support++[src,dst]).Nodup at hr
  have hd := (List.nodup_append.mp hr).2.2
  exact ⟨hd i hi src (by simp),hd i hi dst (by simp)⟩

theorem src_ne_dst (plan : PreparedPublicationPlan T src dst) : src ≠ dst := by
  have hr := plan.hreg
  change (plan.support++[src,dst]).Nodup at hr
  simpa using (List.nodup_append.mp hr).2.1

structure Ready (plan : PreparedPublicationPlan T src dst) (windows : PublicationWindows s L)
    (w missing : ℕ) (borrowed : List (Fin (A+4))) (S : Stacks T A) : Prop where
  count : S.R plan.count = List.replicate windows.origins.length tick
  advances : S.R plan.advances = gatherControls A (originAdvances w 0 windows.origins++[0])++borrowed
  window : (S.R plan.window).length = L*w
  padRows : (S.R plan.padRows).length = missing*L
  wordWidth : (S.R plan.wordWidth).length = w
  fresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
    plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []

theorem Ready.of_frame {plan : PreparedPublicationPlan T src dst} {windows : PublicationWindows s L}
    {w missing : ℕ} {borrowed : List (Fin (A+4))} {S F : Stacks T A}
    (h : plan.Ready windows w missing borrowed S)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i) : plan.Ready windows w missing borrowed F := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hR _ (by simp [support])]; exact h.count
  · rw [hR _ (by simp [support])]; exact h.advances
  · rw [hR _ (by simp [support])]; exact h.window
  · rw [hR _ (by simp [support])]; exact h.padRows
  · rw [hR _ (by simp [support])]; exact h.wordWidth
  · intro i hi
    have hm : i ∈ plan.support := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [support]
    rw [hR i hm]; exact h.fresh i hi

theorem Ready.after_io {plan : PreparedPublicationPlan T src dst} {windows : PublicationWindows s L}
    {w missing : ℕ} {borrowed : List (Fin (A+4))} {S : Stacks T A}
    (h : plan.Ready windows w missing borrowed S) (xs ys : List (Fin (A+4))) :
    plan.Ready windows w missing borrowed
      {S with R := Function.update (Function.update S.R src xs) dst ys} := by
  apply h.of_frame (F := {S with R := Function.update (Function.update S.R src xs) dst ys})
  intro i hi
  simp only [Function.update_of_ne (plan.support_off hi).1,Function.update_of_ne (plan.support_off hi).2]

def program {P U : Type} (plan : PreparedPublicationPlan T src dst) : Pr P T Q A U :=
  preparedWindowPublication plan.count plan.savedControl plan.advances plan.savedAdvances plan.counter plan.window plan.zero
    plan.acc plan.control plan.trash plan.tmp plan.padRows plan.wordWidth plan.retireCount plan.gap src dst

theorem exec {P U : Type} (plan : PreparedPublicationPlan T src dst) (body : P → Pr P T Q A U)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (paddedRows rows : List (List GaussianInt))
    (hlen : rows.length = windows.origins.length) (hrows : ∀ row ∈ rows, row.length = L)
    (hpadded : ∀ row ∈ paddedRows, row.length = L) (hmissing : missing+rows.length = paddedRows.length)
    (hreal : paddedRows.flatten.drop (missing*L) = rows.flatten)
    (E sourceTail outputTail borrowed : List (Fin (A+4))) (hE : E.length = s*w)
    (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready windows w missing borrowed S)
    (hsrc : S.R src = cstream A w paddedRows.flatten++sourceTail) (hdst : S.R dst = E++outputTail) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireCountedLineCost (missing*L) w+72*s*w+31 ∧
      Exec body plan.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          (scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w)++outputTail))}) := by
  exact preparedWindowPublication_exec plan.count plan.savedControl plan.advances plan.savedAdvances plan.counter plan.window plan.zero
    plan.acc plan.control plan.trash plan.tmp plan.padRows plan.wordWidth plan.retireCount plan.gap src dst plan.hreg
    windows w missing hw1 paddedRows rows hlen hrows hpadded hmissing hreal E sourceTail outputTail borrowed hE v S
    hready.count hready.advances hready.window hsrc hdst hready.padRows hready.wordWidth hready.fresh

end PreparedPublicationPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
