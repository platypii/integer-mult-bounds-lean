module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamCropPlan

/-! Crop readiness depends on retained controls, not on the archive destination.
A preceding bulk run may append output while these controls stay unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.SeamCropPlan
open IntegerMultBounds.MathlibTM2.Host
variable {T A s : ℕ} {source : Fin T}

def readPorts (plan : SeamCropPlan T source) (ks : List ℕ) : List (Fin T) :=
  [plan.clock,plan.rows,plan.width]++plan.cleanPorts++ks.flatMap (fun k => [plan.skip k,plan.count k])

theorem Ready.of_frame {plan : SeamCropPlan T source} {p width replicas : ℕ} {ks : List ℕ}
    {S F : Stacks T A} (ready : plan.Ready p s width replicas ks S)
    (hframe : ∀ r ∈ plan.readPorts ks, F.R r = S.R r) : plan.Ready p s width replicas ks F := by
  have hcontrol (r : Fin T) (hr : r ∈ [plan.clock,plan.rows,plan.width]) :=
    hframe r (List.mem_append_left _ (List.mem_append_left _ hr))
  have hclean (r : Fin T) (hr : r ∈ plan.cleanPorts) :=
    hframe r (List.mem_append_left _ (List.mem_append_right _ hr))
  have hcrop (k : ℕ) (hk : k ∈ ks) (r : Fin T) (hr : r ∈ [plan.skip k,plan.count k]) :=
    hframe r (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k,hk,hr⟩))
  refine {ready with clock := ?_,skip := ?_,count := ?_,rows := ?_,width := ?_,clean := ?_}
  · rw [hcontrol _ (by simp)]; exact ready.clock
  · intro k hk; rw [hcrop k hk _ (by simp)]; exact ready.skip k hk
  · intro k hk; rw [hcrop k hk _ (by simp)]; exact ready.count k hk
  · rw [hcontrol _ (by simp)]; exact ready.rows
  · rw [hcontrol _ (by simp)]; exact ready.width
  · intro r hr; rw [hclean r hr]; exact ready.clean r hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.SeamCropPlan
