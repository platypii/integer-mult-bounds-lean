module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputPlan

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
variable {T A s : ℕ} [NeZero s]

/-- Retained inputs and generated workspace read by full-line preparation. -/
def support (plan : FullLineInputPlan T) : List (Fin T) :=
  List.ofFn plan.work ++ List.ofFn plan.parameters ++
    [plan.word,plan.saved,plan.tmp,plan.queue,plan.ambient,plan.replicas]

theorem Ready.of_frame {plan : FullLineInputPlan T} {p u l target t : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {S F : Stacks T A}
    (h : plan.Ready p u l target t Fs S)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i)
    (hL : ∀ i, F.L (plan.work i) = S.L (plan.work i)) :
    plan.Ready p u l target t Fs F := by
  have hw (i : Fin 303) : F.R (plan.work i) = S.R (plan.work i) :=
    hR _ (by simp only [support,List.mem_append,List.mem_ofFn]; exact Or.inl (Or.inl ⟨i,rfl⟩))
  have hp (i : Fin 8) : F.R (plan.parameters i) = S.R (plan.parameters i) :=
    hR _ (by simp only [support,List.mem_append,List.mem_ofFn]; exact Or.inl (Or.inr ⟨i,rfl⟩))
  have hc (i : Fin T) (hi : i ∈ [plan.word,plan.saved,plan.tmp,plan.queue,plan.ambient,plan.replicas]) :
      F.R i = S.R i := hR i (List.mem_append_right _ hi)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i; rw [hp]; exact h.parameters i
  · rw [hw]; exact h.width
  · intro i hi; exact (hw i).trans (h.blank i hi)
  · intro i; exact (hL i).trans (h.left i)
  · intro i hi
    rw [hc i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)]
    exact h.scratch i hi
  · rw [hc _ (by simp)]; exact h.ambient
  · rw [hc _ (by simp)]; exact h.replicas

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan
