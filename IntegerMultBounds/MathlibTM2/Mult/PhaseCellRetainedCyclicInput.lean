module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicCallerInput

/-! A produced tensor-selection endpoint transports ordinary caller context
once, independently of the numerical problems and component solutions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {A s : ℕ} [NeZero s]

structure SelectedInput (Fs : List (ZMod s → GaussianInt)) (a n W : ℕ)
    (S F : Stacks tapes A) : Prop where
  archive : F.R caller.archive = cstream A W (Fs.map (packedInterval a n)).flatten
  count : (F.R caller.count).length = Fs.length*n*W
  span : F.R caller.span = List.replicate n Node.tick
  word : F.R (caller.controls 0) = S.R (caller.controls 0)
  batch : ∀ j : Fin 6, F.R (selector (LocalRecoveryLayout.batch j)) =
    if j = 0 then [] else S.R (selector (LocalRecoveryLayout.batch j))
  recovery : ∀ i, F.R (selector (LocalRecoveryLayout.recovery i)) = S.R (selector (LocalRecoveryLayout.recovery i))
  left : F.L = S.L
  outside : ∀ j, j ≠ caller.count → (∀ r, selector r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j

private theorem contextSupport_cases (r : Fin tapes) (h : caller.contextSupport r) :
    r = geometry 94 ∨ (r ≠ caller.count ∧ ∀ j, selector j ≠ r) := by
  rcases h with ⟨i,rfl⟩ | ⟨i,_,h | h⟩ | ⟨i,rfl⟩ | h
  · right
    exact ⟨by simp [caller,numeric,aux,port_injective.eq_iff],fun j => selector_ne_numeric j i⟩
  · subst r
    right
    exact ⟨by simp [caller,seedL,aux,port_injective.eq_iff],fun j => selector_ne_seedL j i⟩
  · subst r
    right
    exact ⟨by simp [caller,seedR,aux,port_injective.eq_iff],fun j => selector_ne_seedR j i⟩
  · fin_cases i
    · exact Or.inl rfl
    · right; exact ⟨by simp [caller,controls,aux,port_injective.eq_iff],fun j => selector_ne_aux j 0⟩
    · right; exact ⟨by simp [caller,controls,aux,port_injective.eq_iff],fun j => selector_ne_aux j 1⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · right; exact ⟨by simp [caller,aux,port_injective.eq_iff],fun j => selector_ne_aux j 3⟩
    · right; exact ⟨by simp [caller,aux,port_injective.eq_iff],fun j => selector_ne_aux j 4⟩

theorem SelectedInput.toPackedInput {Fs : List (ZMod s → GaussianInt)} {a n W radius rows : ℕ}
    {S F : Stacks tapes A} {H K : ReplicaHaloProblem s}
    (h : SelectedInput Fs a n W S F)
    (context : caller.InputContext H K W Fs.length radius rows S) :
    caller.PackedInput H K Fs a n W radius rows F := by
  refine ⟨context.frame ?_ ?_,h.archive,h.count,?_⟩
  · intro i
    exact (h.outside _ (by simp [caller,numeric,aux,port_injective.eq_iff])
      (fun r => selector_ne_numeric r i)).1
  · intro r hr
    rcases contextSupport_cases r hr with hr | ⟨hne,hoff⟩
    · subst r; exact h.word
    · exact (h.outside r hne hoff).2
  · rw [h.span]
    simp

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
