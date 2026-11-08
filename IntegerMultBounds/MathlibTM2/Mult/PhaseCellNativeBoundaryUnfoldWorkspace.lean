module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Native scratch outside the numerical factor-state projection, retained for
the inverse fold. Numerical factor scratch is already in BoundarySolveReady. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

structure NativeBoundaryUnfoldWorkspace {A : ℕ} (N : ℕ) (S : Stacks 234 A) : Prop where
  mul : ∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []
  scalar : S.R 184 = []
  exponent : S.R 223 = []
  count : (S.R 116).length = N

theorem NativeBoundaryUnfoldWorkspace.of_frame {A N : ℕ} {S F : Stacks 234 A}
    (h : NativeBoundaryUnfoldWorkspace N S)
    (hf : ∀ k : Fin 234, k.val < 64 ∨ k = 184 ∨ k = 223 ∨ k = 116 → F.R k = S.R k) :
    NativeBoundaryUnfoldWorkspace N F := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; rw [hf _ (Or.inl i.isLt)]; exact h.mul i
  · rw [hf 184 (Or.inr (Or.inl rfl))]; exact h.scalar
  · rw [hf 223 (Or.inr (Or.inr (Or.inl rfl)))]; exact h.exponent
  · rw [hf 116 (Or.inr (Or.inr (Or.inr rfl)))]; exact h.count

theorem NativeBoundaryUnfoldWorkspace.updateR {A N : ℕ} {S : Stacks 234 A}
    (h : NativeBoundaryUnfoldWorkspace N S) (k : Fin 234) (xs : List (Fin (A+4)))
    (hk : 64 ≤ k.val) (h184 : k ≠ 184) (h223 : k ≠ 223) (h116 : k ≠ 116) :
    NativeBoundaryUnfoldWorkspace N {S with R := Function.update S.R k xs} := by
  apply h.of_frame
  intro i hi
  apply Function.update_of_ne
  intro he
  subst i
  rcases hi with hi | hi | hi | hi
  · omega
  · exact h184 hi
  · exact h223 hi
  · exact h116 hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
