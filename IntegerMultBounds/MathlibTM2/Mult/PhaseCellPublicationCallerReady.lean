module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedPublicationPlacement

/-! Owned publication words start blank and all placed left stacks are fresh.
The same contract survives updates outside its owned right ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {N A : ℕ}

structure PublicationCallerReady (src : Fin 10 → Fin N)
    (placement : Fin PackedTranspose.tapeCount → Fin N) (S : Stacks N A) : Prop where
  ownedBlank : ∀ j ∈ [(0 : Fin 10),1,2,4,6,8,9], S.R (src j) = []
  leftBlank : ∀ i, (embStk placement S).L i = []

namespace PublicationCallerReady
variable {src : Fin 10 → Fin N} {placement : Fin PackedTranspose.tapeCount → Fin N} {S : Stacks N A}

theorem reframe (h : PublicationCallerReady src placement S) (F : Stacks N A) (output : Fin N)
    (hR : ∀ k, k ≠ output → F.R k = S.R k) (hL : F.L = S.L)
    (hoff : ∀ j ∈ [(0 : Fin 10),1,2,4,6,8,9], src j ≠ output) :
    PublicationCallerReady src placement F := by
  constructor
  · intro j hj
    exact (hR _ (hoff j hj)).trans (h.ownedBlank j hj)
  · intro i
    change F.L (placement i) = []
    rw [hL]
    exact h.leftBlank i

theorem updateOutput (h : PublicationCallerReady src placement S) (output : Fin N)
    (xs : List (Fin (A+4))) (hoff : ∀ j ∈ [(0 : Fin 10),1,2,4,6,8,9], src j ≠ output) :
    PublicationCallerReady src placement {S with R := Function.update S.R output xs} :=
  h.reframe _ output (fun _ hk => Function.update_of_ne hk xs S.R) rfl hoff

end PublicationCallerReady
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
