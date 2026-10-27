module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBCore

/-! The obsolete unfolding headers have a fixed volume throughout the solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast

def boundaryUnfoldHeaderVolume {A : ℕ} (σ : RsbR → List (Fin (A+4))) : ℕ :=
  (σ .m2wn).length+(σ .kn).length+(σ .tK).length+(σ .sel).length

@[simp] theorem boundaryUnfoldHeaderVolume_update_vk {A : ℕ}
    (σ : RsbR → List (Fin (A+4))) (xs : List (Fin (A+4))) :
    boundaryUnfoldHeaderVolume (Function.update σ .vk xs) = boundaryUnfoldHeaderVolume σ := rfl

@[simp] theorem boundaryUnfoldHeaderVolume_update_dout {A : ℕ}
    (σ : RsbR → List (Fin (A+4))) (xs : List (Fin (A+4))) :
    boundaryUnfoldHeaderVolume (Function.update σ .dout xs) = boundaryUnfoldHeaderVolume σ := rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
