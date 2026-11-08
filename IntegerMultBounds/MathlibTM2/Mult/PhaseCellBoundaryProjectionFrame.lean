module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! The retained nonnumerical controls needed to project a solved boundary
batch. Its unrelated private left stacks may have arbitrary contents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

structure BoundaryProjectionFrame {A : ℕ} (replicas : ℕ) (S : Stacks 234 A) : Prop where
  left : ∀ i : Fin 224, S.L (Fin.castLE (by decide) i) = []
  replicas : (S.R 229).length = replicas
  fresh : ∀ i ∈ [(227 : Fin 234),228,231,232,233], S.R i = []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
