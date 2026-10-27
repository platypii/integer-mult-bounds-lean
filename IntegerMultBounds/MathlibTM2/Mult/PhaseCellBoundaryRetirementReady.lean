module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! The retained headers and restored scratch needed to retire published boundary data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Host

structure BoundaryRetirementReady {A : ℕ} (S : Stacks 224 A) (s N W w : ℕ) : Prop where
  ambient : (S.R 121).length = s
  rows : (S.R 116).length = N
  band : (S.R 190).length = W
  width : (S.R 160).length = w
  scratch : ∀ i ∈ ([184,217,152,151,131,134,135,136,137,138] : List (Fin 224)), S.R i = []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
