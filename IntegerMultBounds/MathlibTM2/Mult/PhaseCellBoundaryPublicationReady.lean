module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Physical handoff needed by fully generated boundary publication. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2 IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

structure BoundaryPublicationReady {A : ℕ} (S : Stacks 224 A) (s N V w : ℕ) : Prop where
  left : ∀ i, S.L i = []
  mul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []
  ambient : (S.R 121).length = s
  width : (S.R 160).length = w
  geometry : (S.R 115).length = V
  count : S.R 116 = List.replicate N IntegerMultBounds.MathlibTM2.Node.tick
  scratch : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,184,217,223,201,208,211,215,220,206] : List (Fin 224)), S.R i = []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
