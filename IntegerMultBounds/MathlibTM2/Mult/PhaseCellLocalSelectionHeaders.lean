module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowHeaderLoad

/-! Ordinary input headers shared by single-field and bulk local selection. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

/-- Ordinary selector headers and initially empty local scratch. -/
structure LocalSelectionHeaders (A W V s t a origin w n : ℕ) (S : Stacks 117 A) : Prop where
  width : (S.R 114).length = W
  movementWidth : (S.R 115).length = V
  sourceSize : S.R 32 = binSyms W s
  targetSize : S.R 33 = binSyms W t
  sourceOrigin : S.R 34 = binSyms W a
  targetOrigin : S.R 35 = binSyms W origin
  rowCount : S.R 36 = binSyms W n
  zero : S.R 37 = []
  table : ∀ k : Fin 117, k.val < 31 → S.R k = []
  word : (S.R 94).length = w
  zero104 : S.R 104 = []
  zero106 : S.R 106 = []
  zero116 : S.R 116 = []
  fresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = []
  row : (S.R 103).length = 1
  control : S.R 91 = []
  clean : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], S.R k = []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
