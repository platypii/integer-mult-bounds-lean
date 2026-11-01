module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerSizing

/-! Ordinary scalar data and format bounds for one inverse-header generation.
This contains no numerical solution or execution premise. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure InverseMasterInput (s : ℕ) [NeZero s] where
  B : ℕ
  p : ℕ
  u : ℕ
  l : ℕ
  target : ℕ
  t : ℕ
  a : ℕ
  b : ℕ
  hst : s < t
  has : a ≤ s
  hbs : b ≤ s
  hband : PhaseCellBand.width p u ≤ s
  band_room : 64*(p+1)+u < 2^B
  geometry_room : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B
  precision_room : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
    (PhaseCellBand.width p u) < 2^B
  values_fit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B

namespace InverseMasterInput
variable {s : ℕ} [NeZero s]
/-- The standard ambient scalar width supplies all room premises uniformly in
local endpoints. Only ordinary interval geometry is required. -/
noncomputable def ofCuts (p u l target t a b : ℕ) (hst : s < t) (has : a ≤ s) (hbs : b ≤ s)
    (hband : PhaseCellBand.width p u ≤ s) : InverseMasterInput s := by
  let B := inverseCallerWordWidth p u l target s t
  have hrooms := inverseCallerWordWidth_fits_cuts p u l target s t a b
  refine ⟨B,p,u,l,target,t,a,b,hst,has,hbs,hband,hrooms.1,hrooms.2.1,hrooms.2.2,?_⟩
  have hfit := inverseInputScalars_fit (A := 0) hst has hbs hrooms.1 hrooms.2.1 hrooms.2.2
  intro i
  have hi := hfit ⟨i.val,by have := i.isLt; omega⟩
  fin_cases i <;> exact hi

def values (d : InverseMasterInput s) : Fin 8 → ℕ := ![d.p,d.u,d.l,d.target,s,d.t,d.a,d.b]
noncomputable def masters (d : InverseMasterInput s) : Fin 10 → ℕ :=
  inverseMasterValues d.p d.u d.l d.target s d.t d.a d.b
noncomputable def timeCost (d : InverseMasterInput s) : ℕ :=
  generateInverseMastersCost d.B d.p d.u d.l d.target s d.t d.a d.b+(50*d.B+51)
noncomputable def stock (d : InverseMasterInput s) : ℕ :=
  (392*d.B+396)+3*(inverseScalarAtoms d.p s d.t d.u d.a d.b*tblC d.B 0+inverseMasterCopyCost d.B d.masters)
end InverseMasterInput
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
