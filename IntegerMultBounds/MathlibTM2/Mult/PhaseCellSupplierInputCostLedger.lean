module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierReadyCosts

/-! Ordinary supplier setup has an exact replica-independent part, plus unary
replica-count copying and actual payload copying. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ} [NeZero s]

def headerSharedCost (r : PackedNormalizedJob A s) : ℕ :=
  4*(r.W+r.p+(r.b-r.a)*r.W)+17

theorem headerCopyCost_affine (r : PackedNormalizedJob A s) :
    r.headerCopyCost = r.headerSharedCost+4*r.Fs.length := by
  simp [headerCopyCost,headerSharedCost,List.ofFn_succ]
  omega

noncomputable def inputSharedTimeCost (r : PackedNormalizedJob A s) : ℕ :=
  (r.masterCopyCost+factoryGeometryCost r.a r.b r.V)+
    ((r.radius*(4*r.V+10)+4*r.V+8+(r.headerSharedCost+6))+
      ((coreLength s r.coreWidth r.k+r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b)*(4*r.Bcore+10)+72*r.Bcore+109))

noncomputable def inputSharedStock (r : PackedNormalizedJob A s) : ℕ :=
  (2*r.masterCopyCost+(8*r.a+8*r.b+24*r.V+40))+
    ((2*(4*r.V+4)+(2*r.headerSharedCost+12))+10*(2*(4*r.Bcore+4)))

theorem inputTimeCost_affine (r : PackedNormalizedJob A s) :
    r.inputTimeCost = r.inputSharedTimeCost+4*r.Fs.length+6*r.inputPayload.length := by
  simp only [inputTimeCost,inputSharedTimeCost,r.headerCopyCost_affine]
  omega

theorem inputStock_affine (r : PackedNormalizedJob A s) :
    r.inputStock = r.inputSharedStock+8*r.Fs.length+12*r.inputPayload.length := by
  simp only [inputStock,inputSharedStock,r.headerCopyCost_affine]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
