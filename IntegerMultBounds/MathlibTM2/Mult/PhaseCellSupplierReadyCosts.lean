module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedRoutedSupplier

/-! Readiness determines setup bills numerically, independently of the physical
state produced by header generation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T A s : ℕ} [NeZero s]

namespace PackedNormalizedJob

noncomputable def masterCopyCost (r : PackedNormalizedJob A s) : ℕ :=
  (List.ofFn fun i => 4*r.factoryMasters i+4).sum+1

def headerCopyCost (r : PackedNormalizedJob A s) : ℕ :=
  (List.ofFn fun i : Fin 4 => 4*(![r.Fs.length,r.W,r.p,(r.b-r.a)*r.W] i)+4).sum+1

noncomputable def inputTimeCost (r : PackedNormalizedJob A s) : ℕ :=
  (r.masterCopyCost+factoryGeometryCost r.a r.b r.V)+
    ((r.radius*(4*r.V+10)+4*r.V+8+(r.headerCopyCost+(6*r.inputPayload.length+6)))+
      ((coreLength s r.coreWidth r.k+r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b)*(4*r.Bcore+10)+72*r.Bcore+109))

noncomputable def inputStock (r : PackedNormalizedJob A s) : ℕ :=
  (2*r.masterCopyCost+(8*r.a+8*r.b+24*r.V+40))+
    ((2*(4*r.V+4)+(2*r.headerCopyCost+2*(6*r.inputPayload.length+6)))+10*(2*(4*r.Bcore+4)))

end PackedNormalizedJob

namespace SupplierInputPlan.Ready

theorem masterCost_eq {plan : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : plan.Ready r S) : plan.masterCost S = r.masterCopyCost := by
  simp only [SupplierInputPlan.masterCost,masterHeaderCopies,copyUnaryHeadersCost,
    List.map_ofFn,Function.comp_def,h.masters,PackedNormalizedJob.masterCopyCost]

theorem headerCost_eq {plan : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : plan.Ready r S) : plan.headerCost S = r.headerCopyCost := by
  simp only [SupplierInputPlan.headerCost,descriptorHeaderCopies,copyUnaryHeadersCost,
    List.map_ofFn,Function.comp_def,h.headers,PackedNormalizedJob.headerCopyCost]

theorem timeCost_eq {plan : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : plan.Ready r S) : plan.timeCost r S = r.inputTimeCost := by
  simp only [SupplierInputPlan.timeCost,h.masterCost_eq,h.headerCost_eq,
    PackedNormalizedJob.inputTimeCost,PackedNormalizedJob.inputPayload]

theorem stock_eq {plan : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : plan.Ready r S) : plan.stock r S = r.inputStock := by
  simp only [SupplierInputPlan.stock,h.masterCost_eq,h.headerCost_eq,
    PackedNormalizedJob.inputStock,PackedNormalizedJob.inputPayload]

end SupplierInputPlan.Ready
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
