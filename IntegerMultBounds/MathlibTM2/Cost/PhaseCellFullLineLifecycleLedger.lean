module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedFullLineRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLinePacketVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorScheduleVolume

/-! The restoring full-period lifecycle adds only data-linear traffic and a
replica-independent scalar charge to the existing S3 producer bills. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan

noncomputable def fullLineTimeScalar (p u l target s t : ℕ) : ℕ :=
  let B := inverseCallerWordWidth p u l target s t
  (p+u+l+target+s+t+0+s)*(4*B+10)+18306*B+26708

noncomputable def fullLineStockScalar (p u l target s t : ℕ) : ℕ :=
  24758*inverseCallerWordWidth p u l target s t+35610

private theorem lifecycleBills (values B payload replicas volume tape grid stock C : ℕ)
    (hvolume : volume ≤ B+((392*B+396)+(2*(6*payload+6)+2*(4*replicas+4))))
    (htape : tape = 2*volume+303) :
    (((values*(4*B+10)+228*B+263)+(6*payload+6)+(4*replicas+4))+
      ((grid+22*tape+26)+(2*volume+607)) ≤
      grid+558*payload+372*replicas+(values*(4*B+10)+18306*B+26708)) ∧
    (((392*B+396)+(2*(6*payload+6)+2*(4*replicas+4)))+(31*tape+9+(C+1)*stock) ≤
      (C+1)*stock+756*payload+504*replicas+(24758*B+35610)) := by
  constructor <;> omega

theorem fullLineLifecycleCosts_le {T Q A s p u l target t : ℕ} [NeZero s] {U : Type}
    (input : FullLineInputPlan T) (producer : PackedProducerPlan T Q) (C : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (v : HS T Q A U) (S : Stacks T A)
    (hready : input.Ready p u l target t Fs S) (hst : s < t) :
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let payload := Fs.length*s*inverseFullInputWidth p u l target s t
    (setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607)) ≤
      r.gridCost p l t producer.gridWork+558*payload+372*Fs.length+fullLineTimeScalar p u l target s t) ∧
    (setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r) ≤
      (C+1)*producer.gridStock p l t r+756*payload+504*Fs.length+fullLineStockScalar p u l target s t) := by
  dsimp only
  let r := fullLineGridRecord (A := A) p u l target t Fs
  have hv := hready.packetVolume_le hst v
  have htape := descriptorScheduleTape_length producer.gridWork FamilyDispatchInput.words [r]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at htape
  have hb := lifecycleBills (p+u+l+target+s+t+0+s) (inverseCallerWordWidth p u l target s t)
    (Fs.length*s*inverseFullInputWidth p u l target s t) Fs.length (∑ i, (r.words i).length)
    (descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]).length
    (r.gridCost p l t producer.gridWork) (producer.gridStock p l t r) C hv htape
  exact hb

end IntegerMultBounds.MathlibTM2.Cost
