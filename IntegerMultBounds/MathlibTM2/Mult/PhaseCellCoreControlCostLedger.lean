module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputCostLedger
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorScheduleVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierPacketVolume

/-! The actual fixed core body pays numerical execution, descriptor bytes,
payload bytes and ordinary scalar control work as distinct exact charges. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {U : Type}

noncomputable def coreControlTimeCost (V : ℕ) (r : PackedNormalizedJob A s) : ℕ :=
  readSupplierEndpointsCost V r.a (r.b-r.a)+timeCost r+r.inputSharedTimeCost+
    retirementCost r+2*(r.a+r.b)+7171

noncomputable def coreControlStock (V : ℕ) (r : PackedNormalizedJob A s) : ℕ :=
  3*readSupplierEndpointsCost V r.a (r.b-r.a)+stock r+r.inputSharedStock+10096

theorem coreTimeCost_eq (producer : PackedProducerPlan T Q) (V : ℕ) (r : PackedNormalizedJob A s) :
    coreTimeCost (U := U) producer V r = producer.timeCost (U := U) [r]+
      42*(∑ i, (r.words i).length)+14*r.inputPayload.length+4*r.Fs.length+coreControlTimeCost V r := by
  have ht := descriptorScheduleTape_length producer.work PackedNormalizedJob.words [r]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at ht
  simp only [coreTimeCost,r.inputTimeCost_affine,ht,coreControlTimeCost]
  omega

theorem coreStock_eq (producer : PackedProducerPlan T Q) (C V : ℕ) (r : PackedNormalizedJob A s) :
    coreStock (U := U) producer C V r = (C+1)*producer.workspace (U := U) [r]+
      62*(∑ i, (r.words i).length)+24*r.inputPayload.length+8*r.Fs.length+coreControlStock V r := by
  have ht := descriptorScheduleTape_length producer.work PackedNormalizedJob.words [r]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at ht
  simp only [coreStock,r.inputStock_affine,ht,coreControlStock]
  omega

/-- Actual readiness bounds descriptor bytes through their installation trace. -/
theorem coreTimeCost_le_ready (producer : PackedProducerPlan T Q) (V : ℕ) (r : PackedNormalizedJob A s)
    (input : SupplierInputPlan T) (S : Stacks T A) (hready : input.Ready r S) (v : HS T Q A U) :
    coreTimeCost (U := U) producer V r ≤ producer.timeCost (U := U) [r]+
      518*r.inputPayload.length+340*r.Fs.length+(coreControlTimeCost V r+42*r.inputSharedStock) := by
  rw [coreTimeCost_eq]
  have hvolume := hready.packetVolume_le v
  rw [r.inputStock_affine] at hvolume
  omega

theorem coreStock_le_ready (producer : PackedProducerPlan T Q) (C V : ℕ) (r : PackedNormalizedJob A s)
    (input : SupplierInputPlan T) (S : Stacks T A) (hready : input.Ready r S) (v : HS T Q A U) :
    coreStock (U := U) producer C V r ≤ (C+1)*producer.workspace (U := U) [r]+
      768*r.inputPayload.length+504*r.Fs.length+(coreControlStock V r+62*r.inputSharedStock) := by
  rw [coreStock_eq]
  have hvolume := hready.packetVolume_le v
  rw [r.inputStock_affine] at hvolume
  omega

/-- Ordinary setup readiness suffices: the generated header witness is produced
by the existing setup theorem, not assumed by the pricing contract. -/
theorem coreCosts_le_setupReady {input : SupplierInputPlan T} (plan : SupplierSetupPlan input)
    (producer : PackedProducerPlan T Q) (C V : ℕ) (r : PackedNormalizedJob A s)
    (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready r S) :
    (coreTimeCost (U := U) producer V r ≤ producer.timeCost (U := U) [r]+
      518*r.inputPayload.length+340*r.Fs.length+(coreControlTimeCost V r+42*r.inputSharedStock)) ∧
    (coreStock (U := U) producer C V r ≤ (C+1)*producer.workspace (U := U) [r]+
      768*r.inputPayload.length+504*r.Fs.length+(coreControlStock V r+62*r.inputSharedStock)) := by
  obtain ⟨w,H,n,_,_,_,hheaders,_,_,_,_⟩ := plan.generate_exec
    (body := fun f : Empty => nomatch f) r v S hready 0
  exact ⟨coreTimeCost_le_ready producer V r input H hheaders w,
    coreStock_le_ready producer C V r input H hheaders w⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
