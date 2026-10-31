module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreControlCostLedger
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedJobWorkspaceLedger

/-! The actual singleton producer's loader and retirement are data-linear once
its shared numerical workspace is separated from replica storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s : ℕ} [NeZero s] {U : Type}
namespace PackedProducerPlan

private theorem singletonTime {β : Type} (r : β) (load setup cleanup count replica : β → ℕ)
    (tape : List β → ℕ) (volume : ℕ)
    (hload : load r = 23*volume+24*325+1) (htape : tape [r] = 2*volume+325) :
    (([r].reverse.map fun x => load x+setup x+cleanup x+3).sum+
      ([r].reverse.map fun x => count x*replica x).sum+6*[r].length+
      2*tape [r].reverse+10) = setup r+count r*replica r+27*volume+cleanup r+8470 := by
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,Nat.add_zero,hload,htape]
  omega

private theorem singletonStock {β : Type} (r : β) (output load persistent workspace cleanup : β → ℕ)
    (tape : List β → ℕ) (volume : ℕ)
    (hload : load r = 23*volume+24*325+1) (htape : tape [r] = 2*volume+325) :
    (([r].reverse.map output).sum+
      ([r].reverse.map fun x => load x+(persistent x+workspace x)+cleanup x).foldr max 0+
      6*[r].length+2*tape [r].reverse+8) =
      output r+27*volume+persistent r+workspace r+cleanup r+8465 := by
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,List.foldr_cons,List.foldr_nil,
    max_eq_left (Nat.zero_le _),Nat.add_zero,hload,htape]
  omega

theorem singleton_timeCost_eq (producer : PackedProducerPlan T Q) (r : PackedNormalizedJob A s) :
    producer.timeCost (U := U) [r] = r.setupTime+r.Fs.length*r.replicaTime+
      27*(∑ i, (r.words i).length)+r.cleanup (U := U) producer.hR producer.hQ+8470 := by
  have ht := descriptorScheduleTape_length producer.work PackedNormalizedJob.words [r]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at ht
  have hb := singletonTime r
    (fun x => takeDescriptorBankCost (placedDescriptorFields producer.work x.words))
    PackedNormalizedJob.setupTime (PackedNormalizedJob.cleanup (U := U) producer.hR producer.hQ)
    (fun x => x.Fs.length) PackedNormalizedJob.replicaTime
    (fun records => (descriptorScheduleTape producer.work PackedNormalizedJob.words records).length)
    (∑ i, (r.words i).length) (takePlacedDescriptorBankCost_eq producer.work r.words) ht
  exact hb

theorem singleton_workspace_eq (producer : PackedProducerPlan T Q) (r : PackedNormalizedJob A s) :
    producer.workspace (U := U) [r] = r.outputVolume+
      27*(∑ i, (r.words i).length)+r.persistent+r.workspace+
      r.cleanup (U := U) producer.hR producer.hQ+8465 := by
  have ht := descriptorScheduleTape_length producer.work PackedNormalizedJob.words [r]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at ht
  have hb := singletonStock r PackedNormalizedJob.outputVolume
    (fun x => takeDescriptorBankCost (placedDescriptorFields producer.work x.words))
    PackedNormalizedJob.persistent PackedNormalizedJob.workspace
    (PackedNormalizedJob.cleanup (U := U) producer.hR producer.hQ)
    (fun records => (descriptorScheduleTape producer.work PackedNormalizedJob.words records).length)
    (∑ i, (r.words i).length) (takePlacedDescriptorBankCost_eq producer.work r.words) ht
  exact hb

private theorem cleanupBill (volume persistent workspace pushes c : ℕ) (hpush : pushes ≤ c) :
    6*(volume+persistent+(pushes+1)*workspace)+1956 ≤
      6*(volume+persistent+(c+1)*workspace)+1956 := by
  have hm := Nat.mul_le_mul_right workspace (Nat.add_le_add_right hpush 1)
  omega

theorem cleanup_le (producer : PackedProducerPlan T Q) (r : PackedNormalizedJob A s) (c : ℕ)
    (hpush : mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) producer.hR producer.hQ) ≤ c) :
    r.cleanup (U := U) producer.hR producer.hQ ≤
      6*((∑ i, (r.words i).length)+r.persistent+(c+1)*r.workspace)+1956 := by
  have hb := cleanupBill (∑ i, (r.words i).length) r.persistent r.workspace
    (mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) producer.hR producer.hQ)) c hpush
  exact hb

private theorem singletonBounds
    (volume persistent workspace output cleanup shared payload replicas inputStock V setup replica c : ℕ)
    (hvolume : volume ≤ inputStock+8*replicas+12*payload)
    (hpersistent : persistent ≤ 2*payload+V) (houtput : output ≤ payload)
    (hworkspace : workspace ≤ shared+500*(payload+replicas))
    (hcleanup : cleanup ≤ 6*(volume+persistent+(c+1)*workspace)+1956) :
    (setup+replicas*replica+27*volume+cleanup+8470 ≤ setup+replicas*replica+
      6*(c+1)*shared+(3000*(c+1)+1000)*(payload+replicas)+33*inputStock+6*V+10426) ∧
    (output+27*volume+persistent+workspace+cleanup+8465 ≤
      (6*(c+1)+1)*shared+(3000*(c+1)+1000)*(payload+replicas)+33*inputStock+7*V+10421) := by
  have ht := Nat.mul_le_mul_left (6*(c+1)) hworkspace
  have hs := Nat.mul_le_mul_left (6*(c+1)+1) hworkspace
  constructor <;> nlinarith only [hvolume,hpersistent,houtput,hcleanup,ht,hs]

/-- The actual producer's nonnumerical costs are data-linear, with one shared
numerical allowance and the actual fixed program's push bound explicit. -/
theorem singleton_costs_le_ready (producer : PackedProducerPlan T Q) (r : PackedNormalizedJob A s)
    (input : SupplierInputPlan T) (S : Stacks T A) (hready : input.Ready r S)
    (v : HS T Q A U) (c : ℕ)
    (hpush : mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) producer.hR producer.hQ) ≤ c) :
    (producer.timeCost (U := U) [r] ≤ r.setupTime+r.Fs.length*r.replicaTime+
      6*(c+1)*r.sharedWorkspace+(3000*(c+1)+1000)*(r.inputPayload.length+r.Fs.length)+
      33*r.inputSharedStock+6*r.V+10426) ∧
    (producer.workspace (U := U) [r] ≤ (6*(c+1)+1)*r.sharedWorkspace+
      (3000*(c+1)+1000)*(r.inputPayload.length+r.Fs.length)+
      33*r.inputSharedStock+7*r.V+10421) := by
  have hvolume := hready.packetVolume_le v
  rw [r.inputStock_affine] at hvolume
  have hb := singletonBounds (∑ i, (r.words i).length) r.persistent r.workspace r.outputVolume
    (r.cleanup (U := U) producer.hR producer.hQ) r.sharedWorkspace r.inputPayload.length r.Fs.length
    r.inputSharedStock r.V r.setupTime r.replicaTime c hvolume r.persistent_le_payload
    r.outputVolume_le_payload r.workspace_le_shared_add_payload (producer.cleanup_le r c hpush)
  exact ⟨(producer.singleton_timeCost_eq r).trans_le hb.1,
    (producer.singleton_workspace_eq r).trans_le hb.2⟩

end PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
