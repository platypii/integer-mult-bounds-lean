module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPackedProducerLifecycle
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputFrame
public import IntegerMultBounds.MathlibTM2.Host.AppendRuns

/-! Structural batches of generated, restored suppliers. The actual retained
inputs differ by call; output accumulation shares one maximum scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s t : ℕ} [NeZero s] [NeZero t]

structure GeneratedSupplierCall (producer : PackedProducerPlan T Q)
    (t : ℕ) [NeZero t] (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) where
  input : SupplierInputPlan T
  job : PackedNormalizedJob A s
  sourceRegs : ∀ i, [input.work i,producer.src,producer.tmp,producer.saved].Nodup
  workOff : ∀ i j, producer.work i ≠ input.work j
  resultOff : producer.result ∉ input.support
  controlOff : ∀ k ∈ [producer.count,producer.tmp,producer.spare,producer.clock,producer.saved,producer.savedClock],
    ∀ i, k ≠ input.work i
  ht : job.t = t
  hp : 4 ≤ job.p
  target : job.p+2 ≤ job.targetOut
  locality : job.localityTarget = job.targetOut
  inverse : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t job.α = 1

namespace GeneratedSupplierCall
variable {producer : PackedProducerPlan T Q} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}

noncomputable def timeCost (c : GeneratedSupplierCall (A := A) producer t J) (S : Stacks T A) {U : Type} : ℕ :=
  c.input.timeCost c.job S+(producer.timeCost (U := U) [c.job]+
    20*(descriptorScheduleTape producer.work PackedNormalizedJob.words [c.job]).length+7)+
      (2*(∑ i, (c.job.words i).length)+651)

noncomputable def stock (c : GeneratedSupplierCall (A := A) producer t J) (S : Stacks T A) (C : ℕ) {U : Type} : ℕ :=
  c.input.stock c.job S+(31*(descriptorScheduleTape producer.work PackedNormalizedJob.words [c.job]).length+9+
    (C+1)*producer.workspace (U := U) [c.job])

def volume (c : GeneratedSupplierCall (A := A) producer t J) : ℕ :=
  c.job.Fs.length*coreLength s c.job.coreWidth c.job.k*c.job.W

noncomputable def Rows (c : GeneratedSupplierCall (A := A) producer t J) (xs : List (Fin (A+4))) : Prop :=
  ∃ rows : Fin c.job.Fs.length → List GaussianInt,
    (∀ i, (rows i).length = coreLength s c.job.coreWidth c.job.k) ∧
    c.job.ExactRowOutput J (List.ofFn rows) ∧ xs = (List.ofFn fun i => cstream A c.job.W (rows i)).flatten

end GeneratedSupplierCall
namespace PackedProducerPlan
variable {P U : Type} {body : P → Pr P T Q A U}

private theorem result_off_support (producer : PackedProducerPlan T Q) : producer.result ∉ producer.support := by
  intro hm
  simp only [support,List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact producer.hsep i (by rw [hi]; simp)
  · have hr := producer.hreg
    regs_ne hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm
    · exact ‹producer.src ≠ producer.result› hm.symm
    · exact ‹producer.saved ≠ producer.result› hm.symm
    · exact ‹producer.count ≠ producer.result› hm.symm
    · exact ‹producer.tmp ≠ producer.result› hm.symm
    · exact ‹producer.spare ≠ producer.result› hm.symm
    · exact ‹producer.result ≠ producer.clock› hm
    · exact ‹producer.result ≠ producer.savedClock› hm

noncomputable def generatedBatch (producer : PackedProducerPlan T Q)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (calls : List (GeneratedSupplierCall (A := A) producer t J)) : Pr P T Q A U :=
  appendRuns (fun c => c.input.run producer) calls

theorem generatedBatch_exec (producer : PackedProducerPlan T Q)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (calls : List (GeneratedSupplierCall (A := A) producer t J))
    (hA : 96 ≤ A) (v : HS T Q A U) (S : Stacks T A)
    (hinputs : ∀ c ∈ calls, c.input.Ready c.job S)
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ v' n outputs, v'.user = v.user ∧ n ≤ (calls.map (fun c => c.timeCost (U := U) S)).sum+1 ∧
      List.Forall₂ GeneratedSupplierCall.Rows calls outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((calls.map GeneratedSupplierCall.volume).sum+maxRunStock (fun c => c.stock (U := U) S C) calls)) depth
        (producer.generatedBatch calls) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R producer.result (outputs.reverse.flatten++S.R producer.result)}) := by
  let I : Stacks T A → Prop := fun F => (∀ i, i ≠ producer.result → F.R i = S.R i) ∧ F.L = S.L
  apply appendRuns_exec (fun c => c.input.run producer) producer.result calls
    (fun c => c.timeCost (U := U) S) (fun c => c.stock (U := U) S C) GeneratedSupplierCall.volume
    GeneratedSupplierCall.Rows I ?_ depth ?_ v S ⟨fun _ _ => rfl,rfl⟩
  · intro F xs hI
    refine ⟨?_,hI.2⟩
    intro i hi
    change Function.update F.R producer.result _ i = _
    rw [Function.update_of_ne hi,hI.1 i hi]
  · intro c hc w F hI
    have hR : ∀ i ∈ c.input.support, F.R i = S.R i := by
      intro i hi
      apply hI.1 i
      intro he
      exact c.resultOff (he ▸ hi)
    have hready := (hinputs c hc).of_frame hR hI.2
    have hk := hkernel.of_frame (F := F) (by
      intro i hi
      apply hI.1 i
      intro he
      exact producer.result_off_support (he ▸ hi)) (by intro i; rw [hI.2])
    obtain ⟨w',n,rows,hu,hn,hlen,hrows,he⟩ := c.input.run_exec (body := body) producer c.job c.sourceRegs c.workOff
      (by intro i he; exact c.resultOff (he ▸ c.input.work_mem i)) c.controlOff hA t c.job.Fs.length
      (coreLength s c.job.coreWidth c.job.k) c.ht c.hp c.target c.locality J c.inverse rfl rfl w F hready
      hk.hblank hk.hleft hk.hscratch (List.eq_nil_of_length_eq_zero (by simpa using hk.hclock)) hk.hsaved hk.hsavedClock
      C depth hpush hbody
    have htime : c.timeCost (U := U) F = c.timeCost (U := U) S := by
      simp only [GeneratedSupplierCall.timeCost,c.input.timeCost_congr c.job S F hR]
    have hstock : c.stock (U := U) F C = c.stock (U := U) S C := by
      simp only [GeneratedSupplierCall.stock,c.input.stock_congr c.job S F hR]
    change n ≤ c.timeCost (U := U) F at hn
    change ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk w F)+depth+c.stock (U := U) F C) _ _ _ _ _ at he
    rw [htime] at hn
    rw [hstock] at he
    let xs := (List.ofFn fun i => (List.ofFn fun j => cstream A c.job.W (rows i j)).flatten).flatten
    have hxs : xs = (List.ofFn fun j => cstream A c.job.W (rows 0 j)).flatten := by
      simp [xs,List.ofFn_succ]
    refine ⟨w',n,xs,hu,hn,?_,?_,he⟩
    · rw [hxs]
      simp only [List.length_flatten,List.map_ofFn,Function.comp_def,length_cstream,hlen,List.sum_ofFn,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,GeneratedSupplierCall.volume,Nat.mul_assoc]
      exact le_rfl
    · exact ⟨rows 0,hlen 0,hrows 0,hxs⟩

end PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
