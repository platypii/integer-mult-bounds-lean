module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreSupplierCalls

/-! Consume the exact real-core stream produced by grouped exposure. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s t : ℕ} [NeZero s] [NeZero t]
namespace PackedProducerPlan
variable {P U : Type} {body : P → Pr P T Q A U}

theorem coreRoutedBatch_exec (producer : PackedProducerPlan T Q)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (calls : Fin (coreGatherIndices s width radius L).length → GeneratedSupplierCall (A := A) producer t J)
    (hwidth : ∀ i, (calls i).job.coreWidth = width) (hradius : ∀ i, (calls i).job.radius = radius)
    (hk : ∀ i, (calls i).job.k = (coreGatherIndices s width radius L)[i.val])
    (hword : ∀ i, (calls i).job.W = w) (hFs : ∀ i, (calls i).job.Fs = Fs)
    (count source saved tmp : Fin T) (tail : List (Fin (A+4)))
    (hregs : [source,producer.result,count,saved,tmp].Nodup)
    (hcallRegs : ∀ c ∈ List.ofFn calls, [count,source,c.input.publication.retained 6,saved,tmp].Nodup)
    (hsourceInput : ∀ c ∈ List.ofFn calls, source ∉ c.input.support)
    (hsourceKernel : source ∉ producer.support)
    (hpayloadKernel : ∀ c ∈ List.ofFn calls, c.input.publication.retained 6 ∉ producer.support)
    (hA : 96 ≤ A) (v : HS T Q A U) (S : Stacks T A)
    (hinputs : ∀ c ∈ List.ofFn calls, c.input.Ready c.job (c.input.payloadState c.job S))
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (hsource : S.R source =
      (List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
        cstream A w (Fs.map (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten).flatten++tail)
    (hcount : (S.R count).length = Fs.length*L*w)
    (hpayload : ∀ c ∈ List.ofFn calls, S.R (c.input.publication.retained 6) = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ ((List.ofFn calls).map (fun c => (6*c.payload.length+6)+
        c.timeCost (U := U) (c.input.payloadState c.job S)+(2*c.payload.length+2))).sum+1 ∧
      List.Forall₂ GeneratedSupplierCall.Rows (List.ofFn calls) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((coreGatherIndices s width radius L).length*(Fs.length*(L-2*radius)*w)+
          maxRunStock (fun c => 2*(6*c.payload.length+6)+c.stock (U := U) (c.input.payloadState c.job S) C) (List.ofFn calls))) depth
        (producer.routedBatch (List.ofFn calls) count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) producer.result
          (outputs.reverse.flatten++S.R producer.result))}) := by
  have hpayloads := coreSupplierCalls_payload width radius L w Fs calls hwidth hradius hk hword hFs
  have hvolume := coreSupplierCalls_volume width radius L w Fs calls hwidth hk hword hFs
  obtain ⟨v',n,outputs,hu,hn,hcert,he⟩ := producer.routedBatch_exec (body := body) J (List.ofFn calls)
    count source saved tmp tail hregs hcallRegs hsourceInput hsourceKernel hpayloadKernel hA v S hinputs hkernel
    (by rw [hpayloads]; exact hsource)
    (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [hcount]
      exact ((calls i).payload_length_coreGather width radius L w Fs (hwidth i) (hradius i)
        (by rw [hk i]; exact List.getElem_mem i.isLt) (hword i) (hFs i)).symm)
    hpayload hsaved htmp C depth hpush hbody
  rw [hvolume] at he
  exact ⟨v',n,outputs,hu,hn,hcert,he⟩
end PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
