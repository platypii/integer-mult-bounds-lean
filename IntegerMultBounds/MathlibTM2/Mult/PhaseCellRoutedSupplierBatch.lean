module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedPackedProducer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedSupplierBatch
public import IntegerMultBounds.MathlibTM2.Host.ConsumeRuns

/-! Actual supplier calls consume a contiguous archive and share one scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s t : ℕ} [NeZero s] [NeZero t]

namespace GeneratedSupplierCall
variable {producer : PackedProducerPlan T Q} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
noncomputable def payload (c : GeneratedSupplierCall (A := A) producer t J) : List (Fin (A+4)) :=
  cstream A c.job.W (c.job.Fs.map (packedInterval c.job.a (c.job.b-c.job.a))).flatten
end GeneratedSupplierCall

namespace PackedProducerPlan
variable {P U : Type} {body : P → Pr P T Q A U}

noncomputable def routedBatch (producer : PackedProducerPlan T Q)
    {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)} (calls : List (GeneratedSupplierCall (A := A) producer t J))
    (count source saved tmp : Fin T) : Pr P T Q A U :=
  appendRuns (fun c => c.input.routedRun producer count source saved tmp) calls

theorem routedBatch_exec (producer : PackedProducerPlan T Q)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (calls : List (GeneratedSupplierCall (A := A) producer t J))
    (count source saved tmp : Fin T) (tail : List (Fin (A+4)))
    (hregs : [source,producer.result,count,saved,tmp].Nodup)
    (hcallRegs : ∀ c ∈ calls, [count,source,c.input.publication.retained 6,saved,tmp].Nodup)
    (hsourceInput : ∀ c ∈ calls, source ∉ c.input.support)
    (hsourceKernel : source ∉ producer.support)
    (hpayloadKernel : ∀ c ∈ calls, c.input.publication.retained 6 ∉ producer.support)
    (hA : 96 ≤ A) (v : HS T Q A U) (S : Stacks T A)
    (hinputs : ∀ c ∈ calls, c.input.Ready c.job (c.input.payloadState c.job S))
    (hkernel : producer.Ready ([] : List (PackedNormalizedJob A s)) (S.R producer.src) S)
    (hsource : S.R source = calls.flatMap GeneratedSupplierCall.payload++tail)
    (hcount : ∀ c ∈ calls, (S.R count).length = c.payload.length)
    (hpayload : ∀ c ∈ calls, S.R (c.input.publication.retained 6) = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (C depth : ℕ) (hpush : mnProgPush (producer.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (calls.map (fun c => (6*c.payload.length+6)+
        c.timeCost (U := U) (c.input.payloadState c.job S)+(2*c.payload.length+2))).sum+1 ∧
      List.Forall₂ GeneratedSupplierCall.Rows calls outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((calls.map GeneratedSupplierCall.volume).sum+
          maxRunStock (fun c => 2*(6*c.payload.length+6)+c.stock (U := U) (c.input.payloadState c.job S) C) calls)) depth
        (producer.routedBatch calls count source saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R source tail) producer.result
          (outputs.reverse.flatten++S.R producer.result))}) := by
  have hr := hregs
  regs_ne hr
  let I : Stacks T A → Prop := fun F => (∀ i, i ≠ source → i ≠ producer.result → F.R i = S.R i) ∧ F.L = S.L
  apply consumeRuns_exec (fun c => c.input.routedRun producer count source saved tmp) source producer.result
    ‹source ≠ producer.result› GeneratedSupplierCall.payload calls tail
    (fun c => (6*c.payload.length+6)+c.timeCost (U := U) (c.input.payloadState c.job S)+(2*c.payload.length+2))
    (fun c => 2*(6*c.payload.length+6)+c.stock (U := U) (c.input.payloadState c.job S) C)
    GeneratedSupplierCall.volume GeneratedSupplierCall.Rows I ?_ depth ?_ v S ⟨fun _ _ _ => rfl,rfl⟩ hsource
  · intro F rest xs hI
    refine ⟨?_,hI.2⟩
    intro i his hir
    simp only [Function.update_of_ne hir,Function.update_of_ne his]
    exact hI.1 i his hir
  · intro c hc w F rest hI hsrc
    have hcall := hcallRegs c hc
    have hcr := hcall
    regs_ne hcr
    have hresultPayload : c.input.publication.retained 6 ≠ producer.result := by
      intro he
      exact c.resultOff (he ▸ c.input.retained_mem 6)
    have hframe : ∀ i ∈ c.input.support,
        (c.input.payloadState c.job {F with R := Function.update F.R source rest}).R i =
          (c.input.payloadState c.job S).R i := by
      intro i hi
      by_cases hp : i = c.input.publication.retained 6
      · subst i; simp [SupplierInputPlan.payloadState]
      · have his : i ≠ source := by intro he; exact hsourceInput c hc (he ▸ hi)
        have hir : i ≠ producer.result := by intro he; exact c.resultOff (he ▸ hi)
        simp only [SupplierInputPlan.payloadState,Function.update_of_ne hp,Function.update_of_ne his]
        exact hI.1 i his hir
    have hready := (hinputs c hc).of_frame hframe hI.2
    have hk := hkernel.of_frame (F := F) (by
      intro i hi
      apply hI.1 i
      · intro he; exact hsourceKernel (he ▸ hi)
      · intro he; exact producer.result_off_support (he ▸ hi)) (by intro i; rw [hI.2])
    obtain ⟨w',n,rows,hu,hn,hlen,hrows,he⟩ := c.input.routedRun_exec (body := body) producer c.job
      c.sourceRegs c.workOff c.resultOff c.controlOff hA t c.job.Fs.length
      (coreLength s c.job.coreWidth c.job.k) c.ht c.hp c.target c.locality J c.inverse rfl rfl
      w F rest count source saved tmp hcall hready
      (by rw [hI.1 count ‹source ≠ count›.symm ‹producer.result ≠ count›.symm]; exact hcount c hc)
      hsrc
      (by rw [hI.1 _ ‹source ≠ c.input.publication.retained 6›.symm hresultPayload]; exact hpayload c hc)
      (by rw [hI.1 saved ‹source ≠ saved›.symm ‹producer.result ≠ saved›.symm]; exact hsaved)
      (by rw [hI.1 tmp ‹source ≠ tmp›.symm ‹producer.result ≠ tmp›.symm]; exact htmp)
      hsourceKernel ‹source ≠ producer.result›.symm (hpayloadKernel c hc)
      hk.hblank hk.hleft hk.hscratch (List.eq_nil_of_length_eq_zero (by simpa using hk.hclock)) hk.hsaved hk.hsavedClock
      C depth hpush hbody
    have htime := c.input.timeCost_congr c.job (c.input.payloadState c.job S)
      (c.input.payloadState c.job {F with R := Function.update F.R source rest}) hframe
    have hstock := c.input.stock_congr c.job (c.input.payloadState c.job S)
      (c.input.payloadState c.job {F with R := Function.update F.R source rest}) hframe
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
