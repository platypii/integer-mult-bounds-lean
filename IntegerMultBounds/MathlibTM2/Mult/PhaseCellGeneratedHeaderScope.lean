module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! One lifecycle proof for an owned generated header bank. Setup and consumer
share a chronological space trace; retirement preserves the consumer output. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def withGeneratedHeaders (headers : List (Fin T)) (setup consumer : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.seq setup consumer) (clearWords headers)

theorem withGeneratedHeaders_exec_within (body : P → Pr P T Q A U)
    (headers : List (Fin T)) (hnd : headers.Nodup) (dst : Fin T) (hdst : dst ∉ headers)
    (S M : Stacks T A) (hin : M.inp = S.inp) (hout : M.out = S.out) (hleft : M.L = S.L)
    (hframe : ∀ i, i ∉ headers → M.R i = S.R i)
    (hblank : ∀ i ∈ headers, S.R i = [])
    (setup consumer : Pr P T Q A U) (setupTime setupSpace time space depth : ℕ)
    (v : HS T Q A U) (post : List (Fin (A+4)) → Prop)
    (hsetup : ∃ v₁ n, v₁.user = v.user ∧ n ≤ setupTime ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+setupSpace)
        depth setup (mk v S) n (mk v₁ M))
    (hconsumer : ∀ v₁ : HS T Q A U,
      ∃ v₂ n result, v₂.user = v₁.user ∧ n ≤ time ∧ post result ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v₁ M)+depth+space)
          depth consumer (mk v₁ M) n (mk v₂ {M with R := Function.update M.R dst result})) :
    ∃ v' n result, v'.user = v.user ∧
      n ≤ setupTime+time+(2*(headers.map (fun i => (M.R i).length)).sum+2*headers.length+1) ∧
      post result ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+(setupSpace+space))
        depth (withGeneratedHeaders headers setup consumer) (mk v S) n
        (mk v' {S with R := Function.update S.R dst result}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := hsetup
  obtain ⟨v₂,n₂,result,hu₂,hn₂,hpost,he₂⟩ := hconsumer v₁
  obtain ⟨v',hu₃,he₃⟩ := retireHeaderFrame_pair_exec body headers hnd S M hin hout hleft hframe hblank
    dst dst hdst hdst (M.R dst) result v₂ depth
  have he₃' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₂ {M with R := Function.update M.R dst result})+depth+0) depth
      (clearWords headers) (mk v₂ {M with R := Function.update M.R dst result})
      (2*(headers.map (fun i => (M.R i).length)).sum+2*headers.length+1)
      (mk v' {S with R := Function.update S.R dst result}) := by
    simpa only [Function.update_idem,Nat.add_zero] using he₃
  refine ⟨v',n₁+n₂+(2*(headers.map (fun i => (M.R i).length)).sum+2*headers.length+1),result,
    hu₃.trans (hu₂.trans hu₁),by omega,hpost,?_⟩
  simpa only [withGeneratedHeaders,Nat.add_zero] using
    mn_seq_within_add (mn_seq_within_add he₁ he₂) he₃'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
