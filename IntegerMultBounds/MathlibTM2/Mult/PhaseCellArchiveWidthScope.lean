module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveWidthSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement
public import IntegerMultBounds.MathlibTM2.Host.ReplaceRightStock

/-! Scope generated width masters around a restoring consumer. The consumer may
include publication and raw retirement; its complete trace shares the masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def withArchiveWidth (replicas core word packet width saved tmp : Fin T) (consumer : Pr P T Q A U) :
    Pr P T Q A U :=
  .seq (.seq (archiveWidthSetup replicas core word packet width saved tmp) consumer) (clearWords [packet,width])

theorem withArchiveWidth_exec_within (body : P → Pr P T Q A U)
    (replicas core word packet width saved tmp dst : Fin T)
    (hreg : [replicas,core,word,packet,width,saved,tmp].Nodup)
    (hdst : dst ∉ [packet,width]) (R L W depth time space : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = R) (hcore : (S.R core).length = L)
    (hword : (S.R word).length = W)
    (hblank : ∀ i ∈ [packet,width,saved,tmp], S.R i = [])
    (consumer : Pr P T Q A U) (post : List (Fin (A+4)) → Prop)
    (hconsumer : ∀ v₁ : HS T Q A U,
      ∃ v₂ n result, v₂.user = v₁.user ∧ n ≤ time ∧ post result ∧
        ExecWithin body (fun z state => mnSize state+z ≤
          mnSize (mk v₁ (archiveWidthState packet width R L W S))+depth+space) depth consumer
          (mk v₁ (archiveWidthState packet width R L W S)) n
          (mk v₂ {archiveWidthState packet width R L W S with R :=
            (Function.update (archiveWidthState packet width R L W S).R dst result)})) :
    ∃ v' n result, v'.user = v.user ∧
      n ≤ archiveWidthSetupCost R L W+time+2*(L*W+R*(L*W))+5 ∧ post result ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (2*archiveWidthSetupCost R L W+space)) depth
        (withArchiveWidth replicas core word packet width saved tmp consumer) (mk v S) n
        (mk v' {S with R := Function.update S.R dst result}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := archiveWidthSetup_exec_within body
    replicas core word packet width saved tmp hreg R L W depth v S hreplicas hcore hword hblank
  obtain ⟨v₂,n₂,result,hu₂,hn₂,hpost,he₂⟩ := hconsumer v₁
  let M := archiveWidthState packet width R L W S
  have hnd : packet ≠ width := by
    have hr := hreg
    regs_ne hr
    assumption
  have hframe (i : Fin T) (hi : i ∉ [packet,width]) : M.R i = S.R i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp only [M,archiveWidthState,Function.update_of_ne hi.2,Function.update_of_ne hi.1]
  obtain ⟨v',hu₃,he₃⟩ := retireHeaderFrame_pair_exec body [packet,width] (by simp [hnd]) S M
    rfl rfl rfl hframe
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl <;> exact hblank _ (by simp))
    dst dst hdst hdst (M.R dst) result v₂ depth
  have hcost : 2*([packet,width].map (fun i => (M.R i).length)).sum+2*[packet,width].length+1 =
      2*(L*W+R*(L*W))+5 := by simp [M,archiveWidthState,hnd]
  have he₃' : ExecWithin body (fun z state => mnSize state+z ≤
      mnSize (mk v₂ {M with R := Function.update M.R dst result})+depth+0) depth
      (clearWords [packet,width]) (mk v₂ {M with R := Function.update M.R dst result})
      (2*(L*W+R*(L*W))+5) (mk v' {S with R := Function.update S.R dst result}) := by
    simpa only [hcost,Function.update_idem,Nat.add_zero] using he₃
  refine ⟨v',n₁+n₂+(2*(L*W+R*(L*W))+5),result,hu₃.trans (hu₂.trans hu₁),?_,hpost,?_⟩
  · omega
  · simpa only [withArchiveWidth,M,Nat.add_zero] using
      mn_seq_within_add (mn_seq_within_add he₁ he₂) he₃'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
