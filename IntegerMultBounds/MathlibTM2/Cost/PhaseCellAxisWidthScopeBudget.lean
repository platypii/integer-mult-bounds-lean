module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationHandoffBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAxisWidthSetup
public import IntegerMultBounds.MathlibTM2.Host.ReplaceRightStock

/-! One shared lifecycle generates both fitting payload count and archive width.
No generated count is an ordinary input assumption.
Superseded archive-only scopes can be restored from commit d0ad7c6e. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

def withAxisWidths (replicas core span word packet width count saved tmp : Fin T)
    (consumer : Pr P T Q A U) : Pr P T Q A U :=
  withGeneratedHeaders [packet,width,count]
    (axisWidthSetup replicas core span word packet width count saved tmp) consumer

theorem withAxisWidths_exec_within_traffic (body : P → Pr P T Q A U)
    (replicas core span word packet width count saved tmp dst : Fin T)
    (hreg : [replicas,core,span,word,packet,width,count,saved,tmp].Nodup)
    (hdst : dst ∉ [packet,width,count]) (R s L H W depth time space : ℕ)
    (hL : 1 ≤ L) (hLfit : L ≤ s) (hH : 1 ≤ H) (hHfit : H ≤ s) (hR : 1 ≤ R) (hW : 1 ≤ W)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = R) (hcore : (S.R core).length = L)
    (hspan : (S.R span).length = H) (hword : (S.R word).length = W)
    (hblank : ∀ i ∈ [packet,width,count,saved,tmp], S.R i = [])
    (consumer : Pr P T Q A U) (post : List (Fin (A+4)) → Prop)
    (hlength : ∀ result, post result → result.length = (S.R dst).length)
    (hconsumer : ∀ v₁ : HS T Q A U,
      ∃ v₂ n result, v₂.user = v₁.user ∧ n ≤ time ∧ post result ∧
        ExecWithin body (fun z state => mnSize state+z ≤
          mnSize (mk v₁ (axisWidthState packet width count R L H W S))+depth+space) depth consumer
          (mk v₁ (axisWidthState packet width count R L H W S)) n
          (mk v₂ {axisWidthState packet width count R L H W S with R :=
            (Function.update (axisWidthState packet width count R L H W S).R dst result)})) :
    ∃ v' n result, v'.user = v.user ∧ n ≤ 160*(R*(s*W))+time ∧ post result ∧
      mnSize (mk v' {S with R := Function.update S.R dst result}) = mnSize (mk v S) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (160*(R*(s*W))+space)) depth
        (withAxisWidths replicas core span word packet width count saved tmp consumer) (mk v S) n
        (mk v' {S with R := Function.update S.R dst result}) := by
  let M := axisWidthState packet width count R L H W S
  have hr := hreg
  regs_ne hr
  have hframe (i : Fin T) (hi : i ∉ [packet,width,count]) : M.R i = S.R i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp only [M,axisWidthState,archiveWidthState,Function.update_of_ne hi.1,
      Function.update_of_ne hi.2.1,Function.update_of_ne hi.2.2]
  obtain ⟨v',n,result,hu,hn,hpost,hex⟩ := withGeneratedHeaders_exec_within body
    [packet,width,count] (by regs_nodup) dst hdst S M rfl rfl rfl hframe
    (by intro i hi; exact hblank i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
    (axisWidthSetup replicas core span word packet width count saved tmp) consumer
    (axisWidthSetupCost R L H W) (2*(archiveWidthSetupCost R H W+archiveWidthSetupCost R L W))
    time space depth v post
    (axisWidthSetup_exec_within body replicas core span word packet width count saved tmp
      hreg R L H W depth v S hreplicas hcore hspan hword hblank) hconsumer
  have hsize : ([packet,width,count].map (fun i => (M.R i).length)).sum =
      L*W+R*(L*W)+R*(H*W) := by
    simp [M,axisWidthState,archiveWidthState,‹packet ≠ width›,‹packet ≠ count›,‹width ≠ count›,‹packet ≠ count›.symm,‹width ≠ count›.symm,Nat.add_assoc]
  rw [hsize] at hn
  have hcL := archiveWidthSetupCosts_le_traffic R s L W hL hLfit hR hW
  have hcH := archiveWidthSetupCosts_le_traffic R s H W hH hHfit hR hW
  have htime : axisWidthSetupCost R L H W+2*(L*W+R*(L*W)+R*(H*W))+7 ≤ 160*(R*(s*W)) := by
    unfold axisWidthSetupCost
    omega
  have hspace : 2*(archiveWidthSetupCost R H W+archiveWidthSetupCost R L W) ≤ 160*(R*(s*W)) := by omega
  refine ⟨v',n,result,hu,?_,hpost,mnSize_replace_right_eq v v' S dst result (hlength result hpost),?_⟩
  · simp only [List.length_cons,List.length_nil] at hn
    omega
  · exact hex.mono (by intro z state hz; omega)

end IntegerMultBounds.MathlibTM2.Cost
