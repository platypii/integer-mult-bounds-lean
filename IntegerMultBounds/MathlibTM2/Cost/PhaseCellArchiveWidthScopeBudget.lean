module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationHandoffBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveWidthScope

/-! An ordinary-input width scope preserves a restoring axis's postcondition and
final stock equality, with one ambient-linear charge for the entire lifecycle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type}

theorem withArchiveWidth_exec_within_traffic (body : P → Pr P T Q A U)
    (replicas core word packet width saved tmp dst : Fin T)
    (hreg : [replicas,core,word,packet,width,saved,tmp].Nodup)
    (hdst : dst ∉ [packet,width]) (R s L W depth time space : ℕ)
    (hL : 1 ≤ L) (hfit : L ≤ s) (hR : 1 ≤ R) (hW : 1 ≤ W)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = R) (hcore : (S.R core).length = L)
    (hword : (S.R word).length = W)
    (hblank : ∀ i ∈ [packet,width,saved,tmp], S.R i = [])
    (consumer : Pr P T Q A U) (post : List (Fin (A+4)) → Prop)
    (hlength : ∀ result, post result → result.length = (S.R dst).length)
    (hconsumer : ∀ v₁ : HS T Q A U,
      ∃ v₂ n result, v₂.user = v₁.user ∧ n ≤ time ∧ post result ∧
        ExecWithin body (fun z state => mnSize state+z ≤
          mnSize (mk v₁ (archiveWidthState packet width R L W S))+depth+space) depth consumer
          (mk v₁ (archiveWidthState packet width R L W S)) n
          (mk v₂ {archiveWidthState packet width R L W S with R :=
            (Function.update (archiveWidthState packet width R L W S).R dst result)})) :
    ∃ v' n result, v'.user = v.user ∧ n ≤ 80*(R*(s*W))+time ∧ post result ∧
      mnSize (mk v' {S with R := Function.update S.R dst result}) = mnSize (mk v S) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (80*(R*(s*W))+space)) depth
        (withArchiveWidth replicas core word packet width saved tmp consumer) (mk v S) n
        (mk v' {S with R := Function.update S.R dst result}) := by
  obtain ⟨v',n,result,hu,hn,hpost,he⟩ := withArchiveWidth_exec_within body
    replicas core word packet width saved tmp dst hreg hdst R L W depth time space v S
    hreplicas hcore hword hblank consumer post hconsumer
  obtain ⟨ht,hs⟩ := archiveWidthSetupCosts_le_traffic R s L W hL hfit hR hW
  refine ⟨v',n,result,hu,by omega,hpost,mnSize_replace_right_eq v v' S dst result (hlength result hpost),?_⟩
  exact he.mono (by intro z state hz; omega)

end IntegerMultBounds.MathlibTM2.Cost
