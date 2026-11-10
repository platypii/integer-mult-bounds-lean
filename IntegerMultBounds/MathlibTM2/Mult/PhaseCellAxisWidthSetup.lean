module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveWidthSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHeaderScope

/-! Generate the fitting payload count and output row width from shared ordinary
dimensions. The intermediate halo packet reuses the output packet destination. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def axisWidthSetup (replicas core span word packet width count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (.seq (archiveWidthSetup replicas span word packet count saved tmp) (clearWords [packet]))
    (archiveWidthSetup replicas core word packet width saved tmp)

def axisWidthState (packet width count : Fin T) (R L H W : ℕ) (S : Stacks T A) : Stacks T A :=
  archiveWidthState packet width R L W {S with R := Function.update S.R count (List.replicate (R*(H*W)) tick)}

def axisWidthSetupCost (R L H W : ℕ) :=
  archiveWidthSetupCost R H W+(2*(H*W)+3)+archiveWidthSetupCost R L W

theorem axisWidthSetup_exec_within (body : P → Pr P T Q A U)
    (replicas core span word packet width count saved tmp : Fin T)
    (hreg : [replicas,core,span,word,packet,width,count,saved,tmp].Nodup)
    (R L H W depth : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = R) (hcore : (S.R core).length = L)
    (hspan : (S.R span).length = H) (hword : (S.R word).length = W)
    (hblank : ∀ i ∈ [packet,width,count,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ axisWidthSetupCost R L H W ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*(archiveWidthSetupCost R H W+archiveWidthSetupCost R L W)) depth
        (axisWidthSetup replicas core span word packet width count saved tmp) (mk v S) n
        (mk v' (axisWidthState packet width count R L H W S)) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := archiveWidthSetup_exec_within body
    replicas span word packet count saved tmp (by regs_nodup) R H W depth v S
    hreplicas hspan hword (by intro i hi; exact hblank i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let M := archiveWidthState packet count R H W S
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [packet] (by simp) v₁ M
  have he₂' : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v₁ M)+depth+0) depth
      (clearWords [packet]) (mk v₁ M) (2*(H*W)+3)
      (mk v₂ {S with R := Function.update S.R count (List.replicate (R*(H*W)) tick)}) := by
    have hend : ({M with R := fun i => if i ∈ [packet] then [] else M.R i} : Stacks T A) =
        {S with R := Function.update S.R count (List.replicate (R*(H*W)) tick)} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = packet
      · subst i; simp [M,archiveWidthState,‹packet ≠ count›,hblank packet (by simp)]
      · simp only [M,archiveWidthState,List.mem_singleton,hi,ite_false,Function.update_apply]
    rw [hend] at he₂
    have hcost : 2*([packet].map (fun i => (M.R i).length)).sum+2*[packet].length+1 = 2*(H*W)+3 := by
      simp [M,archiveWidthState,‹packet ≠ count›]
    rw [hcost] at he₂
    exact mn_native_exec_within he₂ 0 (clearWords_native _) depth _ (by simp)
  let B : Stacks T A := {S with R := Function.update S.R count (List.replicate (R*(H*W)) tick)}
  have hread (i : Fin T) (hi : i ≠ count) : B.R i = S.R i := Function.update_of_ne hi _ _
  obtain ⟨v',n₃,hu₃,hn₃,he₃⟩ := archiveWidthSetup_exec_within body
    replicas core word packet width saved tmp (by regs_nodup) R L W depth v₂ B
    (by rw [hread _ ‹replicas ≠ count›]; exact hreplicas)
    (by rw [hread _ ‹core ≠ count›]; exact hcore)
    (by rw [hread _ ‹word ≠ count›]; exact hword)
    (by intro i hi
        have hiCount : i ≠ count := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl <;> first | assumption | exact Ne.symm (by assumption)
        rw [hread i hiCount]
        exact hblank i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  refine ⟨v',n₁+(2*(H*W)+3)+n₃,hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · exact Nat.add_le_add (Nat.add_le_add_right hn₁ _) hn₃
  · have hex := mn_seq_within_add (mn_seq_within_add he₁ he₂') he₃
    simpa only [axisWidthSetup,axisWidthState,M,B,Nat.add_zero,Nat.mul_add] using hex

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
