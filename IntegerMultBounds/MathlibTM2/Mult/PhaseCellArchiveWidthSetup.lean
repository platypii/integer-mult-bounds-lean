module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOpsStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Generate the archive row width from ordinary replica/core/word dimensions.
Keep both products across publication and raw retirement, then release them. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def archiveWidthSetup (replicas core word packet width saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct core word packet saved tmp) (unaryProduct replicas packet width saved tmp)

def archiveWidthSetupCost (R L W : ℕ) := L*(4*W+9)+4+R*(4*(L*W)+9)+4

def archiveWidthState (packet width : Fin T) (R L W : ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R packet (List.replicate (L*W) tick)) width
    (List.replicate (R*(L*W)) tick))}

theorem archiveWidthSetup_exec_within (body : P → Pr P T Q A U)
    (replicas core word packet width saved tmp : Fin T)
    (hreg : [replicas,core,word,packet,width,saved,tmp].Nodup) (R L W depth : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = R) (hcore : (S.R core).length = L)
    (hword : (S.R word).length = W)
    (hblank : ∀ i ∈ [packet,width,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ archiveWidthSetupCost R L W ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        2*archiveWidthSetupCost R L W) depth (archiveWidthSetup replicas core word packet width saved tmp)
        (mk v S) n (mk v' (archiveWidthState packet width R L W S)) := by
  regs_ne hreg
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [core,word,packet,saved,tmp].Nodup by regs_nodup) v S
    (hblank _ (by simp)) (hblank _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R packet (List.replicate (L*W) tick)}
  have he₁' : Exec body (unaryProduct core word packet saved tmp) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hcore,hword,hblank packet (by simp),List.append_nil,M] using he₁
  obtain ⟨v',n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (show [replicas,packet,width,saved,tmp].Nodup by regs_nodup) v₁ M
    (by simp [M,‹packet ≠ saved›.symm,hblank saved (by simp)])
    (by simp [M,‹packet ≠ tmp›.symm,hblank tmp (by simp)])
  have hr : (M.R replicas).length = R := by simp [M,‹replicas ≠ packet›,hreplicas]
  have hp : (M.R packet).length = L*W := by simp [M]
  have hw : M.R width = [] := by simp [M,‹packet ≠ width›.symm,hblank width (by simp)]
  have he₂' : Exec body (unaryProduct replicas packet width saved tmp) (mk v₁ M) n₂
      (mk v' (archiveWidthState packet width R L W S)) := by
    simp only [hr,hp,hw,List.append_nil] at he₂
    simpa only [M,archiveWidthState] using he₂
  have htime : n₁+n₂ ≤ archiveWidthSetupCost R L W := by
    simpa only [archiveWidthSetupCost,hcore,hword,hr,hp,Nat.add_assoc] using Nat.add_le_add hn₁ hn₂
  have he := Exec.seq he₁' he₂'
  refine ⟨v',n₁+n₂,hu₂.trans hu₁,htime,?_⟩
  apply mn_native_exec_within he 2 _ depth _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 htime) _)
  exact ⟨unaryProduct_native ..,unaryProduct_native ..⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
