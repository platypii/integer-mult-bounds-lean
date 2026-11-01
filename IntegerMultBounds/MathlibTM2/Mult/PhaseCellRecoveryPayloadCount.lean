module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! Generate one class payload counter from ordinary dimensions, without a
supplier descriptor or numerical setup bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def recoveryPayloadCount (replicas halo wide symbols count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct halo wide symbols saved tmp)
    (.seq (unaryProduct replicas symbols count saved tmp) (uclear symbols))

def recoveryPayloadCountCost (N H W : ℕ) : ℕ :=
  (H*(4*W+9)+4)+(N*(4*(H*W)+9)+4)+(2*(H*W)+2)

theorem recoveryPayloadCountCost_linear (N H W : ℕ) (hW : 1 ≤ W) :
    recoveryPayloadCountCost N H W ≤ 20*((N+1)*(H*W+1)) := by
  have hH : H ≤ H*W := by simpa using Nat.mul_le_mul_left H hW
  unfold recoveryPayloadCountCost
  nlinarith

theorem recoveryPayloadCount_native (replicas halo wide symbols count saved tmp : Fin T) :
    mnNativePushBound 2 (recoveryPayloadCount (P := P) (Q := Q) (A := A) (U := U)
      replicas halo wide symbols count saved tmp) := by
  simp only [recoveryPayloadCount,mnNativePushBound]
  exact ⟨unaryProduct_native _ _ _ _ _,unaryProduct_native _ _ _ _ _,by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩

theorem recoveryPayloadCount_exec (replicas halo wide symbols count saved tmp : Fin T)
    (hreg : [replicas,halo,wide,symbols,count,saved,tmp].Nodup)
    (N H W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R replicas).length = N) (hH : (S.R halo).length = H) (hW : (S.R wide).length = W)
    (hblank : ∀ k ∈ [symbols,count,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryPayloadCountCost N H W ∧
      Exec body (recoveryPayloadCount replicas halo wide symbols count saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R count (List.replicate (N*(H*W)) tick)}) ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*recoveryPayloadCountCost N H W) depth
        (recoveryPayloadCount replicas halo wide symbols count saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R count (List.replicate (N*(H*W)) tick)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := halo) (b := wide) (dst := symbols) (t₁ := saved) (t₂ := tmp)
    (by simp_all) v S (hblank saved (by simp)) (hblank tmp (by simp))
  let F : Stacks T A := {S with R := Function.update S.R symbols (List.replicate (H*W) tick)}
  have he₁' : Exec body (unaryProduct halo wide symbols saved tmp) (Host.mk v S) n₁ (Host.mk v₁ F) := by
    simpa only [hH,hW,hblank symbols (by simp),List.append_nil,F] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := replicas) (b := symbols) (dst := count) (t₁ := saved) (t₂ := tmp)
    (by simp_all) v₁ F (by simp_all [F,ne_comm]) (by simp_all [F,ne_comm])
  let G : Stacks T A := {F with R := Function.update F.R count (List.replicate (N*(H*W)) tick)}
  have he₂' : Exec body (unaryProduct replicas symbols count saved tmp) (Host.mk v₁ F) n₂ (Host.mk v₂ G) := by
    simpa [F,G,hN,hblank count (by simp),‹replicas ≠ symbols›,‹symbols ≠ count›.symm] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) symbols v₂ G
  have hg : (G.R symbols).length = H*W := by simp_all [G,F,ne_comm]
  have hf : {G with R := Function.update G.R symbols []} =
      {S with R := Function.update S.R count (List.replicate (N*(H*W)) tick)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hs : k = symbols
    · subst k; simp_all [G,F,ne_comm]
    · by_cases hc : k = count
      · subst k; simp_all [G,F,ne_comm]
      · simp [G,F,hs,hc]
  rw [hg,hf] at he₃
  have hn : n₁+(n₂+(2*(H*W)+2)) ≤ recoveryPayloadCountCost N H W := by
    simp only [hH,hW] at hn₁
    simp only [F,Function.update_of_ne ‹replicas ≠ symbols›,Function.update_self,List.length_replicate,hN] at hn₂
    unfold recoveryPayloadCountCost
    omega
  have hex := Exec.seq he₁' (Exec.seq he₂' he₃)
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hn,hex,fun depth => ?_⟩
  exact mn_native_exec_within hex 2 (recoveryPayloadCount_native _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
