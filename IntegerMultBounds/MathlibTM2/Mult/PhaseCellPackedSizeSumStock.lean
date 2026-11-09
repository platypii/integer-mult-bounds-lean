module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSizeSum
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSizeLoopStock

/-! Retire packed-address controls without multiplying the transient scan reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem packedSizeSum_exec_within (N W start L : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hN : (S.R 116).length = N) (hW : (S.R 94).length = W)
    (hcursor : (S.R 151).length = start) (hcount : (S.R 152).length = L)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,153], S.R k = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ packedSizeSumCost N W start L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (packedBandWordCount N W L start+L)+2*(100*(start+L+W+N+1)+2)) depth packedSizeSum (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 152 []) 0
          (List.replicate (packedBandWordCount N W L start) tick++S.R 0))
          151 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedSizeLoop_exec_within (body := body) N W start L v S hN hW hcursor hcount hfresh depth
  let output := List.replicate (packedBandWordCount N W L start) (tick : Fin (A+4))++S.R 0
  let S₁ : Stacks 154 A := {S with R := (Function.update (Function.update S.R 0 output)
    151 (List.replicate L tick++S.R 151))}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 151 v₁ S₁
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 151 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 152 v₂ S₂
  have hlen151 : (S₁.R 151).length = L+start := by simp [S₁,hcursor]
  have hlen152 : (S₂.R 152).length = L := by simpa [S₂,S₁] using hcount
  let D : Stacks 154 A := {S with R := Function.update S.R 0 output}
  have h₁ : mnSize (mk v D)+(S.R 0).length = mnSize (mk v S)+output.length := by
    simpa only [D,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt 0) output
  have h₂ : mnSize (mk v₁ S₁)+(D.R 151).length =
      mnSize (mk v D)+(List.replicate L tick++S.R 151).length := by
    simpa only [D,S₁,mk,update_rt,get_rt] using
      mn_size_update (mk v D) v₁ (.rt 151) (List.replicate L tick++S.R 151)
  have hsize : mnSize (mk v₁ S₁) = mnSize (mk v S)+packedBandWordCount N W L start+L := by
    have h151 : D.R 151 = S.R 151 := by simp [D]
    rw [h151,List.length_append,List.length_replicate] at h₂
    simp only [output,List.length_append,List.length_replicate] at h₁
    omega
  let bound := mnSize (mk v S)+depth+(packedBandWordCount N W L start+L)+2*(100*(start+L+W+N+1)+2)
  have ht₁ := he₁.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+2*(100*(start+L+W+N+1)+2) at hz
    dsimp only [bound]
    omega)
  have ht₂ := mn_native_exec_within he₂ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth bound
    (by simpa only [Nat.zero_mul,Nat.add_zero] using ht₁.final)
  have ht₃ := mn_native_exec_within he₃ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth bound
    (by simpa only [Nat.zero_mul,Nat.add_zero] using ht₂.final)
  refine ⟨v₃,m₁+((2*(L+start)+2)+(2*L+2)),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_right hm₁ _,
    (ExecWithin.seq ht₁ (ExecWithin.seq ht₂ ht₃)).cast (by rw [hlen151,hlen152]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk151 : k = 151 <;> by_cases hk152 : k = 152 <;>
    simp [S₂,S₁,output,hk0,hk151,hk152]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
