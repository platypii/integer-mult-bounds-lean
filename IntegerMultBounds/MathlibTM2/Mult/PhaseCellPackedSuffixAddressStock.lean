module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSuffixAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSizeSumStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Packed suffix addresses retain a shared controller reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def packedSuffixAddressWorkspace (n W N : ℕ) : ℕ :=
  2*packedSuffixControlsCost n N+
    (packedBandWordCount N W (N-(n+1)) (n+1)+(N-(n+1))+
      2*(100*((n+1)+(N-(n+1))+W+N+1)+2))

theorem packedSuffixAddress_exec_within (n W N : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hn : (S.R 107).length = n) (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,151,152,153], S.R k = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ packedSuffixAddressCost n W N ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+packedSuffixAddressWorkspace n W N)
        depth packedSuffixAddress (mk v S) steps
        (mk v' {S with R := (Function.update S.R 0
          (List.replicate (packedBandWordCount N W (N-(n+1)) (n+1)) tick++S.R 0))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := packedSuffixControls_exec (body := body) n N v S hn hN
    (hfresh 135 (by simp)) (hfresh 151 (by simp)) (hfresh 152 (by simp))
  let S₁ : Stacks 154 A := {S with R := (Function.update (Function.update S.R 151 (List.replicate (n+1) tick))
    152 (List.replicate (N-(n+1)) tick))}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedSizeSum_exec_within (body := body) N W (n+1) (N-(n+1)) v₁ S₁
    (by simpa [S₁] using hN) (by simpa [S₁] using hW) (by simp [S₁]) (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
    depth
  have hcontrols : mnNativePushBound 2 (packedSuffixControls (P := P) (Q := Q) (A := A) (U := U)) := by
    simp [packedSuffixControls,ucopy,umulSym,usub,scanR,drainR,popDo,keepIn,pushN,
      dropTop,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁ 2 hcontrols depth _ (Nat.le_refl _)
  have ht₂ := he₂.mono (J := fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+
    (packedBandWordCount N W (N-(n+1)) (n+1)+(N-(n+1))+
      2*(100*((n+1)+(N-(n+1))+W+N+1)+2))) (by intro d z hz; omega)
  have ht := (mn_seq_within_add ht₁ ht₂).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+packedSuffixAddressWorkspace n W N)
    (by intro d z hz; unfold packedSuffixAddressWorkspace; exact hz)
  refine ⟨v₂,packedSuffixControlsCost n N+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,
    ht.cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk151 : k = 151 <;> by_cases hk152 : k = 152 <;>
    simp [S₁,hk0,hk151,hk152,hfresh 151 (by simp),hfresh 152 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
