module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratePackedAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSuffixAddressStock

/-! Complete packed word addresses share the suffix summation reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def generatePackedAddressWorkspace (n m W N : ℕ) : ℕ :=
  packedSuffixAddressWorkspace n W N+2*packedWithinAddressCost n m W N

theorem generatePackedAddress_exec_within (n m W N : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hn : (S.R 107).length = n) (hm : (S.R 108).length = m)
    (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,151,152,153], S.R k = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ generatePackedAddressCost n m W N ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+generatePackedAddressWorkspace n m W N)
        depth generatePackedAddress (mk v S) steps
        (mk v' {S with R := Function.update S.R 0 (List.replicate (packedEntryOffset N W n m) tick++S.R 0)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedSuffixAddress_exec_within (body := body) n W N v S hn hW hN hfresh depth
  let laterWords := packedBandWordCount N W (N-(n+1)) (n+1)
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate laterWords tick++S.R 0)}
  obtain ⟨v₂,hu₂,he₂⟩ := packedWithinAddress_exec (body := body) n m W N v₁ S₁
    (by simpa [S₁] using hn) (by simpa [S₁] using hm)
    (by simpa [S₁] using hW) (by simpa [S₁] using hN) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  have hwithin : mnNativePushBound 2 (packedWithinAddress (P := P) (Q := Q) (A := A) (U := U)) := by
    simp [packedWithinAddress,bandIntervalEndpoints,clipUnary,clearWords,ucopy,umulSym,usub,
      dropTop,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,uclear,
      mnNativePushBound,mnActPush]
  have ht₂ := mn_native_exec_within he₂ 2 hwithin depth _ (Nat.le_refl _)
  have ht := (mn_seq_within_add he₁ ht₂).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+generatePackedAddressWorkspace n m W N)
    (by intro d z hz; unfold generatePackedAddressWorkspace; exact hz)
  refine ⟨v₂,m₁+packedWithinAddressCost n m W N,hu₂.trans hu₁,Nat.add_le_add_right hm₁ _,
    ht.cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0
  · subst k
    simp only [Function.update_self,S₁]
    rw [← List.append_assoc,List.replicate_append_replicate]
    simp [packedEntryOffset,laterWords,Nat.add_comm]
  · simp [S₁,hk0]

/-- Retained packed words plus linear controllers; no quadratic row-count reserve. -/
theorem generatePackedAddressWorkspace_le (n m W N : ℕ) :
    generatePackedAddressWorkspace n m W N ≤
      N*(2*W+1)+1000*(n+m+W+N+1) := by
  have hcount := (packedBandWordCount_le N W (N-(n+1)) (n+1)).trans
    (Nat.mul_le_mul_right (2*W+1) (Nat.sub_le N (n+1)))
  unfold generatePackedAddressWorkspace packedSuffixAddressWorkspace packedSuffixControlsCost
    packedWithinAddressCost bandIntervalEndpointsCost clipUnaryCost
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
