import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersData

/-! Exact state-indexed wrappers around actual constant, power and product
machines in the common 28+15 descriptor bank. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersAtomic
noncomputable section
open ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def seedProgram (dst : Fin 28) := extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement dst)) 15

theorem seed (st : State) (dst : Fin 28) (hd : st dst=none) :
    HoareTime (seedProgram (a := a) dst) (fun v => v=bank st) (fun v => v=bank (put st dst 1)) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement dst) (caller (a := a) st)
    (by rw [FiniteReturnStackAt.active_bank]; simp [caller,hd])
  have h' : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
      (FiniteReturnStackAt.placement dst)) (fun v => v=caller st)
      (fun v => v=caller (put st dst 1)) 9 := by
    apply h.consequence (fun _ h => h) _ (by decide)
    rintro z ⟨small,rfl,rfl⟩
    rw [put_caller,FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact hoare_extend_eq h' (SharedBank.empty 15 a)

def powerProgram (src dst : Fin 28) (hn : src≠dst) :=
  CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) (two src dst) (two_injective src dst hn)

theorem power (st : State) (src dst : Fin 28) (hn : src≠dst) (n : ℕ)
    (hs : st src=some n) (hd : st dst=none) :
    HoareTime (powerProgram (a := a) src dst hn) (fun v => v=bank st)
      (fun v => v=bank (put st dst (2^n))) (FixedBasePowerDescriptor.constant 2*2^n) := by
  have h := CompactGadgetReservationHeadersPowerRound.power (caller (a := a) st) (two src dst)
    (two_injective src dst hn) (bits n) n (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [caller,two,hs]) (by simp [caller,two,hs])
    (by simp [caller,two,hd]) (by simp [caller,two,hd])
  simpa [powerProgram,two,ActiveRepairRankHeadersCommands.bank,CompactGadgetReservationHeadersCore.bank,put_caller] using h

def productProgram (src left dst : Fin 28) (hf : Function.Injective (![src,left,dst] : Fin 3 → Fin 28)) :=
  CompactGadgetReservationHeadersCore.productProgram (a := a) ![src,left,dst] hf

theorem product (st : State) (src left dst : Fin 28)
    (hf : Function.Injective (![src,left,dst] : Fin 3 → Fin 28)) (m n : ℕ) (hm : 0<m)
    (hs : st src=some m) (hl : st left=some n) (hd : st dst=none) :
    HoareTime (productProgram (a := a) src left dst hf) (fun v => v=bank st)
      (fun v => v=bank (put st dst (m*n))) (53*(m*n)+28) := by
  have h := CompactGadgetReservationHeadersCore.product (caller (a := a) st) ![src,left,dst] hf
    (bits m) (bits n) n m hm
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [caller,hs]) (by simp [caller,hs])
    (by simp [caller,hl]) (by simp [caller,hl])
    (by simp [caller,hd]) (by simp [caller,hd])
  simpa [Nat.mul_comm,productProgram,ActiveRepairRankHeadersCommands.bank,CompactGadgetReservationHeadersCore.bank,put_caller] using h

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersAtomic
