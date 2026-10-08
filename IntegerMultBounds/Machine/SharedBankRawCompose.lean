import IntegerMultBounds.Machine.CleanSubbankCompile

/-! Physical composition of two clean fixed machines on leading permanent tapes.
The shared contents may change arbitrarily between stages, including construction
of formerly blank descriptors. Both independent private banks are left blank. -/
namespace IntegerMultBounds.Machine.SharedBankRawCompose
open SharedBankStageInput (raw)
variable {k t u a : ℕ}
noncomputable section

theorem payload_raw (c : Tapes k a) (slots : Fin k → Fin t)
    (hv : ∀ i, (slots i).val = i.val) : SharedBank.payload (raw c t) slots = c := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [raw,hv,dite_eq_left i.isLt]

theorem strip_raw (c : Tapes k a) (slots : Fin k → Fin t)
    (hv : ∀ i, (slots i).val = i.val) : SharedBank.strip (raw c t) slots = SharedBank.empty t a := by
  have hn (i : Fin t) (hi : ¬∃ j, slots j = i) : ¬i.val < k := by
    intro h
    exact hi ⟨⟨i.val,h⟩,Fin.ext (hv _)⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ j, slots j = i
  all_goals simp only [hi,↓reduceIte,raw]
  all_goals simp only [hn i hi,↓reduceDIte]

theorem bank_eq_raw (c : Tapes k a) : CleanSubbank.bank (s := t) c = raw c (k+t) :=
  SharedBankStageInput.eq_raw _ _ _ (fun _ => rfl) (CleanSubbank.payload_bank c) (CleanSubbank.strip_bank c)

private theorem two_bank_eq_raw (c : Tapes k a) :
    (c.append (SharedBank.empty t a)).append (SharedBank.empty u a) = raw c ((k+t)+u) :=
  SharedBankStageInput.eq_raw _ _ (SharedBankFrames.commonSlots k t u) (fun _ => rfl)
    (SharedBankFrames.payload_common _ _ _) (SharedBankFrames.strip_common_blank _ _ _)

/-- Exact runtime includes the actual single transition between machines. -/
theorem realizes (s r : SharedBankSkeleton.Skeleton k a)
    (hs : ∀ i, (s.slots i).val = i.val) (hr : ∀ i, (r.slots i).val = i.val)
    (c d e : Tapes k a) (m n : ℕ)
    (hM : HoareTime s.program (fun w => w = raw c s.tapes) (fun w => w = raw d s.tapes) m)
    (hN : HoareTime r.program (fun w => w = raw d r.tapes) (fun w => w = raw e r.tapes) n) :
    HoareTime (SharedBankSkeleton.compose s r).program
      (fun w => w = raw c (SharedBankSkeleton.compose s r).tapes)
      (fun w => w = raw e (SharedBankSkeleton.compose s r).tapes) (m+n+1) := by
  have hh := SharedBankPair.pair_hoare hM hN s.slots s.slots_injective r.slots r.slots_injective
    ((payload_raw d s.slots hs).trans (payload_raw d r.slots hr).symm)
  simpa only [SharedBankSkeleton.compose,SharedBankPair.input,SharedBankPair.output,SharedBank.bank,
    payload_raw _ _ hs,payload_raw _ _ hr,strip_raw _ _ hs,strip_raw _ _ hr,two_bank_eq_raw] using hh

end
end IntegerMultBounds.Machine.SharedBankRawCompose
