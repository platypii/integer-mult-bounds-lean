module

public import IntegerMultBounds.Machine.SharedBankRawCompose
public import IntegerMultBounds.Machine.SharedBankPairWithin

/-! Clean leading-bank blocks compose with one shared prefix head interval. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedBankRawCompose
open SharedBankStageInput (raw)
variable {k t u a : ℕ}
noncomputable section

theorem realizes_within (s r : SharedBankSkeleton.Skeleton k a) (lo hi : ℤ)
    (hs : ∀ i, (s.slots i).val = i.val) (hr : ∀ i, (r.slots i).val = i.val)
    (c d e : Tapes k a) (m n : ℕ)
    (hM : HoareWithin s.program (fun w => w = raw c s.tapes) (fun w => w = raw d s.tapes) m (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (hN : HoareWithin r.program (fun w => w = raw d r.tapes) (fun w => w = raw e r.tapes) n (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    HoareWithin (SharedBankSkeleton.compose s r).program
      (fun w => w = raw c (SharedBankSkeleton.compose s r).tapes)
      (fun w => w = raw e (SharedBankSkeleton.compose s r).tapes) (m+n+1) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hh := SharedBankPair.pair_within hM hN s.slots s.slots_injective r.slots r.slots_injective
    ((payload_raw d s.slots hs).trans (payload_raw d r.slots hr).symm) hlo hhi
  simpa only [SharedBankSkeleton.compose,SharedBankPair.input,SharedBankPair.output,SharedBank.bank,
    payload_raw _ _ hs,payload_raw _ _ hr,strip_raw _ _ hs,strip_raw _ _ hr,two_bank_eq_raw] using hh

end
end IntegerMultBounds.Machine.SharedBankRawCompose
