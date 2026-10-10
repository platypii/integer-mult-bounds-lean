import IntegerMultBounds.Machine.CompactComplexScheduledPCLayout

/-! The original packed saved address is cast by its literal cardinality
identity, without changing its value or any saved bit. Unused padded slots
have no child continuation, while every real saved PC decodes exactly. -/
namespace IntegerMultBounds.Machine.CompactComplexScheduledPCDecode
noncomputable section
open Networks CompactComplexScheduledPCLayout CompactComplexCompletedLiveLower
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule

private theorem packed_count_eq (sites base : ℕ) :
    sites*base=CompactComplexCallReturn.addressCount sites base := rfl

theorem rawCount_eq : ComplexRecursiveCallSchema.sites.length*(25^3)=originalCount :=
  packed_count_eq ComplexRecursiveCallSchema.sites.length (25^3)

def callAddress (c : ComplexRecursiveCallSchema.Call) : Fin originalCount :=
  Fin.cast rawCount_eq (CompactComplexCallReturn.pc c)

theorem callAddress_val (c : ComplexRecursiveCallSchema.Call) :
    (callAddress c).val=(CompactComplexCallReturn.pc c).val :=
  Fin.val_cast rawCount_eq (CompactComplexCallReturn.pc c)

theorem callAddress_injective : Function.Injective callAddress := by
  intro a b he
  have hv := congrArg Fin.val he
  rw [callAddress_val,callAddress_val] at hv
  exact CompactComplexCallReturn.pc_injective (Fin.ext hv)

private theorem address_eq_of_val {N M k : ℕ} (hN : N≤2^k) (hM : M≤2^k)
    (a : Fin N) (b : Fin M) (he : a.val=b.val) :
    FiniteReturnStack.address hN a=FiniteReturnStack.address hM b :=
  congrArg (FiniteReturnStack.codeEquiv k).symm (Fin.ext he)

private theorem codeFor_cast {sites base : ℕ} (site : Fin sites) (coordinate : Fin base)
    (pc : Fin (sites*base)) (hp : pc.val=site.val*base+coordinate.val) :
    CompactComplexCallReturn.codeFor site coordinate=
      FiniteReturnStack.address (CompactComplexCallReturn.roomFor sites base)
        (Fin.cast (packed_count_eq sites base) pc) := by
  unfold CompactComplexCallReturn.codeFor
  apply address_eq_of_val
  rw [Fin.val_cast,hp]
  rfl

/-- Literal original pushed bits are unchanged by the explicit address cast. -/
theorem saved_code (c : ComplexRecursiveCallSchema.Call) :
    CompactComplexCallReturn.code c=
      FiniteReturnStack.address
        (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3))
        (callAddress c) :=
  codeFor_cast c.site c.slot (CompactComplexCallReturn.pc c) rfl

def savedPC (c : ComplexRecursiveCallSchema.Call) :=
  GuardedFiniteReturnExtraFlow.returnPC (extra:=4+schedule.length) (callAddress c)

theorem saved_ne_event (c : ComplexRecursiveCallSchema.Call) (i : Fin schedule.length) :
    savedPC c≠eventPC i :=
  GuardedFiniteReturnExtraFlow.return_extra_ne (callAddress c) (Fin.natAdd 4 i)

/-- The table keeps slots which do not correspond to an actual call harmless. -/
def decodeCall (address : Fin originalCount) : Option ComplexRecursiveCallSchema.Call := by
  classical
  exact if h : ∃ c,callAddress c=address then some (Classical.choose h) else none

theorem decodeCall_actual (c : ComplexRecursiveCallSchema.Call) :
    decodeCall (callAddress c)=some c := by
  classical
  unfold decodeCall
  rw [dite_eq_left ⟨c,rfl⟩]
  congr 1
  apply callAddress_injective
  exact Classical.choose_spec (show ∃ d,callAddress d=callAddress c from ⟨c,rfl⟩)

end
end IntegerMultBounds.Machine.CompactComplexScheduledPCDecode
