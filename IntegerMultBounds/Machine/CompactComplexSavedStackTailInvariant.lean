import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! A next-free stack head has a genuinely blank tail. Initialization derives
this from a support bound; arbitrary physical binary pushes preserve it.
The older tail required by pop comes from the pre-push invariant, rather than
from an equality describing only the occupied word. -/
namespace IntegerMultBounds.Machine.CompactComplexSavedStackTailInvariant
noncomputable section
open FiniteReturnStack (Code wordPart)
variable {a t k : ℕ}

def BlankTail (f : ℤ → Fin (a+4)) (head : ℤ) : Prop :=
  ∀ z,head≤z → f z=blank

def Invariant (slot : Fin t) (v : Tapes t a) : Prop :=
  BlankTail (v.tape slot) (v.head slot)

/-- A support bound at or below the actual head initializes the invariant. -/
theorem of_support_bound (f : ℤ → Fin (a+4)) (bound head : ℤ)
    (hsupport : ∀ z,f z≠blank → z<bound) (hle : bound≤head) :
    BlankTail f head := by
  intro z hz
  by_contra h
  have := hsupport z h
  omega

theorem invariant_of_support_bound (slot : Fin t) (v : Tapes t a) (bound : ℤ)
    (hsupport : ∀ z,v.tape slot z≠blank → z<bound) (hle : bound≤v.head slot) :
    Invariant slot v := of_support_bound _ bound _ hsupport hle

theorem empty (head : ℤ) : BlankTail (fun _ => (blank : Fin (a+4))) head :=
  fun _ _ => rfl

/-- Written prefix cells may be nonblank; every cell beyond them stays blank. -/
theorem wordPart_tail (f : ℤ → Fin (a+4)) (head : ℤ) (code : Code k)
    (n : ℕ) (hn : n≤k) (h : BlankTail f head) :
    BlankTail (wordPart f head code n hn) (head+n) := by
  intro z hz
  have houtside : ¬(head≤z ∧ z<head+n) := by omega
  rw [wordPart,dite_eq_right houtside]
  exact h z (by omega)

theorem pushed (slot : Fin t) (code : Code k) (v : Tapes t a)
    (h : Invariant slot v) : Invariant slot (FiniteReturnStackAt.pushed slot code v) := by
  unfold Invariant FiniteReturnStackAt.pushed
  simp only [SharedPlacementAlphabet.setTape,Function.update_self]
  exact wordPart_tail _ _ code k le_rfl h

/-- Any routine retaining the literal stack bank retains its blank-tail proof. -/
theorem retained (slot : Fin t) (before after : Tapes t a)
    (hbank : FiniteReturnStack.bank (after.tape slot) (after.head slot)=
      FiniteReturnStack.bank (before.tape slot) (before.head slot))
    (h : Invariant slot before) : Invariant slot after := by
  have ht := congrArg (fun z : Tapes 1 a => z.tape 0) hbank
  have hh := congrArg (fun z : Tapes 1 a => z.head 0) hbank
  change BlankTail (after.tape slot) (after.head slot)
  change after.tape slot=before.tape slot at ht
  change after.head slot=before.head slot at hh
  rw [ht,hh]
  exact h

/-- Actual placed push carries both the new free-tail invariant and the old
blank tail needed later to erase this exact frame during pop. -/
theorem push_hoare (slot : Fin t) (code : Code k) (v : Tapes t a)
    (h : Invariant slot v) :
    HoareTime (FiniteReturnStackAt.pushProgram slot code) (fun w => w=v)
      (fun w => w=FiniteReturnStackAt.pushed slot code v ∧
        Invariant slot w ∧ BlankTail (v.tape slot) (v.head slot)) k := by
  apply (FiniteReturnStackAt.push_hoare slot code v).consequence
    (fun _ hw => hw) _ le_rfl
  intro w hw
  exact ⟨hw,hw.symm ▸ pushed slot code v h,h⟩

/-- A stack built from a blank initial tape by actual fixed-width frames. -/
inductive History (width : ℕ) (origin : ℤ) : (ℤ → Fin (a+4)) → ℤ → Prop
  | empty : History width origin (fun _ => blank) origin
  | push {f head} (older : History width origin f head) (code : Code width) :
      History width origin (wordPart f head code width le_rfl) (head+width)

theorem history_tail {width : ℕ} {origin head : ℤ} {f : ℤ → Fin (a+4)}
    (h : History width origin f head) : BlankTail f head := by
  induction h with
  | empty => exact empty _
  | push older code ih => exact wordPart_tail _ _ code _ le_rfl ih

/-- A genuine nonempty history supplies an older-stack witness with its blank
tail. This witness is retained separately from the occupied-word equality. -/
theorem history_cases {width : ℕ} {origin head : ℤ} {f : ℤ → Fin (a+4)}
    (h : History width origin f head) :
    (f=(fun _ => blank) ∧ head=origin) ∨
      ∃ older top code,History width origin older top ∧ BlankTail older top ∧
        f=wordPart older top code width le_rfl ∧ head=top+width := by
  cases h with
  | empty => exact Or.inl ⟨rfl,rfl⟩
  | push older code => exact Or.inr ⟨_,_,code,older,history_tail older,rfl,rfl⟩

/-- Direct physical pop at the named stack port. The decoded code stays in the
underlying finite halt state; this contract only records restored tapes. -/
def popProgram (slot : Fin t) (width : ℕ) :
    Program t (Fintype.card (FiniteReturnStack.Control width)) a :=
  Placement.placed (FiniteReturnStack.pop a width) (FiniteReturnStackAt.placement slot)

/-- A genuine older history supplies every erased-cell blank. Physical pop
restores that history, preserves its free tail and retains all other tapes. -/
theorem pop_hoare (slot : Fin t) (code : Code k) (v : Tapes t a)
    (older : ℤ → Fin (a+4)) (origin top : ℤ)
    (hHistory : History k origin older top)
    (ht : v.tape slot=wordPart older top code k le_rfl)
    (hh : v.head slot=top+k) :
    HoareTime (popProgram slot k) (fun w => w=v)
      (fun w => w=SharedPlacementAlphabet.setTape v slot older top ∧
        History k origin (w.tape slot) (w.head slot) ∧ Invariant slot w) (k+1) := by
  have hf : ∀ j<k,older (top+j)=blank := by
    intro j _
    exact history_tail hHistory _ (by omega)
  have h := Placement.hoare_at (FiniteReturnStack.pop_hoare code older top hf)
    (FiniteReturnStackAt.placement slot) v
    (by rw [FiniteReturnStackAt.active_bank,ht,hh])
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  refine ⟨rfl,?_⟩
  simp only [Invariant,SharedPlacementAlphabet.setTape,Function.update_self]
  exact ⟨hHistory,history_tail hHistory⟩

end
end IntegerMultBounds.Machine.CompactComplexSavedStackTailInvariant
