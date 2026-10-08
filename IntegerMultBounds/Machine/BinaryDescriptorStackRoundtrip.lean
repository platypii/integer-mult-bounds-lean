import IntegerMultBounds.Machine.BinaryDescriptorStack
import IntegerMultBounds.Machine.Placement
import IntegerMultBounds.Machine.RadixZeroFill

/-! A concrete push/pop roundtrip on three tapes: preserved source descriptor,
stack, and initially blank restoration destination. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
open BinaryDescriptorStack
variable {a : ℕ}

/-- The descriptor representation is exactly the one used by the runtime
binary length-header machinery. -/
theorem descriptor_encoded (xs : List Bool) :
    descriptor (a := a) xs = RadixZeroFill.encodedBinary xs := by
  have hw (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
      putWord (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (f z)) p (bs.map bitSymbol) =
      (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (putBits f p bs z)) := by
    induction bs generalizing p with
    | nil => rfl
    | cons b bs ih =>
      funext z
      by_cases hz : z = p
      · subst z; cases b <;> simp [putWord,putBits,RadixToBinary.binaryEncoding,bitSymbol]
      · simpa [putWord,putBits,hz] using congrFun (ih (p+1)) z
  have he : (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.empty z)) = empty := by
    funext z
    by_cases hz : z = 0 <;> simp [CountedCopyReuse.empty,empty,hz,RadixToBinary.binaryEncoding,separator,blank]
  have h := hw CountedCopyReuse.empty 1 xs
  rw [he] at h
  exact h

def bank (src stack dst : ℤ → Fin (a+4)) (p q r : ℤ) : Tapes 3 a :=
  ⟨![p,q,r],![src,stack,dst]⟩

def pushSlots : Fin (2+1) ≃ Fin 3 := Equiv.refl _
def popSlots : Fin (2+1) ≃ Fin 3 where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def program : Program 3 16 a :=
  seq (Placement.placed push pushSlots) (Placement.placed pop popSlots)

private theorem active_push (f g h : ℤ → Fin (a+4)) (p q r : ℤ) :
    Placement.active pushSlots (bank f g h p q r) = Copy.tapes f g p q := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem active_pop (f g h : ℤ → Fin (a+4)) (p q r : ℤ) :
    Placement.active popSlots (bank f g h p q r) = Copy.tapes g h q r := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace_push (f g h f' g' : ℤ → Fin (a+4)) (p q r p' q' : ℤ) :
    Placement.replace pushSlots (bank f g h p q r) (Copy.tapes f' g' p' q') = bank f' g' h p' q' r := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace_pop (f g h g' h' : ℤ → Fin (a+4)) (p q r q' r' : ℤ) :
    Placement.replace popSlots (bank f g h p q r) (Copy.tapes g' h' q' r') = bank f g' h' p q' r' := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Both directions run on one fixed bank. All stack contents and its exact
head are restored, and the copied descriptor is returned at head one. -/
theorem roundtrip_hoare (xs : List Bool) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hf : ∀ z, p ≤ z → z < p+1+xs.length → f z = blank) :
    HoareTime program
      (fun v => v = bank (descriptor xs) f (fun _ => blank) 1 p 0)
      (fun v => v = bank (descriptor xs) f (descriptor xs) 1 p 1)
      (4*xs.length+15) := by
  have hp := Placement.hoare_at (push_hoare xs f p) pushSlots
    (bank (descriptor xs) f (fun _ => blank) 1 p 0) (active_push _ _ _ _ _ _)
  have hp' : HoareTime (Placement.placed push pushSlots)
      (fun v => v = bank (descriptor xs) f (fun _ => blank) 1 p 0)
      (fun v => v = bank (descriptor xs) (frame f p xs) (fun _ => blank) 1 (p+1+xs.length) 0)
      (2*xs.length+7) := by
    apply hp.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    exact replace_push _ _ _ _ _ _ _ _ _ _
  have hq := Placement.hoare_at (pop_hoare xs f p hf) popSlots
    (bank (descriptor xs) (frame f p xs) (fun _ => blank) 1 (p+1+xs.length) 0) (active_pop _ _ _ _ _ _)
  have hq' : HoareTime (Placement.placed pop popSlots)
      (fun v => v = bank (descriptor xs) (frame f p xs) (fun _ => blank) 1 (p+1+xs.length) 0)
      (fun v => v = bank (descriptor xs) f (descriptor xs) 1 p 1)
      (2*xs.length+7) := by
    apply hq.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    exact replace_pop _ _ _ _ _ _ _ _ _ _
  exact (hp'.seq hq').consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
