import IntegerMultBounds.Machine.BinaryCanonicalTrim
import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! Copy a raw division quotient onto a fresh marked descriptor, erase its raw
source, physically trim high zero bits, and return the descriptor head to one.
For a quotient ending at cell zero, the erased source head is also exactly zero. -/
namespace IntegerMultBounds.Machine.BinaryQuotientNormalize
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}
noncomputable section

def raw (xs : List Bool) (p : ℤ) : ℤ → Fin (a+4) := putWord (fun _ => blank) p (xs.map bitSymbol)

def initializeProgram : Program 2 2 a := DescriptorStackControl.once (by decide)
  (fun sy i => if i = 0 then (sy i,Move.stay) else (separator,Move.right))

private theorem initializeProgram_hoare (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime initializeProgram (fun v => v = Copy.tapes f (fun _ => blank) p 0)
      (fun v => v = Copy.tapes f BinaryDescriptorStack.empty p 1) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (Copy.tapes f (fun _ => blank) p 0)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes,Move.offset]
  · funext i z; fin_cases i <;> by_cases hz : z = p <;> by_cases hq : z = 0 <;>
      simp_all [Copy.tapes,Copy.cfg,Config.tapes,BinaryDescriptorStack.empty]

private theorem erased_blank (p : ℤ) (xs : List (Fin (a+4))) :
    putWord (fun _ => blank) p (xs.map (Copy.retained true)) = fun _ => blank := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp [putWord,ih,Copy.retained,Function.update_eq_self]

def destination : Fin (1+1) ≃ Fin 2 := FiniteReturnStackAt.placement (1 : Fin 2)

private theorem active_destination (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    Placement.active destination (Copy.tapes f g p q) = FiniteReturnStack.bank g q := by
  rw [destination,FiniteReturnStackAt.active_bank]
  rfl

private theorem replace_destination (f g h : ℤ → Fin (a+4)) (p q r : ℤ) :
    Placement.replace destination (Copy.tapes f g p q) (FiniteReturnStack.bank h r) = Copy.tapes f h p r := by
  rw [destination,FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes]

def program : Program 2 9 a :=
  seq (seq (seq initializeProgram (Copy.program blank true)) (Placement.placed StepLeft.program destination))
    (Placement.placed BinaryCanonicalTrim.program destination)

/-- No origin shift is assumed: the copy itself moves the erased source to
its old endpoint, which is zero for the literal long-division quotient. -/
theorem normalize_exists (xs : List Bool) (p : ℤ) :
    ∃ ys : List Bool, GrowingCounterData.Canonical ys ∧ Counter.value ys = Counter.value xs ∧
      ys.length ≤ xs.length ∧
      HoareTime (program (a := a)) (fun v => v = Copy.tapes (raw xs p) (fun _ => blank) p 0)
        (fun v => v = Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor ys) (p+xs.length) 1)
        (2*xs.length+8) := by
  obtain ⟨ys,hcanon,hval,hlen,htrim⟩ := BinaryCanonicalTrim.normalize_exists (a := a) xs
  refine ⟨ys,hcanon,hval,hlen,?_⟩
  have hc := Copy.copy_hoare (blank : Fin (a+4)) true (fun _ => blank) BinaryDescriptorStack.empty p 1
    (xs.map bitSymbol) (by
      intro z hz
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
      cases b <;> simp [bitSymbol,blank,Fin.ext_iff]) rfl
  rw [erased_blank] at hc
  simp only [List.length_map] at hc
  have hm := Placement.hoare_at (StepLeft.step_hoare (BinaryDescriptorStack.descriptor (a := a) xs) (1+xs.length))
    destination (Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor xs) (p+xs.length) (1+xs.length))
    (active_destination _ _ _ _)
  have hm' : HoareTime (Placement.placed (StepLeft.program (a := a)) destination)
      (fun v => v = Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor xs) (p+xs.length) (1+xs.length))
      (fun v => v = Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor xs) (p+xs.length) xs.length) 1 := by
    apply hm.consequence (fun _ h => h) _ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    change Placement.replace destination _ (FiniteReturnStack.bank (BinaryDescriptorStack.descriptor xs) (1+xs.length-1)) = _
    rw [replace_destination]
    congr 1
    omega
  have hn := Placement.hoare_at htrim destination
    (Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor xs) (p+xs.length) xs.length)
    (active_destination _ _ _ _)
  have hn' : HoareTime (Placement.placed (BinaryCanonicalTrim.program (a := a)) destination)
      (fun v => v = Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor xs) (p+xs.length) xs.length)
      (fun v => v = Copy.tapes (fun _ => blank) (BinaryDescriptorStack.descriptor ys) (p+xs.length) 1) (xs.length+3) := by
    apply hn.consequence (fun _ h => h) _ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    exact replace_destination _ _ _ _ _ _
  exact ((((initializeProgram_hoare (raw xs p) p).seq hc).seq hm').seq hn').consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryQuotientNormalize
