import IntegerMultBounds.Machine.ScanRight
import IntegerMultBounds.Machine.BinaryCanonicalTrim

/-! Normalize an arbitrary marked binary descriptor starting at its usual
head one. Scanning, high-zero erasure and return to head one are all paid. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorNormalize
variable {a : ℕ}
open BinaryDescriptorStack (descriptor)

def bank (xs : List Bool) := BinaryCanonicalTrim.one (a := a) xs 1

def program := seq (seq (ScanRight.program (blank : Fin (a+4))) StepLeft.program)
  BinaryCanonicalTrim.program

theorem normalizes (xs : List Bool) :
    ∃ ys : List Bool, GrowingCounterData.Canonical ys ∧ Counter.value ys = Counter.value xs ∧
      ys.length ≤ xs.length ∧ HoareTime (program (a := a))
        (fun v => v = bank xs) (fun v => v = bank ys) (2*xs.length+6) := by
  obtain ⟨ys,hc,hv,hl,hn⟩ := BinaryCanonicalTrim.normalize_exists (a := a) xs
  have hs := ScanRight.scan_hoare (blank : Fin (a+4)) (descriptor xs) 1 xs.length
    (by
      intro j hj
      have hm := ReturnOrigin.putWord_mem BinaryDescriptorStack.empty 1 (xs.map (bitSymbol (a := a)))
        (1+j) (by simp only [List.length_map]; omega)
      obtain ⟨b,_,hb⟩ := List.mem_map.mp hm
      change descriptor xs (1+j) ≠ blank
      rw [descriptor,← hb]
      cases b <;> simp [bitSymbol,blank,Fin.ext_iff])
    (by
      rw [descriptor,putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega))]
      simp [BinaryDescriptorStack.empty,show (1 : ℤ)+xs.length ≠ 0 by omega])
  have hlft := StepLeft.step_hoare (descriptor (a := a) xs) (1+xs.length)
  simp only [add_sub_cancel_left] at hlft
  have h := (hs.seq hlft).seq hn
  refine ⟨ys,hc,hv,hl,?_⟩
  apply h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.BinaryDescriptorNormalize
