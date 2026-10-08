import IntegerMultBounds.Machine.RecursiveVolumeClean
import IntegerMultBounds.Machine.RecursiveAffinePrepare
import IntegerMultBounds.Machine.CleanSubbank
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physically synthesize a call's volume count from its six headers, leaving
the reusable counted-loop clock blank at origin. The count can be erased before
recursive entry and regenerated from restored headers for recovery. -/
namespace IntegerMultBounds.Machine.RecursiveCallCount
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveInterchangeLayout (Descriptor volume)
variable {q t : ℕ}

def ports : Fin 8 → Fin 34 := ![0,16,3,4,5,6,7,8]

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

def idle (hs : Fin 6 → List Bool) (bs : List Bool) :=
  setTape (RecursiveVolumeClean.bank (q := q) hs (some bs)) 0 (fun _ => blank) 0

def localProgram (hq : 2 ≤ q) :=
  seq (RecursiveVolumeClean.program hq) (BinaryDescriptorCleanupList.oneProgram 0)

private theorem local_realizes (hq : 2 ≤ q) (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (localProgram hq) (fun w => w = RecursiveVolumeClean.bank hs none)
      (fun w => w = idle hs (RecursiveVolumeConstruct.bits (q := q) v)) (51787*volume q v) := by
  have hg := RecursiveVolumeClean.realizes hq v hs hv hp
  have hc := BinaryDescriptorCleanupList.one_hoare (0 : Fin 34)
    (RecursiveVolumeClean.bank (q := q) hs (some (RecursiveVolumeConstruct.bits (q := q) v))) [] (by rfl) (by rfl)
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  have hb := RecursiveVolumeClean.bound_linear (volume q v) hV
  exact (hg.seq hc).consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_nil] at *; omega)

private theorem local_clean (hs : Fin 6 → List Bool) (bs : Option (List Bool)) :
    SharedBank.strip (RecursiveVolumeClean.bank (q := q) hs bs) ports = SharedBank.empty 34 q := by
  have hb (i : Fin 34) (hi : ¬∃ j, ports j = i) :
      (RecursiveVolumeClean.bank (q := q) hs bs).head i = 0 ∧
      (RecursiveVolumeClean.bank (q := q) hs bs).tape i = fun _ => blank := by
    have hs' : ∀ j : Fin 17, RecursiveVolumeClean.keep j = true → ∃ z, ports z = Fin.castAdd 17 j := by
      intro j hj
      fin_cases j <;> simp_all [RecursiveVolumeClean.keep,RecursiveVolumeClean.right]
      all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ |
        exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩
    change Fin (17+17) at i
    induction i using Fin.addCases with
    | left i => exact RecursiveVolumeClean.private_blank hs bs i (Bool.eq_false_iff.mpr (fun h => hi (hs' i h)))
    | right i => exact RecursiveVolumeClean.trackers_blank hs bs i
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hb i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hb i hi).2

private theorem strip_setTape {s c a : ℕ} (v : Tapes s a) (ps : Fin c → Fin s) (j : Fin c)
    (f : ℤ → Fin (a+4)) (p : ℤ) : SharedBank.strip (setTape v (ps j) f p) ps = SharedBank.strip v ps := by
  have hn (i : Fin s) (hi : ¬∃ k, ps k = i) : i ≠ ps j := fun h => hi ⟨j,h.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ k, ps k = i
  all_goals simp only [hi,↓reduceIte]
  all_goals simp only [setTape,Function.update_of_ne (hn i hi)]

/-- Selected ports are clock, count, then the six original headers. -/
def Ready (slot : Fin 8 → Fin t) (hs : Fin 6 → List Bool) (v : Tapes t q) : Prop :=
  v.head (slot 0) = 0 ∧ v.tape (slot 0) = (fun _ => blank) ∧
  v.head (slot 1) = 0 ∧ v.tape (slot 1) = (fun _ => blank) ∧
  ∀ j : Fin 6, v.head (slot (Fin.natAdd 2 j)) = 1 ∧
    v.tape (slot (Fin.natAdd 2 j)) = RadixZeroFill.encodedBinary (hs j)

def counted (slot : Fin 8 → Fin t) (v : Tapes t q) (bs : List Bool) :=
  setTape v (slot 1) (RadixZeroFill.encodedBinary bs) 1

def program (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot) :=
  Placement.placed (localProgram hq) (CleanSubbank.placement ports slot hi)

/-- Count generation preserves every non-count tape exactly, including the
blank clock, all payload/descriptor/PC stacks, role arrays and older frames. -/
theorem realizes (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (v : Tapes t q) (d : Descriptor) (hs : Fin 6 → List Bool)
    (hr : Ready slot hs v) (hv : RecursiveDimensionBank.Headers d hs) (hp : d.Positive) :
    HoareTime (program hq slot hi) (fun w => w = CleanSubbank.bank v)
      (fun w => w = CleanSubbank.bank (counted slot v (RecursiveVolumeConstruct.bits (q := q) d)))
      (51787*volume q d) := by
  obtain ⟨hc,tc,hn,tn,hh⟩ := hr
  apply CleanSubbank.realizes _ ports slot ports_injective hi _ _
    (RecursiveVolumeClean.bank hs none) (idle hs (RecursiveVolumeConstruct.bits (q := q) d)) _
  · apply congrArg₂ Tapes.mk
    · funext i
      fin_cases i <;> first | exact hc.symm | exact hn.symm |
        exact (hh 0).1.symm | exact (hh 1).1.symm | exact (hh 2).1.symm |
        exact (hh 3).1.symm | exact (hh 4).1.symm | exact (hh 5).1.symm
    · funext i
      fin_cases i <;> first | exact tc.symm | exact tn.symm |
        exact (hh 0).2.symm | exact (hh 1).2.symm | exact (hh 2).2.symm |
        exact (hh 3).2.symm | exact (hh 4).2.symm | exact (hh 5).2.symm
  · apply congrArg₂ Tapes.mk
    · funext i
      fin_cases i <;> simp only [counted,setTape,hi.eq_iff,Function.update_apply]
      all_goals first | exact hc.symm | rfl | exact (hh 0).1.symm | exact (hh 1).1.symm |
        exact (hh 2).1.symm | exact (hh 3).1.symm | exact (hh 4).1.symm | exact (hh 5).1.symm
    · funext i
      fin_cases i <;> simp only [counted,setTape,hi.eq_iff,Function.update_apply]
      all_goals first | exact tc.symm | rfl | exact (hh 0).2.symm | exact (hh 1).2.symm |
        exact (hh 2).2.symm | exact (hh 3).2.symm | exact (hh 4).2.symm | exact (hh 5).2.symm
  · exact local_clean hs none
  · exact (strip_setTape _ ports 0 _ _).trans (local_clean hs _)
  · exact (strip_setTape v slot 1 _ _).symm
  · exact local_realizes hq d hs hv hp

theorem clears (slot : Fin 8 → Fin t) (v : Tapes t q) (bs : List Bool)
    (hh : v.head (slot 1) = 0) (ht : v.tape (slot 1) = fun _ => blank) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (slot 1))
      (fun w => w = counted slot v bs) (fun w => w = v) (2*bs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (slot 1) (counted slot v bs) bs
    (by simp [counted,setTape,BinaryDescriptorStackRoundtrip.descriptor_encoded]) (by simp [counted,setTape])
  apply h.consequence (fun _ h => h) _ le_rfl
  intro w hw
  rw [hw,counted,SharedPlacementAlphabet.setTape_setTape]
  rw [← ht,← hh]
  exact SharedPlacementAlphabet.setTape_self _ _

end
end IntegerMultBounds.Machine.RecursiveCallCount
