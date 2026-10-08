import IntegerMultBounds.Machine.StackPop
import IntegerMultBounds.Machine.Reflection

/-! Destructive forward parking with a reusable length clock. Reflection changes
the physical transition table of StackPop, reversing both payload head motions
but leaving the binary controls unchanged. It is not a free tape reversal. -/
namespace IntegerMultBounds.Machine.StackPush
variable {a : ℕ}

def mask (i : Fin 4) : Bool := decide (i.val < 2)
def program : Program 4 (7+(2+5)+4) a := Reflection.program StackPop.program mask

def controls (v : Tapes 2 a) (bs : List Bool) : Tapes 4 a :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1

theorem mirror_controls (v : Tapes 2 a) (bs : List Bool) :
    Reflection.tapes mask (controls v bs) =
      controls (Reflection.tapes (fun _ => true) v) bs := by
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [Reflection.tapes,Reflection.coord,mask,controls,
      CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases]
  · funext i j
    fin_cases i <;> simp [Reflection.tapes,Reflection.coord,mask,controls,
      CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases]

def result (v : Tapes 2 a) (n : ℕ) : Tapes 2 a :=
  Reflection.tapes (fun _ => true)
    (StackPop.transfer (Reflection.tapes (fun _ => true) v) n)

/-- Append a known number of symbols, erase the source, and restore the clock.
The complete source/destination banks remain explicit even outside the regions. -/
theorem push_hoare (v : Tapes 2 a) (bs : List Bool) (n : ℕ)
    (hc : Counter.value bs = n) :
    HoareTime program (fun w => w = controls v bs)
      (fun w => w = controls (result v n) bs) (7*n+7*bs.length+16) := by
  have hh := Reflection.hoare (StackPop.pop_hoare
    (Reflection.tapes (fun _ => true) v) bs n hc) mask
  apply hh.consequence ?_ ?_ le_rfl
  · intro w hw
    subst w
    refine ⟨_,rfl,?_⟩
    rw [show CountedLoopReuseAlphabet.bank _ _ _ 1 1 =
      controls (Reflection.tapes (fun _ => true) v) bs from rfl,
      mirror_controls,Reflection.tapes_tapes]
  · rintro w ⟨original,rfl,rfl⟩
    exact mirror_controls _ bs

/-- Physical payload heads advance exactly by the parked length. -/
theorem heads (v : Tapes 2 a) (n : ℕ) (i : Fin 2) :
    (result v n).head i = v.head i+n := by
  simp only [result,Reflection.tapes,Reflection.coord,↓reduceIte,StackPop.heads]
  omega

/-- Only the transferred source interval is erased. -/
theorem source (v : Tapes 2 a) (n : ℕ) (j : ℤ) :
    (result v n).tape 0 j =
      if v.head 0 ≤ j ∧ j < v.head 0+n then blank else v.tape 0 j := by
  simp only [result,Reflection.tapes,Reflection.coord,↓reduceIte,StackPop.source,neg_neg]
  have he : -v.head 0-(n : ℤ) < -j ∧ -j ≤ -v.head 0 ↔
      v.head 0 ≤ j ∧ j < v.head 0+n := by omega
  simp only [he]

/-- The stack receives data in its original order without touching an ancestor
outside the appended interval, including when data contains blanks/separators. -/
theorem destination (v : Tapes 2 a) (n : ℕ) (j : ℤ) :
    (result v n).tape 1 j =
      if v.head 1 ≤ j ∧ j < v.head 1+n then
        v.tape 0 (v.head 0+(j-v.head 1)) else v.tape 1 j := by
  simp only [result,Reflection.tapes,Reflection.coord,↓reduceIte,StackPop.destination,neg_neg]
  have he : -v.head 1-(n : ℤ) < -j ∧ -j ≤ -v.head 1 ↔
      v.head 1 ≤ j ∧ j < v.head 1+n := by omega
  have hp : -(-v.head 0+(-j- -v.head 1)) = v.head 0+(j-v.head 1) := by omega
  simp only [he,hp]

end IntegerMultBounds.Machine.StackPush
