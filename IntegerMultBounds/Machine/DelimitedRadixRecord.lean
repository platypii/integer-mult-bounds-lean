import IntegerMultBounds.Machine.DelimitedRadixEmit

/-! Literal coefficient serialization for arithmetic stream kernels. A field is
one radix word followed by a separator; a complex coefficient consists of its
real and imaginary fields. Read correctness derives all delimiter conditions. -/
namespace IntegerMultBounds.Machine.DelimitedRadixRecord
open RadixDigits
variable {q : ℕ}

def field (xs : List (Fin q)) : List (Fin (q+4)) := xs.map digitSymbol++[separator]
def complex (re im : List (Fin q)) : List (Fin (q+4)) := field re++field im

theorem field_length (xs : List (Fin q)) : (field xs).length=xs.length+1 := by simp [field]

theorem complex_length (re im : List (Fin q)) (w : ℕ) (hr : re.length=w) (hi : im.length=w) :
    (complex re im).length=2*(w+1) := by simp [complex,field_length,hr,hi]; omega

/-- Every field interior is a data symbol, disjoint from every stream delimiter. -/
theorem digit_ne_separator (x : Fin q) : digitSymbol x≠separator := by
  simp [digitSymbol,separator,Fin.ext_iff]

/-- Extract a field from its literal position in a serialized stream. There is
no caller-supplied delimiter or coefficient codec correctness premise. -/
theorem read_field (f : ℤ → Fin (q+4)) (p : ℤ) (front back : List (Fin (q+4)))
    (xs : List (Fin q)) :
    HoareTime DelimitedRadixRead.program
      (fun v => v=Copy.tapes (putWord f p (front++field xs++back)) (fun _ => blank) (p+front.length) 0)
      (fun v => v=Copy.tapes (putWord f p (front++field xs++back))
        (MarkedWordCleanup.marked (xs.map digitSymbol)) (p+front.length+xs.length+1) 1)
      (2*xs.length+6) := by
  let base := putWord (putWord f p front) (p+front.length+xs.length) (separator::back)
  have he : base (p+front.length+xs.length)=separator := putWord_head _ _ _ _
  have hs : putWord base (p+front.length) (xs.map digitSymbol)=putWord f p (front++field xs++back) := by
    dsimp [base]
    rw [show (p+(front.length:ℤ)+xs.length)=p+front.length+(xs.map digitSymbol).length by simp]
    rw [←putWord_append,putWord_append_forward]
    simp [field,List.append_assoc]
  have hh := DelimitedRadixRead.runs base (p+front.length) xs he
  rw [hs] at hh
  exact hh

/-- Emission writes exactly the same field format and cleans the local result. -/
theorem emit_field (f : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin q)) :
    HoareTime DelimitedRadixEmit.program
      (fun v => v=Copy.tapes (MarkedWordCleanup.word (xs.map digitSymbol)) f 0 p)
      (fun v => v=Copy.tapes (fun _ => blank) (putWord f p (field xs)) 0 (p+xs.length+1))
      (2*xs.length+6) := DelimitedRadixEmit.runs f p xs

structure Context (q : ℕ) where
  background : ℤ → Fin (q+4)
  origin : ℤ
  front : List (Fin (q+4))
  back : List (Fin (q+4))
  re : List (Fin q)
  im : List (Fin q)

def Context.tape (c : Context q) := putWord c.background c.origin (c.front++complex c.re c.im++c.back)
def Context.start (c : Context q) : ℤ := c.origin+c.front.length

theorem read_real (c : Context q) :
    HoareTime DelimitedRadixRead.program
      (fun v => v=Copy.tapes c.tape (fun _ => blank) c.start 0)
      (fun v => v=Copy.tapes c.tape (MarkedWordCleanup.marked (c.re.map digitSymbol))
        (c.start+c.re.length+1) 1) (2*c.re.length+6) := by
  simpa only [Context.tape,Context.start,complex,List.append_assoc] using
    read_field c.background c.origin c.front (field c.im++c.back) c.re

theorem read_imaginary (c : Context q) :
    HoareTime DelimitedRadixRead.program
      (fun v => v=Copy.tapes c.tape (fun _ => blank) (c.start+c.re.length+1) 0)
      (fun v => v=Copy.tapes c.tape (MarkedWordCleanup.marked (c.im.map digitSymbol))
        (c.start+c.re.length+c.im.length+2) 1) (2*c.im.length+6) := by
  have hh := read_field c.background c.origin (c.front++field c.re) c.back c.im
  simp only [List.length_append,field_length,Nat.cast_add,Nat.cast_one] at hh
  convert hh using 1 <;> simp only [Context.tape,Context.start,complex,List.append_assoc]
  · funext v; congr 2; omega
  · funext v; congr 2; omega

end IntegerMultBounds.Machine.DelimitedRadixRecord
