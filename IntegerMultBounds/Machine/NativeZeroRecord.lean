import IntegerMultBounds.Machine.CountedLoopHeaderClean
import IntegerMultBounds.Machine.ButterflyStreamData

/-! Physical signed zero coefficients use radix-zero digits and actual field
separators. Uniform false Boolean padding is not this representation. -/
namespace IntegerMultBounds.Machine.NativeZeroRecord
noncomputable section
open CountedLoopReuseAlphabet (one)

def digits (w : ℕ) : List (Fin 2) := List.replicate w 0
def coefficient (w : ℕ) : ButterflyStreamData.Coefficient := (digits w,digits w)
def word (w : ℕ) : List (Fin 6) := ButterflyStreamData.encoded (coefficient w)
def field (w : ℕ) : List (Fin 6) := DelimitedRadixRecord.field (digits w)

theorem word_eq (w : ℕ) : word w=field w++field w := rfl
@[simp] theorem length (w : ℕ) : (word w).length=2*(w+1) := by
  simp [word,coefficient,ButterflyStreamData.encoded,DelimitedRadixRecord.complex,
    DelimitedRadixRecord.field_length,digits]
  omega

theorem nonblank (w : ℕ) (x : Fin 6) (hx : x∈word w) : x≠blank := by
  simp [word,ButterflyStreamData.encoded,coefficient,DelimitedRadixRecord.complex,
    DelimitedRadixRecord.field,digits,List.map_replicate] at hx
  rcases hx with ⟨_,rfl⟩|rfl|⟨_,rfl⟩|rfl <;> decide

@[simp] theorem value (w : ℕ) : RadixDigits.value (digits w)=0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa [digits,List.replicate_succ,RadixDigits.value] using ih

@[simp] theorem signed (b w : ℕ) : ButterflySigned.signedValue b (digits w)=0 := by
  simp [ButterflySigned.signedValue,pow_pos (by decide : 0<2) b]

def cell (symbol : Fin 6) : Program 1 2 2 where
  tapes_pos := by decide
  start := 0
  transition := fun st _ => if st=0 then some (1,fun _ => (symbol,.right)) else none

theorem cell_runs (symbol : Fin 6) (f : ℤ → Fin 6) (p : ℤ) :
    HoareTime (cell symbol) (fun v => v=one f p)
      (fun v => v=one (Function.update f p symbol) (p+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => p+1,fun _ => Function.update f p symbol⟩,le_rfl,?_,?_,rfl⟩
  · simp [run_one,step,cell,Tapes.start,one,Move.offset]
    funext i z
    by_cases h : z=p <;> simp [h]
  · simp [step,cell]

def core (f : ℤ → Fin 6) (p : ℤ) (bs : List Bool) : Tapes 2 2 :=
  (one f p).append (one (RadixZeroFill.encodedBinary bs) 1)
def bank (f : ℤ → Fin 6) (p : ℤ) (bs : List Bool) := CountedLoopHeaderClean.bank (core f p bs)
def fillProgram := CountedLoopHeaderClean.program (extend (cell (RadixDigits.digitSymbol (0 : Fin 2))) 1) 1
def fieldProgram := seq fillProgram (extend (cell separator) 3)
def program := seq fieldProgram fieldProgram

theorem append_digit (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :
    Function.update (putWord f p ((digits n).map RadixDigits.digitSymbol)) (p+n)
      (RadixDigits.digitSymbol (0 : Fin 2))=
      putWord f p ((digits (n+1)).map RadixDigits.digitSymbol) := by
  simp only [digits,List.replicate_add,List.map_append,List.replicate_one,List.map_singleton]
  simpa only [digits,List.length_map,List.length_replicate,putWord] using
    putWord_append_forward f p ((digits n).map RadixDigits.digitSymbol) [RadixDigits.digitSymbol (0 : Fin 2)]

theorem fill_runs (f : ℤ → Fin 6) (p : ℤ) (bs : List Bool) (w : ℕ) (hw : Counter.value bs=w) :
    HoareTime fillProgram (fun v => v=bank f p bs)
      (fun v => v=bank (putWord f p ((digits w).map RadixDigits.digitSymbol)) (p+w) bs)
      (7*w+11*bs.length+35) := by
  let v := fun n => core (putWord f p ((digits n).map RadixDigits.digitSymbol)) (p+n) bs
  have hh := CountedLoopHeaderClean.runs (extend (cell (RadixDigits.digitSymbol (0 : Fin 2))) 1) 1 bs w v
    (fun _ => 1) (by constructor <;> rfl) hw (by
      intro i _
      have hi := hoare_extend_eq (cell_runs (RadixDigits.digitSymbol (0 : Fin 2))
        (putWord f p ((digits i).map RadixDigits.digitSymbol)) (p+i))
        (one (RadixZeroFill.encodedBinary bs) 1)
      rw [append_digit] at hi
      simpa only [v,core,Nat.cast_add,Nat.cast_one,add_assoc] using hi)
  apply hh.consequence _ _ (by simp [CountedLoopHeaderClean.cost]; omega)
  · intro z hz; simpa only [v,core,bank,digits,List.replicate_zero,List.map_nil,putWord,Nat.cast_zero,add_zero] using hz
  · intro z hz; exact hz

theorem bank_assoc (f : ℤ → Fin 6) (p : ℤ) (bs : List Bool) :
    bank f p bs=(one f p).append ((one (RadixZeroFill.encodedBinary bs) 1).append (SharedBank.empty 2 2)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem field_runs (f : ℤ → Fin 6) (p : ℤ) (bs : List Bool) (w : ℕ) (hw : Counter.value bs=w) :
    HoareTime fieldProgram (fun v => v=bank f p bs)
      (fun v => v=bank (putWord f p (field w)) (p+w+1) bs) (7*w+11*bs.length+37) := by
  have h0 := fill_runs f p bs w hw
  have h1 := hoare_extend_eq (cell_runs separator (putWord f p ((digits w).map RadixDigits.digitSymbol)) (p+w))
    ((one (RadixZeroFill.encodedBinary bs) 1).append (SharedBank.empty 2 2))
  have he : Function.update (putWord f p ((digits w).map RadixDigits.digitSymbol)) (p+w) separator=putWord f p (field w) := by
    simpa only [field,DelimitedRadixRecord.field,List.length_map,digits,List.length_replicate,putWord] using
      putWord_append_forward f p ((digits w).map RadixDigits.digitSymbol) [separator]
  rw [he] at h1
  simp only [←bank_assoc] at h1
  have hh := h0.seq h1
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs (f : ℤ → Fin 6) (p : ℤ) (bs : List Bool) (w : ℕ) (hw : Counter.value bs=w) :
    HoareTime program (fun v => v=bank f p bs)
      (fun v => v=bank (putWord f p (word w)) (p+2*(w+1)) bs) (14*w+22*bs.length+75) := by
  have h0 := field_runs f p bs w hw
  have h1 := field_runs (putWord f p (field w)) (p+w+1) bs w hw
  have he : putWord (putWord f p (field w)) (p+w+1) (field w)=putWord f p (word w) := by
    rw [word_eq]
    have hl : (field w).length=w+1 := by simp [field,DelimitedRadixRecord.field_length,digits]
    simpa only [hl,Nat.cast_add,Nat.cast_one,add_assoc] using putWord_append_forward f p (field w) (field w)
  rw [he] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => by
    have hp : p+w+1+w+1=p+2*(w+1) := by ring
    simpa only [hp] using h) (by omega)

end
end IntegerMultBounds.Machine.NativeZeroRecord
