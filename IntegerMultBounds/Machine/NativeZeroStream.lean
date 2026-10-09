import IntegerMultBounds.Machine.NativeZeroRecord

/-! Repeated valid native zero coefficients are emitted by a physical outer
countdown. Both inner and outer generated controls start and finish blank. -/
namespace IntegerMultBounds.Machine.NativeZeroStream
noncomputable section
open CountedLoopReuseAlphabet (one)

def records (w n : ℕ) : List (Fin 6) := (List.replicate n (NativeZeroRecord.word w)).flatten
@[simp] theorem length (w n : ℕ) : (records w n).length=n*(2*(w+1)) := by
  simp [records,List.length_flatten]
@[simp] theorem zero (w : ℕ) : records w 0=[] := rfl

theorem succ (w n : ℕ) : records w (n+1)=records w n++NativeZeroRecord.word w := by
  simp [records,List.replicate_add,List.flatten_append]

theorem nonblank (w n : ℕ) (x : Fin 6) (hx : x∈records w n) : x≠blank := by
  simp only [records,List.mem_flatten] at hx
  obtain ⟨xs,hxs,hx⟩ := hx
  have he : xs=NativeZeroRecord.word w := (List.mem_replicate.mp hxs).2
  subst xs
  exact NativeZeroRecord.nonblank w x hx

def bodyBank (f : ℤ → Fin 6) (p : ℤ) (width count : List Bool) :=
  (NativeZeroRecord.bank f p width).append (one (RadixZeroFill.encodedBinary count) 1)
def bank (f : ℤ → Fin 6) (p : ℤ) (width count : List Bool) :=
  CountedLoopHeaderClean.bank (bodyBank f p width count)
def program := CountedLoopHeaderClean.program (extend NativeZeroRecord.program 1) 4

def state (f : ℤ → Fin 6) (p : ℤ) (w : ℕ) (width count : List Bool) (i : ℕ) :=
  bodyBank (putWord f p (records w i)) (p+i*(2*(w+1))) width count

theorem body_runs (f : ℤ → Fin 6) (p : ℤ) (w : ℕ) (width count : List Bool)
    (hw : Counter.value width=w) (i : ℕ) :
    HoareTime (extend NativeZeroRecord.program 1)
      (fun v => v=state f p w width count i) (fun v => v=state f p w width count (i+1))
      (14*w+22*width.length+75) := by
  have hh := hoare_extend_eq (NativeZeroRecord.runs (putWord f p (records w i))
    (p+i*(2*(w+1))) width w hw) (one (RadixZeroFill.encodedBinary count) 1)
  have he : putWord (putWord f p (records w i)) (p+i*(2*(w+1))) (NativeZeroRecord.word w)=
      putWord f p (records w (i+1)) := by
    rw [succ]
    have hh := putWord_append_forward f p (records w i) (NativeZeroRecord.word w)
    rw [NativeZeroStream.length] at hh
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh
  rw [he] at hh
  have hp : p+(i : ℤ)*(2*(w+1))+2*(w+1)=p+(i+1)*(2*(w+1)) := by ring
  simpa only [state,bodyBank,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,hp] using hh

theorem runs (f : ℤ → Fin 6) (p : ℤ) (width count : List Bool) (w n : ℕ)
    (hw : Counter.value width=w) (hn : Counter.value count=n) :
    HoareTime program (fun v => v=bank f p width count)
      (fun v => v=bank (putWord f p (records w n)) (p+n*(2*(w+1))) width count)
      (n*(14*w+22*width.length+81)+11*count.length+35) := by
  have hh := CountedLoopHeaderClean.runs (extend NativeZeroRecord.program 1) 4 count n
    (state f p w width count) (fun _ => 14*w+22*width.length+75)
    (by constructor <;> rfl) hn (fun i _ => body_runs f p w width count hw i)
  apply hh.consequence _ _ (by simp [CountedLoopHeaderClean.cost]; ring_nf; omega)
  · intro z hz; simpa only [state,bodyBank,bank,zero,putWord,Nat.cast_zero,zero_mul,add_zero] using hz
  · intro z hz; exact hz

/-- Appending these records leaves every existing native symbol untouched.
The end pointer is the exact occupied symbol count, rather than a free reset. -/
theorem append_runs (f : ℤ → Fin 6) (p : ℤ) (xs : List (Fin 6)) (width count : List Bool) (w n : ℕ)
    (hw : Counter.value width=w) (hn : Counter.value count=n) :
    HoareTime program (fun v => v=bank (putWord f p xs) (p+xs.length) width count)
      (fun v => v=bank (putWord f p (xs++records w n)) (p+(xs++records w n).length) width count)
      (n*(14*w+22*width.length+81)+11*count.length+35) := by
  have hh := runs (putWord f p xs) (p+xs.length) width count w n hw hn
  rw [putWord_append_forward] at hh
  simpa only [List.length_append,NativeZeroStream.length,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,add_assoc] using hh

end
end IntegerMultBounds.Machine.NativeZeroStream
