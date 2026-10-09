import IntegerMultBounds.Machine.NativeZeroStream
import IntegerMultBounds.Machine.ScanRight
import IntegerMultBounds.Machine.ReturnOrigin

/-! Native row padding physically seeks the original EOF, appends valid signed
zero records and pays the return to origin. Existing coefficients are retained. -/
namespace IntegerMultBounds.Machine.NativeZeroPadding
noncomputable section
open CountedLoopReuseAlphabet (one)

def tail (width count : List Bool) : Tapes 6 2 :=
  (((one (RadixZeroFill.encodedBinary width) 1).append (SharedBank.empty 2 2)).append
    (one (RadixZeroFill.encodedBinary count) 1)).append (SharedBank.empty 2 2)

theorem bank_eq (f : ℤ → Fin 6) (p : ℤ) (width count : List Bool) :
    NativeZeroStream.bank f p width count=(one f p).append (tail width count) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program := seq (seq (extend (ScanRight.program (blank : Fin 6)) 6) NativeZeroStream.program)
  (extend (ReturnOrigin.program (a:=2)) 6)
def word (xs : List (Fin 6)) := putWord (fun _ => blank) 0 xs

theorem scan_runs (xs : List (Fin 6)) (hn : ∀ x∈xs,x≠blank) (width count : List Bool) :
    HoareTime (extend (ScanRight.program (blank : Fin 6)) 6)
      (fun v => v=NativeZeroStream.bank (word xs) 0 width count)
      (fun v => v=NativeZeroStream.bank (word xs) xs.length width count) xs.length := by
  have hh := hoare_extend_eq (ScanRight.scan_hoare (blank : Fin 6) (word xs) 0 xs.length
    (by
      intro j hj
      simpa only [zero_add,word] using hn _ (ReturnOrigin.putWord_mem (fun _ => blank) 0 xs j (by omega)))
    (by exact putWord_outside _ _ _ _ (Or.inr (by omega)))) (tail width count)
  change HoareTime (extend (ScanRight.program (blank : Fin 6)) 6)
    (fun v => v=(one (word xs) 0).append (tail width count))
    (fun v => v=(one (word xs) (0+xs.length)).append (tail width count)) xs.length at hh
  simpa only [zero_add,←bank_eq] using hh

def cost (xs : List (Fin 6)) (width count : List Bool) (w n : ℕ) :=
  xs.length+n*(14*w+22*width.length+81)+11*count.length+35+
    (xs++NativeZeroStream.records w n).length+4

theorem runs (xs : List (Fin 6)) (hnon : ∀ x∈xs,x≠blank) (width count : List Bool) (w n : ℕ)
    (hw : Counter.value width=w) (hn : Counter.value count=n) :
    HoareTime program (fun v => v=NativeZeroStream.bank (word xs) 0 width count)
      (fun v => v=NativeZeroStream.bank (word (xs++NativeZeroStream.records w n)) 0 width count)
      (cost xs width count w n) := by
  have h0 := scan_runs xs hnon width count
  have h1 := NativeZeroStream.append_runs (fun _ => blank) 0 xs width count w n hw hn
  simp only [zero_add] at h1
  have hn' : ∀ x∈xs++NativeZeroStream.records w n,x≠blank := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hnon x hx
    · exact NativeZeroStream.nonblank w n x hx
  have h2 := hoare_extend_eq (ReturnOrigin.return_hoare (xs++NativeZeroStream.records w n) hn') (tail width count)
  change HoareTime (extend (ReturnOrigin.program (a:=2)) 6)
    (fun v => v=(one (word (xs++NativeZeroStream.records w n)) (xs++NativeZeroStream.records w n).length).append (tail width count))
    (fun v => v=(one (word (xs++NativeZeroStream.records w n)) 0).append (tail width count))
    ((xs++NativeZeroStream.records w n).length+2) at h2
  simp only [←bank_eq] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- Added row coefficients decode as zero, with exact nonblank symbol format;
the word is suitable for the existing sentinel-rewound native stage codec. -/
theorem valid_result (xs : List (Fin 6)) (hnon : ∀ x∈xs,x≠blank) (w n : ℕ) :
    (∀ x∈xs++NativeZeroStream.records w n,x≠blank) ∧
      (NativeZeroRecord.coefficient w).1.length=w ∧
      (NativeZeroRecord.coefficient w).2.length=w ∧
      ButterflySigned.signedValue (w-1) (NativeZeroRecord.coefficient w).1=0 ∧
      ButterflySigned.signedValue (w-1) (NativeZeroRecord.coefficient w).2=0 := by
  refine ⟨?_,by simp [NativeZeroRecord.coefficient,NativeZeroRecord.digits],by simp [NativeZeroRecord.coefficient,NativeZeroRecord.digits],?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hnon x hx
    · exact NativeZeroStream.nonblank w n x hx
  all_goals exact NativeZeroRecord.signed _ _

end
end IntegerMultBounds.Machine.NativeZeroPadding
