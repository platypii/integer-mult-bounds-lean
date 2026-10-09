import IntegerMultBounds.Machine.BinaryAddressTableStep
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.SelectedSourceBitsRewind

/-! A live fixed-width binary address counter supplies a complete raw address
word each iteration. Copying, both head returns and increment are physical;
old raw address words are overwritten at equal width. -/
namespace IntegerMultBounds.Machine.BinaryCurrentAddress
noncomputable section
open MarkedWordCleanup (one marked)
open CountedLoopReuseAlphabet (encoding binary)
open BinaryAddressTableData (row)
variable {a : ℕ}

theorem binary_word (xs : List Bool) : (binary xs : ℤ → Fin (a+4))=marked (xs.map bitSymbol) := by
  have h : ∀ (f : ℤ → Fin (a+4)) (p : ℤ),CountedLoopAlphabet.putBits f p xs=putWord f p (xs.map bitSymbol) := by
    induction xs with
    | nil => intros; rfl
    | cons x xs ih => intros; simp only [CountedLoopAlphabet.putBits,putWord,List.map_cons,ih]
  exact h _ _

def increment := Alphabet.program (encoding a) CounterTape.program

theorem increments (xs : List Bool) :
    HoareTime (increment (a := a)) (fun v => v=one (binary xs) 1)
      (fun v => v=one (binary (Counter.increment xs)) 1) (2*xs.length+2) := by
  have h0 := CounterTape.increment_hoare CountedCopyReuse.empty xs rfl
    (by simp [CountedCopyReuse.empty,show (1 : ℤ)+xs.length ≠ 0 by omega])
  have he : ∀ bs,Alphabet.mapTapes (encoding a) (CounterTape.tapes CountedCopyReuse.empty bs)=
      one (binary bs) 1 := by
    intro bs
    apply congrArg₂ Tapes.mk
    · rfl
    · funext i z
      exact congrFun (CountedLoopReuseAlphabet.encoding_binary bs) z
  have h := Alphabet.map_hoare (encoding a) h0
  apply h.consequence _ _ _
  · rintro v rfl
    exact ⟨_,rfl,he xs |>.symm⟩
  · rintro v ⟨original,rfl,rfl⟩
    exact he _
  · have hb := (CounterTape.carrySteps_bounds xs).2.1
    omega

theorem overwrite (old xs : List Bool) (hl : old.length=xs.length) :
    putWord (SelectedSourceBitsScan.word (a := a) old) 0 (xs.map bitSymbol)=
      SelectedSourceBitsScan.word xs := by
  funext z
  by_cases hz : 0≤z ∧ z<xs.length
  · have hn : (z.toNat : ℤ)=z := Int.toNat_of_nonneg hz.1
    have hi : z.toNat<xs.length := by omega
    have h1 := WordSegments.get (SelectedSourceBitsScan.word (a := a) old) 0 (xs.map bitSymbol) z.toNat
      (by simpa using hi)
    have h2 := WordSegments.get (fun _ => (blank : Fin (a+4))) 0 (xs.map bitSymbol) z.toNat
      (by simpa using hi)
    simpa only [hn,zero_add,SelectedSourceBitsScan.word] using h1.trans h2.symm
  · rw [putWord_outside _ _ _ _ (by simp only [List.length_map]; omega)]
    unfold SelectedSourceBitsScan.word
    rw [putWord_outside _ _ _ _ (by simp only [List.length_map]; omega),
      putWord_outside _ _ _ _ (by simp only [List.length_map]; omega)]

def bank (counter addr : List Bool) : Tapes 2 a :=
  Copy.tapes (binary counter) (SelectedSourceBitsScan.word addr) 1 0
def copied (counter addr : List Bool) : Tapes 2 a :=
  Copy.tapes (binary counter) (SelectedSourceBitsScan.word addr) (1+counter.length) addr.length
def sourceReset := extend (MarkedControlStreamReset.rewind (a := a)) 1
def targetReset := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement (1 : Fin 2))
def copyProgram := seq (seq (Copy.program (blank : Fin (a+4)) false) sourceReset) targetReset
def program := seq copyProgram (extend (increment (a := a)) 1)

theorem copies_into (counter : List Bool) (g : ℤ → Fin (a+4))
    (hg : putWord g 0 (counter.map bitSymbol)=SelectedSourceBitsScan.word counter) :
    HoareTime (copyProgram (a := a)) (fun v => v=Copy.tapes (binary counter) g 1 0)
      (fun v => v=bank counter counter) (3*counter.length+7) := by
  have hc := Copy.copy_hoare blank false MarkedWordCleanup.empty g
    1 0 (counter.map bitSymbol) (ReturnOrigin.bits_nonblank _) (by
      simp [MarkedWordCleanup.empty,show (1 : ℤ)+counter.length ≠ 0 by omega])
  have hi : (Copy.retained false : Fin (a+4) → Fin (a+4))=id := rfl
  simp only [hi,List.map_id,List.length_map,zero_add] at hc
  change HoareTime _
    (fun v => v=Copy.tapes (marked (counter.map bitSymbol)) g 1 0)
    (fun v => v=Copy.tapes (marked (counter.map bitSymbol))
      (putWord g 0 (counter.map bitSymbol)) (1+counter.length) counter.length)
    counter.length at hc
  rw [←binary_word,hg] at hc
  have hr := hoare_extend_eq (MarkedControlStreamReset.rewinds (counter.map (bitSymbol (a := a)))
    (by intro x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx; cases b <;> simp [bitSymbol,separator]))
    (one (SelectedSourceBitsScan.word counter) counter.length)
  have he : ∀ (p : ℤ), (one (marked (counter.map (bitSymbol (a := a)))) p).append
      (one (SelectedSourceBitsScan.word counter) counter.length)=
      Copy.tapes (binary counter) (SelectedSourceBitsScan.word counter) p counter.length := by
    intro p
    rw [binary_word]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simp only [List.length_map,he] at hr
  have ht := SelectedSourceBitsRewind.rewinds_at
    (Copy.tapes (binary (a := a) counter) (SelectedSourceBitsScan.word counter) 1 counter.length)
    (1 : Fin 2) counter counter.length le_rfl rfl rfl
  have het : SharedPlacementAlphabet.setTape
      (Copy.tapes (binary (a := a) counter) (SelectedSourceBitsScan.word counter) 1 counter.length)
      1 (SelectedSourceBitsScan.word counter) 0=bank counter counter := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [het] at ht
  exact ((hc.seq hr).seq ht).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem copies (counter old : List Bool) (hl : old.length=counter.length) :
    HoareTime (copyProgram (a := a)) (fun v => v=bank counter old)
      (fun v => v=bank counter counter) (3*counter.length+7) :=
  copies_into counter _ (overwrite old counter hl)

theorem copies_blank (counter : List Bool) :
    HoareTime (copyProgram (a := a))
      (fun v => v=Copy.tapes (binary counter) (fun _ => blank) 1 0)
      (fun v => v=bank counter counter) (3*counter.length+7) :=
  copies_into counter _ rfl

theorem runs (counter old : List Bool) (hl : old.length=counter.length) :
    HoareTime (program (a := a)) (fun v => v=bank counter old)
      (fun v => v=bank (Counter.increment counter) counter) (5*counter.length+10) := by
  have hi := hoare_extend_eq (increments (a := a) counter) (one (SelectedSourceBitsScan.word counter) 0)
  have he : ∀ bs,(one (binary (a := a) bs) 1).append (one (SelectedSourceBitsScan.word counter) 0)=bank bs counter := by
    intro bs
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simp only [he] at hi
  exact ((copies counter old hl).seq hi).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem next (W i : ℕ) (old : List Bool) (hl : old.length=W) :
    HoareTime (program (a := a)) (fun v => v=bank (row W i) old)
      (fun v => v=bank (row W (i+1)) (row W i)) (5*W+10) := by
  simpa only [BinaryAddressTableData.row_length,←BinaryAddressTableData.row_succ] using
    runs (a := a) (row W i) old (by simpa using hl)

end
end IntegerMultBounds.Machine.BinaryCurrentAddress
