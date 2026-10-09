import IntegerMultBounds.Machine.CountedPackedControlLoadLine
import IntegerMultBounds.Machine.WordBankCleanup

/-! Reusable dirty-control loading and unloading with fixed control. The
original dirty word is updated, the control word is preserved, and all
private words, generated headers, and runtime clocks are physically erased. -/
namespace IntegerMultBounds.Machine.CountedPackedControlLoadRun
noncomputable section
variable {a : ℕ}
open ColumnTransducer (Rule)
open CountedPackedControlLoadHeaders (shape)
open WordBankCleanup (write)
abbrev input (v : Tapes 5 a) (hs : Fin 2 → List Bool) : Tapes (5+16) a :=
  CountedPackedControlLoadLine.input v hs

def word {s : ℕ} (R : Rule s) (b : ℕ) (hb : 1 ≤ b) (U X : List Bool) :=
  ColumnTransducer.digits R 0 (U.zip (Gather.gather (fun _ z => z) (shape b hb) X X X.length))

theorem word_length {s : ℕ} (R : Rule s) (b : ℕ) (hb : 1 ≤ b) (U X : List Bool)
    (hU : U.length = X.length*b) : (word R b hb U X).length = U.length := by
  simp [word,ColumnTransducer.digits_length,List.length_zip,Gather.gather_length,shape,hU]

def payload (U X : List Bool) (f g : ℤ → Fin (a+4)) (pu px : ℤ) : Tapes 5 a :=
  PackedLine.bank (fun _ => blank) (putWord f px (X.map bitSymbol)) (fun _ => blank)
    (putWord g pu (U.map bitSymbol)) (fun _ => blank) 0 px 0 pu 0

def copied (U X : List Bool) (f g : ℤ → Fin (a+4)) (pu px : ℤ) : Tapes 5 a :=
  PackedLine.bank (putWord (fun _ => blank) 0 (X.map bitSymbol)) (putWord f px (X.map bitSymbol))
    (fun _ => blank) (putWord g pu (U.map bitSymbol)) (fun _ => blank) 0 px 0 pu 0

def lineOutput {s : ℕ} (R : Rule s) (b : ℕ) (hb : 1 ≤ b) (U X : List Bool)
    (f g : ℤ → Fin (a+4)) (pu px : ℤ) : Tapes 5 a :=
  PackedLine.bank (putWord (fun _ => blank) 0 (X.map bitSymbol)) (putWord f px (X.map bitSymbol))
    (fun _ => blank) (putWord g pu (U.map bitSymbol))
    (putWord (fun _ => blank) 0 ((word R b hb U X).map bitSymbol)) 0 px 0 pu 0

def tail (hs : Fin 2 → List Bool) : Tapes 16 a :=
  (FixedHeaderBankCopy.headerBank hs).append (FixedHeaderBankCopy.empty 14)
theorem input_eq (v : Tapes 5 a) (hs : Fin 2 → List Bool) : input v hs = v.append (tail hs) := by
  unfold input CountedPackedControlLoadLine.input CountedPackedControlLoadLine.caller
    CountedPackedControlLoadHeaders.input tail Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem write_input (v : Tapes 5 a) (hs : Fin 2 → List Bool) (k : Fin 5)
    (f : ℤ → Fin (a+4)) : write (input v hs) (Fin.castAdd 16 k) f = input (write v k f) hs := by
  rw [input_eq,input_eq]
  unfold write Tapes.append
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    fin_cases k <;> fin_cases i <;> rfl

def copyControl (a : ℕ) := WordBankCleanup.replaceProgram (1 : Fin 21) 0 (by decide) (by decide) a
def replaceDirty (a : ℕ) := WordBankCleanup.replaceProgram (4 : Fin 21) 3 (by decide) (by decide) a
def clearControl (a : ℕ) := WordBankCleanup.clearProgram (0 : Fin 21) (by decide) a
def clearResult (a : ℕ) := WordBankCleanup.clearProgram (4 : Fin 21) (by decide) a

def program {s : ℕ} (R : Rule s) (a : ℕ) := seq (seq (copyControl a)
  (CountedPackedControlLoadLine.program (fun _ z => z) R a))
  (seq (seq (replaceDirty a) (clearControl a)) (clearResult a))

theorem copies (U X : List Bool) (f g : ℤ → Fin (a+4)) (pu px : ℤ) (hs : Fin 2 → List Bool)
    (hf : f (px-1) = blank) (hf' : f (px+X.length) = blank) :
    HoareTime (copyControl a) (fun v => v = input (payload U X f g pu px) hs)
      (fun v => v = input (copied U X f g pu px) hs) (3*X.length+6) := by
  have hd : (input (payload U X f g pu px) hs).tape 0 =
      putWord (fun _ => blank) 0 (List.replicate X.length blank) := by
    exact (putWord_replicate_blank (fun _ => blank) 0 X.length (by intros; rfl)).symm
  have h := WordBankCleanup.replace_hoare (input (payload U X f g pu px) hs)
    (1 : Fin 21) 0 (by decide) (by decide) f (fun _ => blank)
    (X.map bitSymbol) (List.replicate X.length blank) (by simp)
    rfl hd (ReturnOrigin.bits_nonblank X) hf (by change f (px+(X.map bitSymbol).length) = blank; simpa using hf') rfl
  change HoareTime (copyControl a) _
    (fun v => v = write (input (payload U X f g pu px) hs) (Fin.castAdd 16 (0 : Fin 5))
      (putWord (fun _ => blank) 0 (X.map bitSymbol))) _ at h
  rw [write_input] at h
  have he : write (payload U X f g pu px) 0 (putWord (fun _ => blank) 0 (X.map bitSymbol)) =
      copied U X f g pu px := by
    unfold write payload copied PackedLine.bank
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  simpa only [List.length_map] using h

def finishPayload (U X Y : List Bool) (f g : ℤ → Fin (a+4)) (pu px : ℤ) : Tapes 5 a :=
  PackedLine.bank (putWord (fun _ => blank) 0 (X.map bitSymbol)) (putWord f px (X.map bitSymbol))
    (fun _ => blank) (putWord g pu (U.map bitSymbol))
    (putWord (fun _ => blank) 0 (Y.map bitSymbol)) 0 px 0 pu 0

def finishProgram (a : ℕ) := seq (seq (replaceDirty a) (clearControl a)) (clearResult a)

theorem finishes (U X Y : List Bool) (f g : ℤ → Fin (a+4)) (pu px : ℤ) (hs : Fin 2 → List Bool)
    (hlen : Y.length = U.length) (hg : g (pu-1) = blank) :
    HoareTime (finishProgram a) (fun v => v = input (finishPayload U X Y f g pu px) hs)
      (fun v => v = input (payload Y X f g pu px) hs) (5*Y.length+2*X.length+14) := by
  let A := input (finishPayload U X Y f g pu px) hs
  let B := write A 3 (putWord g pu (Y.map bitSymbol))
  let C := write B 0 (fun _ => blank)
  have h1 := WordBankCleanup.replace_hoare A (4 : Fin 21) 3 (by decide) (by decide)
    (fun _ => blank) g (Y.map bitSymbol) (U.map bitSymbol) (by simpa using hlen)
    rfl rfl (ReturnOrigin.bits_nonblank Y) rfl rfl hg
  have h2 := WordBankCleanup.clear_hoare B (0 : Fin 21) (by decide) (X.map bitSymbol)
    (ReturnOrigin.bits_nonblank X) (by
      change Function.update A.tape 3 (putWord g pu (Y.map bitSymbol)) 0 =
        putWord (fun _ => blank) 0 (X.map bitSymbol)
      rw [Function.update_of_ne (by decide)]
      rfl)
  have h3 := WordBankCleanup.clear_hoare C (4 : Fin 21) (by decide) (Y.map bitSymbol)
    (ReturnOrigin.bits_nonblank Y) (by
      change Function.update (Function.update A.tape 3 (putWord g pu (Y.map bitSymbol)))
        0 (fun _ => blank) 4 = putWord (fun _ => blank) 0 (Y.map bitSymbol)
      rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
      rfl)
  refine ((h1.seq h2).seq h3).consequence (fun _ h => h) ?_ ?_
  · intro v hv
    rw [hv]
    change write (write (write A (Fin.castAdd 16 (3 : Fin 5)) (putWord g pu (Y.map bitSymbol)))
      (Fin.castAdd 16 (0 : Fin 5)) (fun _ => blank)) (Fin.castAdd 16 (4 : Fin 5)) (fun _ => blank) = _
    dsimp only [A]
    rw [write_input,write_input,write_input]
    apply congrArg (fun w : Tapes 5 a => input w hs)
    unfold write finishPayload payload PackedLine.bank
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · simp only [List.length_map]
    omega

/-- The actual modular update replaces U, preserves X, and returns every
scratch word and generated descriptor to its initial blank whole tape. -/
theorem runs {s : ℕ} (R : Rule s) (b : ℕ) (hb : 1 ≤ b) (U X : List Bool)
    (f g : ℤ → Fin (a+4)) (pu px : ℤ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedControlLoadHeaders.originalValues b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hU : U.length = X.length*b)
    (hf : f (px-1) = blank) (hf' : f (px+X.length) = blank)
    (hg : g (pu-1) = blank) (hg' : g (pu+U.length) = blank) :
    HoareTime (program R a) (fun v => v = input (payload U X f g pu px) hs)
      (fun v => v = input (payload (word R b hb U X) X f g pu px) hs)
      (380*((X.length+1)*(b+2))) := by
  have h0 := copies U X f g pu px hs hf hf'
  have h1 := CountedPackedControlLoadLine.runs (fun _ z => z) R b hb X X U
    (fun _ => blank) f g 0 px 0 pu 0 hs hv hc
    (by change X.length*1 ≤ X.length; omega) hU rfl hf hg hg'
  have h2 := finishes U X (word R b hb U X) f g pu px hs (word_length R b hb U X hU) hg
  have hall := (h0.seq h1).seq h2
  refine hall.consequence (fun _ h => h) (fun _ h => h) ?_
  simp only [word_length R b hb U X hU,hU]
  have hvol : 8*(X.length*b)+5*X.length ≤ 8*((X.length+1)*(b+2)) := by nlinarith
  have hp : 1 ≤ (X.length+1)*(b+2) := by nlinarith
  omega

end
end IntegerMultBounds.Machine.CountedPackedControlLoadRun
