import IntegerMultBounds.Machine.ActivePrefixCompactParityLoadRun

/-! Physical erasure of both emitted offset words and every derived rotation
header. The original ten descriptors and the newly rotated full array remain. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactParityLoadCleanup
noncomputable section
open ActivePrefixCompactParityLoadData
open ActivePrefixCompactParityLoadHeaders (bank)
open ActivePrefixParityOnlyBank (Shape offsetWord)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def clearBase (v : Tapes 19 a) := setTape v 11 (fun _ => blank) 0
def clearRepeated (v : Tapes 19 a) := setTape (clearBase v) 12 (fun _ => blank) 0
def clearHeaders (v : Tapes 19 a) := ActivePrefixOffsetHeadersCleanup.cleared (clearRepeated v) derivedFocus
def result (v : Tapes 19 a) := setTape (clearHeaders v) 18 (fun _ => blank) 0

def rawProgram := seq (seq (seq
  (WordBankCleanup.clearProgram (11 : Fin 19) (by decide) a)
  (WordBankCleanup.clearProgram (12 : Fin 19) (by decide) a))
  (ActivePrefixOffsetHeadersCleanup.program (a := a) derivedFocus))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (18 : Fin 19))
def program := extend (rawProgram (a := a)) 41

def cost (s : Shape) (rows : ℕ) :=
  2*(offsetWord s).length+3+2*(offsets s rows).length+3+
    ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)+
    (2*(bits (prefixCount s rows)).length+4)+3

theorem clear_word (v : Tapes 19 a) (k : Fin 19) (xs : List Bool)
    (ht : v.tape k=ActivePrefixOffsetRepeatAlphabet.word xs) (hh : v.head k=0) :
    HoareTime (WordBankCleanup.clearProgram k (by decide) a) (fun w => w=v)
      (fun w => w=setTape v k (fun _ => blank) 0) (2*xs.length+3) := by
  have h := WordBankCleanup.clear_hoare v k (by decide) (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) (by rw [hh]; exact ht)
  apply h.consequence (fun _ h => h) ?_ (by simp)
  rintro w rfl
  apply congrArg₂ Tapes.mk
  · funext j
    by_cases hj : j=k
    · subst j; simp [hh]
    · simp [hj]
  · rfl

theorem raw_runs (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    HoareTime (rawProgram (a := a))
      (fun v => v=rotated (base s rows B hs rs bs x) s rows B x)
      (fun v => v=result (rotated (base s rows B hs rs bs x) s rows B x)) (cost s rows) := by
  let v := rotated (base (a := a) s rows B hs rs bs x) s rows B x
  have h₀ := clear_word v 11 (offsetWord s) rfl rfl
  have h₁ := clear_word (clearBase v) 12 (offsets s rows) rfl rfl
  have h₂ := ActivePrefixOffsetHeadersCleanup.cleans (clearRepeated v) derivedFocus derived_injective
    (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have h₃ := BinaryDescriptorCleanupList.one_hoare (18 : Fin 19) (clearHeaders v)
    (bits (prefixCount s rows))
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  exact (((h₀.seq h₁).seq h₂).seq h₃).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

theorem result_eq (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    result (rotated (base (a := a) s rows B hs rs bs x) s rows B x)=
      base s rows B hs rs bs (PackedOffsetPayloadArray.array (offsets s rows) (width s) (prefixCount s rows) B x) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [clearHeaders,clearRepeated,clearBase,ActivePrefixOffsetHeadersCleanup.cleared,
    rotated,ActiveTargetRotation.result,repeated,ActivePrefixOffsetRepeatPlaced.result,
    dimensions,headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
    ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
    ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,produced,
    ActivePrefixParityOnlyPlaced.result,setTape,base,producerFocus,headerFocus,derivedFocus,
    repeatFocus,rotateFocus,Matrix.cons_val]
  all_goals rfl

theorem runs (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    HoareTime (program (a := a))
      (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x))
      (fun v => v=bank (base s rows B hs rs bs
        (PackedOffsetPayloadArray.array (offsets s rows) (width s) (prefixCount s rows) B x))) (cost s rows) := by
  have h := hoare_extend_eq (raw_runs (a := a) s rows B hs rs bs x) (SharedBank.empty 41 a)
  simpa only [program,result_eq,bank,CleanSubbank.bank] using h

end
end IntegerMultBounds.Machine.ActivePrefixCompactParityLoadCleanup
