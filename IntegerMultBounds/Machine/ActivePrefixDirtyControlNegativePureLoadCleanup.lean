import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadRun

/-! Erase both offset streams and all three rotation dimensions after the
full-array rotation, retaining precisely the original descriptors and array. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadCleanup
noncomputable section
open ActivePrefixDirtyControlLoadProducer (values width)
open ActivePrefixDirtyControlNegativePureData (negative)
open ActivePrefixDirtyControlLoadData (Array base volume prefixCount)
open ActivePrefixDirtyControlNegativePureLoadData
open ActivePrefixDirtyControlLoadHeaders (bank)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def clearBase (v : Tapes 14 a) := setTape v 9 (fun _ => blank) 0
def clearRepeated (v : Tapes 14 a) := setTape (clearBase v) 10 (fun _ => blank) 0
def clearPower (v : Tapes 14 a) := setTape (clearRepeated v) 11 (fun _ => blank) 0
def clearWidth (v : Tapes 14 a) := setTape (clearPower v) 12 (fun _ => blank) 0
def result (v : Tapes 14 a) := setTape (clearWidth v) 13 (fun _ => blank) 0

def rawProgram := seq (seq (seq (seq
  (WordBankCleanup.clearProgram (9 : Fin 14) (by decide) a)
  (WordBankCleanup.clearProgram (10 : Fin 14) (by decide) a))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (11 : Fin 14)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (12 : Fin 14)))
  (BinaryDescriptorCleanupList.oneProgram (a := a) (13 : Fin 14))
def program := extend (rawProgram (a := a)) 51

def cost (s : Shape) (rows : ℕ) :=
  2*(negative s).length+2*(offsets s rows).length+
  2*(bits (2^s.W)).length+2*(bits (width s)).length+2*(bits (prefixCount s rows)).length+22

theorem clear_word (v : Tapes 14 a) (k : Fin 14) (xs : List Bool)
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

theorem raw_runs (s : Shape) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    HoareTime (rawProgram (a := a)) (fun v => v=rotated (base s rows B hs rs bs x) s rows B x)
      (fun v => v=result (rotated (base s rows B hs rs bs x) s rows B x)) (cost s rows) := by
  let v := rotated (base (a := a) s rows B hs rs bs x) s rows B x
  have h₀ := clear_word v 9 (offsets s rows) rfl rfl
  have h₁ := clear_word (clearBase v) 10 (negative s) rfl rfl
  have h₂ := BinaryDescriptorCleanupList.one_hoare (11 : Fin 14) (clearRepeated v)
    (bits (2^s.W)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h₃ := BinaryDescriptorCleanupList.one_hoare (12 : Fin 14) (clearPower v)
    (bits (width s)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h₄ := BinaryDescriptorCleanupList.one_hoare (13 : Fin 14) (clearWidth v)
    (bits (prefixCount s rows)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  exact ((((h₀.seq h₁).seq h₂).seq h₃).seq h₄).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

theorem result_eq (s : Shape) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    result (rotated (base (a := a) s rows B hs rs bs x) s rows B x)=
      base s rows B hs rs bs (PackedOffsetPayloadArray.array (offsets s rows) (width s) (prefixCount s rows) B x) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (s : Shape) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    HoareTime (program (a := a)) (fun v => v=bank (rotated (base s rows B hs rs bs x) s rows B x))
      (fun v => v=bank (base s rows B hs rs bs
        (PackedOffsetPayloadArray.array (offsets s rows) (width s) (prefixCount s rows) B x))) (cost s rows) := by
  simpa only [program,result_eq,bank,CleanSubbank.bank] using
    hoare_extend_eq (raw_runs (a := a) s rows B hs rs bs x) (SharedBank.empty 51 a)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadCleanup
