import IntegerMultBounds.Machine.NativeSignedGapReturn
import IntegerMultBounds.Machine.NativeSignedGapPromoteScan

/-! One original-header numerator-promotion executable: prepare the gap clock once,
scan each signed field once, replace the original source and erase every private
stream/clock. The runtime has no exponent-gap times serialized-volume factor. -/
namespace IntegerMultBounds.Machine.NativeSignedGapPromoteReturn
noncomputable section
open RadixSignedShiftRight (Word)
open NativeSignedReturnStream (encode volume)
open NativeSignedGapPromoteWord (result)
open NativeSignedGapScan (clock)
open SharedPlacementAlphabet (setTape)

def word (ws : List Word) := putWord (fun _ => (blank:Fin 6)) 0 (encode ws)
def originalStreams (ws : List Word) := RadixSignedShiftRight.tapes (word ws) (fun _ => blank) 0 0

def input (ws : List Word) (bs ls : List Bool) : Tapes 6 2 :=
  ((originalStreams ws).append (RadixZeroFill.input (q:=2) bs)).append (NativeSignedReturnClean.header ls)

def extra (bs ls : List Bool) : Tapes 3 2 :=
  ⟨fun _ => 1,![RadixZeroFill.radixEmpty,RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary ls]⟩

def prepared (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (word ws) (fun _ => blank) (clock d) 0 0 1).append (extra bs ls)
def scanned (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (word ws) (word (ws.map (result d))) (clock d) (volume ws) (volume ws) 1).append (extra bs ls)
def ready (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (word ws) (word (ws.map (result d))) (clock d) 0 0 1).append (extra bs ls)
def cleared (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (fun _ => blank) (word (ws.map (result d))) (clock d) 0 0 1).append (extra bs ls)
def copied (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (word (ws.map (result d))) (word (ws.map (result d))) (clock d)
    (volume ws) (volume ws) 1).append (extra bs ls)
def copiedReady (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (word (ws.map (result d))) (word (ws.map (result d))) (clock d) 0 0 1).append (extra bs ls)
def replaced (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  (NativeSignedGapPromoteScan.tapes (word (ws.map (result d))) (fun _ => blank) (clock d) 0 0 1).append (extra bs ls)
def output (ws : List Word) (d : ℕ) (bs ls : List Bool) : Tapes 6 2 :=
  ⟨![0,0,0,0,1,1],![word (ws.map (result d)),fun _ => blank,fun _ => blank,fun _ => blank,
    RadixZeroFill.encodedBinary bs,RadixZeroFill.encodedBinary ls]⟩

def streams (i : Fin 6) := decide (i.val<2)
def source (i : Fin 6) := decide (i.val=0)
def scratch (i : Fin 6) := decide (i.val=1)
def fillProgram := extend (extend (RawLinearCombinationCleanup.prepend
  (RadixZeroFill.program (q:=2) (by decide)) 2) 1) 2
def scanProgram := extend (extend NativeSignedGapPromoteScan.program 3) 2
def rewindProgram := CountedBankHeaderClean.rewindProgram (a:=2) (by decide : 0<6) streams 5
def eraseSource := CountedBankHeaderClean.program (a:=2) (by decide : 0<6) source 5
def copyProgram := TwoTapeAt.program (CopyWord.program (a:=2)) (1:Fin 8) 0 (by decide)
def eraseScratch := CountedBankHeaderClean.program (a:=2) (by decide : 0<6) scratch 5
def clockCleanup := NativeReturnOneTape.program NativeSignedGapClock.program (2:Fin 8)
def counterCleanup := NativeReturnOneTape.program NativeSignedGapClock.program (3:Fin 8)
def program := seq (seq (seq (seq (seq (seq (seq (seq fillProgram scanProgram)
  rewindProgram) eraseSource) copyProgram) rewindProgram) eraseScratch) clockCleanup) counterCleanup

def cost (ws : List Word) (d : ℕ) (bs ls : List Bool) :=
  NativeSignedGapPromoteScan.work d ws+43*volume ws+10*d+7*bs.length+66*ls.length+251

private theorem fill_endpoint (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    ((originalStreams ws).append (RadixZeroFill.output (q:=2) (by decide) bs d)).append
      (NativeSignedReturnClean.header ls)=prepared ws d bs ls := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [originalStreams,RadixSignedShiftRight.tapes,RadixSignedShiftRight.cfg,
      NativeSignedGapPromoteScan.tapes,NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,
      RadixZeroFill.output,extra,NativeSignedReturnClean.header,NativeSignedGapClock.fill_clock_eq] <;> rfl

private theorem rewound (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    CountedBankReset.rewound streams (scanned ws d bs ls) (volume ws)=ready ws d bs ls := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [streams,scanned,NativeSignedGapPromoteScan.tapes,
      NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,extra]
  · rfl

private theorem source_erased (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    CountedBankReset.restored source (ready ws d bs ls) (volume ws)=cleared ws d bs ls := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> simp [CountedBankReset.after,source,ready,NativeSignedGapPromoteScan.tapes,
      NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,extra,word,volume,CountedBankReset.erased_word]

private theorem copy_endpoint (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    TwoTapeAt.result (CountedLoopHeaderClean.bank (cleared ws d bs ls)) 1 0
      (word (ws.map (result d))) (word (ws.map (result d)))
      (volume (ws.map (result d))) (volume (ws.map (result d)))=
    CountedLoopHeaderClean.bank (copied ws d bs ls) := by
  rw [NativeSignedGapPromoteScan.volume_result]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [setTape,CountedLoopHeaderClean.bank,cleared,copied,NativeSignedGapPromoteScan.tapes,
      NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,extra,SharedBank.empty]

private theorem copied_rewound (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    CountedBankReset.rewound streams (copied ws d bs ls) (volume ws)=copiedReady ws d bs ls := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [streams,copied,NativeSignedGapPromoteScan.tapes,
      NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,extra]
  · rfl

private theorem scratch_erased (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    CountedBankReset.restored scratch (copiedReady ws d bs ls) (volume ws)=replaced ws d bs ls := by
  rw [←NativeSignedGapPromoteScan.volume_result ws d]
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> simp [CountedBankReset.after,scratch,copiedReady,NativeSignedGapPromoteScan.tapes,
      NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,extra,word,volume,CountedBankReset.erased_word]

private theorem final_endpoint (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    setTape (setTape (CountedLoopHeaderClean.bank (replaced ws d bs ls)) 2 (fun _ => blank) 0)
      3 (fun _ => blank) 0=CountedLoopHeaderClean.bank (output ws d bs ls) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [setTape,CountedLoopHeaderClean.bank,replaced,output,NativeSignedGapPromoteScan.tapes,
      NativeSignedGapPromoteScan.cfg,Config.tapes,Tapes.append,Fin.addCases,extra,SharedBank.empty]

/-- The unary gap is physically synthesized once from its retained binary
header; all old data and generated clocks are erased with every move paid. -/
theorem runs (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length) (bs ls : List Bool)
    (hgap : Counter.value bs=d) (hlen : Counter.value ls=volume ws) :
    HoareTime program (fun v => v=CountedLoopHeaderClean.bank (input ws bs ls))
      (fun v => v=CountedLoopHeaderClean.bank (output ws d bs ls)) (cost ws d bs ls) := by
  have hfill := RawLinearCombinationCleanup.prepend_runs (RadixZeroFill.program (q:=2) (by decide)) _ _
    (originalStreams ws) (RadixZeroFill.fill_zeros (q:=2) (by decide) bs d hgap)
  have h0 := hoare_extend_eq (hoare_extend_eq hfill (NativeSignedReturnClean.header ls)) (SharedBank.empty 2 2)
  rw [fill_endpoint] at h0
  have h1 := hoare_extend_eq (hoare_extend_eq
    (NativeSignedGapPromoteScan.runs ws d hd (fun _ => blank) (fun _ => blank) 0 0 (by intro z hz; rfl) rfl)
    (extra bs ls)) (SharedBank.empty 2 2)
  simp only [zero_add] at h1
  have h2 := CountedBankHeaderClean.rewind_runs (a:=2) (by decide : 0<6) streams 5
    (scanned ws d bs ls) ls (volume ws) (by constructor <;> rfl) hlen
  rw [rewound] at h2
  have h3 := CountedBankHeaderClean.runs (a:=2) (by decide : 0<6) source 5
    (ready ws d bs ls) ls (volume ws) (by decide) (by constructor <;> rfl) hlen
  rw [source_erased] at h3
  have hcopy := CopyWord.copy_hoare (a:=2) (fun _ => blank) (fun _ => blank) 0 0
    (encode (ws.map (result d))) (NativeSignedReturnReuse.encode_nonblank _) rfl
  have h4 := TwoTapeAt.runs CopyWord.program (1:Fin 8) 0 (by decide)
    (CountedLoopHeaderClean.bank (cleared ws d bs ls)) _ _ _ _ _ _ _ _
    (by constructor <;> rfl) (by constructor <;> rfl) hcopy
  simp only [zero_add] at h4
  have he := copy_endpoint ws d bs ls
  dsimp only [volume,word] at he
  rw [he] at h4
  have h5 := CountedBankHeaderClean.rewind_runs (a:=2) (by decide : 0<6) streams 5
    (copied ws d bs ls) ls (volume ws) (by constructor <;> rfl) hlen
  rw [copied_rewound] at h5
  have h6 := CountedBankHeaderClean.runs (a:=2) (by decide : 0<6) scratch 5
    (copiedReady ws d bs ls) ls (volume ws) (by decide) (by constructor <;> rfl) hlen
  rw [scratch_erased] at h6
  have h7 := NativeReturnOneTape.runs NativeSignedGapClock.program (2:Fin 8)
    (CountedLoopHeaderClean.bank (replaced ws d bs ls)) _ _ _ _
    (by constructor <;> rfl) (NativeSignedGapClock.runs d)
  have h8 := NativeReturnOneTape.runs NativeSignedGapClock.program (3:Fin 8)
    (setTape (CountedLoopHeaderClean.bank (replaced ws d bs ls)) 2 (fun _ => blank) 0) _ _ _ _
    (by constructor <;> rfl) (NativeSignedGapClock.runs 0)
  rw [final_endpoint] at h8
  have hv := NativeSignedGapPromoteScan.volume_result ws d
  exact ((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; change (encode (ws.map (result d))).length=volume ws at hv; omega)

theorem cost_linear_headers (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length)
    (bs ls : List Bool) (hgap : Counter.value bs=d) (hlen : Counter.value ls=volume ws)
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls) :
    cost ws d bs ls≤113*volume ws+17*d+324 := by
  have hbw := GrowingCounterData.canonical_width bs hb
  have hlw := GrowingCounterData.canonical_width ls hl
  rw [hgap] at hbw
  rw [hlen] at hlw
  have hbd := Nat.log2_le_self d
  have hld := Nat.log2_le_self (volume ws)
  have hscan := NativeSignedGapPromoteScan.work_linear ws d hd
  unfold cost
  omega

/-- With a genuine gap≤field-width relation, one-time unary preparation and all
header lifecycles fit a linear original serialized-volume bound. -/
theorem cost_linear (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length) (hn : ws≠[])
    (bs ls : List Bool) (hgap : Counter.value bs=d) (hlen : Counter.value ls=volume ws)
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls) :
    cost ws d bs ls≤130*volume ws+324 := by
  have hh := cost_linear_headers ws d hd bs ls hgap hlen hb hl
  have hgv : d≤volume ws := by
    cases ws with
    | nil => contradiction
    | cons w ws =>
      have hw := hd w (by simp)
      simp only [volume,NativeSignedReturnStream.encode_cons,List.length_append,DelimitedRadixRecord.field_length]
      omega
  omega

theorem runs_linear (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length) (hn : ws≠[])
    (bs ls : List Bool) (hgap : Counter.value bs=d) (hlen : Counter.value ls=volume ws)
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls) :
    HoareTime program (fun v => v=CountedLoopHeaderClean.bank (input ws bs ls))
      (fun v => v=CountedLoopHeaderClean.bank (output ws d bs ls)) (130*volume ws+324) :=
  (runs ws d hd bs ls hgap hlen).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear ws d hd hn bs ls hgap hlen hb hl)

theorem endpoint (ws : List Word) (d : ℕ) (bs ls : List Bool) :
    let v := CountedLoopHeaderClean.bank (output ws d bs ls)
    v.head 0=0 ∧ v.tape 0=word (ws.map (result d)) ∧
    (∀ i:Fin 8,i∈[1,2,3,6,7] → v.head i=0 ∧ v.tape i=(fun _ => blank)) := by
  simp only [CountedLoopHeaderClean.bank,output,Tapes.append,Fin.addCases,SharedBank.empty]
  constructor
  · rfl
  constructor
  · rfl
  intro i hi
  fin_cases i <;> simp at hi ⊢

end
end IntegerMultBounds.Machine.NativeSignedGapPromoteReturn
