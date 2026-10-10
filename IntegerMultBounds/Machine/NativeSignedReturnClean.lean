import IntegerMultBounds.Machine.NativeSignedReturnStream

/-! Paid complete native precision-return stream: actual field arithmetic,
both head rewinds, obsolete source erasure and generated-control cleanup. -/
namespace IntegerMultBounds.Machine.NativeSignedReturnClean
noncomputable section
open NativeSignedReturnStream (encode volume work)
open RadixSignedShiftRight (Word shifted tapes)

def header (bs : List Bool) : Tapes 1 2 :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary bs⟩

def input (ws : List Word) (bs : List Bool) : Tapes 3 2 :=
  (tapes (putWord (fun _ => blank) 0 (encode ws)) (fun _ => blank) 0 0).append (header bs)

def scanned (ws : List Word) (bs : List Bool) : Tapes 3 2 :=
  (tapes (putWord (fun _ => blank) 0 (encode ws))
    (putWord (fun _ => blank) 0 (encode (ws.map shifted))) (volume ws) (volume ws)).append (header bs)

def ready (ws : List Word) (bs : List Bool) : Tapes 3 2 :=
  (tapes (putWord (fun _ => blank) 0 (encode ws))
    (putWord (fun _ => blank) 0 (encode (ws.map shifted))) 0 0).append (header bs)

def output (ws : List Word) (bs : List Bool) : Tapes 3 2 :=
  (tapes (fun _ => blank) (putWord (fun _ => blank) 0 (encode (ws.map shifted))) 0 0).append (header bs)

def streams (i : Fin 3) := decide (i.val<2)
def source (i : Fin 3) := decide (i.val=0)
def scanProgram := extend (extend NativeSignedReturnStream.program 1) 2
def rewindProgram := CountedBankHeaderClean.rewindProgram (a:=2) (by decide : 0<3) streams 2
def eraseProgram := CountedBankHeaderClean.program (a:=2) (by decide : 0<3) source 2
def program := seq (seq scanProgram rewindProgram) eraseProgram

def cost (ws : List Word) (bs : List Bool) := work ws+21*volume ws+33*bs.length+108

theorem rewound (ws : List Word) (bs : List Bool) :
    CountedBankReset.rewound streams (scanned ws bs) (volume ws)=ready ws bs := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [streams,scanned,tapes,
      RadixSignedShiftRight.cfg,Config.tapes,Tapes.append,Fin.addCases,header]
  · rfl

theorem restored (ws : List Word) (bs : List Bool) :
    CountedBankReset.restored source (ready ws bs) (volume ws)=output ws bs := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> simp [CountedBankReset.after,source,ready,tapes,
      RadixSignedShiftRight.cfg,Config.tapes,Tapes.append,Fin.addCases,header,volume,CountedBankReset.erased_word]

/-- One fixed executable owns the actual native field scan and all restoration.
The length header is retained; both generated loop controls return blank. -/
theorem runs (ws : List Word) (hn : ∀ w∈ws,w≠[]) (bs : List Bool)
    (hlen : Counter.value bs=volume ws) :
    HoareTime program (fun v => v=CountedLoopHeaderClean.bank (input ws bs))
      (fun v => v=CountedLoopHeaderClean.bank (output ws bs)) (cost ws bs) := by
  have h0 := hoare_extend_eq (hoare_extend_eq
    (NativeSignedReturnStream.runs ws hn (fun _ => blank) (fun _ => blank) 0 0 rfl)
    (header bs)) (SharedBank.empty 2 2)
  simp only [zero_add] at h0
  have h1 := CountedBankHeaderClean.rewind_runs (a:=2) (by decide : 0<3) streams 2
    (scanned ws bs) bs (volume ws) (by constructor <;> rfl) hlen
  rw [rewound] at h1
  have h2 := CountedBankHeaderClean.runs (a:=2) (by decide : 0<3) source 2
    (ready ws bs) bs (volume ws) (by decide) (by constructor <;> rfl) hlen
  rw [restored] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem cost_linear (ws : List Word) (bs : List Bool)
    (hlen : Counter.value bs=volume ws) (hc : GrowingCounterData.Canonical bs) :
    cost ws bs≤56*volume ws+141 := by
  have hw := GrowingCounterData.canonical_width bs hc
  rw [hlen] at hw
  have hh := Nat.log2_le_self (volume ws)
  have hs := NativeSignedReturnStream.work_linear ws
  unfold cost
  omega

theorem runs_linear (ws : List Word) (hn : ∀ w∈ws,w≠[]) (bs : List Bool)
    (hlen : Counter.value bs=volume ws) (hc : GrowingCounterData.Canonical bs) :
    HoareTime program (fun v => v=CountedLoopHeaderClean.bank (input ws bs))
      (fun v => v=CountedLoopHeaderClean.bank (output ws bs)) (56*volume ws+141) :=
  (runs ws hn bs hlen).consequence (fun _ h => h) (fun _ h => h) (cost_linear ws bs hlen hc)

end
end IntegerMultBounds.Machine.NativeSignedReturnClean
