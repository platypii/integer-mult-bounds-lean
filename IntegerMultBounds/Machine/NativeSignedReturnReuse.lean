import IntegerMultBounds.Machine.NativeSignedReturnClean
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.WordMoves

/-! A reusable precision lowering pass returns its result on the original
source tape, with the scratch stream blank and both heads at zero. -/
namespace IntegerMultBounds.Machine.NativeSignedReturnReuse
noncomputable section
open RadixSignedShiftRight (Word shifted tapes)
open NativeSignedReturnStream (encode volume work)
open NativeSignedReturnClean (header)

def copied (ws : List Word) (bs : List Bool) : Tapes 3 2 :=
  (tapes (putWord (fun _ => blank) 0 (encode (ws.map shifted)))
    (putWord (fun _ => blank) 0 (encode (ws.map shifted))) (volume ws) (volume ws)).append (header bs)
def ready (ws : List Word) (bs : List Bool) : Tapes 3 2 :=
  (tapes (putWord (fun _ => blank) 0 (encode (ws.map shifted)))
    (putWord (fun _ => blank) 0 (encode (ws.map shifted))) 0 0).append (header bs)
def scratch (i : Fin 3) := decide (i.val=1)
def copyProgram := TwoTapeAt.program (CopyWord.program (a:=2)) (1:Fin 5) 0 (by decide)
def rewindProgram := NativeSignedReturnClean.rewindProgram
def eraseProgram := CountedBankHeaderClean.program (a:=2) (by decide : 0<3) scratch 2
def program := seq (seq (seq NativeSignedReturnClean.program copyProgram) rewindProgram) eraseProgram

def cost (ws : List Word) (bs : List Bool) := work ws+43*volume ws+66*bs.length+218

theorem encode_nonblank (ws : List Word) : ∀ x∈encode ws,x≠blank := by
  induction ws with
  | nil => simp [encode]
  | cons w ws ih =>
    intro x hx
    rw [NativeSignedReturnStream.encode_cons,List.mem_append] at hx
    rcases hx with h|h
    · simp only [DelimitedRadixRecord.field,List.mem_append,List.mem_map,List.mem_singleton] at h
      rcases h with ⟨d,_,rfl⟩|rfl
      · intro h; have he := congrArg Fin.val h
        change d.val+4=0 at he
        omega
      · decide
    · exact ih x h

theorem copy_endpoint (ws : List Word) (bs : List Bool) (hn : ∀ w∈ws,w≠[]) :
    TwoTapeAt.result (CountedLoopHeaderClean.bank (NativeSignedReturnClean.output ws bs)) 1 0
      (putWord (fun _ => blank) 0 (encode (ws.map shifted)))
      (putWord (fun _ => blank) 0 (encode (ws.map shifted)))
      (volume (ws.map shifted)) (volume (ws.map shifted)) =
    CountedLoopHeaderClean.bank (copied ws bs) := by
  rw [NativeSignedReturnStream.volume_shifted ws hn]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [SharedPlacementAlphabet.setTape,CountedLoopHeaderClean.bank,
      NativeSignedReturnClean.output,copied,tapes,RadixSignedShiftRight.cfg,Config.tapes,
      Tapes.append,Fin.addCases,header,SharedBank.empty]

theorem rewound (ws : List Word) (bs : List Bool) :
    CountedBankReset.rewound NativeSignedReturnClean.streams (copied ws bs) (volume ws)=ready ws bs := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [NativeSignedReturnClean.streams,copied,tapes,
      RadixSignedShiftRight.cfg,Config.tapes,Tapes.append,Fin.addCases,header]
  · rfl

theorem restored (ws : List Word) (bs : List Bool) (hn : ∀ w∈ws,w≠[]) :
    CountedBankReset.restored scratch (ready ws bs) (volume ws)=
      NativeSignedReturnClean.input (ws.map shifted) bs := by
  rw [←NativeSignedReturnStream.volume_shifted ws hn]
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i; fin_cases i <;> simp [CountedBankReset.after,scratch,ready,
      tapes,RadixSignedShiftRight.cfg,Config.tapes,Tapes.append,
      Fin.addCases,header,volume,CountedBankReset.erased_word]

theorem runs (ws : List Word) (hn : ∀ w∈ws,w≠[]) (bs : List Bool)
    (hlen : Counter.value bs=volume ws) :
    HoareTime program (fun v => v=CountedLoopHeaderClean.bank (NativeSignedReturnClean.input ws bs))
      (fun v => v=CountedLoopHeaderClean.bank (NativeSignedReturnClean.input (ws.map shifted) bs))
      (cost ws bs) := by
  have h0 := NativeSignedReturnClean.runs ws hn bs hlen
  have hcopy := CopyWord.copy_hoare (a:=2) (fun _ => blank) (fun _ => blank) 0 0
    (encode (ws.map shifted)) (encode_nonblank _) rfl
  have h1 := TwoTapeAt.runs CopyWord.program (1:Fin 5) 0 (by decide)
    (CountedLoopHeaderClean.bank (NativeSignedReturnClean.output ws bs))
    _ _ _ _ _ _ _ _ (by constructor <;> rfl) (by constructor <;> rfl) hcopy
  simp only [zero_add] at h1
  have he := copy_endpoint ws bs hn
  dsimp only [volume] at he
  rw [he] at h1
  have h2 := CountedBankHeaderClean.rewind_runs (a:=2) (by decide : 0<3)
    NativeSignedReturnClean.streams 2 (copied ws bs) bs (volume ws)
    (by constructor <;> rfl) hlen
  rw [rewound] at h2
  have h3 := CountedBankHeaderClean.runs (a:=2) (by decide : 0<3) scratch 2
    (ready ws bs) bs (volume ws) (by decide) (by constructor <;> rfl) hlen
  rw [restored ws bs hn] at h3
  have hv := NativeSignedReturnStream.volume_shifted ws hn
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost NativeSignedReturnClean.cost; change (encode (ws.map shifted)).length=volume ws at hv; omega)

end
end IntegerMultBounds.Machine.NativeSignedReturnReuse
