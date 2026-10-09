import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCommon

/-! Real raw-array formatting, original repair, raw decoding and record-buffer
cleanup in one finite program. The producer headers and original raw array
are retained; all appended formatter and decoder private tapes are restored. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyLate
noncomputable section
open ActiveRepairLayoutRecordsAssemblyCommon
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
open SharedPlacementAlphabet (setTape)

def focus : Fin 4 → Fin 238 := ![237,54,13,19]
theorem focus_injective : Function.Injective focus := by decide
def caller (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :=
  (headers.append (ActiveRepairLayoutRecordsDecodeLate.input d [])).append (rawBank chunks)
def formatted (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :=
  (headers.append (ActiveRepairLayoutRecordsDecodeLate.input d (ActiveRepairRecordFormatWords.records chunks))).append (rawBank chunks)
def decoded (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :=
  (headers.append (ActiveRepairLayoutRecordsDecodeLate.output d (ActiveRepairRecordFormatWords.records chunks))).append (rawBank chunks)
def input (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) := CleanSubbank.bank (s:=6) (caller headers d chunks)
def output (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :=
  setTape (CleanSubbank.bank (s:=6) (decoded headers d chunks)) 54 (fun _ => blank) 0

def repairProgram (side : ActiveRepairRankHeadersData.SourceSide) := extend
  (extend (Placement.placed (ActiveRepairLayoutRecordsDecodeLate.program side)
    (finAddFlip : Fin (194+43) ≃ Fin (43+194))) 1) 6
def program (side : ActiveRepairRankHeadersData.SourceSide) := seq
  (seq (ActiveRepairRecordFormatPlaced.program focus focus_injective) (repairProgram side))
  (atProgram cleanupProgram (54:Fin 244))
def cost (d : Data) (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ) :=
  ActiveRepairRecordFormatEndpoint.cost chunks bs ns R+1+
    ActiveRepairLayoutRecordsDecodeLate.cost d (ActiveRepairRecordFormatWords.records chunks)+1+
    (2*(DropFlag.encode (ActiveRepairRecordFormatWords.records chunks)).length+3)

 theorem format_ready (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) (bs ns : List Bool)
    (hb : headers.tape 13=CountedLoopReuseAlphabet.binary bs) (hbh : headers.head 13=1)
    (hn : headers.tape 19=CountedLoopReuseAlphabet.binary ns) (hnh : headers.head 19=1) :
    SharedBank.payload (caller headers d chunks) focus=ActiveRepairRecordFormatPlaced.sources (a:=1) chunks bs ns := by
  rw [formatter_sources]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i
    · rfl
    · rfl
    · change headers.head 13=1; exact hbh
    · change headers.head 19=1; exact hnh
  · funext i; fin_cases i
    · rfl
    · rfl
    · change headers.tape 13=CountedLoopReuseAlphabet.binary bs; exact hb
    · change headers.tape 19=CountedLoopReuseAlphabet.binary ns; exact hn

 theorem format_result (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    ActiveRepairRecordFormatPlaced.result (caller headers d chunks) focus chunks=formatted headers d chunks := by
  unfold ActiveRepairRecordFormatPlaced.result
  rw [format_word]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

 theorem runs (headers : Tapes 43 1) (d : Data) (h : Valid d) (chunks : List (List Bool)) (bs ns : List Bool)
    (R : ℕ) (hw : ∀ xs∈chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length)
    (hb : headers.tape 13=CountedLoopReuseAlphabet.binary bs) (hbh : headers.head 13=1)
    (hn : headers.tape 19=CountedLoopReuseAlphabet.binary ns) (hnh : headers.head 19=1) :
    HoareTime (program d.side) (fun v => v=input headers d chunks) (fun v => v=output headers d chunks)
      (cost d chunks bs ns R) := by
  have hf := ActiveRepairRecordFormatPlaced.runs (caller headers d chunks) focus focus_injective chunks bs ns R hw hbs hns
    (format_ready headers d chunks bs ns hb hbh hn hnh)
  rw [format_result] at hf
  have hr := hoare_extend_eq (hoare_extend_eq
    (left_frame (ActiveRepairLayoutRecordsDecodeLate.runs d h (ActiveRepairRecordFormatWords.records chunks)) headers)
    (rawBank chunks)) (SharedBank.empty 6 1)
  have hc := at_runs cleanupProgram (CleanSubbank.bank (s:=6) (decoded headers d chunks)) (54:Fin 244)
    _ _ _ _ rfl rfl (cleanup chunks)
  exact ((hf.seq hr).seq hc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

 theorem record_buffer_blank (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    (output headers d chunks).tape 54=fun _ => blank := by simp [output,setTape]
 theorem raw_output (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    (output headers d chunks).tape 232=putWord (fun _ => blank) 0
      ((ActiveRepairLayoutRecordsData.serialize (ActiveRepairLateOriginalPipelineCleanup.repaired d
        (ActiveRepairRecordFormatWords.records chunks))).map bitSymbol) := by
  rfl
 theorem raw_source_retained (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    (output headers d chunks).tape 237=putWord (fun _ => blank) 0 (chunks.flatten.map bitSymbol) := by
  rfl

 theorem raw_head_origin (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    (output headers d chunks).head 232=0 := rfl
 theorem formatter_private_blank (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    SharedBank.payload (output headers d chunks) (Fin.natAdd 238)=SharedBank.empty 6 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
 theorem headers_retained (headers : Tapes 43 1) (d : Data) (chunks : List (List Bool)) :
    SharedBank.payload (output headers d chunks)
      (fun i : Fin 43 => Fin.castAdd 6 (Fin.castAdd 1 (Fin.castAdd 194 i)))=headers := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyLate
