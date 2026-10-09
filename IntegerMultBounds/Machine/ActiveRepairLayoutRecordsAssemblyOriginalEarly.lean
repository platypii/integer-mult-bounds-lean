import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyLayoutEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankBudget

/-! Physical original-header preparation, raw formatting, repair, decoding,
record cleanup and generated-header erasure. No formatted record buffer or
generated descriptor is supplied in the initial bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalEarly
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersCount
open ActiveRepairRankHeadersCommands (bank)
open ActiveRepairLayoutRecordsAssemblyCommon
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def extra (chunks : List (List Bool)) : Tapes 9 1 :=
  ((SharedBank.empty 2 1).append (rawBank chunks)).append (SharedBank.empty 6 1)
def input (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  (ActiveRepairLayoutRecordsBankPlaced.originalInput d []).append (extra chunks)
def assembled (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  ActiveRepairLayoutRecordsAssemblyEarly.output (bank (ready d)) (repair d) chunks
def suffix (d : Inputs s p offset rows) (chunks : List (List Bool)) : Tapes 192 1 :=
  SharedBank.payload (assembled d chunks) (Fin.natAdd 43)
def output (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  (ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=1) d).append (suffix d chunks)
def program := seq
  (seq (extend ActiveRepairLayoutRecordsBankPlaced.prepareProgram 9)
    (ActiveRepairLayoutRecordsAssemblyEarly.program .before))
  (extend (ActiveRepairLayoutRecordsHeadersErase.program (a:=1)) 192)
def cost (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  ActiveRepairLayoutRecordsBankPlaced.runtime d+1+
    ActiveRepairLayoutRecordsAssemblyEarly.cost (repair d) chunks (d.hs 13)
      (RecursiveChildQuotientsConstant.bits (rows*2^s.bits)) s.payload+1+
    ActiveRepairLayoutRecordsHeadersErase.runtime d

theorem prepared (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (ActiveRepairLayoutRecordsBankPlaced.output d []).append (extra chunks)=
      ActiveRepairLayoutRecordsAssemblyEarly.input (bank (ready d)) (repair d) chunks := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem assembled_split (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    assembled d chunks=(bank (ready d)).append (suffix d chunks) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem encoded_binary (bs : List Bool) :
    RadixZeroFill.encodedBinary (q:=1) bs=CountedLoopReuseAlphabet.binary (a:=1) bs := by
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  rfl

theorem width_tape (d : Inputs s p offset rows) :
    (bank (a:=1) (ready d)).tape 13=CountedLoopReuseAlphabet.binary (d.hs 13) := by
  change RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits s.payload)=_
  have hc := ActiveRepairLayoutRecordsHeadersRun.canonical_original d 13
  change d.hs 13=RecursiveChildQuotientsConstant.bits s.payload at hc
  rw [←hc,encoded_binary]

theorem count_tape (d : Inputs s p offset rows) :
    (bank (a:=1) (ready d)).tape 19=
      CountedLoopReuseAlphabet.binary (RecursiveChildQuotientsConstant.bits (rows*2^s.bits)) :=
  encoded_binary _

theorem runs (d : Inputs s p offset rows) (chunks : List (List Bool))
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q)
    (hw : ∀ xs∈chunks,xs.length=s.payload) (hn : chunks.length=rows*2^s.bits) :
    HoareTime program (fun v => v=input d chunks) (fun v => v=output d chunks) (cost d chunks) := by
  have hb := hoare_extend_eq (ActiveRepairLayoutRecordsBankPlaced.prepares d []) (extra chunks)
  rw [prepared] at hb
  have ha := ActiveRepairLayoutRecordsAssemblyEarly.runs (bank (ready d)) (repair d)
    (valid d hfit hq3) chunks (d.hs 13) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
    s.payload hw (d.hv 13) (by rw [RecursiveChildQuotientsConstant.bits_value,hn])
    (width_tape d) rfl (count_tape d) rfl
  have he := hoare_extend_eq (ActiveRepairLayoutRecordsHeadersErase.runs (a:=1) d) (suffix d chunks)
  rw [ActiveRepairLayoutRecordsHeadersRun.input_eq] at he
  rw [←assembled_split] at he
  exact (hb.seq ha).seq he


theorem input_literal (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    input d chunks=
      (((ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=1) d).append
        (SharedBank.empty 185 1)).append (rawBank chunks)).append (SharedBank.empty 6 1) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem original_headers (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    SharedBank.payload (output d chunks) (Fin.castAdd 192)=
      ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=1) d := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem raw_output (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (output d chunks).tape 223=putWord (fun _ => blank) 0
      ((ActiveRepairLayoutRecordsData.serialize (ActiveRepairEarlyOriginalPipelineCleanup.repaired
        (repair d) (ActiveRepairRecordFormatWords.records chunks))).map bitSymbol) := rfl

theorem raw_source (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (input d chunks).tape 228=putWord (fun _ => blank) 0 (chunks.flatten.map bitSymbol) := rfl


def chunks (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :=
  ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks (repair d) s p.before p.after rows offset
    (p.f*p.q) p.compactFits p.activeSize array


theorem input_array (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :
    (input d (chunks d array)).tape 228=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyActual s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (repair d))) array)).map bitSymbol) := by
  rw [raw_source]
  change putWord (fun _ => blank) 0
    ((ActiveRepairLayoutRecordsData.serialize (ActiveRepairLayoutRecordsData.records s (p.n*p.b) (p.n*p.q)
      p.before p.after rows p.compactFits p.activeSize
      (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyActual s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (repair d))) array))).map bitSymbol)=_
  rw [ActiveRepairLayoutRecordsData.records_serialize]

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    (output d (chunks d array)).tape 223=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (repair d))) array)).map bitSymbol) := by
  rw [raw_output]
  have hr := ActiveRepairLayoutRecordsAssemblyLayoutEarly.records_chunks (repair d)
    s p.before p.after rows offset (p.f*p.q) p.compactFits p.activeSize array
  change ActiveRepairRecordFormatWords.records (chunks d array)=_ at hr
  rw [hr]
  have hh := ActiveRepairLayoutRecordsPipelineEarly.repaired_serialize (repair d) (valid d hfit hq3)
    s p.before p.after rows offset (p.f*p.q) (rowBits d) rfl p.compactFits p.activeSize hfit
    (row_bound d) array
  exact congrArg (fun xs : List Bool => putWord (fun _ => blank) 0 (xs.map (bitSymbol (a:=1)))) hh


theorem cost_absorb (A B E V P Q X H : ℕ) (hV : 0<V)
    (hP : P≤A*V) (hQ : Q≤B*V+7*H+58) (hX : X≤E*V) (hH : H≤V+1) :
    P+1+Q+1+X≤(A+B+E+74)*V := by nlinarith

include p in
theorem cost_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((repair d).geom.addressBits+1)≤D) :
    cost d (chunks d array)≤
      (ActiveRepairLayoutRecordsHeadersBudget.constant+
        ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankBudget.eraseConstant+611)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
  have hp : 0<s.payload := by omega
  have hP := ActiveRepairLayoutRecordsHeadersBudget.copies_runtime_linear d hrows hp hfit
  have hX := ActiveRepairLayoutRecordsBankBudget.erase_runtime_linear d hrows hp hfit
  have hbits : (d.hs 13).length≤s.payload+1 := by
    exact (GrowingCounterData.canonical_width _ (d.hc 13)).trans
      (by rw [d.hv 13]; exact Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have hQ := ActiveRepairLayoutRecordsAssemblyLayoutEarly.cost_linear (repair d) (valid d hfit hq3)
    s p.before p.after rows offset (p.f*p.q) (rowBits d) rfl p.compactFits p.activeSize hfit
    (row_bound d) array (d.hs 13) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
    hbits D hrows hR hdensity
  have hH : (RecursiveChildQuotientsConstant.bits (rows*2^s.bits)).length≤
      ActiveRepairLayoutRecordsHeadersBudget.volume s rows+1 := by
    have hcount : rows*2^s.bits≤ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
      unfold ActiveRepairLayoutRecordsHeadersBudget.volume Shape.recordWidth
      rw [←Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ hp
    exact (ActiveRepairRankHeadersCommands.bits_length _).trans (Nat.add_le_add_right hcount 1)
  have hV : 0<ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
    unfold ActiveRepairLayoutRecordsHeadersBudget.volume Shape.recordWidth
    positivity
  change ActiveRepairLayoutRecordsBankPlaced.runtime d≤_ at hP
  have hvEq : rows*2^s.bits*s.payload=ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
    unfold ActiveRepairLayoutRecordsHeadersBudget.volume Shape.recordWidth
    ring
  rw [hvEq] at hQ
  unfold cost
  dsimp only [chunks]
  convert cost_absorb _ _ _ _ _ _ _ _ hV hP hQ hX hH using 1; ring

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d (chunks d array))
      (fun v => v=output d (chunks d array))
      ((ActiveRepairLayoutRecordsHeadersBudget.constant+
        ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankBudget.eraseConstant+611)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows) :=
  (runs d (chunks d array) hfit hq3
    (ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks_lengths _ _ _ _ _ _ _ _ _ _)
    (ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks_count _ _ _ _ _ _ _ _ _ _)).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear d array hfit hq3 hrows hR D hdensity)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalEarly
