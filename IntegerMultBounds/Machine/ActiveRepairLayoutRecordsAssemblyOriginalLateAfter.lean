import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankAfterBudget
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyLayoutLate

/-! Physical original-header preparation, raw formatting, repair, decoding,
record cleanup and generated-header erasure. No formatted record buffer or
generated descriptor is supplied in the initial bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalLateAfter
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersCount
open ActiveRepairRankHeadersCommands (bank)
open ActiveRepairLayoutRecordsAssemblyCommon
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}


def repair (d : Inputs s p offset rows) : ActiveRepairLateKeyOriginalData.Data where
  side := .after
  geom := geom d
  originals := originals d
  cs := []
  ss := sources d
  bs := d.hs 8
  q := p.q
  b := p.b
  n := p.n
  rho := p.rho
  f := p.f
  hb := p.hb
  hbq := p.hbq

theorem valid (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.after)
    (hq3 : p.b+3≤p.q) : ActiveRepairLateKeyOriginalValid.Valid (repair d) := by
  apply ActiveRepairLateKeyOriginalGeometry.geometry_valid (repair d) s (p.n*p.b) (p.n*p.q)
    p.before p.after offset (p.f*p.q) (rowBits d) rfl p.compactFits p.activeSize hfit
    (originals_value d) (originals_canonical d) hq3 rfl rfl rfl p.hnf p.hr
  · intro i
    fin_cases i
    · exact d.hv 7
    · exact d.hv 9
    · exact d.hv 10
    · change Counter.value (RecursiveChildQuotientsConstant.bits (p.n+1))=p.f
      rw [RecursiveChildQuotientsConstant.bits_value]
      exact p.hnf
  · intro i
    fin_cases i <;> first | exact d.hc _ | exact RecursiveChildQuotientsConstant.bits_canonical _
  · exact d.hv 8
  · exact d.hc 8

def extra (chunks : List (List Bool)) : Tapes 18 1 :=
  (SharedBank.empty 9 1).append (((SharedBank.empty 2 1).append (rawBank chunks)).append (SharedBank.empty 6 1))
def input (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  (ActiveRepairLayoutRecordsBankPlaced.originalInput d []).append (extra chunks)
def assembled (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  ActiveRepairLayoutRecordsAssemblyLate.output (bank (ready d)) (repair d) chunks
def suffix (d : Inputs s p offset rows) (chunks : List (List Bool)) : Tapes 201 1 :=
  SharedBank.payload (assembled d chunks) (Fin.natAdd 43)
def output (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  (ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=1) d).append (suffix d chunks)

/-- The late parser reserves one extra private port before the retained
geometry bank. Reindexing moves those ten copied descriptors right by one. -/
def metadataShift : Fin 244 ≃ Fin 244 where
  toFun i := ⟨if 87 ≤ i.val ∧ i.val < 97 then i.val+1 else if i.val=97 then 87 else i.val,by split_ifs <;> omega⟩
  invFun i := ⟨if 88 ≤ i.val ∧ i.val ≤ 97 then i.val-1 else if i.val=87 then 97 else i.val,by split_ifs <;> omega⟩
  left_inv i := by apply Fin.ext; simp only; split_ifs <;> omega
  right_inv i := by apply Fin.ext; simp only; split_ifs <;> omega


def shiftInverse (i : Fin 244) : Fin 244 :=
  ⟨if 88 ≤ i.val ∧ i.val ≤ 97 then i.val-1 else if i.val=87 then 97 else i.val,by split_ifs <;> omega⟩
theorem metadataShift_symm (i : Fin 244) : metadataShift.symm i=shiftInverse i := rfl

theorem input_reindex (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (input d chunks).reindex metadataShift=input d chunks := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program := seq
  (seq (reindex (extend ActiveRepairLayoutRecordsBankPlaced.prepareProgram 18) metadataShift)
    (ActiveRepairLayoutRecordsAssemblyLate.program .after))
  (extend (ActiveRepairLayoutRecordsHeadersErase.program (a:=1)) 201)
def cost (d : Inputs s p offset rows) (chunks : List (List Bool)) :=
  ActiveRepairLayoutRecordsBankPlaced.runtime d+1+
    ActiveRepairLayoutRecordsAssemblyLate.cost (repair d) chunks (d.hs 13)
      (RecursiveChildQuotientsConstant.bits (rows*2^s.bits)) s.payload+1+
    ActiveRepairLayoutRecordsHeadersErase.runtime d


theorem prepared_heads (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (((ActiveRepairLayoutRecordsBankPlaced.output d []).append (extra chunks)).reindex metadataShift).head=
      (ActiveRepairLayoutRecordsAssemblyLate.input (bank (ready d)) (repair d) chunks).head := by
  funext i
  change ((ActiveRepairLayoutRecordsBankPlaced.output d []).append (extra chunks)).head (metadataShift.symm i)=_
  rw [metadataShift_symm]
  fin_cases i <;> rfl

theorem prepared_tapes (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (((ActiveRepairLayoutRecordsBankPlaced.output d []).append (extra chunks)).reindex metadataShift).tape=
      (ActiveRepairLayoutRecordsAssemblyLate.input (bank (ready d)) (repair d) chunks).tape := by
  funext i
  change ((ActiveRepairLayoutRecordsBankPlaced.output d []).append (extra chunks)).tape (metadataShift.symm i)=_
  rw [metadataShift_symm]
  fin_cases i <;> rfl

theorem prepared (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    ((ActiveRepairLayoutRecordsBankPlaced.output d []).append (extra chunks)).reindex metadataShift=
      ActiveRepairLayoutRecordsAssemblyLate.input (bank (ready d)) (repair d) chunks :=
  congrArg₂ Tapes.mk (prepared_heads d chunks) (prepared_tapes d chunks)

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
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q)
    (hw : ∀ xs∈chunks,xs.length=s.payload) (hn : chunks.length=rows*2^s.bits) :
    HoareTime program (fun v => v=input d chunks) (fun v => v=output d chunks) (cost d chunks) := by
  have hb := hoare_reindex_eq
    (hoare_extend_eq (ActiveRepairLayoutRecordsBankPlaced.prepares d []) (extra chunks)) metadataShift
  change HoareTime _ (fun v => v=(input d chunks).reindex metadataShift) _ _ at hb
  rw [input_reindex,prepared] at hb
  have ha := ActiveRepairLayoutRecordsAssemblyLate.runs (bank (ready d)) (repair d)
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
        (SharedBank.empty 194 1)).append (rawBank chunks)).append (SharedBank.empty 6 1) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem original_headers (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    SharedBank.payload (output d chunks) (Fin.castAdd 201)=
      ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=1) d := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem raw_output (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (output d chunks).tape 232=putWord (fun _ => blank) 0
      ((ActiveRepairLayoutRecordsData.serialize (ActiveRepairLateOriginalPipelineCleanup.repaired
        (repair d) (ActiveRepairRecordFormatWords.records chunks))).map bitSymbol) := rfl

theorem raw_source (d : Inputs s p offset rows) (chunks : List (List Bool)) :
    (input d chunks).tape 237=putWord (fun _ => blank) 0 (chunks.flatten.map bitSymbol) := rfl


def chunks (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :=
  ActiveRepairLayoutRecordsAssemblyLayoutLate.chunks (repair d) s p.before p.after rows offset
    (p.f*p.q) p.compactFits p.activeSize array


theorem input_array (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows) :
    (input d (chunks d array)).tape 237=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateActual s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) array)).map bitSymbol) := by
  rw [raw_source]
  change putWord (fun _ => blank) 0
    ((ActiveRepairLayoutRecordsData.serialize (ActiveRepairLayoutRecordsData.records s (p.n*p.b) (p.n*p.q)
      p.before p.after rows p.compactFits p.activeSize
      (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateActual s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) array))).map bitSymbol)=_
  rw [ActiveRepairLayoutRecordsData.records_serialize]

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) :
    (output d (chunks d array)).tape 232=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (repair d))) array)).map bitSymbol) := by
  rw [raw_output]
  have hr := ActiveRepairLayoutRecordsAssemblyLayoutLate.records_chunks (repair d)
    s p.before p.after rows offset (p.f*p.q) p.compactFits p.activeSize array
  change ActiveRepairRecordFormatWords.records (chunks d array)=_ at hr
  rw [hr]
  have hh := ActiveRepairLayoutRecordsPipelineLate.repaired_serialize (repair d) (valid d hfit hq3)
    s p.before p.after rows offset (p.f*p.q) (rowBits d) rfl p.compactFits p.activeSize hfit
    (row_bound d) array
  exact congrArg (fun xs : List Bool => putWord (fun _ => blank) 0 (xs.map (bitSymbol (a:=1)))) hh


theorem cost_absorb (A B E V P Q X H : ℕ) (hV : 0<V)
    (hP : P≤A*V) (hQ : Q≤B*V+7*H+58) (hX : X≤E*V) (hH : H≤V+1) :
    P+1+Q+1+X≤(A+B+E+74)*V := by nlinarith

include p in
theorem cost_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((repair d).geom.addressBits+1)≤D) :
    cost d (chunks d array)≤
      (ActiveRepairLayoutRecordsHeadersAfterBudget.constant+
        ActiveRepairLateOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+611)*
        ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows := by
  have hp : 0<s.payload := by omega
  have hP := ActiveRepairLayoutRecordsHeadersAfterBudget.copies_runtime_linear d hrows hp hfit
  have hX := ActiveRepairLayoutRecordsBankAfterBudget.erase_runtime_linear d hrows hp hfit
  have hbits : (d.hs 13).length≤s.payload+1 := by
    exact (GrowingCounterData.canonical_width _ (d.hc 13)).trans
      (by rw [d.hv 13]; exact Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have hQ := ActiveRepairLayoutRecordsAssemblyLayoutLate.cost_linear (repair d) (valid d hfit hq3)
    s p.before p.after rows offset (p.f*p.q) (rowBits d) rfl p.compactFits p.activeSize hfit
    (row_bound d) array (d.hs 13) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
    hbits D hrows hR hdensity
  have hH : (RecursiveChildQuotientsConstant.bits (rows*2^s.bits)).length≤
      ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows+1 := by
    have hcount : rows*2^s.bits≤ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows := by
      unfold ActiveRepairLayoutRecordsHeadersAfterBudget.volume Shape.recordWidth
      rw [←Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ hp
    exact (ActiveRepairRankHeadersCommands.bits_length _).trans (Nat.add_le_add_right hcount 1)
  have hV : 0<ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows := by
    unfold ActiveRepairLayoutRecordsHeadersAfterBudget.volume Shape.recordWidth
    positivity
  change ActiveRepairLayoutRecordsBankPlaced.runtime d≤_ at hP
  have hvEq : rows*2^s.bits*s.payload=ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows := by
    unfold ActiveRepairLayoutRecordsHeadersAfterBudget.volume Shape.recordWidth
    ring
  rw [hvEq] at hQ
  unfold cost
  dsimp only [chunks]
  convert cost_absorb _ _ _ _ _ _ _ _ hV hP hQ hX hH using 1; ring

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=input d (chunks d array))
      (fun v => v=output d (chunks d array))
      ((ActiveRepairLayoutRecordsHeadersAfterBudget.constant+
        ActiveRepairLateOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+611)*
        ActiveRepairLayoutRecordsHeadersAfterBudget.volume s rows) :=
  (runs d (chunks d array) hfit hq3
    (ActiveRepairLayoutRecordsAssemblyLayoutLate.chunks_lengths _ _ _ _ _ _ _ _ _ _)
    (ActiveRepairLayoutRecordsAssemblyLayoutLate.chunks_count _ _ _ _ _ _ _ _ _ _)).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear d array hfit hq3 hrows hR D hdensity)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalLateAfter
