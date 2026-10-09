import IntegerMultBounds.Machine.ActiveRepairRecordFormatEndpoint
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Literal larger-alphabet execution of the complete raw record formatter.
Flags, bits and delimiters retain their original codes; all clocks are paid. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatAlphabet
noncomputable section
variable (a : ℕ)

def program := Alphabet.program (CountedLoopReuseAlphabet.encoding a) ActiveRepairRecordFormatEndpoint.program
def input (chunks : List (List Bool)) (bs ns : List Bool) :=
  Alphabet.mapTapes (CountedLoopReuseAlphabet.encoding a) (ActiveRepairRecordFormatEndpoint.input chunks bs ns)
def output (chunks : List (List Bool)) (bs ns : List Bool) :=
  Alphabet.mapTapes (CountedLoopReuseAlphabet.encoding a) (ActiveRepairRecordFormatEndpoint.output chunks bs ns)

theorem runs (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs∈chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length) :
    HoareTime (program a) (fun v => v=input a chunks bs ns) (fun v => v=output a chunks bs ns)
      (ActiveRepairRecordFormatEndpoint.cost chunks bs ns R) := by
  have h := Alphabet.map_hoare (CountedLoopReuseAlphabet.encoding a)
    (ActiveRepairRecordFormatEndpoint.runs chunks bs ns R hw hbs hns)
  exact h.consequence (by rintro v rfl; exact ⟨_,rfl,rfl⟩)
    (by rintro v ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem runs_linear (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs∈chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length)
    (hbits : bs.length≤R+1) :
    HoareTime (program a) (fun v => v=input a chunks bs ns) (fun v => v=output a chunks bs ns)
      (35*chunks.length*(R+1)+7*ns.length+40) := by
  have h := Alphabet.map_hoare (CountedLoopReuseAlphabet.encoding a)
    (ActiveRepairRecordFormatEndpoint.runs_linear chunks bs ns R hw hbs hns hbits)
  exact h.consequence (by rintro v rfl; exact ⟨_,rfl,rfl⟩)
    (by rintro v ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem source_retained (chunks : List (List Bool)) (bs ns : List Bool) :
    (output a chunks bs ns).tape 0=(input a chunks bs ns).tape 0 := by
  change (fun z => (CountedLoopReuseAlphabet.encoding a).encode
    ((ActiveRepairRecordFormatEndpoint.output chunks bs ns).tape 0 z))=_
  rw [ActiveRepairRecordFormatEndpoint.source_retained]
  rfl

theorem clock_blank (chunks : List (List Bool)) (bs ns : List Bool) :
    (output a chunks bs ns).tape 2=(fun _ => blank) ∧
      (output a chunks bs ns).tape 4=(fun _ => blank) := by
  obtain ⟨h2,h4⟩ := ActiveRepairRecordFormatEndpoint.clock_blank chunks bs ns
  constructor
  · change (fun z => (CountedLoopReuseAlphabet.encoding a).encode
      ((ActiveRepairRecordFormatEndpoint.output chunks bs ns).tape 2 z))=_
    rw [h2]; rfl
  · change (fun z => (CountedLoopReuseAlphabet.encoding a).encode
      ((ActiveRepairRecordFormatEndpoint.output chunks bs ns).tape 4 z))=_
    rw [h4]; rfl

theorem data_heads_origin (chunks : List (List Bool)) (bs ns : List Bool) :
    (output a chunks bs ns).head 0=0 ∧ (output a chunks bs ns).head 1=0 ∧
      (output a chunks bs ns).head 2=0 ∧ (output a chunks bs ns).head 4=0 :=
  ActiveRepairRecordFormatEndpoint.data_heads_origin chunks bs ns

theorem output_encoded (chunks : List (List Bool)) (bs ns : List Bool) :
    (output a chunks bs ns).tape 1=putWord (fun _ => blank) 0
      ((Partition.encode (ActiveRepairRecordFormatWords.records chunks)).map
        (CountedLoopReuseAlphabet.encoding a).encode) := by
  change RowPaddingConstructedAlphabet.mapTape
    ((ActiveRepairRecordFormatEndpoint.output chunks bs ns).tape 1)=_
  rw [ActiveRepairRecordFormatEndpoint.output_encoded,RowPaddingConstructedAlphabet.map_putWord]
  rfl

end
end IntegerMultBounds.Machine.ActiveRepairRecordFormatAlphabet
