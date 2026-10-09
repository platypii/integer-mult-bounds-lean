import IntegerMultBounds.Machine.ActiveRepairRecordFormatEndpointAt

/-! Complete raw-to-record formatting from blank clock storage, retaining
both canonical binary headers and the original source. Scratch clocks are
physically synthesized and erased; both data heads return to origin. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFormatEndpoint
noncomputable section
open ActiveRepairRecordFormatWords ActiveRepairRecordFormatEndpointAt
open SharedPlacementAlphabet

def input (chunks : List (List Bool)) (bs ns : List Bool) : Tapes 6 0 :=
  ⟨![0,0,0,1,0,1],![putWord (fun _ => blank) 0 (raw chunks),fun _ => blank,fun _ => blank,
    CountedCopyReuse.binary bs,fun _ => blank,CountedLoopReuseAlphabet.binary ns]⟩
def prepared (chunks : List (List Bool)) (bs ns : List Bool) :=
  CountedLoopReuseAlphabet.bank (ActiveRepairRecordFormatStream.stage (fun _ => blank) (fun _ => blank) 0 0 chunks bs 0)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1
def formatted (chunks : List (List Bool)) (bs ns : List Bool) :=
  CountedLoopReuseAlphabet.bank (ActiveRepairRecordFormatStream.stage (fun _ => blank) (fun _ => blank) 0 0 chunks bs chunks.length)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1
def cleared (chunks : List (List Bool)) (bs ns : List Bool) :=
  setTape (setTape (formatted chunks bs ns) 2 (fun _ => blank) 0) 4 (fun _ => blank) 0
def output (chunks : List (List Bool)) (bs ns : List Bool) :=
  setTape (setTape (cleared chunks bs ns) 0 (putWord (fun _ => blank) 0 (raw chunks)) 0)
    1 (putWord (fun _ => blank) 0 (encoded chunks)) 0

def program := seq (seq (seq (seq (seq (seq (atProgram mark 2) (atProgram mark 4))
  ActiveRepairRecordFormatStream.program) (BinaryDescriptorCleanupList.oneProgram (2:Fin 6)))
  (BinaryDescriptorCleanupList.oneProgram (4:Fin 6))) (atProgram ReturnOrigin.program 0))
  (atProgram ReturnOrigin.program 1)
def cost (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ) :=
  chunks.length*(5*R+7*bs.length+26)+7*ns.length+16+(raw chunks).length+(encoded chunks).length+24

 theorem prepared_eq (chunks : List (List Bool)) (bs ns : List Bool) :
    setTape (setTape (input chunks bs ns) 2 CountedCopyReuse.empty 1) 4 CountedCopyReuse.empty 1=
      prepared chunks bs ns := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

 theorem encoded_nonblank (chunks : List (List Bool)) : ∀ x ∈ encoded chunks,x≠blank := by
  induction chunks with
  | nil => simp [encoded,records,Partition.encode]
  | cons xs chunks ih =>
    intro x hx
    simp only [encoded,records,List.map_cons,Partition.encode,List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [Partition.recordWord,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | hx | rfl
      · decide
      · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
        cases b <;> decide
      · decide
    · exact ih x hx

 theorem runs (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs ∈ chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length) :
    HoareTime program (fun v => v=input chunks bs ns) (fun v => v=output chunks bs ns) (cost chunks bs ns R) := by
  have hm2 := at_runs mark (input chunks bs ns) 2 _ _ _ _ rfl rfl marks
  have hm4 := at_runs mark (setTape (input chunks bs ns) 2 CountedCopyReuse.empty 1) 4 _ _ _ _ rfl rfl marks
  have hp := hm2.seq hm4
  rw [prepared_eq] at hp
  have hb := ActiveRepairRecordFormatStream.runs (fun _ => blank) (fun _ => blank) 0 0 chunks bs ns R hw hbs hns
  have hc2 := BinaryDescriptorCleanupList.one_hoare (2:Fin 6) (formatted chunks bs ns) [] (by rfl) (by rfl)
  have hc4 := BinaryDescriptorCleanupList.one_hoare (4:Fin 6)
    (setTape (formatted chunks bs ns) 2 (fun _ => blank) 0) [] (by rfl) (by rfl)
  have hr0 := at_runs ReturnOrigin.program (cleared chunks bs ns) 0 _ _ _ _ (by
    simp [cleared,formatted,ActiveRepairRecordFormatStream.stage,CountedCopyReuse.bank,
      CountedLoopReuseAlphabet.bank,Tapes.append,setTape]; rfl) (by
    simp [cleared,formatted,ActiveRepairRecordFormatStream.stage,CountedCopyReuse.bank,
      CountedLoopReuseAlphabet.bank,Tapes.append,setTape]; rfl)
    (ReturnOrigin.return_hoare (raw chunks) (by exact ReturnOrigin.bits_nonblank chunks.flatten))
  have hr1 := at_runs ReturnOrigin.program
    (setTape (cleared chunks bs ns) 0 (putWord (fun _ => blank) 0 (raw chunks)) 0) 1 _ _ _ _ (by
      simp [cleared,formatted,ActiveRepairRecordFormatStream.stage,CountedCopyReuse.bank,
        CountedLoopReuseAlphabet.bank,Tapes.append,setTape]; rfl) (by
      simp [cleared,formatted,ActiveRepairRecordFormatStream.stage,CountedCopyReuse.bank,
        CountedLoopReuseAlphabet.bank,Tapes.append,setTape]; rfl)
    (ReturnOrigin.return_hoare (encoded chunks) (encoded_nonblank chunks))
  exact (((((hp.seq hb).seq hc2).seq hc4).seq hr0).seq hr1).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; simp only [List.length_nil]; omega)

 theorem source_retained (chunks : List (List Bool)) (bs ns : List Bool) :
    (output chunks bs ns).tape 0=(input chunks bs ns).tape 0 := by
  simp [output,cleared,input,setTape]

 theorem output_encoded (chunks : List (List Bool)) (bs ns : List Bool) :
    (output chunks bs ns).tape 1=putWord (fun _ => blank) 0 (Partition.encode (records chunks)) := by
  simp [output,encoded,setTape]

 theorem clock_blank (chunks : List (List Bool)) (bs ns : List Bool) :
    (output chunks bs ns).tape 2=(fun _ => blank) ∧ (output chunks bs ns).tape 4=(fun _ => blank) := by
  simp [output,cleared,setTape]

 theorem data_heads_origin (chunks : List (List Bool)) (bs ns : List Bool) :
    (output chunks bs ns).head 0=0 ∧ (output chunks bs ns).head 1=0 ∧
    (output chunks bs ns).head 2=0 ∧ (output chunks bs ns).head 4=0 := by
  simp [output,cleared,setTape]

 theorem lengths (chunks : List (List Bool)) (R : ℕ) (hw : ∀ xs ∈ chunks,xs.length=R) :
    (raw chunks).length=chunks.length*R ∧ (encoded chunks).length=chunks.length*(R+2) := by
  induction chunks with
  | nil => simp [raw,encoded,records,Partition.encode]
  | cons xs chunks ih =>
    obtain ⟨hr,he⟩ := ih (fun ys hh => hw ys (List.mem_cons_of_mem _ hh))
    have hx := hw xs List.mem_cons_self
    have hr' : raw (xs::chunks)=xs.map bitSymbol++raw chunks := by
      simp only [raw,List.flatten_cons,List.map_append]
    have he' : encoded (xs::chunks)=Partition.recordWord false xs++encoded chunks := rfl
    rw [hr',he',List.length_append,List.length_append]
    simp only [List.length_map,Partition.recordWord,List.length_cons,List.length_append,List.length_nil] at *
    constructor <;> nlinarith

 theorem runs_linear (chunks : List (List Bool)) (bs ns : List Bool) (R : ℕ)
    (hw : ∀ xs ∈ chunks,xs.length=R) (hbs : Counter.value bs=R) (hns : Counter.value ns=chunks.length)
    (hbits : bs.length≤R+1) :
    HoareTime program (fun v => v=input chunks bs ns) (fun v => v=output chunks bs ns)
      (35*chunks.length*(R+1)+7*ns.length+40) := by
  obtain ⟨hr,he⟩ := lengths chunks R hw
  exact (runs chunks bs ns R hw hbs hns).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; rw [hr,he]; nlinarith)

end
end IntegerMultBounds.Machine.ActiveRepairRecordFormatEndpoint
