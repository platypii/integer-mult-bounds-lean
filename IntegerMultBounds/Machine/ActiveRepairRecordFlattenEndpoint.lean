import IntegerMultBounds.Machine.ActiveRepairRecordFlatten
import IntegerMultBounds.Machine.CountedTapeRepairCleanupWord
import IntegerMultBounds.Machine.FiniteReturnStackAt

/-! Complete two-tape flattening: arbitrary record flags and separators are
removed, the source including its sentinel is erased, and raw output returns
to origin. No input-dependent control states or supplied clocks are used. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFlattenEndpoint
noncomputable section
open ActiveRepairRecordFlatten
open SharedPlacementAlphabet (setTape)
open CountedTapeRepairCleanupWord

def input (rs : List Partition.Record) : Tapes 2 1 :=
  (cfg (marked (encode rs)) (fun _ => blank) 0 0 0).tapes
def scanned (rs : List Partition.Record) : Tapes 2 1 :=
  (cfg (marked (encode rs)) (putWord (fun _ => blank) 0 (raw rs))
    (encode rs).length (raw rs).length 0).tapes
def sourceCleared (rs : List Partition.Record) := setTape (scanned rs) 0 (fun _ => blank) 0
def output (rs : List Partition.Record) := setTape (sourceCleared rs) 1 (putWord (fun _ => blank) 0 (raw rs)) 0

def atProgram {q : ℕ} (M : Program 1 q 1) (i : Fin 2) := Placement.placed M (FiniteReturnStackAt.placement i)
def program := seq (seq (ActiveRepairRecordFlatten.program false) (atProgram markedEndProgram 0))
  (atProgram plainBackProgram 1)
def cost (rs : List Partition.Record) := 2*(encode rs).length+(raw rs).length+9

 theorem at_runs {q B : ℕ} (M : Program 1 q 1) (v : Tapes 2 1) (i : Fin 2)
    (f g : ℤ → Fin 5) (p r : ℤ) (ht : v.tape i=f) (hp : v.head i=p)
    (h0 : HoareTime M (fun w => w=one f p) (fun w => w=one g r) B) :
    HoareTime (atProgram M i) (fun w => w=v) (fun w => w=setTape v i g r) B := by
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement i) v (by
    rw [FiniteReturnStackAt.active_bank,ht,hp]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]

 theorem encoded_nonblank (rs : List Partition.Record) : ∀ x ∈ encode rs,x≠blank := by
  induction rs with
  | nil => simp [encode]
  | cons r rs ih =>
    intro x hx
    simp only [encode,List.mem_append,recordWord,List.mem_cons] at hx
    rcases hx with (rfl | hx) | hx
    · cases r.key <;> decide
    · exact RepairStage.encode_nonblank [r.payload] x (by simpa [KeySelect.encode] using hx)
    · exact ih x hx

 theorem raw_eq (rs : List Partition.Record) :
    raw rs=((rs.map Partition.Record.payload).flatten).map bitSymbol := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [raw,payloadWord,List.map_cons,List.flatten_cons,List.map_append,ih]

 theorem raw_nonblank (rs : List Partition.Record) : ∀ x ∈ raw rs,x≠blank := by
  rw [raw_eq]
  exact ReturnOrigin.bits_nonblank _

 theorem scan_runs (rs : List Partition.Record) :
    HoareTime (ActiveRepairRecordFlatten.program false) (fun v => v=input rs) (fun v => v=scanned rs)
      (encode rs).length := by
  have h := stream_hoare false rs (PartitionMarked.markedTape 0 []) (fun _ => blank) 0 0
    (RepairStage.markedTape_nil _ (by omega))
  have hm : (encode rs).map (retained false)=encode rs := by
    exact List.map_id' _
  rw [hm] at h
  simpa only [input,scanned,marked,zero_add] using h

 theorem runs (rs : List Partition.Record) :
    HoareTime program (fun v => v=input rs) (fun v => v=output rs) (cost rs) := by
  have hc := at_runs markedEndProgram (scanned rs) 0 _ _ _ _ rfl rfl
    (marked_end (encode rs) (encoded_nonblank rs))
  have hr := at_runs plainBackProgram (sourceCleared rs) 1 _ _ _ _ (by rfl) (by rfl)
    (plain_back (raw rs) (raw_nonblank rs))
  exact ((scan_runs rs).seq hc |>.seq hr).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

 theorem heads_origin (rs : List Partition.Record) (i : Fin 2) : (output rs).head i=0 := by
  fin_cases i <;> simp [output,sourceCleared,setTape]

 theorem source_blank (rs : List Partition.Record) : (output rs).tape 0=fun _ => blank := by
  simp [output,sourceCleared,setTape]

 theorem output_raw (rs : List Partition.Record) :
    (output rs).tape 1=putWord (fun _ => blank) 0 (((rs.map Partition.Record.payload).flatten).map bitSymbol) := by
  simp only [output,setTape,Function.update_self,raw_eq]

 theorem length_bounds (rs : List Partition.Record) (R : ℕ)
    (hw : ∀ r ∈ rs,r.payload.length≤R) :
    (encode rs).length≤rs.length*(R+2) ∧ (raw rs).length≤rs.length*R := by
  induction rs with
  | nil => simp [encode,raw]
  | cons r rs ih =>
    obtain ⟨he,hr⟩ := ih (fun r hh => hw r (List.mem_cons_of_mem _ hh))
    have hh := hw r (List.mem_cons_self)
    simp only [encode,recordWord,KeySelect.recordWord,raw,payloadWord,List.length_append,
      List.length_cons,List.length_map,List.length_nil] at *
    constructor <;> nlinarith

 theorem runs_linear (rs : List Partition.Record) (R : ℕ)
    (hw : ∀ r ∈ rs,r.payload.length≤R) :
    HoareTime program (fun v => v=input rs) (fun v => v=output rs)
      (5*rs.length*(R+1)+9) := by
  obtain ⟨he,hr⟩ := length_bounds rs R hw
  exact (runs rs).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; nlinarith)

end
end IntegerMultBounds.Machine.ActiveRepairRecordFlattenEndpoint
