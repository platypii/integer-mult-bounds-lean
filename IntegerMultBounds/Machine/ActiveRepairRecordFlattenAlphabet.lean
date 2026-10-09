import IntegerMultBounds.Machine.ActiveRepairRecordFlattenOriginal
import IntegerMultBounds.Machine.Alphabet

/-! The real record flattening endpoint on larger caller alphabets. Existing
blank, bits, separators and the temporary source marker keep literal codes. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFlattenAlphabet
noncomputable section
variable (a : ℕ)

def program := Alphabet.program (Alphabet.widen 1 a) ActiveRepairRecordFlattenOriginal.program
def input (rs : List Partition.Record) :=
  Alphabet.mapTapes (Alphabet.widen 1 a) (ActiveRepairRecordFlattenOriginal.input rs)
def output (rs : List Partition.Record) :=
  Alphabet.mapTapes (Alphabet.widen 1 a) (ActiveRepairRecordFlattenEndpoint.output rs)

theorem runs (rs : List Partition.Record) :
    HoareTime (program a) (fun v => v=input a rs) (fun v => v=output a rs)
      (ActiveRepairRecordFlattenOriginal.cost rs) := by
  have h := Alphabet.map_hoare (Alphabet.widen 1 a) (ActiveRepairRecordFlattenOriginal.runs rs)
  exact h.consequence (by rintro v rfl; exact ⟨_,rfl,rfl⟩)
    (by rintro v ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem runs_linear (rs : List Partition.Record) (R : ℕ)
    (hw : ∀ r∈rs,r.payload.length≤R) :
    HoareTime (program a) (fun v => v=input a rs) (fun v => v=output a rs)
      (5*rs.length*(R+1)+12) := by
  have h := Alphabet.map_hoare (Alphabet.widen 1 a) (ActiveRepairRecordFlattenOriginal.runs_linear rs R hw)
  exact h.consequence (by rintro v rfl; exact ⟨_,rfl,rfl⟩)
    (by rintro v ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem heads_origin (rs : List Partition.Record) (i : Fin 2) : (output a rs).head i=0 :=
  ActiveRepairRecordFlattenEndpoint.heads_origin rs i

theorem source_blank (rs : List Partition.Record) : (output a rs).tape 0=fun _ => blank := by
  change (fun z => (Alphabet.widen 1 a).encode ((ActiveRepairRecordFlattenEndpoint.output rs).tape 0 z))=_
  rw [ActiveRepairRecordFlattenEndpoint.source_blank]
  rfl

private theorem map_word (xs : List (Fin 5)) (f : ℤ → Fin 5) (p : ℤ) :
    (fun z => (Alphabet.widen 1 a).encode (putWord f p xs z))=
      putWord (fun z => (Alphabet.widen 1 a).encode (f z)) p
        (xs.map (Alphabet.widen 1 a).encode) := by
  induction xs generalizing f p with
  | nil => rfl
  | cons x xs ih =>
    rw [putWord,List.map_cons,putWord]
    funext z
    by_cases hz : z=p
    · subst z; simp
    · simp only [Function.update_of_ne hz]
      exact congrFun (ih f (p+1)) z

theorem output_raw (rs : List Partition.Record) :
    (output a rs).tape 1=putWord (fun _ => blank) 0
      (((rs.map Partition.Record.payload).flatten).map bitSymbol) := by
  change (fun z => (Alphabet.widen 1 a).encode ((ActiveRepairRecordFlattenEndpoint.output rs).tape 1 z))=_
  rw [ActiveRepairRecordFlattenEndpoint.output_raw,map_word,List.map_map]
  rfl

end
end IntegerMultBounds.Machine.ActiveRepairRecordFlattenAlphabet
