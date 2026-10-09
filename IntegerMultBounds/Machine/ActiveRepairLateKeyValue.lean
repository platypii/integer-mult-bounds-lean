import IntegerMultBounds.Machine.ActiveRepairLateKeyRun
import IntegerMultBounds.Machine.ActiveRepairLateFieldsValue
import IntegerMultBounds.Machine.ActiveRepairDestinationPatchEndpoint

/-! Exact guard classification and complete original-layout destination of
the physical later-key writer. Local concatenation appears only in the proof. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyValue
noncomputable section
open ActiveRepairLateKeyData ActiveRepairLateKeyData.Data ActiveRepairLateKeyRun
open CompactGadgetReservationShape CompactActiveTargetLayout ActiveRepairRankFieldsGeometry
open BinaryAddressTableData (row)
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

theorem flag_rank (d : Data) (h : Valid d) :
    d.flag=rankFlag (lateRankEquiv d.q d.b d.Z) (lateBadSet d.q d.b d.Z)
      (Counter.value (d.V++d.T++d.U)) := by
  have hz : d.Z.length=d.n := SelectedSourceBitsData.selected_length _ _ _ _
  exact ActiveRepairLateFieldsValue.flag_rank d.q d.b d.hb h.hbq3 d.V d.T d.U d.Z
    (by simp [V,hz,h.hV]) (by simp [T,hz,h.hT]) (by simp [U,hz,h.hU])

theorem repaired_local (d : Data) (h : Valid d) :
    d.target++(d.recoveredT++d.recoveredU)=rankKey (lateRankEquiv d.q d.b d.Z) (lateSperm d.q d.b d.Z)
      (lateTperm d.q d.b d.Z) (d.n*d.q+d.n*d.b+d.n*d.b) (Counter.value (d.V++d.T++d.U)) := by
  have hz : d.Z.length=d.n := SelectedSourceBitsData.selected_length _ _ _ _
  simpa only [Data.target,recoveredT,recoveredU,hz] using
    ActiveRepairLateFieldsValue.destination_bits d.q d.b d.hb d.hbq d.V d.T d.U d.Z
      (by simp [V,hz,h.hV]) (by simp [T,hz,h.hT]) (by simp [U,hz,h.hU])

theorem word_row (xs : List Bool) : xs=row xs.length (Counter.value xs) := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp
  · rw [BinaryAddressTableData.row_rank _ _ (Counter.value_lt xs)]

def repairedTarget (d : Data) (h : Valid d) : Fin (2^(d.widths 0)) :=
  ⟨Counter.value d.target,by simpa only [(lengths d h).1] using Counter.value_lt d.target⟩
def repairedT (d : Data) (h : Valid d) : Fin (2^(d.widths 1)) :=
  ⟨Counter.value d.recoveredT,by simpa only [(lengths d h).2.1] using Counter.value_lt d.recoveredT⟩

def repairedU (d : Data) (h : Valid d) : Fin (2^(d.widths 1)) :=
  ⟨Counter.value d.recoveredU,by
    simpa only [(lengths d h).2.2,(lengths d h).2.1] using Counter.value_lt d.recoveredU⟩

theorem generated_word (d : Data) (h : Valid d)
    (s : Shape) (before after rows rho : ℕ) (hw : d.widths 1≤s.H)
    (ha : before+d.widths 0+after=s.active*s.chunk) (hp : s.payload=1) (hr : rows≤2^rho)
    (x : Address s (d.widths 1) (d.widths 0) before after rows)
    (hc : Counter.value d.cs=(index s (d.widths 1) (d.widths 0) before after rows hw ha x).val)
    (hA : d.A=s.bits+rho) (hsv : d.sv=targetStart s after)
    (hst : d.st=tStart s (d.widths 1) (d.widths 0) before after)
    (hsu : d.su=uStart s (d.widths 1) (d.widths 0) before after) :
    d.destination=row (s.bits+rho)
      (index s (d.widths 1) (d.widths 0) before after rows hw ha
        (ActiveRepairDestinationPatchGeometry.replaced s (d.widths 1) (d.widths 0)
          before after rows x (repairedTarget d h) (repairedT d h) (repairedU d h))).val := by
  have hv : d.target=row (d.widths 0) (repairedTarget d h).val := by
    simpa only [(lengths d h).1,repairedTarget] using word_row d.target
  have ht : d.recoveredT=row (d.widths 1) (repairedT d h).val := by
    simpa only [(lengths d h).2.1,repairedT] using word_row d.recoveredT
  have hu : d.recoveredU=row (d.widths 1) (repairedU d h).val := by
    simpa only [(lengths d h).2.2,(lengths d h).2.1,repairedU] using word_row d.recoveredU
  unfold destination
  rw [hA,hsv,hst,hsu,hv,ht,hu]
  exact ActiveRepairDestinationPatchEndpoint.generated_word s (d.widths 1) (d.widths 0)
    before after rows rho hw ha hp hr x d.cs hc (repairedTarget d h) (repairedT d h) (repairedU d h)

theorem key_tape (d : Data) : d.output.tape 31=
    FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination) := by
  rfl

theorem retained (d : Data) (i : Fin 33) (hi : i≠31) :
    d.output.head i=d.input.head i ∧ d.output.tape i=d.input.tape i := by
  simp [output,SharedPlacementAlphabet.setTape,hi]

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyValue
