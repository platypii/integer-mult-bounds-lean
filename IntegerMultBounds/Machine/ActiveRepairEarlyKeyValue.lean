import IntegerMultBounds.Machine.ActiveRepairEarlyKeyRun
import IntegerMultBounds.Machine.ActiveRepairEarlyFieldsValue
import IntegerMultBounds.Machine.ActiveRepairDestinationPatchEndpoint

/-! Exact guard classification and complete original-layout destination of
the physical early-key writer. Local concatenation appears only in the proof. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyValue
noncomputable section
open ActiveRepairEarlyKeyData ActiveRepairEarlyKeyData.Data ActiveRepairEarlyKeyRun
open CompactGadgetReservationShape CompactActiveTargetLayout ActiveRepairRankFieldsGeometry
open BinaryAddressTableData (row)
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

theorem flag_rank (d : Data) (h : Valid d) :
    d.flag=rankFlag (rankEquiv d.q d.b d.Z) (badSet d.q d.b d.Z)
      (Counter.value (d.V++d.T)) := by
  have hz : d.Z.length=d.n := SelectedSourceBitsData.selected_length _ _ _ _
  exact ActiveRepairEarlyFieldsValue.flag_rank d.q d.b d.hb h.hbq3 d.V d.T d.Z
    (by simp [V,hz,h.hV]) (by simp [T,hz,h.hT])

theorem repaired_local (d : Data) (h : Valid d) :
    d.target++d.recoveredT=rankKey (rankEquiv d.q d.b d.Z) (Sperm d.q d.b d.Z)
      (Tperm d.q d.b d.Z) (d.n*d.q+d.n*d.b) (Counter.value (d.V++d.T)) := by
  have hz : d.Z.length=d.n := SelectedSourceBitsData.selected_length _ _ _ _
  simpa only [Data.target,recoveredT,hz] using
    ActiveRepairEarlyFieldsValue.destination_bits d.q d.b d.hb d.hbq d.V d.T d.Z
      (by simp [V,hz,h.hV]) (by simp [T,hz,h.hT])

theorem word_row (xs : List Bool) : xs=row xs.length (Counter.value xs) := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp
  · rw [BinaryAddressTableData.row_rank _ _ (Counter.value_lt xs)]

def repairedTarget (d : Data) (h : Valid d) : Fin (2^(d.widths 0)) :=
  ⟨Counter.value d.target,by simpa only [(lengths d h).1] using Counter.value_lt d.target⟩
def repairedT (d : Data) (h : Valid d) : Fin (2^(d.widths 1)) :=
  ⟨Counter.value d.recoveredT,by simpa only [(lengths d h).2.1] using Counter.value_lt d.recoveredT⟩

theorem generated_word (d : Data) (h : Valid d)
    (s : Shape) (before after rows rho : ℕ) (hw : d.widths 1≤s.H)
    (ha : before+d.widths 0+after=s.active*s.chunk) (hp : s.payload=1) (hr : rows≤2^rho)
    (x : Address s (d.widths 1) (d.widths 0) before after rows)
    (hc : Counter.value d.cs=(index s (d.widths 1) (d.widths 0) before after rows hw ha x).val)
    (hA : d.A=s.bits+rho) (hsv : d.sv=targetStart s after)
    (hst : d.st=tStart s (d.widths 1) (d.widths 0) before after)
    (hsu : d.su=uStart s (d.widths 1) (d.widths 0) before after)
    (hU : d.starts 2=uStart s (d.widths 1) (d.widths 0) before after) :
    d.destination=row (s.bits+rho)
      (index s (d.widths 1) (d.widths 0) before after rows hw ha
        (ActiveRepairDestinationPatchGeometry.replaced s (d.widths 1) (d.widths 0)
          before after rows x (repairedTarget d h) (repairedT d h) x.u)).val := by
  have hv : d.target=row (d.widths 0) (repairedTarget d h).val := by
    simpa only [(lengths d h).1,repairedTarget] using word_row d.target
  have ht : d.recoveredT=row (d.widths 1) (repairedT d h).val := by
    simpa only [(lengths d h).2.1,repairedT] using word_row d.recoveredT
  have hu : d.U=row (d.widths 1) x.u.val := by
    have he : d.widths 2=d.widths 1 := h.hU.trans h.hT.symm
    rw [U,hU,he]
    exact ActiveRepairRankFieldsGeometry.u_word s (d.widths 1) (d.widths 0)
      before after rows hw ha hp x d.cs hc
  unfold destination
  rw [hA,hsv,hst,hsu,hv,ht,hu]
  exact ActiveRepairDestinationPatchEndpoint.generated_word s (d.widths 1) (d.widths 0)
    before after rows rho hw ha hp hr x d.cs hc (repairedTarget d h) (repairedT d h) x.u

theorem key_tape (d : Data) : d.output.tape 30=
    FlagCopy.keyTape (FlagCopy.keyWord d.flag d.destination) := by
  rfl

theorem retained (d : Data) (i : Fin 32) (hi : i≠30) :
    d.output.head i=d.input.head i ∧ d.output.tape i=d.input.tape i := by
  simp [output,SharedPlacementAlphabet.setTape,hi]

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyValue
