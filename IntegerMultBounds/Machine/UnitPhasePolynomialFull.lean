import IntegerMultBounds.Machine.UnitPhasePolynomialRestore
import IntegerMultBounds.Machine.UnitPhaseRecordAddress

/-! A polynomial body physically reads and advances the live address once,
then shares that address's phase over all coefficients. The polynomial
multiplicity and outer address count are retained for the next iteration. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialFull
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (extend UnitPhaseRecordAddress.program 3) (UnitPhasePolynomialRecord.program m ws)
def advanced (W i : ℕ) (z : Tapes 4 2) := setTape z 1 (binary (row W (i+1))) 1

def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  UnitPhasePolynomialRecord.output order v rows axis m ws (row s.bits i) (advanced s.bits i z) ctx R

def nextTail (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  UnitPhasePolynomialRestore.nextTail order v rows axis m ws (row s.bits i) (advanced s.bits i z) ctx R

private theorem addressed (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (old : List Bool) (i : ℕ) (z : Tapes 4 2) :
    UnitPhaseRecordAddress.output
      ((SparsePhaseFlagsCaller.input order v rows axis old (SharedBank.empty 6 2)).append z) s.bits i=
    ((SparsePhaseFlagsCaller.input order v rows axis (row s.bits i) (SharedBank.empty 6 2)).append (advanced s.bits i z)) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

theorem restored (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    output order v rows axis m ws i z ctx R=
    UnitPhasePolynomialRecord.initial order v rows axis (row s.bits i)
      (nextTail order v rows axis m ws i z ctx R) R :=
  UnitPhasePolynomialRestore.restored _ _ _ _ _ _ _ _ _ _

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (old : List Bool) (hold : old.length=s.bits) (i : ℕ)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (z : Tapes 4 2) (ctx : ℕ → Context 2) (R w : ℕ)
    (hw : ∀ j<R,(ctx j).re.length=w ∧ (ctx j).im.length=w)
    (hs : z.tape 0=(ctx 0).tape ∧ z.head 0=(ctx 0).start)
    (hc : z.tape 1=binary (row s.bits i) ∧ z.head 1=1)
    (hnext : ∀ j,j+1<R → (ctx (j+1)).tape=(ctx j).tape ∧
      (ctx (j+1)).start=(ctx j).start+(ctx j).re.length+(ctx j).im.length+2) :
    HoareTime (program m ws)
      (fun t => t=UnitPhasePolynomialRecord.initial order v rows axis old z R)
      (fun t => t=output order v rows axis m ws i z ctx R)
      (5*s.bits+10 + (10400*(s.bits+1)+2*m+4 +
        (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+35) +
        UnitPhaseControlReset.cost (UnitPhaseRecordKernel.selected v axis m (row s.bits i))
          (UnitPhaseRecordKernel.headerWords v axis m)+2)+1) := by
  have h0 := hoare_extend_eq (UnitPhaseRecordAddress.runs
    ((SparsePhaseFlagsCaller.input order v rows axis old (SharedBank.empty 6 2)).append z)
    s.bits i old hold
    (by simpa [Tapes.append,Fin.addCases] using hc) ⟨rfl,rfl⟩)
    ((UnitPhasePolynomialRecord.multiplicity R).append (SharedBank.empty 2 2))
  rw [addressed] at h0
  have h1 := UnitPhasePolynomialRecord.runs order v rows axis m ws hm hslots hl
    (row s.bits i) (BinaryAddressTableData.row_length _ _) (by simpa only [BinaryAddressTableData.row_length] using hspan)
    (advanced s.bits i z) ctx R w hw (by simpa [advanced,setTape] using hs) hnext
  have hinput : UnitPhasePolynomialRecord.initial order v rows axis old z R=
      ((SparsePhaseFlagsCaller.input order v rows axis old (SharedBank.empty 6 2)).append z).append
        ((UnitPhasePolynomialRecord.multiplicity R).append (SharedBank.empty 2 2)) := by
    apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl
  have hready : UnitPhasePolynomialRecord.initial order v rows axis (row s.bits i) (advanced s.bits i z) R=
      ((SparsePhaseFlagsCaller.input order v rows axis (row s.bits i) (SharedBank.empty 6 2)).append (advanced s.bits i z)).append
        ((UnitPhasePolynomialRecord.multiplicity R).append (SharedBank.empty 2 2)) := by
    apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl
  rw [← hready,← hinput] at h0
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.UnitPhasePolynomialFull
