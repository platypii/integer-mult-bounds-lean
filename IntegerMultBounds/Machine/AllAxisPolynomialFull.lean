import IntegerMultBounds.Machine.AllAxisPolynomialRestore
import IntegerMultBounds.Machine.UnitPhaseRecordAddress

/-! A polynomial body physically reads and advances the live address once,
then shares that address's phase over all coefficients. The polynomial
multiplicity and outer address count are retained for the next iteration. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialFull
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
  seq (extend UnitPhaseRecordAddress.program 3) (AllAxisPolynomialRecord.program m ws)
def advanced (W i : ℕ) (z : Tapes 4 2) := setTape z 1 (binary (row W (i+1))) 1

def output (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  AllAxisPolynomialRecord.output order v rows m ws (row s.bits i) (advanced s.bits i z) ctx R

def nextTail (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :=
  AllAxisPolynomialRestore.nextTail order v rows m ws (row s.bits i) (advanced s.bits i z) ctx R

private theorem addressed (order : Order) (v : Stage s) (rows : ℕ)
    (old : List Bool) (i : ℕ) (z : Tapes 4 2) :
    UnitPhaseRecordAddress.output
      ((AllAxisPhaseFlagsCaller.input order v rows old (SharedBank.empty 6 2)).append z) s.bits i=
    ((AllAxisPhaseFlagsCaller.input order v rows (row s.bits i) (SharedBank.empty 6 2)).append (advanced s.bits i z)) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

theorem restored (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (i : ℕ) (z : Tapes 4 2) (ctx : ℕ → Context 2) (R : ℕ) :
    output order v rows m ws i z ctx R=
    AllAxisPolynomialRecord.initial order v rows (row s.bits i)
      (nextTail order v rows m ws i z ctx R) R :=
  AllAxisPolynomialRestore.restored _ _ _ _ _ _ _ _ _

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (old : List Bool) (hold : old.length=s.bits) (i : ℕ)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (z : Tapes 4 2) (ctx : ℕ → Context 2) (R w : ℕ)
    (hw : ∀ j<R,(ctx j).re.length=w ∧ (ctx j).im.length=w)
    (hs : z.tape 0=(ctx 0).tape ∧ z.head 0=(ctx 0).start)
    (hc : z.tape 1=binary (row s.bits i) ∧ z.head 1=1)
    (hnext : ∀ j,j+1<R → (ctx (j+1)).tape=(ctx j).tape ∧
      (ctx (j+1)).start=(ctx j).start+(ctx j).re.length+(ctx j).im.length+2) :
    HoareTime (program m ws)
      (fun t => t=AllAxisPolynomialRecord.initial order v rows old z R)
      (fun t => t=output order v rows m ws i z ctx R)
      (5*s.bits+10 + (10400*(s.bits+1)+m*(7*v.f+11*(RecursiveChildQuotientsConstant.bits v.f).length+36)+4 +
        (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+35) +
        UnitPhaseControlReset.cost (AllAxisPhaseFlagsCaller.controls v m (row s.bits i))
          (AllAxisPhaseFlagsEndpoint.headerWords v m)+2)+1) := by
  have h0 := hoare_extend_eq (UnitPhaseRecordAddress.runs
    ((AllAxisPhaseFlagsCaller.input order v rows old (SharedBank.empty 6 2)).append z)
    s.bits i old hold
    (by simpa [Tapes.append,Fin.addCases] using hc) ⟨rfl,rfl⟩)
    ((AllAxisPolynomialRecord.multiplicity R).append (SharedBank.empty 2 2))
  rw [addressed] at h0
  have h1 := AllAxisPolynomialRecord.runs order v rows m ws hm hslots hl
    (row s.bits i) (BinaryAddressTableData.row_length _ _) (by simpa only [BinaryAddressTableData.row_length] using hspan)
    (advanced s.bits i z) ctx R w hw (by simpa [advanced,setTape] using hs) hnext
  have hinput : AllAxisPolynomialRecord.initial order v rows old z R=
      ((AllAxisPhaseFlagsCaller.input order v rows old (SharedBank.empty 6 2)).append z).append
        ((AllAxisPolynomialRecord.multiplicity R).append (SharedBank.empty 2 2)) := by
    apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl
  have hready : AllAxisPolynomialRecord.initial order v rows (row s.bits i) (advanced s.bits i z) R=
      ((AllAxisPhaseFlagsCaller.input order v rows (row s.bits i) (SharedBank.empty 6 2)).append (advanced s.bits i z)).append
        ((AllAxisPolynomialRecord.multiplicity R).append (SharedBank.empty 2 2)) := by
    apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl
  rw [← hready,← hinput] at h0
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by rw [←hl]; omega)

end
end IntegerMultBounds.Machine.AllAxisPolynomialFull
