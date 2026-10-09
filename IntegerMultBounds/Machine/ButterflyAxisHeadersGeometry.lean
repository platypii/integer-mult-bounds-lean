import IntegerMultBounds.Machine.ButterflyAxisHeadersData
import IntegerMultBounds.Machine.ButterflyAxisRun

/-! The synthesized binary words name the exact shape and loop counts consumed
by the native coefficient machine, including fixed signed guard width. -/
namespace IntegerMultBounds.Machine.ButterflyAxisHeadersGeometry
noncomputable section
open ButterflyAxisHeadersData
open RecursiveChildQuotientsConstant (bits)

def descriptor (D t R p : ℕ) := CompactRowHeaders.descriptor (higher D t*2) (rowLength D t R p)
def headerValues (D t R p : ℕ) : Fin 6 → ℕ := ![1,higher D t*2,rowLength D t R p,0,1,1]
def headers (D t R p : ℕ) : Fin 6 → List Bool := fun i => bits (headerValues D t R p i)
def words (D t R p : ℕ) (i : Fin 8) : List Bool :=
  Fin.addCases (m:=2) (n:=6) ![bits (pairCount D t R),bits (streamLength D t R p)] (headers D t R p) i

theorem groups_eq (D t R p : ℕ) : RecursiveInterchangeRows.groups 2 (descriptor D t R p)=higher D t := by
  simp [RecursiveInterchangeRows.groups,descriptor,CompactRowHeaders.descriptor]

theorem row_length (D t R p : ℕ) :
    RecursiveInterchangeRows.rowLength 2 (descriptor D t R p)=lower t R*(2*(ButterflyGuard.width p D+1)) := by
  simp [RecursiveInterchangeRows.rowLength,descriptor,CompactRowHeaders.descriptor,rowLength,recordLength,width_eq,Nat.mul_comm]

theorem descriptor_positive (D t R p : ℕ) (hR : 0<R) : (descriptor D t R p).Positive := by
  have hH : 0<higher D t := pow_pos (by decide) _
  have hN : 0<lower t R := Nat.mul_pos (pow_pos (by decide) _) hR
  simp only [descriptor,CompactRowHeaders.descriptor,RecursiveInterchangeLayout.Descriptor.Positive]
  refine ⟨by decide,by positivity,?_,by decide,by decide⟩
  unfold rowLength recordLength
  positivity

theorem divides (D t R p : ℕ) : 2 ∣ (descriptor D t R p).rows := by
  exact dvd_mul_left 2 (higher D t)

theorem headers_spec (D t R p : ℕ) : RecursiveDimensionBank.Headers (descriptor D t R p) (headers D t R p) := by
  constructor
  · intro i
    fin_cases i <;> simp [headers,headerValues,descriptor,CompactRowHeaders.descriptor,
      RecursiveDimensionBank.values,RecursiveChildQuotientsConstant.bits_value]
  · intro i; exact RecursiveChildQuotientsConstant.bits_canonical _

theorem paired_count (D t R p : ℕ) :
    Counter.value (words D t R p 0)=RecursiveInterchangeRows.groups 2 (descriptor D t R p)*lower t R := by
  simp [words,groups_eq,pairCount,RecursiveChildQuotientsConstant.bits_value,Fin.addCases]

theorem stream_count (D t R p : ℕ) :
    Counter.value (words D t R p 1)=ButterflyStreamCleanData.streamLength
      (RecursiveInterchangeRows.groups 2 (descriptor D t R p)*lower t R) (ButterflyGuard.width p D) := by
  simp [words,groups_eq,streamLength,rowLength,recordLength,ButterflyStreamCleanData.streamLength,
    width_eq,RecursiveChildQuotientsConstant.bits_value,Fin.addCases]
  ring

theorem words_canonical (D t R p : ℕ) (i : Fin 8) : GrowingCounterData.Canonical (words D t R p i) := by
  induction i using (Fin.addCases (m:=2) (n:=6)) with
  | left i => fin_cases i <;> exact RecursiveChildQuotientsConstant.bits_canonical _
  | right i => simpa only [words,Fin.addCases_right,headers] using RecursiveChildQuotientsConstant.bits_canonical (headerValues D t R p i)

end
end IntegerMultBounds.Machine.ButterflyAxisHeadersGeometry
