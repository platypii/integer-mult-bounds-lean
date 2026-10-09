import IntegerMultBounds.Machine.ButterflyAxisHeadersInstall
import IntegerMultBounds.Machine.ButterflyAxisPorts

/-! Lift the complete native axis machine onto the physically installed header
bank. Original shape inputs and generated arithmetic headers are framed; the
axis machine retains only its common stream and the eight real header copies. -/
namespace IntegerMultBounds.Machine.ButterflyAxisPrepared
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry ButterflyAxisHeadersBudget
open ButterflyAxisHeadersInstall (prepared)
open ButterflyStreamData (Coefficient)
open ButterflyStreamSemantics (transformed)

abbrev count := 52+ButterflyAxisPorts.count

def commonPorts : Fin 9 → Fin 52 := Fin.natAdd 43

theorem common_injective : Function.Injective commonPorts := Fin.natAdd_injective _ _

def program := Placement.placed ButterflyAxisRun.program
  (CleanSubbank.placement ButterflyAxisPorts.ports commonPorts common_injective)

def bank (D t R p : ℕ) (f : ℤ → Fin 6) :=
  (prepared D t R p f).append (SharedBank.empty ButterflyAxisPorts.count 2)

theorem payload (D t R p : ℕ) (f : ℤ → Fin 6) :
    SharedBank.payload (prepared D t R p f) commonPorts=
      (CountedLoopReuseAlphabet.one f 0).append
        (ButterflyAxisPorts.headers (words D t R p 0) (words D t R p 1) (headers D t R p)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem frame (D t R p : ℕ) (f g : ℤ → Fin 6) :
    SharedBank.strip (prepared D t R p f) commonPorts=
      SharedBank.strip (prepared D t R p g) commonPorts := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    by_cases hi : ∃ j,commonPorts j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      induction i using (Fin.addCases (m:=44) (n:=8)) with
      | left i =>
        induction i using (Fin.addCases (m:=43) (n:=1)) with
        | left i => simp [prepared,ButterflyAxisHeadersInstall.caller,Tapes.append]
        | right i => fin_cases i; exact (hi ⟨0,rfl⟩).elim
      | right i => simp [prepared,Tapes.append]

theorem volume_eq (D t R p : ℕ) (ht : t<D) :
    RecursiveInterchangeLayout.volume 2 (descriptor D t R p)=logicalVolume D R p := by
  rw [ButterflyAxisHeadersBudget.volume_eq D t R p ht]
  simp only [RecursiveInterchangeLayout.volume,descriptor,CompactRowHeaders.descriptor,
    streamLength,pow_zero,mul_one,one_mul]
  ring

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → Coefficient)
    (hw : ∀ h j k,(xs h j k).1.length=ButterflyGuard.width p D ∧
      (xs h j k).2.length=ButterflyGuard.width p D) :
    HoareTime program (fun z => z=bank D t R p (ButterflyAxisBank.word xs))
      (fun z => z=bank D t R p (ButterflyAxisBank.word (transformed xs)))
      (ButterflyAxisRun.constant*logicalVolume D R p) := by
  have hh := ButterflyAxisRun.runs_linear (headers D t R p) (headers_spec D t R p)
    (descriptor_positive D t R p hR) (divides D t R p) xs (ButterflyGuard.width p D) hw
    (row_length D t R p) (words D t R p 0) (words D t R p 1)
    (paired_count D t R p) (stream_count D t R p) (words_canonical D t R p 0) (words_canonical D t R p 1)
  rw [volume_eq D t R p ht] at hh
  apply CleanSubbank.realizes (c:=9) (s:=ButterflyAxisPorts.count) (k:=52) ButterflyAxisRun.program
    ButterflyAxisPorts.ports commonPorts ButterflyAxisPorts.injective common_injective
    (prepared D t R p (ButterflyAxisBank.word xs)) (prepared D t R p (ButterflyAxisBank.word (transformed xs)))
    _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · rw [ButterflyAxisPorts.payload,payload]
  · rw [ButterflyAxisPorts.payload,payload]
  · exact ButterflyAxisPorts.clean _ _ _ _
  · exact ButterflyAxisPorts.clean _ _ _ _
  · exact frame D t R p _ _

end
end IntegerMultBounds.Machine.ButterflyAxisPrepared
