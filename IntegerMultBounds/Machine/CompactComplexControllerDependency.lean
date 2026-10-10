import IntegerMultBounds.Machine.CompactComplexControllerChildBudget
import IntegerMultBounds.Machine.CompactRecursiveDependencyBudget

/-! The paid child prefix advances the real occurrence-indexed dependency
Path and installs exactly its child interval and exponent on physical tapes.
This connects geometric dependency accounting to actual controller/header
words; execution of the intervening recursive child remains separate. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerDependency
noncomputable section
open CompactComplexRecursiveGeometry CompactRecursiveDependencyBudget
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State put)
open CompactComplexControllerChildPrefix (native saved)
open CompactComplexControllerNativeFrame (tapes bank controllerSlot nativeSlot)
open RecursiveChildQuotientsConstant (bits)
open Networks.ComplexRecursiveCallSchema (Call)
variable {a s : ℕ}

def exponentPort : Fin (tapes s) := controllerSlot (Fin.castAdd 15 (1 : Fin 28))
def headerPort (i : Fin 28) : Fin (tapes s) := nativeSlot (Fin.castAdd 23 (Fin.castAdd 15 i))

/-- The actual physical exponent, slot width and left/right interval words. -/
def Words (v : Tapes (tapes s) a) (k f left right : ℕ) : Prop :=
  v.head (exponentPort)=1 ∧ v.tape (exponentPort)=RadixZeroFill.encodedBinary (bits k) ∧
  v.head (headerPort 7)=1 ∧ v.tape (headerPort 7)=RadixZeroFill.encodedBinary (bits f) ∧
  v.head (headerPort 8)=1 ∧ v.tape (headerPort 8)=RadixZeroFill.encodedBinary (bits left) ∧
  v.head (headerPort 9)=1 ∧ v.tape (headerPort 9)=RadixZeroFill.encodedBinary (bits right)

theorem words {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) (rows k : ℕ)
    (st : State) (h1 : st 1=some k) (queue : Tapes 1 a) (tail : Tapes 23 a) (storage : Tapes s a) :
    Words (bank (ActiveRepairRankHeadersCommands.bank st) queue (native v rows tail) storage)
      k v.f v.left v.right := by
  simp only [Words,exponentPort,headerPort,bank,controllerSlot,nativeSlot,native,
    ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,
    Fin.addCases_right,Fin.addCases_left]
  simp [ActiveRepairRankHeadersCommands.caller,ActivePrefixStageHeadersData.initial,
    ActivePrefixStageHeadersData.originalValues,h1]


/-- The real occurrence chooses the saved return PC and its actual residual
slot chooses the child. The postcondition certifies both physical words and
all dependency indices, with the complete prefix cost paid. -/
theorem entry {sh : Shape} (rho : Fin sh.chunk) {left k levels frames returned : ℕ}
    (path : Path sh.active left (k+2) levels frames returned) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows : ℕ)
    (headerStack pcStack : Fin s) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 a) (tail : Tapes 23 a) (storage : Tapes s a) :
    let visit := path.visit
    let child := CompactComplexChildHeadersData.child rho visit hactive pair call.slot
    let after := bank (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
      (native child rows tail)
      (saved storage headerStack pcStack call.site call.slot
        (CompactComplexChildHeadersData.parent rho visit hactive pair))
    HoareTime (CompactComplexControllerChildPrefix.program headerStack pcStack call.site call.slot).2
      (fun v => v=bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)
      (fun v => v=after ∧ Words v (k+1) (arity^k)
        (left+call.slot.val*arity^(k+1))
        (sh.active-(left+call.slot.val*arity^(k+1)+arity^(k+1))) ∧
        Path sh.active (left+call.slot.val*arity^(k+1)) (k+1) (levels+1)
          (frames+arity^(k+2)) (returned+precedingCalls call*arity^(k+1)))
      (CompactComplexControllerChildBudget.entryCost
        Networks.ComplexRecursiveCallSchema.sites.length rho visit hactive pair call.slot rows) := by
  dsimp only
  have h := CompactComplexControllerChildPrefix.runs rho path.visit hactive pair call.slot rows
    headerStack pcStack call.site st h1 queue tail storage
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v rfl
  refine ⟨rfl,?_,Path.child path call⟩
  exact words _ rows (k+1) (put st 1 (k+1)) (by simp [put]) queue tail _

/-- After the real return-PC decoder has consumed its frame, the paid parent
restoration recovers exactly the ancestor Path's original geometric words and
exponent while retaining arbitrary computed child payload in the native tail. -/
theorem restore_parent {sh : Shape} (rho : Fin sh.chunk) {left k levels frames returned : ℕ}
    (path : Path sh.active left (k+2) levels frames returned) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (rows : ℕ)
    (headerStack : Fin s) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 a) (tail : Tapes 23 a) (storage : Tapes s a)
    (hb : ∀ z,storage.head headerStack≤z → storage.tape headerStack z=blank) :
    let visit := path.visit
    let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
    let child := CompactComplexChildHeadersData.child rho visit hactive pair call.slot
    let after := bank (ActiveRepairRankHeadersCommands.bank st) queue (native parent rows tail) storage
    HoareTime (CompactComplexControllerChildReturn.program headerStack).2
      (fun v => v=bank (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native child rows tail)
        (CompactComplexControllerHeaderStack.saved storage headerStack
          (CompactComplexControllerChildPrefix.data parent)))
      (fun v => v=after ∧ Words v (k+2) (arity^(k+1)) left
        (sh.active-(left+arity^(k+2))))
      (CompactComplexControllerChildBudget.returnCost rho visit hactive pair call.slot) := by
  dsimp only
  have h := CompactComplexControllerChildReturn.runs rho path.visit hactive pair call.slot rows
    headerStack st h1 queue tail storage hb
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v rfl
  exact ⟨rfl,words _ rows (k+2) st h1 queue tail storage⟩

end
end IntegerMultBounds.Machine.CompactComplexControllerDependency
