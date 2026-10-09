import IntegerMultBounds.Machine.CompactComplexControllerHeaderReturn
import IntegerMultBounds.Machine.CompactComplexControllerReturnStack
import IntegerMultBounds.Machine.CompactComplexControllerExponent
import IntegerMultBounds.Machine.CompactComplexChildHeadersData

/-! Concrete internal-child call entry: save parent descriptors on appended
storage, push the literal occurrence/coordinate PC, decrement the physical
exponent and generate the actual selected child headers. No child descriptor
or runtime return address is supplied as an input tape. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerChildPrefix
noncomputable section
open CompactComplexControllerNativeFrame (tapes)
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State put)
open ActivePrefixStageHeadersData (initial)
open RecursiveChildQuotientsConstant (bits)
variable {a s siteCount : ℕ}

def data {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) : Fin 3 → List Bool :=
  ![bits v.f,bits v.left,bits v.right]
def native {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) (rows : ℕ) (tail : Tapes 23 a) :=
  (ActiveRepairRankHeadersCommands.bank (initial v rows)).append tail

def saved (storage : Tapes s a) (headerStack pcStack : Fin s) (site : Fin siteCount)
    (slot : Fin arity) {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) :=
  CompactComplexControllerReturnStack.saved
    (CompactComplexControllerHeaderStack.saved storage headerStack (data v)) pcStack site slot

def program (headerStack pcStack : Fin s) (site : Fin siteCount) (slot : Fin arity) :
    Σ q, Program (tapes s) q a :=
  ⟨_,seq (seq (seq (CompactComplexControllerHeaderStack.saveProgram headerStack)
    (CompactComplexControllerReturnStack.pushProgram pcStack site slot))
      CompactComplexControllerExponent.program)
        (CompactComplexControllerNativeFrame.program (CompactComplexChildHeadersData.placedProgram slot))⟩

/-- This is an actual paid child-call prefix, not an abstract header update.
It retains original role rows and every native payload/controller spectator. -/
theorem runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack pcStack : Fin s) (site : Fin siteCount) (st : State)
    (h1 : st 1=some (k+2)) (queue : Tapes 1 a) (tail : Tapes 23 a) (storage : Tapes s a) :
    HoareTime (program headerStack pcStack site slot).2
      (fun v => v=CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)
      (fun v => v=CompactComplexControllerNativeFrame.bank
        (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
        (saved storage headerStack pcStack site slot (CompactComplexChildHeadersData.parent rho visit hactive pair)))
      (CompactChildHeadersStack.cost (data (CompactComplexChildHeadersData.parent rho visit hactive pair))+
        CompactComplexCallReturn.addressWidth siteCount arity+20*(k+3)+103+
        CompactChildHeadersArithmetic.scheduleCost (CompactComplexChildHeadersData.schedule slot)
          (initial (CompactComplexChildHeadersData.parent rho visit hactive pair) rows)) := by
  let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
  let child := CompactComplexChildHeadersData.child rho visit hactive pair slot
  let headers := CompactComplexControllerHeaderStack.saved storage headerStack (data parent)
  let stores := CompactComplexControllerReturnStack.saved headers pcStack site slot
  have hs := CompactComplexControllerHeaderStack.save headerStack (ActiveRepairRankHeadersCommands.bank st) queue
    (native parent rows tail) storage (data parent)
    (by intro i; fin_cases i <;> simp [native,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,initial,ActivePrefixStageHeadersData.originalValues,
      Tapes.append,Fin.addCases,data,BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by intro i; fin_cases i <;> simp [native,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,initial,ActivePrefixStageHeadersData.originalValues,Tapes.append,Fin.addCases])
  have hp := CompactComplexControllerReturnStack.push pcStack site slot (ActiveRepairRankHeadersCommands.bank st) queue
    (native parent rows tail) headers
  have hd := CompactComplexControllerExponent.descend st (k+2) (by omega) h1 queue
    (native parent rows tail) stores
  rw [show k+2-1=k+1 by omega] at hd
  have hc := CompactComplexControllerNativeFrame.runs
    (CompactComplexChildHeadersData.runs_framed (a := a) rho visit hactive pair slot rows tail)
    (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue stores
  have h := ((hs.seq hp).seq hd).seq hc
  apply h.consequence (fun _ h => h) (fun _ h => h)
  dsimp only [parent]
  omega

end
end IntegerMultBounds.Machine.CompactComplexControllerChildPrefix
