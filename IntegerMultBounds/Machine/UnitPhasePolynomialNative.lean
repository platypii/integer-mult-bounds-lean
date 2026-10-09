import IntegerMultBounds.Machine.UnitPhasePolynomialSourceEndpoint
import IntegerMultBounds.Machine.UnitPhaseFullStreamNormalized
import IntegerMultBounds.Machine.BlankWordOverwriteAt

/-! Literal polynomial phase machine with native stream reuse: traverse the
whole array, physically rewind both streams, copy the equal-width result
back into the original source, erase temporary output, and return heads0. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialNative
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape)
open UnitPhaseFullStreamNormalized (serialized nonblank length)
open UnitPhasePolynomialLiteralEndpoint (result)
variable {s : Shape}

def rewinds := seq (BlankWordReturnAt.program (a := 2) (56 : Fin 66)) (BlankWordReturnAt.program (a := 2) (58 : Fin 66))
def overwrite := BlankWordOverwriteAt.program (a := 2) (56 : Fin 66) 58 (by decide)
def program (m : ℕ) (ws : List (ZMod 4)) := seq (UnitPhasePolynomialStream.program m ws) (seq rewinds overwrite)
def raw (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  UnitPhasePolynomialStream.output order v rows axis m ws
    (UnitPhasePolynomialLiteral.contexts (fun _ => blank) 0 xs)
    (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell

def rewindSource (z : Tapes 66 2) (xs : List (Fin 6)) := setTape z 56 (putWord (fun _ => blank) 0 xs) 0
def rewindBoth (z : Tapes 66 2) (xs ys : List (Fin 6)) := setTape (rewindSource z xs) 58 (putWord (fun _ => blank) 0 ys) 0
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  BlankWordOverwriteAt.output (rewindBoth (raw order v rows axis m ws ell xs)
    (serialized xs) (serialized (result v axis m ws xs))) 56 58 (serialized (result v axis m ws xs))

def cost (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m ell w : ℕ) :=
  FixedBasePowerDescriptor.constant 2*2^ell+UnitPhaseFullStreamInit.cost order v rows axis+1+
    CountedLoopHeaderClean.cost (rows*2^s.bits) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
      (UnitPhasePolynomialStreamLoop.bodyCost v axis m (2^ell) w)+1+
    (5*s.bits+11+BinaryDescriptorCleanupList.cost UnitPhasePolynomialStreamClean.slots
      (UnitPhasePolynomialStreamClean.words (rows*2^s.bits) (2^ell))+1)+1+
    5*((rows*2^s.bits)*2^ell)*(2*(w+1))+13

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    HoareTime (program m ws)
      (fun t => t=UnitPhasePolynomialStreamInit.input order v rows axis
        (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 xs) ell)
      (fun t => t=output order v rows axis m ws ell xs) (cost order v rows axis m ell w) := by
  let z := raw order v rows axis m ws ell xs
  let ys := serialized (result v axis m ws xs)
  have h0 := UnitPhasePolynomialLiteral.runs order v rows hr axis m ws hm hslots hl hspan
    (fun _ => blank) (fun _ => blank) 0 0 ell w xs hw
  have hs := UnitPhasePolynomialSourceEndpoint.endpoint order v rows hr axis m ws
    (fun _ => blank) (fun _ => blank) 0 0 ell w xs hw
  have ho := UnitPhasePolynomialLiteralEndpoint.endpoint order v rows axis m ws
    (fun _ => blank) (fun _ => blank) 0 0 ell w xs hw
  have hwidth := UnitPhasePolynomialLiteralEndpoint.result_width v axis m ws xs w hw
  have hlen : (serialized xs).length=ys.length := by rw [length xs w hw,length _ w hwidth]
  have h1 := BlankWordReturnAt.runs z (56 : Fin 66) (serialized xs) (nonblank xs) hs.1
    (by rw [length xs w hw]; simpa [z,raw] using hs.2)
  have h2 := BlankWordReturnAt.runs (rewindSource z (serialized xs)) (58 : Fin 66) ys (nonblank _) ho.1
    (by rw [length _ w hwidth]; simpa [rewindSource,setTape,z,raw] using ho.2)
  have h3 := BlankWordOverwriteAt.runs (rewindBoth z (serialized xs) ys) (56 : Fin 66) 58 (by decide)
    (serialized xs) ys hlen (nonblank _) (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
  apply (h0.seq ((h1.seq h2).seq h3)).consequence (fun _ h => h) (fun _ h => h) _
  unfold cost
  dsimp only [ys]
  rw [length xs w hw,length _ w hwidth]
  nlinarith

theorem restored (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    output order v rows axis m ws ell xs=
      UnitPhasePolynomialStreamInit.input order v rows axis
        (UnitPhasePolynomialLiteral.tail (fun _ => blank) (fun _ => blank) 0 0 (result v axis m ws xs)) ell := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4)) (ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    (output order v rows axis m ws ell xs).tape 56=putWord (fun _ => blank) 0 (serialized (result v axis m ws xs)) ∧
    (output order v rows axis m ws ell xs).head 56=0 ∧
    (output order v rows axis m ws ell xs).tape 58=(fun _ => blank) ∧
    (output order v rows axis m ws ell xs).head 58=0 ∧
    (output order v rows axis m ws ell xs).tape 65=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits ell) ∧
    (output order v rows axis m ws ell xs).head 65=1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.UnitPhasePolynomialNative
