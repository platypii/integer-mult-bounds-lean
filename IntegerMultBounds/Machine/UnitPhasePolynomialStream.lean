import IntegerMultBounds.Machine.UnitPhasePolynomialStreamInit

/-! A complete prepared-stage polynomial phase traversal on66 tapes:
physical immutable ell/header initialization, full-address outer counting,
shared phase coefficient inner counting, and paid final control erasure.
The streams remain serialized with their heads at the actual endpoints. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialStream
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (seq UnitPhasePolynomialStreamInit.program (extend (UnitPhasePolynomialStreamLoop.loop m ws) 1))
    (extend UnitPhasePolynomialStreamClean.program 1)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (ell : ℕ) :=
  (UnitPhasePolynomialStreamClean.output order v rows axis m ws ctx
    (UnitPhaseFullStreamInit.readyTail (s := s) rows z) (2^ell) (rows*2^s.bits)).append
      (UnitPhasePolynomialStreamInit.scalar ell)

theorem ready (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (ell : ℕ) :
    UnitPhasePolynomialStreamInit.output order v rows axis z ell=
      (CountedLoopHeaderClean.bank (UnitPhasePolynomialStreamLoop.state order v rows axis m ws ctx
        (UnitPhaseFullStreamInit.readyTail (s := s) rows z) (2^ell) 0)).append
          (UnitPhasePolynomialStreamInit.scalar ell) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (ell w : ℕ)
    (hw : ∀ i<rows*2^s.bits,∀ j<2^ell,(ctx i j).re.length=w ∧ (ctx i j).im.length=w)
    (hs : z.tape 0=(ctx 0 0).tape ∧ z.head 0=(ctx 0 0).start)
    (hc : z.tape 1=(fun _ => blank) ∧ z.head 1=0)
    (hn : z.tape 3=(fun _ => blank) ∧ z.head 3=0)
    (hnext : ∀ i<rows*2^s.bits,∀ j,j+1<2^ell → (ctx i (j+1)).tape=(ctx i j).tape ∧
      (ctx i (j+1)).start=(ctx i j).start+(ctx i j).re.length+(ctx i j).im.length+2)
    (hb : ∀ i,i+1<rows*2^s.bits → (ctx (i+1) 0).tape=(ctx i (2^ell-1)).tape ∧
      (ctx (i+1) 0).start=(ctx i (2^ell-1)).start+(ctx i (2^ell-1)).re.length+(ctx i (2^ell-1)).im.length+2) :
    HoareTime (program m ws)
      (fun t => t=UnitPhasePolynomialStreamInit.input order v rows axis z ell)
      (fun t => t=output order v rows axis m ws ctx z ell)
      (FixedBasePowerDescriptor.constant 2*2^ell+UnitPhaseFullStreamInit.cost order v rows axis+1+
        CountedLoopHeaderClean.cost (rows*2^s.bits) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
          (UnitPhasePolynomialStreamLoop.bodyCost v axis m (2^ell) w)+1+
        (5*s.bits+11+BinaryDescriptorCleanupList.cost UnitPhasePolynomialStreamClean.slots
          (UnitPhasePolynomialStreamClean.words (rows*2^s.bits) (2^ell))+1)+1) := by
  let z' := UnitPhaseFullStreamInit.readyTail (s := s) rows z
  have h0 := UnitPhasePolynomialStreamInit.runs order v rows axis z ell hc hn
  rw [ready order v rows axis m ws ctx z ell] at h0
  have h1 := hoare_extend_eq (UnitPhasePolynomialStreamLoop.runs order v rows (rows*2^s.bits)
    axis m ws hm hslots hl hspan ctx z' (2^ell) w (by positivity) hw
    (by simpa [z',UnitPhaseFullStreamInit.readyTail,UnitPhaseCountTransfer.tailCount,SharedPlacementAlphabet.setTape] using hs)
    ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ hnext hb) (UnitPhasePolynomialStreamInit.scalar ell)
  have h2 := hoare_extend_eq (UnitPhasePolynomialStreamClean.runs order v rows axis m ws ctx z'
    (2^ell) (rows*2^s.bits) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩) (UnitPhasePolynomialStreamInit.scalar ell)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.UnitPhasePolynomialStream
