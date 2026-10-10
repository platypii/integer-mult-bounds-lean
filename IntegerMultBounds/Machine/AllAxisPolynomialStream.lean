import IntegerMultBounds.Machine.AllAxisPolynomialStreamInit

/-! A complete prepared-stage polynomial phase traversal on66 tapes:
physical immutable ell/header initialization, full-address outer counting,
shared phase coefficient inner counting, and paid final control erasure.
The streams remain serialized with their heads at the actual endpoints. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialStream
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (seq AllAxisPolynomialStreamInit.program (extend (AllAxisPolynomialStreamLoop.loop m ws) 1))
    (extend AllAxisPolynomialStreamClean.program 1)
def output (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (ell : ℕ) :=
  (AllAxisPolynomialStreamClean.output order v rows m ws ctx
    (AllAxisFullStreamInit.readyTail (s := s) rows z) (2^ell) (rows*2^s.bits)).append
      (AllAxisPolynomialStreamInit.scalar ell)

theorem ready (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → ℕ → Context 2) (z : Tapes 4 2) (ell : ℕ) :
    AllAxisPolynomialStreamInit.output order v rows z ell=
      (CountedLoopHeaderClean.bank (AllAxisPolynomialStreamLoop.state order v rows m ws ctx
        (AllAxisFullStreamInit.readyTail (s := s) rows z) (2^ell) 0)).append
          (AllAxisPolynomialStreamInit.scalar ell) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
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
      (fun t => t=AllAxisPolynomialStreamInit.input order v rows z ell)
      (fun t => t=output order v rows m ws ctx z ell)
      (FixedBasePowerDescriptor.constant 2*2^ell+AllAxisFullStreamInit.cost order v rows+1+
        CountedLoopHeaderClean.cost (rows*2^s.bits) (RecursiveChildQuotientsConstant.bits (rows*2^s.bits))
          (AllAxisPolynomialStreamLoop.bodyCost v m (2^ell) w)+1+
        (5*s.bits+11+BinaryDescriptorCleanupList.cost AllAxisPolynomialStreamClean.slots
          (AllAxisPolynomialStreamClean.words (rows*2^s.bits) (2^ell))+1)+1) := by
  let z' := AllAxisFullStreamInit.readyTail (s := s) rows z
  have h0 := AllAxisPolynomialStreamInit.runs order v rows z ell hc hn
  rw [ready order v rows m ws ctx z ell] at h0
  have h1 := hoare_extend_eq (AllAxisPolynomialStreamLoop.runs order v rows (rows*2^s.bits)
    m ws hm hslots hl hspan ctx z' (2^ell) w (by positivity) hw
    (by simpa [z',AllAxisFullStreamInit.readyTail,AllAxisCountTransfer.tailCount,SharedPlacementAlphabet.setTape] using hs)
    ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ hnext hb) (AllAxisPolynomialStreamInit.scalar ell)
  have h2 := hoare_extend_eq (AllAxisPolynomialStreamClean.runs order v rows m ws ctx z'
    (2^ell) (rows*2^s.bits) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩) (AllAxisPolynomialStreamInit.scalar ell)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.AllAxisPolynomialStream
